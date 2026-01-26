{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RecordWildCards #-}

-- | Loop Fusion and Fission optimizations.
--
-- == Loop Fusion
-- Merges adjacent loops that iterate over the same range:
-- @
-- for (i = 0; i < n; i++) { A[i] = ...; }
-- for (i = 0; i < n; i++) { B[i] = ...; }
-- @
-- becomes:
-- @
-- for (i = 0; i < n; i++) { A[i] = ...; B[i] = ...; }
-- @
--
-- == Loop Fission
-- Splits loops with independent operations for better cache behavior:
-- @
-- for (i = 0; i < n; i++) { A[i] = ...; B[i] = ...; }  // independent
-- @
-- becomes two separate loops if it improves locality.
--
module LiveOak.LoopFusion
  ( -- * Loop Fusion
    fuseLoops
  , FusionResult(..)

    -- * Loop Fission
  , fissLoops
  , FissionResult(..)

    -- * Analysis
  , canFuse
  , shouldFiss
  ) where

import LiveOak.SSATypes
import LiveOak.CFG
import LiveOak.Loop
import LiveOak.Dominance (DomTree, computeDominators)
import LiveOak.Alias (PointsToInfo, computePointsTo, queryAlias, mayAlias)
import LiveOak.Ast (BinaryOp(..))

import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Set (Set)
import qualified Data.Set as Set
import Data.List (foldl', partition)
import Data.Maybe (mapMaybe)

--------------------------------------------------------------------------------
-- Types
--------------------------------------------------------------------------------

-- | Loop fusion result
data FusionResult = FusionResult
  { fuseOptBlocks :: ![SSABlock]
  , fuseFused :: !Int            -- ^ Number of loop pairs fused
  } deriving (Show)

-- | Loop fission result
data FissionResult = FissionResult
  { fissOptBlocks :: ![SSABlock]
  , fissSplit :: !Int            -- ^ Number of loops split
  } deriving (Show)

-- | Loop characteristics for fusion analysis
data LoopCharacteristics = LoopCharacteristics
  { lcHeader :: !BlockId
  , lcPreheader :: !(Maybe BlockId)
  , lcLatch :: ![BlockId]
  , lcBound :: !(Maybe LoopBound)     -- ^ Loop bound expression
  , lcInductionVar :: !(Maybe String) -- ^ Primary induction variable
  , lcBody :: !(Set BlockId)
  , lcExits :: ![BlockId]
  } deriving (Show)

-- | Loop bound information
data LoopBound = LoopBound
  { lbStart :: !SSAExpr          -- ^ Initial value
  , lbEnd :: !SSAExpr            -- ^ End condition
  , lbStep :: !Int               -- ^ Step value
  } deriving (Eq, Show)

--------------------------------------------------------------------------------
-- Loop Fusion
--------------------------------------------------------------------------------

-- | Fuse adjacent compatible loops
fuseLoops :: SSAMethod -> FusionResult
fuseLoops method =
  let cfg = buildCFG method
      domTree = computeDominators cfg
      loopNest = findLoops cfg domTree
      blocks = ssaMethodBlocks method
      blockMap = Map.fromList [(blockLabel b, b) | b <- blocks]
      ptInfo = computePointsTo method

      -- Find fusable loop pairs
      loopChars = Map.map (analyzeLoop cfg blockMap) loopNest
      fusablePairs = findFusablePairs cfg loopChars ptInfo blockMap

      -- Apply fusion
      (optimized, count) = applyFusions fusablePairs blockMap
  in FusionResult
    { fuseOptBlocks = Map.elems optimized
    , fuseFused = count
    }

-- | Analyze loop characteristics
analyzeLoop :: CFG -> Map BlockId SSABlock -> Loop -> LoopCharacteristics
analyzeLoop cfg blockMap loop =
  let header = loopHeader loop
      headerBlock = Map.lookup header blockMap
      bound = headerBlock >>= extractLoopBound
      iv = headerBlock >>= extractInductionVar loop
  in LoopCharacteristics
    { lcHeader = header
    , lcPreheader = loopPreheader loop
    , lcLatch = loopLatches loop
    , lcBound = bound
    , lcInductionVar = iv
    , lcBody = loopBody loop
    , lcExits = loopExits cfg loop
    }

-- | Extract loop bound from header block
extractLoopBound :: SSABlock -> Maybe LoopBound
extractLoopBound SSABlock{..} =
  case findBranch blockInstrs of
    Just (SSABranch (SSABinary op (SSAUse _iv) bound) _ _) ->
      case op of
        Lt -> Just $ LoopBound (SSAInt 0) bound 1
        Le -> Just $ LoopBound (SSAInt 0) bound 1
        _ -> Nothing
    _ -> Nothing
  where
    findBranch [] = Nothing
    findBranch (i@SSABranch{} : _) = Just i
    findBranch (_:rest) = findBranch rest

-- | Extract primary induction variable
extractInductionVar :: Loop -> SSABlock -> Maybe String
extractInductionVar loop SSABlock{..} =
  case blockPhis of
    (phi:_) | isInductionPhi loop phi -> Just $ varNameString (ssaName (phiVar phi))
    _ -> Nothing
  where
    isInductionPhi l PhiNode{..} =
      let (outside, inside) = partition (\(p, _) -> not (Set.member p (loopBody l))) phiArgs
      in length outside == 1 && length inside == 1

-- | Find pairs of loops that can be fused
findFusablePairs :: CFG -> Map BlockId LoopCharacteristics -> PointsToInfo
                 -> Map BlockId SSABlock -> [(BlockId, BlockId)]
findFusablePairs cfg loopChars ptInfo blockMap =
  [(h1, h2) | h1 <- Map.keys loopChars
            , h2 <- Map.keys loopChars
            , h1 /= h2
            , areAdjacent cfg h1 h2 loopChars
            , canFuse ptInfo blockMap (loopChars Map.! h1) (loopChars Map.! h2)]

-- | Check if two loops are adjacent (first exits to second's preheader)
areAdjacent :: CFG -> BlockId -> BlockId -> Map BlockId LoopCharacteristics -> Bool
areAdjacent cfg h1 h2 loopChars =
  case (Map.lookup h1 loopChars, Map.lookup h2 loopChars) of
    (Just lc1, Just lc2) ->
      case lcPreheader lc2 of
        Just preheader -> preheader `elem` lcExits lc1
        Nothing -> False
    _ -> False

-- | Check if two loops can be fused
canFuse :: PointsToInfo -> Map BlockId SSABlock -> LoopCharacteristics -> LoopCharacteristics -> Bool
canFuse ptInfo blockMap lc1 lc2 =
  -- Same bounds
  sameBounds lc1 lc2
  -- No dependencies between loop bodies
  && noDependencies ptInfo blockMap lc1 lc2

-- | Check if loops have same bounds
sameBounds :: LoopCharacteristics -> LoopCharacteristics -> Bool
sameBounds lc1 lc2 =
  case (lcBound lc1, lcBound lc2) of
    (Just b1, Just b2) -> b1 == b2
    _ -> False

-- | Check for dependencies between loop bodies
noDependencies :: PointsToInfo -> Map BlockId SSABlock -> LoopCharacteristics -> LoopCharacteristics -> Bool
noDependencies ptInfo blockMap lc1 lc2 =
  let body1Blocks = [b | bid <- Set.toList (lcBody lc1), Just b <- [Map.lookup bid blockMap]]
      body2Blocks = [b | bid <- Set.toList (lcBody lc2), Just b <- [Map.lookup bid blockMap]]
      writes1 = collectWrites body1Blocks
      writes2 = collectWrites body2Blocks
      reads1 = collectReads body1Blocks
      reads2 = collectReads body2Blocks
      -- Check RAW: writes in loop1 read by loop2
      raw = not $ any (\w -> any (mayAliasAccess ptInfo w) reads2) writes1
      -- Check WAR: reads in loop1 written by loop2
      war = not $ any (\r -> any (mayAliasAccess ptInfo r) writes2) reads1
      -- Check WAW: writes in both loops
      waw = not $ any (\w1 -> any (mayAliasAccess ptInfo w1) writes2) writes1
  in raw && war && waw

-- | Memory access for dependence checking
data MemAccess = MemAccess
  { maBase :: !SSAExpr
  , maField :: !String
  } deriving (Eq, Show)

-- | Collect writes from blocks
collectWrites :: [SSABlock] -> [MemAccess]
collectWrites = concatMap blockWrites
  where
    blockWrites SSABlock{..} = mapMaybe instrWrite blockInstrs
    instrWrite (SSAFieldStore target field _ _) = Just $ MemAccess target field
    instrWrite _ = Nothing

-- | Collect reads from blocks
collectReads :: [SSABlock] -> [MemAccess]
collectReads = concatMap blockReads
  where
    blockReads SSABlock{..} = concatMap instrReads blockInstrs
    instrReads (SSAAssign _ expr) = exprReads expr
    instrReads _ = []
    exprReads (SSAFieldAccess target field) = [MemAccess target field]
    exprReads (SSABinary _ l r) = exprReads l ++ exprReads r
    exprReads (SSAUnary _ e) = exprReads e
    exprReads _ = []

-- | Check if two memory accesses may alias
mayAliasAccess :: PointsToInfo -> MemAccess -> MemAccess -> Bool
mayAliasAccess ptInfo a1 a2 =
  maField a1 == maField a2 && mayAlias (queryAlias ptInfo (maBase a1) (maBase a2))

-- | Apply loop fusions
applyFusions :: [(BlockId, BlockId)] -> Map BlockId SSABlock -> (Map BlockId SSABlock, Int)
applyFusions pairs blockMap = foldl' applyOneFusion (blockMap, 0) pairs

-- | Apply a single fusion
applyOneFusion :: (Map BlockId SSABlock, Int) -> (BlockId, BlockId) -> (Map BlockId SSABlock, Int)
applyOneFusion (blockMap, count) (h1, h2) =
  case (Map.lookup h1 blockMap, Map.lookup h2 blockMap) of
    (Just block1, Just block2) ->
      let -- Merge body instructions
          merged = mergeLoopBodies block1 block2
          -- Update block map: replace first loop's body, remove second
          blockMap' = Map.insert h1 merged blockMap
      in (blockMap', count + 1)
    _ -> (blockMap, count)

-- | Merge two loop bodies
mergeLoopBodies :: SSABlock -> SSABlock -> SSABlock
mergeLoopBodies b1 b2 =
  b1 { blockInstrs = blockInstrs b1 ++ blockInstrs b2 }

--------------------------------------------------------------------------------
-- Loop Fission
--------------------------------------------------------------------------------

-- | Split loops with independent operations
fissLoops :: SSAMethod -> FissionResult
fissLoops method =
  let cfg = buildCFG method
      domTree = computeDominators cfg
      loopNest = findLoops cfg domTree
      blocks = ssaMethodBlocks method
      blockMap = Map.fromList [(blockLabel b, b) | b <- blocks]
      ptInfo = computePointsTo method

      -- Find loops worth splitting
      toSplit = [(h, l) | (h, l) <- Map.toList loopNest
                        , shouldFiss ptInfo blockMap l]

      -- Apply fission
      (optimized, count) = applyFissions toSplit blockMap
  in FissionResult
    { fissOptBlocks = Map.elems optimized
    , fissSplit = count
    }

-- | Check if a loop should be split
shouldFiss :: PointsToInfo -> Map BlockId SSABlock -> Loop -> Bool
shouldFiss ptInfo blockMap loop =
  let bodyBlocks = [b | bid <- Set.toList (loopBody loop), Just b <- [Map.lookup bid blockMap]]
      -- Count distinct memory access patterns
      writes = collectWrites bodyBlocks
      -- Split if there are multiple independent write streams
      streams = groupByBase writes
  in length streams > 1 && all (independentStreams ptInfo) (pairs streams)
  where
    pairs xs = [(a, b) | a <- xs, b <- xs, a /= b]

-- | Group writes by base object
groupByBase :: [MemAccess] -> [[MemAccess]]
groupByBase = map snd . Map.toList . foldl' addToGroup Map.empty
  where
    addToGroup m acc =
      let key = show (maBase acc)  -- Simple grouping by expression string
      in Map.insertWith (++) key [acc] m

-- | Check if two write streams are independent
independentStreams :: PointsToInfo -> ([MemAccess], [MemAccess]) -> Bool
independentStreams ptInfo (s1, s2) =
  not $ any (\a1 -> any (mayAliasAccess ptInfo a1) s2) s1

-- | Apply loop fissions
applyFissions :: [(BlockId, Loop)] -> Map BlockId SSABlock -> (Map BlockId SSABlock, Int)
applyFissions loops blockMap = foldl' applyOneFission (blockMap, 0) loops

-- | Apply a single fission
applyOneFission :: (Map BlockId SSABlock, Int) -> (BlockId, Loop) -> (Map BlockId SSABlock, Int)
applyOneFission (blockMap, count) (_header, _loop) =
  -- Fission is complex to implement correctly - for now just return unchanged
  -- A proper implementation would:
  -- 1. Duplicate the loop structure
  -- 2. Partition instructions between the two copies
  -- 3. Update control flow
  (blockMap, count)
