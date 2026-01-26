{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RecordWildCards #-}

-- | Partial Inlining.
-- Inlines only the hot path of a function, leaving cold code out-of-line.
--
-- == Strategy
-- 1. Identify hot/cold blocks in callee using heuristics
-- 2. Clone hot blocks into the caller
-- 3. Leave cold blocks as a separate function called on the cold path
--
-- == Heuristics for Hot/Cold
-- - Entry block and immediate successors are hot
-- - Error handling, exception paths are cold
-- - Deeply nested or rarely-taken branches are cold
--
module LiveOak.PartialInline
  ( -- * Partial Inlining
    partialInline
  , PartialInlineResult(..)

    -- * Hot/Cold Analysis
  , BlockTemperature(..)
  , classifyBlocks
  ) where

import LiveOak.SSATypes
import LiveOak.CFG
import LiveOak.Dominance (DomTree, computeDominators)
import LiveOak.Loop (LoopNest, findLoops, loopDepth)

import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Set (Set)
import qualified Data.Set as Set
import Data.List (foldl', partition)
import Data.Maybe (mapMaybe)

--------------------------------------------------------------------------------
-- Types
--------------------------------------------------------------------------------

-- | Partial inlining result
data PartialInlineResult = PartialInlineResult
  { piOptProgram :: !SSAProgram
  , piInlined :: !Int                -- ^ Number of partial inlines
  , piOutlined :: !Int               -- ^ Number of cold functions created
  } deriving (Show)

-- | Block temperature classification
data BlockTemperature
  = Hot                              -- ^ Likely to execute
  | Warm                             -- ^ Moderately likely
  | Cold                             -- ^ Unlikely to execute
  deriving (Eq, Ord, Show)

-- | Candidate for partial inlining
data PartialCandidate = PartialCandidate
  { pcCallee :: !String              -- ^ Method being inlined
  , pcHotBlocks :: ![BlockId]        -- ^ Blocks to inline
  , pcColdBlocks :: ![BlockId]       -- ^ Blocks to leave out
  , pcHotSize :: !Int                -- ^ Size of hot region
  } deriving (Show)

--------------------------------------------------------------------------------
-- Block Classification
--------------------------------------------------------------------------------

-- | Classify blocks as hot or cold
classifyBlocks :: CFG -> DomTree -> LoopNest -> [SSABlock] -> Map BlockId BlockTemperature
classifyBlocks cfg domTree loops blocks =
  let entry = cfgEntry cfg
      -- Start with all blocks cold, then mark hot ones
      initial = Map.fromList [(blockLabel b, Cold) | b <- blocks]
      -- Entry block is always hot
      withEntry = Map.insert entry Hot initial
      -- Blocks in loops are warm/hot
      withLoops = foldl' (markLoopBlocks loops) withEntry blocks
      -- Blocks dominated by entry with short paths are hot
      withDom = markDominatorHot cfg domTree entry withLoops
      -- Error handling patterns are cold
      withErrors = markErrorsCold blocks withDom
  in withErrors

-- | Mark loop blocks as warm/hot
markLoopBlocks :: LoopNest -> Map BlockId BlockTemperature -> SSABlock -> Map BlockId BlockTemperature
markLoopBlocks loops temps block =
  let bid = blockLabel block
      depth = loopDepth loops bid
  in if depth > 0
     then Map.insert bid (if depth > 1 then Hot else Warm) temps
     else temps

-- | Mark blocks close to entry as hot
markDominatorHot :: CFG -> DomTree -> BlockId -> Map BlockId BlockTemperature -> Map BlockId BlockTemperature
markDominatorHot cfg domTree entry temps =
  let -- BFS from entry, mark first few levels as hot
      level0 = [entry]
      level1 = concatMap (successors cfg) level0
      level2 = concatMap (successors cfg) level1
      hotBlocks = Set.fromList (level0 ++ level1)
      warmBlocks = Set.fromList level2 Set.\\ hotBlocks
      temps' = Set.foldr (\b t -> Map.insert b Hot t) temps hotBlocks
      temps'' = Set.foldr (\b t -> Map.insertWith max b Warm t) temps' warmBlocks
  in temps''

-- | Mark error-related blocks as cold
markErrorsCold :: [SSABlock] -> Map BlockId BlockTemperature -> Map BlockId BlockTemperature
markErrorsCold blocks temps = foldl' checkBlock temps blocks
  where
    checkBlock t block
      | hasErrorPattern block = Map.insert (blockLabel block) Cold t
      | otherwise = t

    -- Heuristics for error blocks
    hasErrorPattern SSABlock{..} = any isErrorInstr blockInstrs

    isErrorInstr = \case
      -- Calls to methods with "error", "throw", "assert" in name
      SSAExprStmt (SSACall name _) -> isErrorName name
      SSAAssign _ (SSACall name _) -> isErrorName name
      _ -> False

    isErrorName name =
      any (`elem` words name) ["error", "throw", "assert", "fail", "panic"]
    words = filter (not . null) . splitOn '_'
    splitOn c s = case break (== c) s of
      (a, "") -> [a]
      (a, _:b) -> a : splitOn c b

--------------------------------------------------------------------------------
-- Partial Inlining
--------------------------------------------------------------------------------

-- | Apply partial inlining to a program
partialInline :: SSAProgram -> PartialInlineResult
partialInline prog@(SSAProgram classes) =
  let -- Analyze all methods for partial inlining candidates
      methodInfos = collectMethodInfos prog
      -- Find partial inlining opportunities
      candidates = findCandidates methodInfos
      -- Apply partial inlining
      (optimized, inlined, outlined) = applyPartialInlines candidates classes
  in PartialInlineResult
    { piOptProgram = SSAProgram optimized
    , piInlined = inlined
    , piOutlined = outlined
    }

-- | Method information for partial inlining decisions
data MethodInfo = MethodInfo
  { miFullName :: !String
  , miBlocks :: ![SSABlock]
  , miTemps :: !(Map BlockId BlockTemperature)
  , miTotalSize :: !Int
  , miHotSize :: !Int
  } deriving (Show)

-- | Collect method information
collectMethodInfos :: SSAProgram -> Map String MethodInfo
collectMethodInfos (SSAProgram classes) = Map.fromList
  [(fullName cls m, analyzeMethod cls m) | cls <- classes, m <- ssaClassMethods cls]
  where
    fullName cls m = ssaClassName cls ++ "_" ++ methodNameString (ssaMethodName m)

    analyzeMethod cls m =
      let blocks = ssaMethodBlocks m
          cfg = buildCFG m
          domTree = computeDominators cfg
          loops = findLoops cfg domTree
          temps = classifyBlocks cfg domTree loops blocks
          totalSize = sum [length (blockInstrs b) | b <- blocks]
          hotSize = sum [length (blockInstrs b) | b <- blocks
                        , Map.findWithDefault Cold (blockLabel b) temps >= Warm]
      in MethodInfo
        { miFullName = fullName cls m
        , miBlocks = blocks
        , miTemps = temps
        , miTotalSize = totalSize
        , miHotSize = hotSize
        }

-- | Find partial inlining candidates
findCandidates :: Map String MethodInfo -> [PartialCandidate]
findCandidates infos = mapMaybe makeCandidate (Map.toList infos)
  where
    makeCandidate (name, info)
      -- Only consider methods where hot region is significantly smaller
      | miHotSize info < miTotalSize info `div` 2
      , miHotSize info <= 20  -- Hot region should be small
      , miTotalSize info > 10  -- Total should be non-trivial
      = let (hot, cold) = partition (isHot info) (map blockLabel (miBlocks info))
        in Just $ PartialCandidate
          { pcCallee = name
          , pcHotBlocks = hot
          , pcColdBlocks = cold
          , pcHotSize = miHotSize info
          }
      | otherwise = Nothing

    isHot info bid = Map.findWithDefault Cold bid (miTemps info) >= Warm

-- | Apply partial inlining transformations
applyPartialInlines :: [PartialCandidate] -> [SSAClass] -> ([SSAClass], Int, Int)
applyPartialInlines candidates classes =
  -- For now, just return unchanged - full implementation would:
  -- 1. Clone hot blocks into call sites
  -- 2. Create outlined cold functions
  -- 3. Update control flow
  (classes, 0, 0)
