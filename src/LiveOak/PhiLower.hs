{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RecordWildCards #-}

-- | Phi Node Lowering.
-- Converts phi nodes to parallel copies, then sequentializes them
-- while handling cycles correctly using temporary variables.
module LiveOak.PhiLower
  ( -- * Phi Lowering
    lowerPhis
  , LowerResult(..)

    -- * Critical Edge Splitting
  , splitCriticalEdges
  , isCriticalEdge

    -- * Parallel Copy Sequentialization
  , ParallelCopy(..)
  , sequentializeCopies
  ) where

import LiveOak.SSATypes
import LiveOak.CFG hiding (isCriticalEdge, splitCriticalEdges, findCriticalEdges, splitEdge)

import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Set (Set)
import qualified Data.Set as Set
import Data.List (foldl', partition)
import Data.Maybe (mapMaybe)

--------------------------------------------------------------------------------
-- Types
--------------------------------------------------------------------------------

-- | A parallel copy (all happen simultaneously)
data ParallelCopy = ParallelCopy
  { pcDest :: !String       -- ^ Destination variable
  , pcSrc :: !String        -- ^ Source variable
  , pcFromBlock :: !BlockId -- ^ Predecessor block
  } deriving (Eq, Show)

-- | Sequentialized copy instruction
data SeqCopy
  = CopyMove !String !String    -- ^ dest := src
  | CopySwap !String !String    -- ^ swap dest, src
  | CopyTemp !String !String    -- ^ temp := src (for breaking cycles)
  deriving (Show)

-- | Result of phi lowering
data LowerResult = LowerResult
  { lrBlocks :: ![SSABlock]       -- ^ Lowered blocks (phis removed)
  , lrCopiesInserted :: !Int      -- ^ Number of copy instructions added
  , lrEdgesSplit :: !Int          -- ^ Number of critical edges split
  } deriving (Show)

--------------------------------------------------------------------------------
-- Critical Edge Splitting
--------------------------------------------------------------------------------

-- | Check if an edge is critical
-- A critical edge goes from a block with multiple successors
-- to a block with multiple predecessors
isCriticalEdge :: CFG -> BlockId -> BlockId -> Bool
isCriticalEdge cfg from to =
  length (successors cfg from) > 1 &&
  length (predecessors cfg to) > 1

-- | Split all critical edges in the CFG
splitCriticalEdges :: CFG -> [SSABlock] -> (CFG, [SSABlock])
splitCriticalEdges cfg blocks =
  let blockMap = Map.fromList [(blockLabel b, b) | b <- blocks]
      -- Find all critical edges
      criticalEdges = findCriticalEdges cfg blocks
      -- Split each edge
      (cfg', blockMap', newBlocks) = foldl' splitEdge (cfg, blockMap, []) criticalEdges
      -- Reconstruct block list
      allBlocks = Map.elems blockMap' ++ newBlocks
  in (cfg', allBlocks)

-- | Find all critical edges
findCriticalEdges :: CFG -> [SSABlock] -> [(BlockId, BlockId)]
findCriticalEdges cfg blocks =
  [(from, to) | SSABlock{..} <- blocks
              , let from = blockLabel
              , to <- blockSuccessors blockInstrs
              , isCriticalEdge cfg from to]
  where
    blockSuccessors instrs = concatMap instrSuccessors instrs
    instrSuccessors = \case
      SSAJump target -> [target]
      SSABranch _ thenB elseB -> [thenB, elseB]
      _ -> []

-- | Split a single critical edge by inserting a new block
splitEdge :: (CFG, Map BlockId SSABlock, [SSABlock]) ->
             (BlockId, BlockId) ->
             (CFG, Map BlockId SSABlock, [SSABlock])
splitEdge (cfg, blockMap, newBlocks) (from, to) =
  let -- Create new block name
      splitName = from ++ "_to_" ++ to
      -- Create new block with just a jump
      newBlock = SSABlock
        { blockLabel = splitName
        , blockPhis = []
        , blockInstrs = [SSAJump to]
        }
      -- Update the source block to jump to new block instead
      blockMap' = Map.adjust (redirectSuccessor to splitName) from blockMap
      -- Update phi nodes in target block to reference new block
      blockMap'' = Map.adjust (updatePhiPreds from splitName) to blockMap'
      -- Update CFG (simplified - would need proper CFG update)
      cfg' = cfg  -- Note: would need to update CFG edges properly
  in (cfg', blockMap'', newBlock : newBlocks)

-- | Redirect a successor in a block's terminator
redirectSuccessor :: BlockId -> BlockId -> SSABlock -> SSABlock
redirectSuccessor oldTarget newTarget block@SSABlock{..} =
  block { blockInstrs = map (redirectInstr oldTarget newTarget) blockInstrs }

-- | Redirect target in an instruction
redirectInstr :: BlockId -> BlockId -> SSAInstr -> SSAInstr
redirectInstr old new = \case
  SSAJump target
    | target == old -> SSAJump new
    | otherwise -> SSAJump target
  SSABranch cond thenB elseB ->
    SSABranch cond
      (if thenB == old then new else thenB)
      (if elseB == old then new else elseB)
  other -> other

-- | Update phi node predecessors
updatePhiPreds :: BlockId -> BlockId -> SSABlock -> SSABlock
updatePhiPreds oldPred newPred block@SSABlock{..} =
  block { blockPhis = map updatePhi blockPhis }
  where
    updatePhi phi@PhiNode{..} =
      phi { phiArgs = [(if p == oldPred then newPred else p, v) | (p, v) <- phiArgs] }

--------------------------------------------------------------------------------
-- Phi Node to Parallel Copies
--------------------------------------------------------------------------------

-- | Convert phi nodes to parallel copies for a specific predecessor
phisToCopies :: BlockId -> [PhiNode] -> [ParallelCopy]
phisToCopies fromBlock phis =
  mapMaybe (phiToCopy fromBlock) phis

-- | Convert a single phi to a copy (if applicable for this predecessor)
phiToCopy :: BlockId -> PhiNode -> Maybe ParallelCopy
phiToCopy fromBlock PhiNode{..} =
  case lookup fromBlock phiArgs of
    Just srcVar -> Just $ ParallelCopy
      { pcDest = ssaName phiVar
      , pcSrc = ssaName srcVar
      , pcFromBlock = fromBlock
      }
    Nothing -> Nothing

--------------------------------------------------------------------------------
-- Parallel Copy Sequentialization
--------------------------------------------------------------------------------

-- | Sequentialize a set of parallel copies
-- Handles cycles using temporary variables
sequentializeCopies :: [ParallelCopy] -> [SeqCopy]
sequentializeCopies copies =
  let -- Build dependency graph: dest -> src mapping
      destToSrc = Map.fromList [(pcDest c, pcSrc c) | c <- copies]
      srcToDests = foldl' addDep Map.empty copies

      -- Find variables that are both sources and destinations (potential cycles)
      dests = Set.fromList (map pcDest copies)
      srcs = Set.fromList (map pcSrc copies)
      conflicts = Set.intersection dests srcs

      -- Separate trivial copies (no conflict) from potentially cyclic ones
      (trivial, complex) = partition (not . isComplex conflicts) copies

      -- Emit trivial copies directly
      trivialSeq = [CopyMove (pcDest c) (pcSrc c) | c <- trivial]

      -- Handle complex copies with cycle detection
      complexSeq = handleCycles complex
  in trivialSeq ++ complexSeq
  where
    addDep m copy = Map.insertWith (++) (pcSrc copy) [pcDest copy] m
    isComplex conflicts copy = Set.member (pcSrc copy) conflicts

-- | Handle potentially cyclic copies
handleCycles :: [ParallelCopy] -> [SeqCopy]
handleCycles copies
  | null copies = []
  | otherwise = go copies Set.empty []
  where
    go [] _ acc = reverse acc
    go remaining processed acc =
      let -- Find copies whose source is not a destination of unprocessed copies
          remainingDests = Set.fromList [pcDest c | c <- remaining]
          ready = [c | c <- remaining, not (Set.member (pcSrc c) remainingDests)]
      in case ready of
        (c:_) ->
          -- Emit this copy and continue
          go (filter (/= c) remaining)
             (Set.insert (pcDest c) processed)
             (CopyMove (pcDest c) (pcSrc c) : acc)
        [] ->
          -- Cycle detected! Use a temporary to break it
          case remaining of
            (c:rest) ->
              let tempVar = "__phi_temp_" ++ pcDest c
                  -- Save the destination to temp first
                  saveToTemp = CopyTemp tempVar (pcDest c)
                  -- Now we can safely overwrite dest
                  copyToTemp = CopyMove (pcDest c) (pcSrc c)
                  -- Fix remaining copies that used dest as source
                  remaining' = [if pcSrc r == pcDest c
                                then r { pcSrc = tempVar }
                                else r
                               | r <- rest]
              in go remaining' (Set.insert (pcDest c) processed)
                    (copyToTemp : saveToTemp : acc)
            [] -> reverse acc

--------------------------------------------------------------------------------
-- Phi Lowering
--------------------------------------------------------------------------------

-- | Lower all phi nodes in a program
lowerPhis :: CFG -> [SSABlock] -> LowerResult
lowerPhis cfg blocks =
  let -- First, split critical edges
      (cfg', blocks') = splitCriticalEdges cfg blocks
      numSplit = length blocks' - length blocks

      -- For each block, lower its phi nodes by inserting copies in predecessors
      blockMap = Map.fromList [(blockLabel b, b) | b <- blocks']
      (lowered, copyCount) = lowerAllPhis cfg' blockMap
  in LowerResult
    { lrBlocks = lowered
    , lrCopiesInserted = copyCount
    , lrEdgesSplit = max 0 numSplit
    }

-- | Lower phi nodes in all blocks
lowerAllPhis :: CFG -> Map BlockId SSABlock -> ([SSABlock], Int)
lowerAllPhis cfg blockMap =
  let -- Collect all phi nodes and their target blocks
      phiInfos = [(bid, blockPhis block) | (bid, block) <- Map.toList blockMap
                                         , not (null (blockPhis block))]

      -- For each phi-containing block, generate copies for each predecessor
      copyInsns = concatMap (generateCopies cfg) phiInfos

      -- Group copies by the block they should be inserted into
      copyByBlock = foldl' groupCopy Map.empty copyInsns

      -- Insert copies and remove phis
      (result, count) = foldl' (insertCopies copyByBlock) ([], 0) (Map.toList blockMap)
  in (result, count)

-- | Generate copies for a block's phi nodes
generateCopies :: CFG -> (BlockId, [PhiNode]) -> [(BlockId, [SeqCopy])]
generateCopies cfg (bid, phis) =
  [(pred, sequentializeCopies (phisToCopies pred phis))
  | pred <- predecessors cfg bid]

-- | Group copies by target block
groupCopy :: Map BlockId [[SeqCopy]] -> (BlockId, [SeqCopy]) -> Map BlockId [[SeqCopy]]
groupCopy m (bid, copies) = Map.insertWith (++) bid [copies] m

-- | Insert copies into blocks and remove phis
insertCopies :: Map BlockId [[SeqCopy]] ->
                ([SSABlock], Int) -> (BlockId, SSABlock) ->
                ([SSABlock], Int)
insertCopies copyMap (acc, count) (bid, block@SSABlock{..}) =
  let copies = concat $ Map.findWithDefault [] bid copyMap
      copyInstrs = map copyToInstr copies
      -- Remove phi nodes and insert copies before terminator
      newInstrs = insertBeforeTerminator blockInstrs copyInstrs
      newBlock = block { blockPhis = [], blockInstrs = newInstrs }
  in (newBlock : acc, count + length copyInstrs)

-- | Convert a sequential copy to an SSA instruction
copyToInstr :: SeqCopy -> SSAInstr
copyToInstr = \case
  CopyMove dest src ->
    SSAAssign (SSAVar dest 0 Nothing) (SSAUse (SSAVar src 0 Nothing))
  CopySwap dest src ->
    -- Swap is typically lowered to multiple moves with temp
    -- For now, treat as a move (would need runtime support for actual swap)
    SSAAssign (SSAVar dest 0 Nothing) (SSAUse (SSAVar src 0 Nothing))
  CopyTemp dest src ->
    SSAAssign (SSAVar dest 0 Nothing) (SSAUse (SSAVar src 0 Nothing))

-- | Insert instructions before the terminator
insertBeforeTerminator :: [SSAInstr] -> [SSAInstr] -> [SSAInstr]
insertBeforeTerminator instrs toInsert =
  let (term, nonTerm) = partition isTerminator (reverse instrs)
  in reverse nonTerm ++ toInsert ++ reverse term
  where
    isTerminator = \case
      SSAJump _ -> True
      SSABranch {} -> True
      SSAReturn _ -> True
      _ -> False

--------------------------------------------------------------------------------
-- Advanced: Lost Copy Problem Prevention
--------------------------------------------------------------------------------

-- | The "lost copy" problem occurs when a phi destination is used
-- after the phi in the same block. We need to ensure the original
-- value is preserved.
--
-- Example:
--   L1: x2 = phi(x1, x3)
--       y = x2 + 1
--       x3 = y
--       jump L1
--
-- Naive lowering might overwrite x2 before it's used.
-- Solution: Insert copies at the right point or use temporaries.

-- | Check for lost copy situations
detectLostCopy :: [PhiNode] -> [SSAInstr] -> [(String, String)]
detectLostCopy phis instrs =
  [(ssaName (phiVar phi), usedVar)
  | phi <- phis
  , let phiDest = ssaName (phiVar phi)
  , instr <- instrs
  , usedVar <- usesInInstr instr
  , usedVar == phiDest
  , isPhiSource phi usedVar
  ]
  where
    usesInInstr = \case
      SSAAssign _ expr -> usesInExpr expr
      SSAReturn (Just expr) -> usesInExpr expr
      SSABranch cond _ _ -> usesInExpr cond
      SSAExprStmt expr -> usesInExpr expr
      _ -> []

    usesInExpr = \case
      SSAUse var -> [ssaName var]
      SSAUnary _ e -> usesInExpr e
      SSABinary _ l r -> usesInExpr l ++ usesInExpr r
      SSATernary c t e -> usesInExpr c ++ usesInExpr t ++ usesInExpr e
      SSACall _ args -> concatMap usesInExpr args
      SSAInstanceCall target _ args ->
        usesInExpr target ++ concatMap usesInExpr args
      SSANewObject _ args -> concatMap usesInExpr args
      SSAFieldAccess target _ -> usesInExpr target
      _ -> []

    isPhiSource phi var = any (\(_, v) -> ssaName v == var) (phiArgs phi)

--------------------------------------------------------------------------------
-- Advanced: Swap Problem Prevention
--------------------------------------------------------------------------------

-- | The "swap problem" occurs with phi cycles:
--   x2 = phi(y1, x1)
--   y2 = phi(x1, y1)
--
-- This is a swap that can't be sequentialized without a temp.
-- Our sequentializeCopies handles this, but we can optimize
-- by detecting and using architecture swap instructions if available.

-- | Detect swap patterns in phi nodes
detectSwaps :: [PhiNode] -> [(String, String)]
detectSwaps phis =
  [(ssaName (phiVar p1), ssaName (phiVar p2))
  | p1 <- phis
  , p2 <- phis
  , ssaName (phiVar p1) < ssaName (phiVar p2)  -- avoid duplicates
  , isSwapPair p1 p2
  ]
  where
    isSwapPair p1 p2 =
      -- Check if p1's sources are p2's dests and vice versa for some pred
      any (isSwapForPred p1 p2) (map fst $ phiArgs p1)

    isSwapForPred p1 p2 pred =
      case (lookup pred (phiArgs p1), lookup pred (phiArgs p2)) of
        (Just s1, Just s2) ->
          ssaName s1 == ssaName (phiVar p2) &&
          ssaName s2 == ssaName (phiVar p1)
        _ -> False
