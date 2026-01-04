{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RecordWildCards #-}

-- | Phi Node Lowering.
-- Converts phi nodes to parallel copies, then sequentializes them
-- while handling cycles correctly using temporary variables.
module LiveOak.PhiLower
  ( -- * Phi Lowering
    lowerPhis
  , LowerResult(..)

    -- * Critical Edge Splitting (re-exported from CFG)
  , CFG.isCriticalEdge
    -- * SSABlock-level splitting
  , splitCriticalEdgesSSA

    -- * Parallel Copy Sequentialization
  , ParallelCopy(..)
  , sequentializeCopies
  ) where

import LiveOak.SSATypes
import LiveOak.SSAUtils (blockMapFromList)
import qualified LiveOak.CFG as CFG
import LiveOak.CFG (CFG, predecessors)
import LiveOak.MapUtils (lookupList)

import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
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
-- Critical Edge Splitting for SSABlocks
--------------------------------------------------------------------------------

-- | Split all critical edges in the CFG (SSABlock version)
-- Uses CFG.findCriticalEdges for detection, but operates on SSABlocks
splitCriticalEdgesSSA :: CFG -> [SSABlock] -> (CFG, [SSABlock])
splitCriticalEdgesSSA cfg blocks =
  let blockMap = blockMapFromList blocks
      -- Find all critical edges using CFG's function
      criticalEdges = CFG.findCriticalEdges cfg
      -- Split each edge
      (cfg', blockMap', newBlocks) = foldl' splitEdgeSSA (cfg, blockMap, []) criticalEdges
      -- Reconstruct block list
      allBlocks = Map.elems blockMap' ++ newBlocks
  in (cfg', allBlocks)

-- | Split a single critical edge by inserting a new SSABlock
splitEdgeSSA :: (CFG, Map BlockId SSABlock, [SSABlock]) ->
                (BlockId, BlockId) ->
                (CFG, Map BlockId SSABlock, [SSABlock])
splitEdgeSSA (cfg, blockMap, newBlocks) (from, to) =
  let -- Create new block name
      splitName = blockId (blockIdName from ++ "_to_" ++ blockIdName to)
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
phisToCopies fromBlock = mapMaybe (phiToCopy fromBlock)

-- | Convert a single phi to a copy (if applicable for this predecessor)
phiToCopy :: BlockId -> PhiNode -> Maybe ParallelCopy
phiToCopy fromBlock PhiNode{..} =
  case lookup fromBlock phiArgs of
    Just srcVar -> Just $ ParallelCopy
      { pcDest = varNameString (ssaName phiVar)
      , pcSrc = varNameString (ssaName srcVar)
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
  let -- Find variables that are both sources and destinations (potential cycles)
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
          let c:rest = remaining
              tempVar = "__phi_temp_" ++ pcDest c
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

--------------------------------------------------------------------------------
-- Phi Lowering
--------------------------------------------------------------------------------

-- | Lower all phi nodes in a program
lowerPhis :: CFG -> [SSABlock] -> LowerResult
lowerPhis cfg blocks =
  let -- First, split critical edges
      (cfg', blocks') = splitCriticalEdgesSSA cfg blocks
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
  [(predId, sequentializeCopies (phisToCopies predId phis))
  | predId <- predecessors cfg bid]

-- | Group copies by target block
groupCopy :: Map BlockId [[SeqCopy]] -> (BlockId, [SeqCopy]) -> Map BlockId [[SeqCopy]]
groupCopy m (bid, copies) = Map.insertWith (++) bid [copies] m

-- | Insert copies into blocks and remove phis
insertCopies :: Map BlockId [[SeqCopy]] ->
                ([SSABlock], Int) -> (BlockId, SSABlock) ->
                ([SSABlock], Int)
insertCopies copyMap (acc, count) (bid, block@SSABlock{..}) =
  let copies = concat $ lookupList bid copyMap
      copyInstrs = map copyToInstr copies
      -- Remove phi nodes and insert copies before terminator
      newInstrs = insertBeforeTerminator blockInstrs copyInstrs
      newBlock = block { blockPhis = [], blockInstrs = newInstrs }
  in (newBlock : acc, count + length copyInstrs)

-- | Convert a sequential copy to an SSA instruction
copyToInstr :: SeqCopy -> SSAInstr
copyToInstr = \case
  CopyMove dest src ->
    SSAAssign (SSAVar (varName dest) 0 Nothing) (SSAUse (SSAVar (varName src) 0 Nothing))
  CopySwap dest src ->
    -- Swap is typically lowered to multiple moves with temp
    -- For now, treat as a move (would need runtime support for actual swap)
    SSAAssign (SSAVar (varName dest) 0 Nothing) (SSAUse (SSAVar (varName src) 0 Nothing))
  CopyTemp dest src ->
    SSAAssign (SSAVar (varName dest) 0 Nothing) (SSAUse (SSAVar (varName src) 0 Nothing))

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
