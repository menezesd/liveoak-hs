{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RecordWildCards #-}

-- | Block Merging.
-- Merges basic blocks to simplify the CFG.
--
-- == Merge Conditions
--
-- Two blocks A and B can be merged if:
-- 1. A has exactly one successor (B)
-- 2. B has exactly one predecessor (A)
-- 3. A ends with an unconditional jump to B
-- 4. B has no phi nodes (or they can be eliminated)
--
-- == Example
--
-- @
-- Before:                After:
--   block_1:               block_1:
--     x = 1                  x = 1
--     jump block_2           y = x + 1
--   block_2:                 return y
--     y = x + 1
--     return y
-- @
--
module LiveOak.BlockMerge
  ( -- * Block Merging
    mergeBlocks
  , mergeBlocksMethod
  , BlockMergeResult(..)
  ) where

import LiveOak.SSATypes

import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Data.List (foldl')
import Data.Maybe (mapMaybe)

--------------------------------------------------------------------------------
-- Types
--------------------------------------------------------------------------------

-- | Block merge result
data BlockMergeResult = BlockMergeResult
  { bmOptBlocks :: ![SSABlock]
  , bmMerged :: !Int              -- ^ Number of blocks merged
  } deriving (Show)

--------------------------------------------------------------------------------
-- Block Merging
--------------------------------------------------------------------------------

-- | Merge blocks in a list
mergeBlocks :: [SSABlock] -> BlockMergeResult
mergeBlocks blocks =
  let -- Build predecessor and successor maps
      (predMap, succMap) = buildPredSuccMaps blocks
      -- Find mergeable pairs
      mergeablePairs = findMergeablePairs blocks predMap succMap
      -- Apply merges iteratively
      (merged, count) = applyMerges blocks mergeablePairs
  in BlockMergeResult
    { bmOptBlocks = merged
    , bmMerged = count
    }

-- | Merge blocks in a method
mergeBlocksMethod :: SSAMethod -> BlockMergeResult
mergeBlocksMethod method = mergeBlocks (ssaMethodBlocks method)

-- | Build predecessor and successor maps
buildPredSuccMaps :: [SSABlock] -> (Map BlockId [BlockId], Map BlockId [BlockId])
buildPredSuccMaps blocks =
  let edges = concatMap getBlockEdges blocks
      succMap = Map.fromListWith (++) [(src, [dst]) | (src, dst) <- edges]
      predMap = Map.fromListWith (++) [(dst, [src]) | (src, dst) <- edges]
  in (predMap, succMap)

-- | Get edges from a block
getBlockEdges :: SSABlock -> [(BlockId, BlockId)]
getBlockEdges SSABlock{..} =
  case filter isTerminator blockInstrs of
    [SSAJump target] -> [(blockLabel, target)]
    [SSABranch _ t f] -> [(blockLabel, t), (blockLabel, f)]
    _ -> []
  where
    isTerminator (SSAJump _) = True
    isTerminator (SSABranch _ _ _) = True
    isTerminator (SSAReturn _) = True
    isTerminator _ = False

-- | Find pairs of blocks that can be merged
-- Returns list of (predecessor, successor) pairs
findMergeablePairs :: [SSABlock] -> Map BlockId [BlockId] -> Map BlockId [BlockId]
                   -> [(BlockId, BlockId)]
findMergeablePairs blocks predMap succMap =
  let blockMap = Map.fromList [(blockLabel b, b) | b <- blocks]
  in mapMaybe (canMerge blockMap predMap succMap) blocks

-- | Check if a block can be merged with its successor
canMerge :: Map BlockId SSABlock -> Map BlockId [BlockId] -> Map BlockId [BlockId]
         -> SSABlock -> Maybe (BlockId, BlockId)
canMerge blockMap predMap _succMap block =
  let srcLabel = blockLabel block
  in -- Check if block ends with unconditional jump
  case getUnconditionalTarget block of
    Nothing -> Nothing
    Just target ->
      -- Check if target has exactly one predecessor (this block)
      case Map.lookup target predMap of
        Just [predBlock] | predBlock == srcLabel ->
          -- Check if target has no phi nodes
          case Map.lookup target blockMap of
            Just targetBlock | null (blockPhis targetBlock) ->
              Just (srcLabel, target)
            _ -> Nothing
        _ -> Nothing

-- | Get the target of an unconditional jump
getUnconditionalTarget :: SSABlock -> Maybe BlockId
getUnconditionalTarget SSABlock{..} =
  case filter isJump blockInstrs of
    [SSAJump target] -> Just target
    _ -> Nothing
  where
    isJump (SSAJump _) = True
    isJump _ = False

-- | Apply merges iteratively until no more can be done
applyMerges :: [SSABlock] -> [(BlockId, BlockId)] -> ([SSABlock], Int)
applyMerges blocks [] = (blocks, 0)
applyMerges blocks pairs =
  let -- Build block map
      blockMap = Map.fromList [(blockLabel b, b) | b <- blocks]
      -- Apply one merge at a time and recurse
      (blockMap', count) = foldl' applyOneMerge (blockMap, 0) pairs
      -- Convert back to list
      blocks' = Map.elems blockMap'
  in (blocks', count)

-- | Apply a single merge
applyOneMerge :: (Map BlockId SSABlock, Int) -> (BlockId, BlockId)
              -> (Map BlockId SSABlock, Int)
applyOneMerge (blockMap, count) (predId, succId) =
  case (Map.lookup predId blockMap, Map.lookup succId blockMap) of
    (Just predBlock, Just succBlock) ->
      let -- Merge the blocks
          mergedBlock = doMerge predBlock succBlock
          -- Update map: keep pred with merged content, remove succ
          blockMap' = Map.insert predId mergedBlock $ Map.delete succId blockMap
          -- Update any jumps to succId to go to predId
          blockMap'' = updateJumpTargets succId predId blockMap'
      in (blockMap'', count + 1)
    _ -> (blockMap, count)  -- One of the blocks was already merged

-- | Merge two blocks into one
doMerge :: SSABlock -> SSABlock -> SSABlock
doMerge pred succ =
  let -- Remove the jump from predecessor
      predInstrs = filter (not . isJump) (blockInstrs pred)
      -- Combine instructions
      mergedInstrs = predInstrs ++ blockInstrs succ
  in pred { blockInstrs = mergedInstrs }
  where
    isJump (SSAJump _) = True
    isJump _ = False

-- | Update jump targets from oldTarget to newTarget
updateJumpTargets :: BlockId -> BlockId -> Map BlockId SSABlock -> Map BlockId SSABlock
updateJumpTargets oldTarget newTarget = Map.map updateBlock
  where
    updateBlock block@SSABlock{..} =
      let instrs' = map updateInstr blockInstrs
          phis' = map updatePhi blockPhis
      in block { blockInstrs = instrs', blockPhis = phis' }

    updateInstr = \case
      SSAJump t | t == oldTarget -> SSAJump newTarget
      SSABranch c t f ->
        let t' = if t == oldTarget then newTarget else t
            f' = if f == oldTarget then newTarget else f
        in SSABranch c t' f'
      i -> i

    updatePhi phi@PhiNode{..} =
      let args' = map updatePhiArg phiArgs
      in phi { phiArgs = args' }

    updatePhiArg (bid, var)
      | bid == oldTarget = (newTarget, var)
      | otherwise = (bid, var)
