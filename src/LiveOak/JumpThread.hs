{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RecordWildCards #-}

-- | Jump Threading Optimization.
-- Eliminates redundant control flow by threading jumps through intermediate blocks.
--
-- == Patterns Handled
--
-- 1. __Empty Block Threading__: Jump to block that only jumps elsewhere
--    @
--    B1: ... goto B2
--    B2: goto B3        -->   B1: ... goto B3
--    @
--
-- 2. __Redundant Branch Threading__: Branch where condition is known
--    @
--    B1: if (x) goto B2 else goto B3
--    B2: if (x) goto B4 else goto B5   -->   B1: if (x) goto B4 else goto B3
--    @
--
-- 3. __Critical Edge Splitting__: (prerequisite for other opts)
--
module LiveOak.JumpThread
  ( -- * Jump Threading
    threadJumps
  , JumpThreadResult(..)
  ) where

import LiveOak.SSATypes
import LiveOak.SSAUtils (blockMapFromList)

import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Set (Set)
import qualified Data.Set as Set
import Data.List (foldl')

--------------------------------------------------------------------------------
-- Types
--------------------------------------------------------------------------------

-- | Jump threading result
data JumpThreadResult = JumpThreadResult
  { jtOptBlocks :: ![SSABlock]    -- ^ Optimized blocks
  , jtThreaded :: !Int            -- ^ Number of jumps threaded
  , jtEliminatedBlocks :: !Int    -- ^ Number of blocks eliminated
  } deriving (Show)

--------------------------------------------------------------------------------
-- Jump Threading
--------------------------------------------------------------------------------

-- | Apply jump threading to SSA blocks
threadJumps :: [SSABlock] -> JumpThreadResult
threadJumps blocks =
  let blockMap = blockMapFromList blocks
      -- Build jump target map (only for blocks that are safe to thread through)
      targetMap = buildTargetMap blockMap
      -- Apply threading and update phi nodes
      (threaded, count) = applyThreadingWithPhis blockMap targetMap
      -- Remove empty blocks
      (cleaned, eliminated) = removeEmptyBlocks threaded
  in JumpThreadResult
    { jtOptBlocks = Map.elems cleaned
    , jtThreaded = count
    , jtEliminatedBlocks = eliminated
    }

-- | Build a map of blocks that just jump to another block
-- Maps: block -> final target (skipping intermediate jumps)
buildTargetMap :: Map BlockId SSABlock -> Map BlockId BlockId
buildTargetMap blockMap = Map.foldlWithKey' addTarget Map.empty blockMap
  where
    addTarget acc bid block =
      case findJumpTarget block of
        Just target ->
          -- Follow the chain to find ultimate target
          let finalTarget = followChain blockMap (Set.singleton bid) target
          in Map.insert bid finalTarget acc
        Nothing -> acc

-- | Find the target of a block if it only contains a jump
findJumpTarget :: SSABlock -> Maybe BlockId
findJumpTarget SSABlock{..}
  | null blockPhis && length blockInstrs == 1 =
      case head blockInstrs of
        SSAJump target -> Just target
        _ -> Nothing
  | otherwise = Nothing

-- | Follow a chain of jumps to find the ultimate target
followChain :: Map BlockId SSABlock -> Set BlockId -> BlockId -> BlockId
followChain blockMap visited target
  | Set.member target visited = target  -- Cycle detected
  | otherwise =
      case Map.lookup target blockMap of
        Just block ->
          case findJumpTarget block of
            Just nextTarget -> followChain blockMap (Set.insert target visited) nextTarget
            Nothing -> target
        Nothing -> target

-- | Apply jump threading to all blocks, updating phi nodes as needed
applyThreadingWithPhis :: Map BlockId SSABlock -> Map BlockId BlockId -> (Map BlockId SSABlock, Int)
applyThreadingWithPhis blockMap targetMap =
  let -- Build predecessor map BEFORE threading (who jumps to each empty block)
      predMap = buildPredecessorMap blockMap targetMap
      -- Thread the jumps in all blocks
      (count, threaded) = Map.mapAccum (threadBlock targetMap) 0 blockMap
      -- Update phi nodes for the new predecessors
      updated = updatePhisForThreading threaded targetMap predMap
  in (updated, count)

-- | Build map of predecessors for each empty block that will be threaded through
-- predMap[B] = [P1, P2, ...] means P1, P2, etc. currently jump to B
-- Only records edges that will ACTUALLY be threaded (not self-loops)
buildPredecessorMap :: Map BlockId SSABlock -> Map BlockId BlockId -> Map BlockId [BlockId]
buildPredecessorMap blockMap targetMap =
  Map.foldlWithKey' addPreds Map.empty blockMap
  where
    addPreds acc bid SSABlock{..} =
      foldl' (addPred bid) acc blockInstrs

    -- Only record if threading would NOT create a self-loop
    addPred srcBid acc = \case
      SSAJump target
        | Just finalTarget <- Map.lookup target targetMap
        , finalTarget /= srcBid ->  -- Not a self-loop
            Map.insertWith (++) target [srcBid] acc
      SSABranch _ t f ->
        let -- Only add if threading t wouldn't create self-loop
            acc' = case Map.lookup t targetMap of
                     Just ft | ft /= srcBid -> Map.insertWith (++) t [srcBid] acc
                     _ -> acc
            -- Only add if threading f wouldn't create self-loop
        in case Map.lookup f targetMap of
             Just ff | ff /= srcBid -> Map.insertWith (++) f [srcBid] acc'
             _ -> acc'
      _ -> acc

-- | Update phi nodes when jumps are threaded
-- When B1 -> B2 -> B3 becomes B1 -> B3, phi nodes in B3 that expect B2
-- should now accept values from B1 with the same variable
updatePhisForThreading :: Map BlockId SSABlock -> Map BlockId BlockId -> Map BlockId [BlockId] -> Map BlockId SSABlock
updatePhisForThreading blockMap targetMap predMap =
  Map.map (updateBlockPhis targetMap predMap) blockMap

-- | Update phi nodes in a block for threading
updateBlockPhis :: Map BlockId BlockId -> Map BlockId [BlockId] -> SSABlock -> SSABlock
updateBlockPhis targetMap predMap block@SSABlock{..} =
  if null blockPhis
  then block
  else block { blockPhis = map (updatePhi targetMap predMap) blockPhis }

-- | Update a phi node for threading
-- For each phi arg (B, var) where B was threaded through, add args from B's predecessors
updatePhi :: Map BlockId BlockId -> Map BlockId [BlockId] -> PhiNode -> PhiNode
updatePhi targetMap predMap phi@PhiNode{..} =
  let newArgs = concatMap (expandPhiArg targetMap predMap) phiArgs
  in phi { phiArgs = newArgs }

-- | Expand a phi argument if blocks were threaded through it
-- If B is an empty block (in targetMap), add phi args from all of B's predecessors
expandPhiArg :: Map BlockId BlockId -> Map BlockId [BlockId] -> (BlockId, SSAVar) -> [(BlockId, SSAVar)]
expandPhiArg _targetMap predMap (intermediateBid, var) =
  case Map.lookup intermediateBid predMap of
    Just preds ->
      -- B is an empty block that was threaded through
      -- Add args from its predecessors, keep original in case B isn't fully removed
      (intermediateBid, var) : [(p, var) | p <- preds]
    Nothing ->
      -- B is not an empty block, keep as-is
      [(intermediateBid, var)]

-- | Thread jumps in a single block
threadBlock :: Map BlockId BlockId -> Int -> SSABlock -> (Int, SSABlock)
threadBlock targetMap count block@SSABlock{..} =
  let (newInstrs, c) = threadInstrs blockLabel targetMap blockInstrs
  in (count + c, block { blockInstrs = newInstrs })

-- | Thread jumps in instructions
-- Avoid creating self-loops (block jumping to itself)
threadInstrs :: BlockId -> Map BlockId BlockId -> [SSAInstr] -> ([SSAInstr], Int)
threadInstrs currentBlock targetMap = foldr threadInstr ([], 0)
  where
    threadInstr instr (acc, count) =
      case instr of
        SSAJump target ->
          case Map.lookup target targetMap of
            -- Don't thread if it would create a self-loop
            Just finalTarget | finalTarget /= target && finalTarget /= currentBlock ->
              (SSAJump finalTarget : acc, count + 1)
            _ -> (instr : acc, count)

        SSABranch cond thenTarget elseTarget ->
          -- Don't thread targets that would become self-loops
          let thenTarget' = if Map.findWithDefault thenTarget thenTarget targetMap == currentBlock
                            then thenTarget  -- Keep original to avoid self-loop
                            else Map.findWithDefault thenTarget thenTarget targetMap
              elseTarget' = if Map.findWithDefault elseTarget elseTarget targetMap == currentBlock
                            then elseTarget  -- Keep original to avoid self-loop
                            else Map.findWithDefault elseTarget elseTarget targetMap
              changed = (thenTarget' /= thenTarget) || (elseTarget' /= elseTarget)
          in if changed
             then (SSABranch cond thenTarget' elseTarget' : acc, count + 1)
             else (instr : acc, count)

        _ -> (instr : acc, count)

-- | Remove blocks that are no longer reachable (only contain a jump and have no preds)
removeEmptyBlocks :: Map BlockId SSABlock -> (Map BlockId SSABlock, Int)
removeEmptyBlocks blockMap =
  let -- Find all referenced blocks (by jumps/branches, not phi nodes)
      referenced = collectReferencedByJumps blockMap
      -- Find empty jump-only blocks
      emptyBlocks = Map.keysSet $ Map.filter isEmptyJumpBlock blockMap
      -- Keep blocks that are referenced or not empty
      toRemove = Set.difference emptyBlocks referenced
      kept = Map.filterWithKey (\k _ -> not (Set.member k toRemove)) blockMap
      -- Clean up phi nodes that reference removed blocks
      cleaned = Map.map (cleanupPhis toRemove) kept
  in (cleaned, Set.size toRemove)

-- | Remove phi arguments that reference removed blocks
cleanupPhis :: Set BlockId -> SSABlock -> SSABlock
cleanupPhis removed block@SSABlock{..} =
  if null blockPhis
  then block
  else block { blockPhis = map (cleanupPhi removed) blockPhis }

cleanupPhi :: Set BlockId -> PhiNode -> PhiNode
cleanupPhi removed phi@PhiNode{..} =
  phi { phiArgs = filter (\(bid, _) -> not (Set.member bid removed)) phiArgs }

-- | Check if a block only contains a jump
isEmptyJumpBlock :: SSABlock -> Bool
isEmptyJumpBlock SSABlock{..} =
  null blockPhis && length blockInstrs == 1 &&
  case head blockInstrs of
    SSAJump _ -> True
    _ -> False

-- | Collect all block IDs that are referenced by jumps/branches (not phi nodes)
collectReferencedByJumps :: Map BlockId SSABlock -> Set BlockId
collectReferencedByJumps = Map.foldl' addBlockRefs Set.empty
  where
    addBlockRefs acc SSABlock{..} =
      let instrRefs = concatMap instrRefs' blockInstrs
      in foldl' (flip Set.insert) acc instrRefs

    instrRefs' = \case
      SSAJump target -> [target]
      SSABranch _ t f -> [t, f]
      _ -> []
