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
  , threadJumpsWithEntry
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
  , jtNewEntry :: !(Maybe BlockId) -- ^ New entry block if original was threaded
  } deriving (Show)

-- | Threading info for an empty jump-only block.
data ThreadInfo = ThreadInfo
  { tiFinalTarget :: !BlockId  -- ^ Final target after skipping empty blocks
  , tiLastHop :: !BlockId      -- ^ Last empty block before the final target
  } deriving (Show)

--------------------------------------------------------------------------------
-- Jump Threading
--------------------------------------------------------------------------------

-- | Apply jump threading to SSA blocks
threadJumps :: [SSABlock] -> JumpThreadResult
threadJumps = threadJumpsWithEntry (blockId "entry")

-- | Apply jump threading with explicit entry block
threadJumpsWithEntry :: BlockId -> [SSABlock] -> JumpThreadResult
threadJumpsWithEntry entryBlock blocks =
  let blockMap = blockMapFromList blocks
      -- Build jump threading info (only for blocks that are safe to thread through)
      threadInfo = buildThreadInfo blockMap
      targetMap = Map.map tiFinalTarget threadInfo
      -- Apply threading and update phi nodes
      (threaded, count) = applyThreadingWithPhis blockMap threadInfo
      -- Remove empty blocks
      (cleaned, eliminated) = removeEmptyBlocks threaded
      -- Check if entry block was threaded
      newEntry = case Map.lookup entryBlock targetMap of
                   Just target | not (Map.member entryBlock cleaned) -> Just target
                   _ -> Nothing
  in JumpThreadResult
    { jtOptBlocks = Map.elems cleaned
    , jtThreaded = count
    , jtEliminatedBlocks = eliminated
    , jtNewEntry = newEntry
    }

-- | Build threading info for blocks that just jump to another block.
-- Records both the final target and the last empty block before it.
buildThreadInfo :: Map BlockId SSABlock -> Map BlockId ThreadInfo
buildThreadInfo blockMap = Map.foldlWithKey' addInfo Map.empty blockMap
  where
    addInfo acc bid block =
      case findJumpTarget block of
        Just target ->
          case resolveThreadInfo blockMap (Set.singleton bid) bid target of
            Just info -> Map.insert bid info acc
            Nothing -> acc
        Nothing -> acc

-- | Find the target of a block if it only contains a jump
findJumpTarget :: SSABlock -> Maybe BlockId
findJumpTarget SSABlock{..}
  | null blockPhis && length blockInstrs == 1 =
      case head blockInstrs of
        SSAJump target -> Just target
        _ -> Nothing
  | otherwise = Nothing

-- | Resolve the final target and last empty block in a jump chain.
-- Returns Nothing for cycles to avoid unsafe threading.
resolveThreadInfo :: Map BlockId SSABlock -> Set BlockId -> BlockId -> BlockId -> Maybe ThreadInfo
resolveThreadInfo blockMap visited lastEmpty target
  | Set.member target visited = Nothing  -- Cycle detected
  | otherwise =
      case Map.lookup target blockMap of
        Just block ->
          case findJumpTarget block of
            Just nextTarget ->
              resolveThreadInfo blockMap (Set.insert target visited) target nextTarget
            Nothing -> Just ThreadInfo { tiFinalTarget = target, tiLastHop = lastEmpty }
        Nothing -> Just ThreadInfo { tiFinalTarget = target, tiLastHop = lastEmpty }

-- | Apply jump threading to all blocks, updating phi nodes as needed
applyThreadingWithPhis :: Map BlockId SSABlock -> Map BlockId ThreadInfo -> (Map BlockId SSABlock, Int)
applyThreadingWithPhis blockMap threadInfo =
  let targetMap = Map.map tiFinalTarget threadInfo
      -- Build predecessor map BEFORE threading (who jumps to each threaded-through block)
      predMap = buildPredecessorMap blockMap threadInfo
      -- Thread the jumps in all blocks
      (count, threaded) = Map.mapAccum (threadBlock targetMap) 0 blockMap
      -- Update phi nodes for the new predecessors
      updated = updatePhisForThreading threaded targetMap predMap
  in (updated, count)

-- | Build map of predecessors for each empty block that will be threaded through
-- predMap[B] = [P1, P2, ...] means P1, P2, etc. will become new predecessors
-- of the block that B jumps to (B is the last empty hop in a chain).
-- Only records edges that will ACTUALLY be threaded (not self-loops)
buildPredecessorMap :: Map BlockId SSABlock -> Map BlockId ThreadInfo -> Map BlockId [BlockId]
buildPredecessorMap blockMap threadInfo =
  Map.foldlWithKey' addPreds Map.empty blockMap
  where
    addPreds acc bid SSABlock{..} =
      foldl' (addPred bid) acc blockInstrs

    -- Only record if threading would NOT create a self-loop
    addPred srcBid acc = \case
      SSAJump target
        | Just ThreadInfo{..} <- Map.lookup target threadInfo
        , tiFinalTarget /= target
        , tiFinalTarget /= srcBid ->  -- Not a self-loop
            Map.insertWith (++) tiLastHop [srcBid] acc
      SSABranch _ t f ->
        let -- Only add if threading t wouldn't create self-loop
            acc' = case Map.lookup t threadInfo of
                     Just ThreadInfo{..}
                       | tiFinalTarget /= t
                       , tiFinalTarget /= srcBid ->
                           Map.insertWith (++) tiLastHop [srcBid] acc
                     _ -> acc
            -- Only add if threading f wouldn't create self-loop
        in case Map.lookup f threadInfo of
             Just ThreadInfo{..}
               | tiFinalTarget /= f
               , tiFinalTarget /= srcBid ->
                   Map.insertWith (++) tiLastHop [srcBid] acc'
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
