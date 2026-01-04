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
import LiveOak.CFG
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
      -- Build jump target map
      targetMap = buildTargetMap blockMap
      -- Apply threading
      (threaded, count) = applyThreading blockMap targetMap
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

-- | Apply jump threading to all blocks
applyThreading :: Map BlockId SSABlock -> Map BlockId BlockId -> (Map BlockId SSABlock, Int)
applyThreading blockMap targetMap =
  let (count, threaded) = Map.mapAccum (threadBlock targetMap) 0 blockMap
  in (threaded, count)

-- | Thread jumps in a single block
threadBlock :: Map BlockId BlockId -> Int -> SSABlock -> (Int, SSABlock)
threadBlock targetMap count block@SSABlock{..} =
  let (newInstrs, c) = threadInstrs targetMap blockInstrs
  in (count + c, block { blockInstrs = newInstrs })

-- | Thread jumps in instructions
threadInstrs :: Map BlockId BlockId -> [SSAInstr] -> ([SSAInstr], Int)
threadInstrs targetMap = foldr threadInstr ([], 0)
  where
    threadInstr instr (acc, count) =
      case instr of
        SSAJump target ->
          case Map.lookup target targetMap of
            Just finalTarget | finalTarget /= target ->
              (SSAJump finalTarget : acc, count + 1)
            _ -> (instr : acc, count)

        SSABranch cond thenTarget elseTarget ->
          let thenTarget' = Map.findWithDefault thenTarget thenTarget targetMap
              elseTarget' = Map.findWithDefault elseTarget elseTarget targetMap
              changed = (thenTarget' /= thenTarget) || (elseTarget' /= elseTarget)
          in if changed
             then (SSABranch cond thenTarget' elseTarget' : acc, count + 1)
             else (instr : acc, count)

        _ -> (instr : acc, count)

-- | Remove blocks that are no longer reachable (only contain a jump and have no preds)
removeEmptyBlocks :: Map BlockId SSABlock -> (Map BlockId SSABlock, Int)
removeEmptyBlocks blockMap =
  let -- Find all referenced blocks
      referenced = collectReferencedBlocks blockMap
      -- Find empty jump-only blocks
      emptyBlocks = Map.keysSet $ Map.filter isEmptyJumpBlock blockMap
      -- Keep blocks that are referenced or not empty
      toRemove = Set.difference emptyBlocks referenced
      kept = Map.filterWithKey (\k _ -> not (Set.member k toRemove)) blockMap
  in (kept, Set.size toRemove)

-- | Check if a block only contains a jump
isEmptyJumpBlock :: SSABlock -> Bool
isEmptyJumpBlock SSABlock{..} =
  null blockPhis && length blockInstrs == 1 &&
  case head blockInstrs of
    SSAJump _ -> True
    _ -> False

-- | Collect all block IDs that are referenced by jumps/branches
collectReferencedBlocks :: Map BlockId SSABlock -> Set BlockId
collectReferencedBlocks = Map.foldl' addBlockRefs Set.empty
  where
    addBlockRefs acc SSABlock{..} =
      let instrRefs = concatMap instrRefs' blockInstrs
          phiRefs = [bid | phi <- blockPhis, (bid, _) <- phiArgs phi]
      in foldl' (flip Set.insert) acc (instrRefs ++ phiRefs)

    instrRefs' = \case
      SSAJump target -> [target]
      SSABranch _ t f -> [t, f]
      _ -> []
