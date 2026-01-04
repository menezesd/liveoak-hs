{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RecordWildCards #-}

-- | Loop Unrolling Optimization.
-- Duplicates loop bodies to reduce loop overhead and enable further optimizations.
--
-- == Strategies
--
-- 1. __Full Unrolling__: For small loops with constant trip count
-- 2. __Partial Unrolling__: Duplicate body N times, reduce iterations by N
--
-- == Benefits
--
-- - Reduces loop overhead (fewer branches, counter updates)
-- - Enables cross-iteration optimizations
-- - Better instruction-level parallelism
--
-- == Limitations
--
-- - Increases code size
-- - Only handles simple loop patterns
-- - Requires constant or analyzable trip counts for full unrolling
--
module LiveOak.Unroll
  ( -- * Loop Unrolling
    unrollLoops
  , UnrollResult(..)
  , UnrollConfig(..)
  , defaultUnrollConfig
  ) where

import LiveOak.SSATypes
import LiveOak.CFG
import LiveOak.Loop (Loop(..), LoopNest, findLoops)
import LiveOak.Dominance
import LiveOak.SSAUtils (blockMapFromList)
import LiveOak.Ast (BinaryOp(..))

import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Set (Set)
import qualified Data.Set as Set
import Data.List (foldl')
import Data.Maybe (mapMaybe, fromMaybe)

--------------------------------------------------------------------------------
-- Types
--------------------------------------------------------------------------------

-- | Unrolling configuration
data UnrollConfig = UnrollConfig
  { ucMaxUnrollFactor :: !Int     -- ^ Maximum unroll factor
  , ucMaxBodySize :: !Int         -- ^ Maximum loop body size to unroll
  , ucFullUnrollLimit :: !Int     -- ^ Max trip count for full unrolling
  , ucPartialUnrollFactor :: !Int -- ^ Factor for partial unrolling
  } deriving (Show)

-- | Default unrolling configuration
defaultUnrollConfig :: UnrollConfig
defaultUnrollConfig = UnrollConfig
  { ucMaxUnrollFactor = 8
  , ucMaxBodySize = 20
  , ucFullUnrollLimit = 16
  , ucPartialUnrollFactor = 4
  }

-- | Unroll result
data UnrollResult = UnrollResult
  { urOptBlocks :: ![SSABlock]    -- ^ Optimized blocks
  , urFullyUnrolled :: !Int       -- ^ Number of fully unrolled loops
  , urPartiallyUnrolled :: !Int   -- ^ Number of partially unrolled loops
  } deriving (Show)

-- | Loop trip count info
data TripCount
  = ConstantTrip !Int       -- ^ Known constant trip count
  | UnknownTrip             -- ^ Trip count unknown at compile time
  deriving (Show)

--------------------------------------------------------------------------------
-- Loop Unrolling
--------------------------------------------------------------------------------

-- | Unroll loops in SSA blocks
unrollLoops :: UnrollConfig -> SSAMethod -> UnrollResult
unrollLoops config method@SSAMethod{..} =
  let cfg = buildCFG method
      domTree = computeDominators cfg
      loops = findLoops cfg domTree
      blockMap = blockMapFromList ssaMethodBlocks

      -- Sort loops by depth (innermost first)
      sortedLoops = sortLoopsByDepth loops

      -- Unroll each loop
      (finalBlocks, fullCount, partialCount) =
        foldl' (unrollLoop config cfg) (blockMap, 0, 0) sortedLoops
  in UnrollResult
    { urOptBlocks = Map.elems finalBlocks
    , urFullyUnrolled = fullCount
    , urPartiallyUnrolled = partialCount
    }

-- | Sort loops by nesting depth (innermost first)
sortLoopsByDepth :: LoopNest -> [Loop]
sortLoopsByDepth = Map.elems  -- TODO: implement proper sorting by nesting depth

-- | Unroll a single loop
unrollLoop :: UnrollConfig -> CFG -> (Map BlockId SSABlock, Int, Int) -> Loop -> (Map BlockId SSABlock, Int, Int)
unrollLoop config cfg (blockMap, fullCount, partialCount) loop =
  let bodySize = computeBodySize blockMap loop
      tripCount = analyzeTripCount blockMap loop
  in case tripCount of
    -- Full unrolling for small constant trip counts
    ConstantTrip n
      | n <= ucFullUnrollLimit config && bodySize <= ucMaxBodySize config ->
          let (newBlocks, _) = fullyUnroll blockMap loop n
          in (newBlocks, fullCount + 1, partialCount)

    -- Partial unrolling for unknown or large trip counts
    _ | bodySize <= ucMaxBodySize config ->
          let factor = ucPartialUnrollFactor config
              (newBlocks, _) = partiallyUnroll blockMap loop factor
          in (newBlocks, fullCount, partialCount + 1)

    -- No unrolling - loop too large
    _ -> (blockMap, fullCount, partialCount)

-- | Compute the size of a loop body
computeBodySize :: Map BlockId SSABlock -> Loop -> Int
computeBodySize blockMap loop =
  sum [maybe 0 blockSize (Map.lookup bid blockMap) | bid <- Set.toList (loopBody loop)]
  where
    blockSize SSABlock{..} = length blockInstrs + length blockPhis

-- | Analyze loop trip count
analyzeTripCount :: Map BlockId SSABlock -> Loop -> TripCount
analyzeTripCount blockMap loop =
  -- Look for patterns like: i = 0; while (i < N) { ... i = i + 1; }
  case analyzeLoopBounds blockMap loop of
    Just (start, end, step)
      | step > 0 && end >= start -> ConstantTrip ((end - start + step - 1) `div` step)
      | step < 0 && start >= end -> ConstantTrip ((start - end - step - 1) `div` (-step))
    _ -> UnknownTrip

-- | Analyze loop bounds (init value, limit, step)
analyzeLoopBounds :: Map BlockId SSABlock -> Loop -> Maybe (Int, Int, Int)
analyzeLoopBounds blockMap loop = do
  -- Find the header block
  headerBlock <- Map.lookup (loopHeader loop) blockMap

  -- Look for a branch with a comparison
  case findLoopCondition (blockInstrs headerBlock) of
    Just (var, limit) -> do
      -- Find the step from back-edge block
      step <- findLoopStep blockMap loop var
      -- For now, assume init = 0
      return (0, limit, step)
    Nothing -> Nothing

-- | Find loop condition (variable compared against constant)
findLoopCondition :: [SSAInstr] -> Maybe (String, Int)
findLoopCondition instrs = case reverse instrs of
  (SSABranch (SSABinary Lt (SSAUse var) (SSAInt limit)) _ _) : _ ->
    Just (varNameString (ssaName var), limit)
  (SSABranch (SSABinary Le (SSAUse var) (SSAInt limit)) _ _) : _ ->
    Just (varNameString (ssaName var), limit + 1)
  (SSABranch (SSABinary Gt (SSAInt limit) (SSAUse var)) _ _) : _ ->
    Just (varNameString (ssaName var), limit)
  _ -> Nothing

-- | Find loop step for an induction variable
findLoopStep :: Map BlockId SSABlock -> Loop -> String -> Maybe Int
findLoopStep blockMap loop varName = do
  -- Look in all loop body blocks for assignment to the variable
  let bodyBlocks = [b | bid <- Set.toList (loopBody loop), Just b <- [Map.lookup bid blockMap]]
  findStepInBlocks varName bodyBlocks

findStepInBlocks :: String -> [SSABlock] -> Maybe Int
findStepInBlocks _ [] = Nothing
findStepInBlocks varName (SSABlock{..}:rest) =
  case findStepInInstrs varName blockInstrs of
    Just step -> Just step
    Nothing -> findStepInBlocks varName rest

findStepInInstrs :: String -> [SSAInstr] -> Maybe Int
findStepInInstrs _ [] = Nothing
findStepInInstrs varName (instr:rest) = case instr of
  SSAAssign var (SSABinary Add (SSAUse v) (SSAInt step))
    | varNameString (ssaName v) == varName || varNameString (ssaName var) == varName ->
        Just step
  SSAAssign var (SSABinary Add (SSAInt step) (SSAUse v))
    | varNameString (ssaName v) == varName || varNameString (ssaName var) == varName ->
        Just step
  SSAAssign var (SSABinary Sub (SSAUse v) (SSAInt step))
    | varNameString (ssaName v) == varName || varNameString (ssaName var) == varName ->
        Just (-step)
  _ -> findStepInInstrs varName rest

--------------------------------------------------------------------------------
-- Full Unrolling
--------------------------------------------------------------------------------

-- | Fully unroll a loop by duplicating the body n times
fullyUnroll :: Map BlockId SSABlock -> Loop -> Int -> (Map BlockId SSABlock, Int)
fullyUnroll blockMap loop n
  | n <= 0 = (blockMap, 0)
  | otherwise =
      -- For full unrolling, we:
      -- 1. Get all loop body blocks
      -- 2. Duplicate them n times with renamed labels/variables
      -- 3. Chain them together
      -- 4. Replace the loop with the unrolled sequence
      --
      -- This is complex, so for now just return unchanged
      -- TODO: implement full unrolling
      (blockMap, 0)

--------------------------------------------------------------------------------
-- Partial Unrolling
--------------------------------------------------------------------------------

-- | Partially unroll a loop by duplicating the body within the loop
partiallyUnroll :: Map BlockId SSABlock -> Loop -> Int -> (Map BlockId SSABlock, Int)
partiallyUnroll blockMap loop factor
  | factor <= 1 = (blockMap, 0)
  | otherwise =
      -- For partial unrolling, we:
      -- 1. Duplicate loop body (factor-1) times within the loop
      -- 2. Adjust the loop counter to step by (factor * original_step)
      -- 3. Add cleanup code for remaining iterations
      --
      -- This is complex, so for now just return unchanged
      -- TODO: implement partial unrolling
      (blockMap, 0)
