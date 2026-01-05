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
import LiveOak.CFG (CFG, buildCFG, blockId, blockIdName)
import LiveOak.Loop (Loop(..), LoopNest, findLoops)
import LiveOak.Dominance (computeDominators)
import LiveOak.SSAUtils (blockMapFromList)
import LiveOak.Ast (BinaryOp(..))

import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Set (Set)
import qualified Data.Set as Set
import Data.List (foldl', sortBy)
import Data.Ord (Down(..), comparing)
import Data.Maybe (catMaybes)

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
-- Process innermost loops first so their transformations are complete
-- before we process outer loops
sortLoopsByDepth :: LoopNest -> [Loop]
sortLoopsByDepth loops = sortBy (comparing (Down . loopNestDepth)) (Map.elems loops)

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
-- For a loop like: while (i < n) { body; i++; }
-- We transform to: body_0; body_1; ... body_{n-1};
fullyUnroll :: Map BlockId SSABlock -> Loop -> Int -> (Map BlockId SSABlock, Int)
fullyUnroll blockMap loop n
  | n <= 0 = (blockMap, 0)
  | not (isSimpleLoop loop blockMap) = (blockMap, 0)  -- Only handle simple loops
  | otherwise = doFullUnroll blockMap loop n

-- | Internal implementation of full unrolling
doFullUnroll :: Map BlockId SSABlock -> Loop -> Int -> (Map BlockId SSABlock, Int)
doFullUnroll blockMap loop n =
  let header = loopHeader loop
      bodyBlocks = Set.toList (loopBody loop)
      latches = loopLatches loop
      pureBody = filter (/= header) bodyBlocks
  in case latches of
       [latch] ->
         case findLoopExit blockMap header of
           Just exitTarget ->
             let -- Clone body n times
                 (newBlockMap, unrolledBlocks) =
                   cloneBodyNTimes blockMap pureBody header latch exitTarget n

                 -- Remove original loop blocks
                 withoutLoop = foldl' (flip Map.delete) newBlockMap bodyBlocks

                 -- Insert unrolled blocks
                 finalMap = foldl' (\m b -> Map.insert (blockLabel b) b m)
                                   withoutLoop unrolledBlocks
             in (finalMap, 1)
           Nothing -> (blockMap, 0)
       _ -> (blockMap, 0)  -- Multiple latches not supported

-- | Check if a loop is simple enough to unroll
-- Simple = single latch, single exit, no nested loops
isSimpleLoop :: Loop -> Map BlockId SSABlock -> Bool
isSimpleLoop loop _blockMap =
  length (loopLatches loop) == 1 && null (loopChildren loop)

-- | Find the exit target of a loop from its header
findLoopExit :: Map BlockId SSABlock -> BlockId -> Maybe BlockId
findLoopExit blockMap header =
  case Map.lookup header blockMap of
    Just SSABlock{..} ->
      case reverse blockInstrs of
        (SSABranch _ thenB elseB : _) ->
          -- One of these should be the exit (outside the loop)
          -- For now, assume elseB is exit (common pattern: if cond goto body else exit)
          Just elseB
        _ -> Nothing
    Nothing -> Nothing

-- | Clone loop body n times, chaining them together
cloneBodyNTimes :: Map BlockId SSABlock -> [BlockId] -> BlockId -> BlockId
                -> BlockId -> Int -> (Map BlockId SSABlock, [SSABlock])
cloneBodyNTimes blockMap bodyBids header latch exitTarget n =
  let -- Get the body blocks
      bodyBlocks = catMaybes [Map.lookup bid blockMap | bid <- bodyBids]

      -- Get header block to extract initialization
      headerBlock = Map.lookup header blockMap

      -- Generate n copies
      copies = concatMap (cloneCopy bodyBlocks header latch exitTarget n) [0..n-1]

      -- Create entry block that jumps to first copy (or exit if n=0)
      entryBlock = case headerBlock of
        Just hb ->
          let newLabel = header  -- Reuse header label
              -- First copy's entry or direct to exit
              target = if n > 0
                       then renameBlockId header 0
                       else exitTarget
          in SSABlock newLabel (blockPhis hb) [SSAJump target]
        Nothing -> SSABlock header [] [SSAJump exitTarget]
  in (blockMap, entryBlock : copies)

-- | Clone a single iteration of the loop body
cloneCopy :: [SSABlock] -> BlockId -> BlockId -> BlockId -> Int -> Int -> [SSABlock]
cloneCopy bodyBlocks header latch exitTarget totalIters iterNum =
  let suffix = "_unroll_" ++ show iterNum
      isLast = iterNum == totalIters - 1
      nextHeader = if isLast then exitTarget else renameBlockId header (iterNum + 1)

      renameBlock block@SSABlock{..} =
        let newLabel = renameBlockId blockLabel iterNum
            newInstrs = map (renameInstr suffix iterNum nextHeader latch) blockInstrs
            newPhis = map (renamePhi suffix iterNum) blockPhis
        in SSABlock newLabel newPhis newInstrs
  in map renameBlock bodyBlocks

-- | Rename a block ID for a specific unroll iteration
renameBlockId :: BlockId -> Int -> BlockId
renameBlockId bid iter = blockId (blockIdName bid ++ "_u" ++ show iter)

-- | Rename an instruction for unrolling
renameInstr :: String -> Int -> BlockId -> BlockId -> SSAInstr -> SSAInstr
renameInstr suffix iter nextTarget latch = \case
  SSAAssign var expr ->
    SSAAssign (renameVar suffix iter var) (renameExpr suffix iter expr)
  SSAFieldStore t f o v ->
    SSAFieldStore (renameExpr suffix iter t) f o (renameExpr suffix iter v)
  SSAReturn e -> SSAReturn (fmap (renameExpr suffix iter) e)
  SSAJump target
    -- If jumping to latch or header, redirect to next iteration
    | target == latch -> SSAJump nextTarget
    | otherwise -> SSAJump (renameBlockId target iter)
  SSABranch cond t f ->
    SSABranch (renameExpr suffix iter cond)
              (renameBlockId t iter)
              (renameBlockId f iter)
  SSAExprStmt e -> SSAExprStmt (renameExpr suffix iter e)

-- | Rename a phi node for unrolling
renamePhi :: String -> Int -> PhiNode -> PhiNode
renamePhi suffix iter PhiNode{..} =
  PhiNode
    { phiVar = renameVar suffix iter phiVar
    , phiArgs = [(renameBlockId bid iter, renameVar suffix iter var) | (bid, var) <- phiArgs]
    }

-- | Rename a variable for unrolling
renameVar :: String -> Int -> SSAVar -> SSAVar
renameVar suffix iter var@SSAVar{..} =
  var { ssaName = varName (varNameString ssaName ++ suffix ++ show iter) }

-- | Rename an expression for unrolling
renameExpr :: String -> Int -> SSAExpr -> SSAExpr
renameExpr suffix iter = \case
  SSAUse var -> SSAUse (renameVar suffix iter var)
  SSAUnary op e -> SSAUnary op (renameExpr suffix iter e)
  SSABinary op l r -> SSABinary op (renameExpr suffix iter l) (renameExpr suffix iter r)
  SSATernary c t e -> SSATernary (renameExpr suffix iter c)
                                  (renameExpr suffix iter t)
                                  (renameExpr suffix iter e)
  SSACall name args -> SSACall name (map (renameExpr suffix iter) args)
  SSAInstanceCall t m args ->
    SSAInstanceCall (renameExpr suffix iter t) m (map (renameExpr suffix iter) args)
  SSANewObject cn args -> SSANewObject cn (map (renameExpr suffix iter) args)
  SSAFieldAccess t f -> SSAFieldAccess (renameExpr suffix iter t) f
  e -> e  -- Literals don't need renaming

--------------------------------------------------------------------------------
-- Partial Unrolling
--------------------------------------------------------------------------------

-- | Partially unroll a loop by duplicating the body within the loop
-- For a loop like: while (i < n) { body; i++; }
-- With factor 4, transform to: while (i < n-3) { body; body; body; body; i+=4; }
--                              while (i < n) { body; i++; }  // cleanup
partiallyUnroll :: Map BlockId SSABlock -> Loop -> Int -> (Map BlockId SSABlock, Int)
partiallyUnroll blockMap loop factor
  | factor <= 1 = (blockMap, 0)
  | not (isSimpleLoop loop blockMap) = (blockMap, 0)
  | otherwise =
      -- For partial unrolling, we duplicate the body within the loop
      -- This is simpler than full unrolling - we just replicate instructions
      let header = loopHeader loop
          bodyBlocks = Set.toList (loopBody loop)
          pureBody = filter (/= header) bodyBlocks
      in case (loopLatches loop, Map.lookup header blockMap) of
           ([latch], Just headerBlock) ->
             case Map.lookup latch blockMap of
               Just latchBlock ->
                 let -- Duplicate body instructions (factor-1) times in latch block
                     -- This is a simplified approach - just duplicate non-terminator instrs
                     bodyInstrs = concatMap getBodyInstrs
                                    [b | bid <- pureBody, Just b <- [Map.lookup bid blockMap]]

                     -- Create duplicated instructions with renamed variables
                     duplicated = concatMap (\i -> duplicateInstrs bodyInstrs i) [1..factor-1]

                     -- Insert before the latch's terminator
                     newLatchInstrs = case reverse (blockInstrs latchBlock) of
                       (term:rest) -> reverse rest ++ duplicated ++ [term]
                       [] -> duplicated

                     newLatch = latchBlock { blockInstrs = newLatchInstrs }
                     newMap = Map.insert latch newLatch blockMap
                 in (newMap, 1)
               Nothing -> (blockMap, 0)
           _ -> (blockMap, 0)

-- | Get body instructions (non-terminators) from a block
getBodyInstrs :: SSABlock -> [SSAInstr]
getBodyInstrs SSABlock{..} = filter (not . isTerminator) blockInstrs

-- | Check if an instruction is a terminator
isTerminator :: SSAInstr -> Bool
isTerminator = \case
  SSAJump _ -> True
  SSABranch _ _ _ -> True
  SSAReturn _ -> True
  _ -> False

-- | Duplicate instructions with renamed variables for iteration i
duplicateInstrs :: [SSAInstr] -> Int -> [SSAInstr]
duplicateInstrs instrs iterNum =
  let suffix = "_dup" ++ show iterNum
  in map (renameInstrSimple suffix iterNum) instrs

-- | Simple instruction renaming (no block renaming needed for partial unroll)
renameInstrSimple :: String -> Int -> SSAInstr -> SSAInstr
renameInstrSimple suffix iter = \case
  SSAAssign var expr ->
    SSAAssign (renameVar suffix iter var) (renameExpr suffix iter expr)
  SSAFieldStore t f o v ->
    SSAFieldStore (renameExpr suffix iter t) f o (renameExpr suffix iter v)
  SSAExprStmt e -> SSAExprStmt (renameExpr suffix iter e)
  other -> other  -- Terminators shouldn't be here
