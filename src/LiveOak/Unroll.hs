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
  , aggressiveUnrollConfig
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
-- NOTE: Loop unrolling is DISABLED pending fixes for the following issues:
--
-- 1. Partial unrolling does not adjust loop bounds - the loop condition still
--    checks against the original limit, but with duplicated body, we iterate
--    factor*N times instead of N times.
--
-- 2. Induction variable chaining is incorrect - the loop condition uses the
--    original induction variable, not the chained variable from the last
--    duplicate.
--
-- 3. Remainder handling is missing - when trip count is not a multiple of
--    the unroll factor, we need an epilogue loop for the remaining iterations.
--
-- 4. Full unrolling has untested edge cases with phi node elimination.
--
-- To fix partial unrolling properly, we need to:
--   a) Transform: while (i < N) { body; i++; }
--   b) Into: while (i < N - (factor-1)) { body; i++; body'; i'++; ... }
--           while (i < N) { body; i++; }  // epilogue
--   c) Ensure the last duplicate's induction variable feeds back to the phi
--
defaultUnrollConfig :: UnrollConfig
defaultUnrollConfig = UnrollConfig
  { ucMaxUnrollFactor = 0     -- Disabled pending fixes
  , ucMaxBodySize = 0         -- Disabled pending fixes
  , ucFullUnrollLimit = 0     -- Disabled pending fixes
  , ucPartialUnrollFactor = 0 -- Disabled pending fixes
  }

-- | Aggressive unrolling configuration (for when bugs are fixed)
aggressiveUnrollConfig :: UnrollConfig
aggressiveUnrollConfig = UnrollConfig
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
-- Key insight: Each iteration uses values from the previous iteration.
-- - Iteration 0 uses values from before the loop (no suffix)
-- - Iteration N uses values from iteration N-1
cloneBodyNTimes :: Map BlockId SSABlock -> [BlockId] -> BlockId -> BlockId
                -> BlockId -> Int -> (Map BlockId SSABlock, [SSABlock])
cloneBodyNTimes blockMap bodyBids header latch exitTarget n =
  let -- Get the body blocks
      bodyBlocks = catMaybes [Map.lookup bid blockMap | bid <- bodyBids]

      -- Get header block to extract initialization and phi nodes
      headerBlock = Map.lookup header blockMap

      -- Collect all variables defined in the loop body (for proper chaining)
      loopDefs = collectLoopDefinitions (catMaybes [Map.lookup h blockMap | h <- [header]] ++ bodyBlocks)

      -- Generate n copies with proper cross-iteration chaining
      copies = concatMap (\i -> cloneCopyWithChaining bodyBlocks header latch exitTarget n loopDefs i) [0..n-1]

      -- Create entry block that jumps to first copy (or exit if n=0)
      -- This block provides initial values to iteration 0
      entryBlock = case headerBlock of
        Just hb ->
          let newLabel = header  -- Reuse header label
              -- First copy's entry or direct to exit
              target = if n > 0
                       then renameBlockId header 0
                       else exitTarget
              -- Keep phi nodes to capture incoming values, but redirect to first iteration
          in SSABlock newLabel [] [SSAJump target]
        Nothing -> SSABlock header [] [SSAJump exitTarget]
  in (blockMap, entryBlock : copies)

-- | Collect all variable definitions in the loop
collectLoopDefinitions :: [SSABlock] -> Set VarKey
collectLoopDefinitions blocks = Set.fromList $ concatMap blockDefs blocks
  where
    blockDefs SSABlock{..} =
      [(ssaName v, ssaVersion v) | PhiNode{phiVar = v} <- blockPhis]
      ++ [(ssaName v, ssaVersion v) | SSAAssign v _ <- blockInstrs]

-- | Clone a single iteration of the loop body with proper cross-iteration chaining
-- Key: Uses in iteration N reference definitions from iteration N-1 (or original for iter 0)
cloneCopyWithChaining :: [SSABlock] -> BlockId -> BlockId -> BlockId -> Int
                      -> Set VarKey -> Int -> [SSABlock]
cloneCopyWithChaining bodyBlocks header latch exitTarget totalIters loopDefs iterNum =
  let suffix = "_unroll_" ++ show iterNum
      isLast = iterNum == totalIters - 1
      nextHeader = if isLast then exitTarget else renameBlockId header (iterNum + 1)

      -- For iteration 0, uses reference original (unsuffixed) variables
      -- For iteration N>0, uses reference iteration N-1 variables
      prevSuffix = if iterNum == 0
                   then ""  -- Use original variable names
                   else "_unroll_" ++ show (iterNum - 1)

      renameBlock block@SSABlock{..} =
        let newLabel = renameBlockId blockLabel iterNum
            -- Rename instructions: definitions get current suffix, uses get previous suffix
            newInstrs = map (renameInstrChained suffix prevSuffix iterNum nextHeader latch loopDefs) blockInstrs
            -- For phi nodes in unrolled iterations, convert to direct assignments
            -- since there's only one predecessor per unrolled block
            newPhis = if iterNum == 0
                      then []  -- Iteration 0 gets values from entry (already set up)
                      else []  -- Later iterations use renamed values directly
        in SSABlock newLabel newPhis newInstrs
  in map renameBlock bodyBlocks

-- | Legacy clone function (kept for backwards compatibility)
cloneCopy :: [SSABlock] -> BlockId -> BlockId -> BlockId -> Int -> Int -> [SSABlock]
cloneCopy bodyBlocks header latch exitTarget totalIters iterNum =
  cloneCopyWithChaining bodyBlocks header latch exitTarget totalIters Set.empty iterNum

-- | Rename a block ID for a specific unroll iteration
renameBlockId :: BlockId -> Int -> BlockId
renameBlockId bid iter = blockId (blockIdName bid ++ "_u" ++ show iter)

-- | Rename an instruction with proper cross-iteration chaining
-- defSuffix: suffix for variables being defined (current iteration)
-- useSuffix: suffix for variables being used (previous iteration)
-- loopDefs: set of variables defined in the loop (need chaining)
renameInstrChained :: String -> String -> Int -> BlockId -> BlockId -> Set VarKey -> SSAInstr -> SSAInstr
renameInstrChained defSuffix useSuffix iter nextTarget latch loopDefs = \case
  SSAAssign var expr ->
    SSAAssign (renameVarDef defSuffix iter var)
              (renameExprChained useSuffix iter loopDefs expr)
  SSAFieldStore t f o v ->
    SSAFieldStore (renameExprChained useSuffix iter loopDefs t) f o
                  (renameExprChained useSuffix iter loopDefs v)
  SSAReturn e -> SSAReturn (fmap (renameExprChained useSuffix iter loopDefs) e)
  SSAJump target
    -- If jumping to latch, redirect to next iteration
    | target == latch -> SSAJump nextTarget
    | otherwise -> SSAJump (renameBlockId target iter)
  SSABranch cond t f ->
    SSABranch (renameExprChained useSuffix iter loopDefs cond)
              (renameBlockId t iter)
              (renameBlockId f iter)
  SSAExprStmt e -> SSAExprStmt (renameExprChained useSuffix iter loopDefs e)

-- | Rename a variable definition (gets current iteration's suffix)
renameVarDef :: String -> Int -> SSAVar -> SSAVar
renameVarDef suffix iter var@SSAVar{..} =
  var { ssaName = varName (varNameString ssaName ++ suffix ++ show iter) }

-- | Rename an expression with chained variable references
-- Only renames variables that are defined in the loop; others keep their original names
renameExprChained :: String -> Int -> Set VarKey -> SSAExpr -> SSAExpr
renameExprChained suffix iter loopDefs = \case
  SSAUse var ->
    let key = (ssaName var, ssaVersion var)
    in if Set.member key loopDefs
       then SSAUse (renameVarUse suffix iter var)
       else SSAUse var  -- Not a loop variable, keep original
  SSAUnary op e -> SSAUnary op (renameExprChained suffix iter loopDefs e)
  SSABinary op l r -> SSABinary op (renameExprChained suffix iter loopDefs l)
                                   (renameExprChained suffix iter loopDefs r)
  SSATernary c t e -> SSATernary (renameExprChained suffix iter loopDefs c)
                                  (renameExprChained suffix iter loopDefs t)
                                  (renameExprChained suffix iter loopDefs e)
  SSACall name args -> SSACall name (map (renameExprChained suffix iter loopDefs) args)
  SSAInstanceCall t m args ->
    SSAInstanceCall (renameExprChained suffix iter loopDefs t) m
                    (map (renameExprChained suffix iter loopDefs) args)
  SSANewObject cn args -> SSANewObject cn (map (renameExprChained suffix iter loopDefs) args)
  SSAFieldAccess t f -> SSAFieldAccess (renameExprChained suffix iter loopDefs t) f
  e -> e  -- Literals don't need renaming

-- | Rename a variable use (gets previous iteration's suffix)
renameVarUse :: String -> Int -> SSAVar -> SSAVar
renameVarUse suffix iter var@SSAVar{..}
  | null suffix = var  -- Iteration 0 uses original names (no suffix)
  | otherwise = var { ssaName = varName (varNameString ssaName ++ suffix) }

-- | Legacy rename instruction (for backwards compat)
renameInstr :: String -> Int -> BlockId -> BlockId -> SSAInstr -> SSAInstr
renameInstr suffix iter nextTarget latch =
  renameInstrChained suffix suffix iter nextTarget latch Set.empty

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
--
-- Key: Each duplicated body uses variables from the previous duplicate.
-- We need to properly chain the variable names across duplicates.
partiallyUnroll :: Map BlockId SSABlock -> Loop -> Int -> (Map BlockId SSABlock, Int)
partiallyUnroll blockMap loop factor
  | factor <= 1 = (blockMap, 0)
  | not (isSimpleLoop loop blockMap) = (blockMap, 0)
  | otherwise =
      let header = loopHeader loop
          bodyBlocks = Set.toList (loopBody loop)
          pureBody = filter (/= header) bodyBlocks
      in case (loopLatches loop, Map.lookup header blockMap) of
           ([latch], Just headerBlock) ->
             case Map.lookup latch blockMap of
               Just latchBlock ->
                 let -- Get all body blocks and collect loop definitions
                     allBodyBlocks = catMaybes [Map.lookup bid blockMap | bid <- pureBody]
                     loopDefs = collectLoopDefinitions (headerBlock : allBodyBlocks)

                     -- Get body instructions (non-terminators)
                     bodyInstrs = concatMap getBodyInstrs allBodyBlocks

                     -- Create duplicated instructions with proper chaining
                     -- Each duplicate i uses vars from duplicate i-1
                     -- Duplicate 0 (original) is already in the loop body
                     duplicated = concatMap (\i -> duplicateInstrsChained bodyInstrs loopDefs i) [1..factor-1]

                     -- Insert before the latch's terminator
                     -- Also need to update the latch's terminator to use the last duplicate's vars
                     latchInstrs = blockInstrs latchBlock
                     newLatchInstrs = case reverse latchInstrs of
                       (term:rest) ->
                         -- Update terminator to use vars from last duplicate
                         let lastSuffix = "_dup" ++ show (factor - 1)
                             term' = renameInstrForPartial lastSuffix loopDefs term
                         in reverse rest ++ duplicated ++ [term']
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

-- | Duplicate instructions with proper chaining for partial unrolling
-- iterNum is 1-based (duplicate 1 uses vars from original, duplicate 2 uses from duplicate 1, etc.)
duplicateInstrsChained :: [SSAInstr] -> Set VarKey -> Int -> [SSAInstr]
duplicateInstrsChained instrs loopDefs iterNum =
  let defSuffix = "_dup" ++ show iterNum
      useSuffix = if iterNum == 1
                  then ""  -- Duplicate 1 uses original (unsuffixed) vars
                  else "_dup" ++ show (iterNum - 1)
  in map (renameInstrForPartialChained defSuffix useSuffix iterNum loopDefs) instrs

-- | Rename an instruction for partial unrolling with proper chaining
renameInstrForPartialChained :: String -> String -> Int -> Set VarKey -> SSAInstr -> SSAInstr
renameInstrForPartialChained defSuffix useSuffix iter loopDefs = \case
  SSAAssign var expr ->
    SSAAssign (renameVarWithSuffix defSuffix iter var)
              (renameExprWithSuffix useSuffix loopDefs expr)
  SSAFieldStore t f o v ->
    SSAFieldStore (renameExprWithSuffix useSuffix loopDefs t) f o
                  (renameExprWithSuffix useSuffix loopDefs v)
  SSAExprStmt e -> SSAExprStmt (renameExprWithSuffix useSuffix loopDefs e)
  other -> other  -- Terminators shouldn't be here

-- | Rename instruction for partial unroll terminator update
renameInstrForPartial :: String -> Set VarKey -> SSAInstr -> SSAInstr
renameInstrForPartial suffix loopDefs = \case
  SSABranch cond t f ->
    SSABranch (renameExprWithSuffix suffix loopDefs cond) t f
  SSAJump t -> SSAJump t
  SSAReturn e -> SSAReturn (fmap (renameExprWithSuffix suffix loopDefs) e)
  other -> other

-- | Rename a variable with a specific suffix
renameVarWithSuffix :: String -> Int -> SSAVar -> SSAVar
renameVarWithSuffix suffix iter var@SSAVar{..} =
  var { ssaName = varName (varNameString ssaName ++ suffix) }

-- | Rename an expression, only renaming loop variables
renameExprWithSuffix :: String -> Set VarKey -> SSAExpr -> SSAExpr
renameExprWithSuffix suffix loopDefs = \case
  SSAUse var ->
    let key = (ssaName var, ssaVersion var)
    in if Set.member key loopDefs && not (null suffix)
       then SSAUse (var { ssaName = varName (varNameString (ssaName var) ++ suffix) })
       else SSAUse var
  SSAUnary op e -> SSAUnary op (renameExprWithSuffix suffix loopDefs e)
  SSABinary op l r -> SSABinary op (renameExprWithSuffix suffix loopDefs l)
                                   (renameExprWithSuffix suffix loopDefs r)
  SSATernary c t e -> SSATernary (renameExprWithSuffix suffix loopDefs c)
                                  (renameExprWithSuffix suffix loopDefs t)
                                  (renameExprWithSuffix suffix loopDefs e)
  SSACall name args -> SSACall name (map (renameExprWithSuffix suffix loopDefs) args)
  SSAInstanceCall t m args ->
    SSAInstanceCall (renameExprWithSuffix suffix loopDefs t) m
                    (map (renameExprWithSuffix suffix loopDefs) args)
  SSANewObject cn args -> SSANewObject cn (map (renameExprWithSuffix suffix loopDefs) args)
  SSAFieldAccess t f -> SSAFieldAccess (renameExprWithSuffix suffix loopDefs t) f
  e -> e

-- | Legacy duplicate instructions (for backwards compat)
duplicateInstrs :: [SSAInstr] -> Int -> [SSAInstr]
duplicateInstrs instrs iterNum =
  let suffix = "_dup" ++ show iterNum
  in map (renameInstrSimple suffix iterNum) instrs

-- | Legacy simple instruction renaming
renameInstrSimple :: String -> Int -> SSAInstr -> SSAInstr
renameInstrSimple suffix iter = \case
  SSAAssign var expr ->
    SSAAssign (renameVar suffix iter var) (renameExpr suffix iter expr)
  SSAFieldStore t f o v ->
    SSAFieldStore (renameExpr suffix iter t) f o (renameExpr suffix iter v)
  SSAExprStmt e -> SSAExprStmt (renameExpr suffix iter e)
  other -> other
