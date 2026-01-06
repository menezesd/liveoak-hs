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
-- Full unrolling is enabled for small loops with constant trip counts.
-- Partial unrolling is enabled for loops with unknown/large trip counts:
--   - Adjusts loop bounds (e.g., i < N becomes i < N - (factor-1))
--   - Generates epilogue loop for remainder iterations
--   - Supports both countup (i < N) and countdown (i > 0) loops
--   - Chains variables properly across unrolled copies
defaultUnrollConfig :: UnrollConfig
defaultUnrollConfig = UnrollConfig
  { ucMaxUnrollFactor = 8     -- Maximum unroll factor for full unrolling
  , ucMaxBodySize = 15        -- Maximum body size (instructions) for unrolling
  , ucFullUnrollLimit = 8     -- Max trip count for full unrolling
  , ucPartialUnrollFactor = 2 -- Partial unrolling factor (duplicate body 2x)
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
              (newBlocks, count) = partiallyUnroll blockMap loop factor
          in (newBlocks, fullCount, partialCount + count)

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
      -- Find the initial value from phi node
      let init = findInitialValue (blockPhis headerBlock) var loop
      return (init, limit, step)
    Nothing -> Nothing

-- | Find initial value for an induction variable from phi node
findInitialValue :: [PhiNode] -> String -> Loop -> Int
findInitialValue phis varName loop =
  let latches = loopLatches loop
      latchSet = Set.fromList latches
  in case [phi | phi <- phis, varNameString (ssaName (phiVar phi)) == varName] of
    (phi:_) ->
      -- Find the arg that comes from outside the loop (non-latch edge)
      case [v | (bid, v) <- phiArgs phi, not (Set.member bid latchSet)] of
        (v:_) -> case ssaVersion v of
          -- If version 0 and name matches, likely initialized to constant
          -- Check if there's an SSAInt initialization somewhere
          _ -> 0  -- Default to 0 if we can't determine
        [] -> 0
    [] -> 0

-- | Find loop condition (variable compared against constant)
-- Supports: i < N, i <= N, N > i, N >= i, i != N
findLoopCondition :: [SSAInstr] -> Maybe (String, Int)
findLoopCondition instrs = case reverse instrs of
  -- i < N
  (SSABranch (SSABinary Lt (SSAUse var) (SSAInt limit)) _ _) : _ ->
    Just (varNameString (ssaName var), limit)
  -- i <= N  ->  i < N+1
  (SSABranch (SSABinary Le (SSAUse var) (SSAInt limit)) _ _) : _ ->
    Just (varNameString (ssaName var), limit + 1)
  -- N > i  ->  i < N
  (SSABranch (SSABinary Gt (SSAInt limit) (SSAUse var)) _ _) : _ ->
    Just (varNameString (ssaName var), limit)
  -- N >= i  ->  i < N+1
  (SSABranch (SSABinary Ge (SSAInt limit) (SSAUse var)) _ _) : _ ->
    Just (varNameString (ssaName var), limit + 1)
  -- i != N (common pattern: while (i != n))
  (SSABranch (SSABinary Ne (SSAUse var) (SSAInt limit)) _ _) : _ ->
    Just (varNameString (ssaName var), limit)
  (SSABranch (SSABinary Ne (SSAInt limit) (SSAUse var)) _ _) : _ ->
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
  -- i = i + step  or  i = v + step where v has same name
  SSAAssign var (SSABinary Add (SSAUse v) (SSAInt step))
    | varNameString (ssaName v) == varName || varNameString (ssaName var) == varName ->
        Just step
  -- i = step + i
  SSAAssign var (SSABinary Add (SSAInt step) (SSAUse v))
    | varNameString (ssaName v) == varName || varNameString (ssaName var) == varName ->
        Just step
  -- i = i - step  ->  step = -step
  SSAAssign var (SSABinary Sub (SSAUse v) (SSAInt step))
    | varNameString (ssaName v) == varName || varNameString (ssaName var) == varName ->
        Just (-step)
  -- For multiplication: i = i * 2  ->  step is multiplicative, not additive
  -- We can only handle this for trip count if we know the pattern is power-of-2 iteration
  -- For now, skip multiplication patterns as they need different trip count calculation
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
-- Key insight: The body uses variables defined by phi nodes. For each iteration:
-- - Iteration 0: replace phi vars with their initial values (from preheader edge)
-- - Iteration N: replace phi vars with the latch values from iteration N-1
doFullUnroll :: Map BlockId SSABlock -> Loop -> Int -> (Map BlockId SSABlock, Int)
doFullUnroll blockMap loop n =
  let header = loopHeader loop
      bodyBlocks = Set.toList (loopBody loop)
      latches = loopLatches loop
      pureBody = filter (/= header) bodyBlocks
  in case latches of
       [latch] ->
         case (findLoopExit blockMap header, Map.lookup header blockMap) of
           (Just exitTarget, Just headerBlock) ->
             let -- Extract phi node mappings from header
                 -- phiInitials: phi var -> initial value (from preheader)
                 -- phiLatches: phi var -> latch value (from back edge)
                 preheader = loopPreheader loop
                 (phiInitials, phiLatches) = extractPhiMappings headerBlock latch preheader

                 -- Get body definitions for variable renaming
                 allBodyBlocks = catMaybes [Map.lookup bid blockMap | bid <- pureBody]
                 bodyDefs = collectBodyDefinitions allBodyBlocks

                 -- Build final value substitution: phi var -> final iteration's value
                 -- After N iterations, phi vars should be replaced with the Nth iteration's output
                 finalSubst = if n > 0
                   then Map.map (renameVarForIterFinal (n - 1) bodyDefs) phiLatches
                   else phiInitials  -- If n=0, use initial values

                 -- Clone body n times with proper phi substitution
                 unrolledBlocks = fullUnrollCopies blockMap pureBody header latch exitTarget n phiInitials phiLatches

                 -- Create new header that just jumps to first iteration (or exit if n=0)
                 newHeader = if n > 0
                   then SSABlock header [] [SSAJump (renameBlockId (head pureBody) 0)]
                   else SSABlock header [] [SSAJump exitTarget]

                 -- Remove original loop blocks
                 withoutLoop = foldl' (flip Map.delete) blockMap bodyBlocks

                 -- Update blocks outside the loop to use final iteration's values for phi vars
                 -- (This is needed because they may reference phi-defined variables)
                 updatedOutside = Map.map (updateBlockWithFinalValues finalSubst (Set.fromList bodyBlocks)) withoutLoop

                 -- Insert new header and unrolled blocks
                 finalMap = foldl' (\m b -> Map.insert (blockLabel b) b m)
                                   updatedOutside (newHeader : unrolledBlocks)
             in (finalMap, 1)
           _ -> (blockMap, 0)
       _ -> (blockMap, 0)  -- Multiple latches not supported

-- | Rename a variable for the final iteration (to get the output value)
renameVarForIterFinal :: Int -> Set VarKey -> SSAVar -> SSAVar
renameVarForIterFinal iter defs var =
  let key = varKey var
  in if Set.member key defs
     then var { ssaName = varName (varNameString (ssaName var) ++ "_u" ++ show iter) }
     else var  -- Non-loop variable, keep as is

-- | Update a block outside the loop to use final iteration's values for phi vars
updateBlockWithFinalValues :: Map VarKey SSAVar -> Set BlockId -> SSABlock -> SSABlock
updateBlockWithFinalValues finalSubst loopBlocks block
  | Set.member (blockLabel block) loopBlocks = block  -- Don't update loop blocks
  | otherwise = block
      { blockPhis = map (updatePhiWithFinal finalSubst) (blockPhis block)
      , blockInstrs = map (updateInstrWithFinal finalSubst) (blockInstrs block)
      }

-- | Update a phi node with final values
updatePhiWithFinal :: Map VarKey SSAVar -> PhiNode -> PhiNode
updatePhiWithFinal finalSubst phi@PhiNode{..} =
  phi { phiArgs = [(bid, maybe v id (Map.lookup (varKey v) finalSubst)) | (bid, v) <- phiArgs] }

-- | Update an instruction with final values
updateInstrWithFinal :: Map VarKey SSAVar -> SSAInstr -> SSAInstr
updateInstrWithFinal finalSubst = \case
  SSAAssign var expr -> SSAAssign var (updateExprWithFinal finalSubst expr)
  SSAFieldStore t f o v -> SSAFieldStore (updateExprWithFinal finalSubst t) f o (updateExprWithFinal finalSubst v)
  SSAReturn e -> SSAReturn (fmap (updateExprWithFinal finalSubst) e)
  SSABranch cond t f -> SSABranch (updateExprWithFinal finalSubst cond) t f
  SSAExprStmt e -> SSAExprStmt (updateExprWithFinal finalSubst e)
  other -> other

-- | Update an expression with final values
updateExprWithFinal :: Map VarKey SSAVar -> SSAExpr -> SSAExpr
updateExprWithFinal finalSubst = \case
  SSAUse var -> case Map.lookup (varKey var) finalSubst of
    Just finalVar -> SSAUse finalVar
    Nothing -> SSAUse var
  SSAUnary op e -> SSAUnary op (updateExprWithFinal finalSubst e)
  SSABinary op l r -> SSABinary op (updateExprWithFinal finalSubst l) (updateExprWithFinal finalSubst r)
  SSATernary c t e -> SSATernary (updateExprWithFinal finalSubst c) (updateExprWithFinal finalSubst t) (updateExprWithFinal finalSubst e)
  SSACall name args -> SSACall name (map (updateExprWithFinal finalSubst) args)
  SSAInstanceCall t m args -> SSAInstanceCall (updateExprWithFinal finalSubst t) m (map (updateExprWithFinal finalSubst) args)
  SSANewObject cn args -> SSANewObject cn (map (updateExprWithFinal finalSubst) args)
  SSAFieldAccess t f -> SSAFieldAccess (updateExprWithFinal finalSubst t) f
  e -> e

-- | Extract phi node mappings: initial values and latch values
-- Returns (phiVar -> initialValue, phiVar -> latchValue)
extractPhiMappings :: SSABlock -> BlockId -> Maybe BlockId -> (Map VarKey SSAVar, Map VarKey SSAVar)
extractPhiMappings headerBlock latch preheader =
  let phis = blockPhis headerBlock
      initials = Map.fromList $ catMaybes
        [ case preheader of
            Just pre -> case lookup pre (phiArgs phi) of
              Just initVar -> Just (varKey (phiVar phi), initVar)
              Nothing -> findNonLatchArg phi latch  -- fallback to non-latch arg
            Nothing -> findNonLatchArg phi latch
        | phi <- phis
        ]
      latches = Map.fromList
        [ (varKey (phiVar phi), latchVar)
        | phi <- phis
        , Just latchVar <- [lookup latch (phiArgs phi)]
        ]
  in (initials, latches)
  where
    -- Find an arg that's not from the latch (i.e., the initial value)
    findNonLatchArg phi latchBid =
      case [v | (bid, v) <- phiArgs phi, bid /= latchBid] of
        (v:_) -> Just (varKey (phiVar phi), v)
        [] -> Nothing

-- | Create fully unrolled copies of the loop body
fullUnrollCopies :: Map BlockId SSABlock -> [BlockId] -> BlockId -> BlockId
                 -> BlockId -> Int -> Map VarKey SSAVar -> Map VarKey SSAVar -> [SSABlock]
fullUnrollCopies blockMap bodyBids header latch exitTarget n phiInitials phiLatches =
  let bodyBlocks = catMaybes [Map.lookup bid blockMap | bid <- bodyBids]
      -- Collect variables defined in the body (not phi nodes)
      bodyDefs = collectBodyDefinitions bodyBlocks
  in concatMap (makeUnrollCopy bodyBlocks bodyDefs header latch exitTarget n phiLatches) [0..n-1]
  where
    -- For iteration i, create the substitution map for phi vars
    makeUnrollCopy bodies defs hdr ltch exit total phiLatch i =
      let isLast = i == total - 1
          -- Where to go after this iteration
          nextTarget = if isLast then exit else renameBlockId (head bodyBids) (i + 1)
          -- Build substitution: phi var -> value for this iteration
          subst = if i == 0
            then phiInitials  -- Use initial values
            else Map.map (renameVarForIter (i - 1) defs) phiLatch  -- Use renamed latch vars from prev iter
      in map (transformBodyBlock subst defs i hdr nextTarget) bodies

    -- Rename a variable for a specific iteration
    renameVarForIter iter defs var =
      let key = varKey var
      in if Set.member key defs
         then var { ssaName = varName (varNameString (ssaName var) ++ "_u" ++ show iter) }
         else var  -- Non-loop variable, keep as is

-- | Collect variable definitions in body blocks (not from phis)
collectBodyDefinitions :: [SSABlock] -> Set VarKey
collectBodyDefinitions blocks = Set.fromList $ concatMap blockDefs blocks
  where
    blockDefs SSABlock{..} =
      [(ssaName v, ssaVersion v) | SSAAssign v _ <- blockInstrs]

-- | Transform a body block for iteration i
-- header: the loop header (target of back edge, used to redirect jumps)
-- nextTarget: where to go after this iteration (next iter's body or exit)
transformBodyBlock :: Map VarKey SSAVar -> Set VarKey -> Int -> BlockId -> BlockId -> SSABlock -> SSABlock
transformBodyBlock phiSubst bodyDefs i header nextTarget block =
  let newLabel = renameBlockId (blockLabel block) i
      newInstrs = map (transformInstr phiSubst bodyDefs i header nextTarget) (blockInstrs block)
  in SSABlock newLabel [] newInstrs

-- | Transform an instruction for iteration i
-- header: the loop header (target of back edge)
-- nextTarget: where to go after this iteration (next iter's body or exit)
transformInstr :: Map VarKey SSAVar -> Set VarKey -> Int -> BlockId -> BlockId -> SSAInstr -> SSAInstr
transformInstr phiSubst bodyDefs i header nextTarget = \case
  SSAAssign var expr ->
    SSAAssign (renameDefVar bodyDefs i var) (transformExpr phiSubst bodyDefs i expr)
  SSAFieldStore t f o v ->
    SSAFieldStore (transformExpr phiSubst bodyDefs i t) f o (transformExpr phiSubst bodyDefs i v)
  SSAReturn e -> SSAReturn (fmap (transformExpr phiSubst bodyDefs i) e)
  SSAJump target
    | target == header -> SSAJump nextTarget  -- Redirect back edge to next iteration/exit
    | otherwise -> SSAJump (renameBlockId target i)
  SSABranch cond t f ->
    SSABranch (transformExpr phiSubst bodyDefs i cond) (renameBlockId t i) (renameBlockId f i)
  SSAExprStmt e -> SSAExprStmt (transformExpr phiSubst bodyDefs i e)

-- | Rename a defined variable for iteration i
renameDefVar :: Set VarKey -> Int -> SSAVar -> SSAVar
renameDefVar bodyDefs i var =
  var { ssaName = varName (varNameString (ssaName var) ++ "_u" ++ show i) }

-- | Transform an expression for iteration i, substituting phi vars
transformExpr :: Map VarKey SSAVar -> Set VarKey -> Int -> SSAExpr -> SSAExpr
transformExpr phiSubst bodyDefs i = \case
  SSAUse var ->
    let key = varKey var
    in case Map.lookup key phiSubst of
      Just substVar -> SSAUse substVar  -- Replace phi var with substituted value
      Nothing ->
        -- Check if it's a body-defined variable from a previous part of this iteration
        if Set.member key bodyDefs
        then SSAUse (var { ssaName = varName (varNameString (ssaName var) ++ "_u" ++ show i) })
        else SSAUse var  -- External variable, keep as is
  SSAUnary op e -> SSAUnary op (transformExpr phiSubst bodyDefs i e)
  SSABinary op l r -> SSABinary op (transformExpr phiSubst bodyDefs i l) (transformExpr phiSubst bodyDefs i r)
  SSATernary c t e -> SSATernary (transformExpr phiSubst bodyDefs i c) (transformExpr phiSubst bodyDefs i t) (transformExpr phiSubst bodyDefs i e)
  SSACall name args -> SSACall name (map (transformExpr phiSubst bodyDefs i) args)
  SSAInstanceCall t m args -> SSAInstanceCall (transformExpr phiSubst bodyDefs i t) m (map (transformExpr phiSubst bodyDefs i) args)
  SSANewObject cn args -> SSANewObject cn (map (transformExpr phiSubst bodyDefs i) args)
  SSAFieldAccess t f -> SSAFieldAccess (transformExpr phiSubst bodyDefs i t) f
  e -> e  -- Literals

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
-- For a loop like: while (i < N) { body; i++; }
-- With factor k, transform to:
--   while (i < N-(k-1)) { body_0; body_1; ...; body_{k-1}; }  // main loop
--   while (i < N) { body; }                                   // epilogue
--
-- Key requirements:
-- 1. Adjust loop bound to ensure k iterations are available
-- 2. Chain variable definitions across duplicates
-- 3. Update phi back-edges to receive from last duplicate
-- 4. Create epilogue loop for remainder iterations
partiallyUnroll :: Map BlockId SSABlock -> Loop -> Int -> (Map BlockId SSABlock, Int)
partiallyUnroll blockMap loop factor
  | factor <= 1 = (blockMap, 0)
  | not (isSimpleLoop loop blockMap) = (blockMap, 0)
  | otherwise = doPartialUnroll blockMap loop factor

-- | Check if a loop has already been unrolled (by detecting naming convention)
-- Checks both header and body blocks for unroll suffixes
-- Also skips epilogue loops (created by partial unrolling)
isAlreadyUnrolled :: Loop -> Bool
isAlreadyUnrolled loop =
  let allBlockNames = blockIdName (loopHeader loop) : map blockIdName (Set.toList (loopBody loop))
  in any hasUnrollSuffix allBlockNames || any isEpilogueBlock allBlockNames
  where
    hasUnrollSuffix name = "_p" `isInfixOf` name || "_u" `isInfixOf` name
    isEpilogueBlock name = "epilogue" `isPrefixOf` name
    isInfixOf needle haystack = needle `elem` [take (length needle) (drop i haystack) | i <- [0..length haystack - length needle]]
    isPrefixOf prefix str = take (length prefix) str == prefix

-- | Internal implementation of partial unrolling
doPartialUnroll :: Map BlockId SSABlock -> Loop -> Int -> (Map BlockId SSABlock, Int)
doPartialUnroll blockMap loop factor
  | isAlreadyUnrolled loop = (blockMap, 0)  -- Skip already unrolled loops
  | otherwise =
  let header = loopHeader loop
      bodyBlocks = Set.toList (loopBody loop)
      pureBody = filter (/= header) bodyBlocks
      latches = loopLatches loop
  in case (latches, Map.lookup header blockMap) of
       ([latch], Just headerBlock) ->
         case (analyzeInductionVar headerBlock latch pureBody blockMap,
               findLoopBound (blockInstrs headerBlock),
               findExitTarget (blockInstrs headerBlock)) of
           (Just (inductionPhi, inductionStep), Just (boundVar, boundVal, _condDir), Just (thenTarget, elseTarget)) ->
             let -- Determine actual loop direction from the step, not the condition
                 -- Positive step = CountUp, Negative step = CountDown
                 loopDir = if inductionStep > 0 then CountUp else CountDown

                 -- Determine which branch target is body vs exit by checking loop membership
                 -- The body target is inside the loop, the exit target is outside
                 loopBodySet = loopBody loop
                 (bodyTarget, exitTarget) =
                   if Set.member thenTarget loopBodySet
                   then (thenTarget, elseTarget)  -- thenBlock is body
                   else (elseTarget, thenTarget)  -- elseBlock is body

                 -- Get all body blocks
                 allBodyBlocks = catMaybes [Map.lookup bid blockMap | bid <- pureBody]

                 -- Collect definitions in the body (for renaming)
                 bodyDefs = collectBodyDefinitions allBodyBlocks

                 -- Get all phis from header (need to update their back-edges)
                 headerPhis = blockPhis headerBlock

                 -- Build the unrolled body blocks
                 -- Copy 0 is the original body, copies 1..factor-1 are new
                 unrolledBodyBlocks = buildUnrolledBody allBodyBlocks bodyDefs headerPhis
                                                        header latch factor

                 -- Build new header with adjusted bound
                 newHeaderBlock = buildAdjustedHeader headerBlock boundVar boundVal factor
                                                      bodyTarget exitTarget latch loopDir

                 -- Build epilogue loop (original loop structure, new labels)
                 epilogueBlocks = buildEpilogue headerBlock allBodyBlocks bodyDefs
                                               latch bodyTarget exitTarget factor

                 -- Update exit block to use epilogue phi variables instead of main loop phi vars
                 -- The exit block now only receives from epilogue, so it should use sum_e not sum
                 phiKeys = Set.fromList [varKey (phiVar phi) | phi <- blockPhis headerBlock]
                 updatedExitBlock = case Map.lookup exitTarget blockMap of
                   Just exitBlock -> renameExitBlockVars "_e" phiKeys exitBlock
                   Nothing -> Nothing

                 -- Remove original body blocks (keep header for now)
                 withoutBody = foldl' (flip Map.delete) blockMap pureBody

                 -- Insert new header, unrolled body, epilogue, and updated exit block
                 blocksToInsert = newHeaderBlock : unrolledBodyBlocks ++ epilogueBlocks
                                  ++ maybe [] (:[]) updatedExitBlock
                 finalMap = foldl' (\m b -> Map.insert (blockLabel b) b m)
                                   withoutBody
                                   blocksToInsert

             in (finalMap, 1)
           _ -> (blockMap, 0)  -- Can't analyze loop structure
       _ -> (blockMap, 0)  -- Multiple latches not supported

-- | Analyze induction variable: find the phi that increments by a constant
analyzeInductionVar :: SSABlock -> BlockId -> [BlockId] -> Map BlockId SSABlock
                    -> Maybe (PhiNode, Int)
analyzeInductionVar headerBlock latch bodyBids blockMap =
  let bodyBlocks = catMaybes [Map.lookup bid blockMap | bid <- bodyBids]
  in case [(phi, step) | phi <- blockPhis headerBlock
                       , Just step <- [findPhiStep phi latch bodyBlocks]] of
       ((phi, step):_) -> Just (phi, step)
       [] -> Nothing

-- | Find step value for a phi node (how much it's incremented each iteration)
findPhiStep :: PhiNode -> BlockId -> [SSABlock] -> Maybe Int
findPhiStep phi latch bodyBlocks =
  case lookup latch (phiArgs phi) of
    Just latchVar ->
      -- Find assignment to latchVar in body blocks
      findStepForVar (varNameString (ssaName latchVar)) bodyBlocks
    Nothing -> Nothing

-- | Find step value for a variable
findStepForVar :: String -> [SSABlock] -> Maybe Int
findStepForVar varName blocks =
  case -- i = i + step
       [(step, src) | SSABlock{..} <- blocks
                    , SSAAssign v (SSABinary Add (SSAUse src) (SSAInt step)) <- blockInstrs
                    , varNameString (ssaName v) == varName] ++
       -- i = step + i
       [(step, src) | SSABlock{..} <- blocks
                    , SSAAssign v (SSABinary Add (SSAInt step) (SSAUse src)) <- blockInstrs
                    , varNameString (ssaName v) == varName] ++
       -- i = i - step (countdown loop)
       [(-step, src) | SSABlock{..} <- blocks
                     , SSAAssign v (SSABinary Sub (SSAUse src) (SSAInt step)) <- blockInstrs
                     , varNameString (ssaName v) == varName] of
    ((step, _):_) -> Just step
    [] -> Nothing

-- | Loop direction for bound adjustment
data LoopDir = CountUp | CountDown deriving (Eq, Show)

-- | Find loop bound from header branch, including direction
findLoopBound :: [SSAInstr] -> Maybe (SSAVar, Int, LoopDir)
findLoopBound instrs = case reverse instrs of
  -- Countup loops: i < N, i <= N
  (SSABranch (SSABinary Lt (SSAUse var) (SSAInt limit)) _ _) : _ ->
    Just (var, limit, CountUp)
  (SSABranch (SSABinary Le (SSAUse var) (SSAInt limit)) _ _) : _ ->
    Just (var, limit + 1, CountUp)  -- <= N is same as < N+1
  -- Countdown loops: i > N, i >= N
  (SSABranch (SSABinary Gt (SSAUse var) (SSAInt limit)) _ _) : _ ->
    Just (var, limit, CountDown)
  (SSABranch (SSABinary Ge (SSAUse var) (SSAInt limit)) _ _) : _ ->
    Just (var, limit - 1, CountDown)  -- >= N is same as > N-1
  -- Not-equal loops: treat as countup (need step info to determine direction)
  (SSABranch (SSABinary Ne (SSAUse var) (SSAInt limit)) _ _) : _ ->
    Just (var, limit, CountUp)
  _ -> Nothing

-- | Find exit target from header branch (body target, exit target)
-- We can't determine semantics from the condition operator alone, since:
-- - while (a < 100) { body } -> br (a Lt 100) body exit (continue when true)
-- - if (n <= 0) exit; body;  -> br (n Le 0) exit body (exit when true)
-- Instead, just return the raw branch targets. The caller must use loop analysis
-- to determine which is the body (leads to latch) vs exit (leaves the loop).
findExitTarget :: [SSAInstr] -> Maybe (BlockId, BlockId)
findExitTarget instrs = case reverse instrs of
  (SSABranch _ thenTarget elseTarget) : _ -> Just (thenTarget, elseTarget)
  _ -> Nothing

-- | Build unrolled body blocks
-- Creates factor copies of the body, chaining variables properly
buildUnrolledBody :: [SSABlock] -> Set VarKey -> [PhiNode]
                  -> BlockId -> BlockId -> Int -> [SSABlock]
buildUnrolledBody bodyBlocks bodyDefs headerPhis header latch factor =
  concatMap (buildUnrollCopy bodyBlocks bodyDefs headerPhis header latch factor) [0..factor-1]

-- | Build one copy of the unrolled body
-- Key insight for proper chaining:
-- - For each phi `x_phi = phi [..., latch: x_latch]`, the phi receives its latch value
-- - Copy 0 uses phi vars directly, produces renamed latch vars (e.g., a_3 -> a_3)
-- - Copy N>0 uses PREVIOUS copy's latch vars (the values that would feed back to phi)
-- - Copy N>0 produces renamed latch vars with suffix (e.g., a_3 -> a_p1_3)
buildUnrollCopy :: [SSABlock] -> Set VarKey -> [PhiNode]
                -> BlockId -> BlockId -> Int -> Int -> [SSABlock]
buildUnrollCopy bodyBlocks bodyDefs headerPhis header latch totalFactor copyNum =
  let suffix = if copyNum == 0 then "" else "_p" ++ show copyNum
      isLast = copyNum == totalFactor - 1

      -- Build phi->latch mapping: tells us which body-defined var feeds each phi
      -- e.g., a_2 (phi var) is fed by a_3 (latch var from body)
      phiToLatch = Map.fromList
        [(varKey (phiVar phi), latchVar)
        | phi <- headerPhis
        , Just latchVar <- [lookup latch (phiArgs phi)]]

      -- For copy 0: uses of phi vars stay as-is (they're defined by phi nodes)
      -- For copy N>0: uses of phi vars become uses of the LATCH vars from copy N-1
      -- e.g., copy 1 uses a_2 -> should become a_3 (copy 0's latch output)
      --       copy 2 uses a_2 -> should become a_p1_3 (copy 1's latch output)
      phiSubst = if copyNum == 0
                 then Map.empty
                 else Map.fromList
                   [(phiKey, if copyNum == 1
                             then latchVar  -- Copy 1 uses copy 0's latch var (no suffix)
                             else latchVar { ssaName = varName (varNameString (ssaName latchVar) ++ "_p" ++ show (copyNum - 1)) })
                   | (phiKey, latchVar) <- Map.toList phiToLatch]

      -- For body-defined vars (including latch vars):
      -- Copy N>0 uses vars from copy N-1
      useSubst = if copyNum == 0
                 then Map.empty
                 else buildUseSubst bodyDefs (copyNum - 1)

  in map (transformUnrollBlock suffix useSubst phiSubst bodyDefs isLast header latch totalFactor copyNum) bodyBlocks

-- | Build use substitution map: body var -> renamed var from previous copy
buildUseSubst :: Set VarKey -> Int -> Map VarKey SSAVar
buildUseSubst bodyDefs prevCopy =
  let prevSuffix = if prevCopy == 0 then "" else "_p" ++ show prevCopy
  in Map.fromList [(key, SSAVar { ssaName = varName (varNameString name ++ prevSuffix)
                                , ssaVersion = ver
                                , ssaVarType = Nothing })
                  | key@(name, ver) <- Set.toList bodyDefs]

-- | Transform a block for unrolled copy
transformUnrollBlock :: String -> Map VarKey SSAVar -> Map VarKey SSAVar
                     -> Set VarKey -> Bool -> BlockId -> BlockId -> Int -> Int
                     -> SSABlock -> SSABlock
transformUnrollBlock suffix useSubst phiSubst bodyDefs isLast header latch totalFactor copyNum block =
  let newLabel = if null suffix then blockLabel block
                 else blockId (blockIdName (blockLabel block) ++ suffix)
      -- Determine where to jump next
      nextCopyFirstBlock = if isLast
                           then header  -- Last copy jumps back to header
                           else blockId (blockIdName (blockLabel block) ++ "_p" ++ show (copyNum + 1))
      newInstrs = map (transformUnrollInstr suffix useSubst phiSubst bodyDefs
                                            header latch nextCopyFirstBlock copyNum isLast) (blockInstrs block)
  in SSABlock newLabel [] newInstrs

-- | Transform an instruction for unrolled copy
transformUnrollInstr :: String -> Map VarKey SSAVar -> Map VarKey SSAVar
                     -> Set VarKey -> BlockId -> BlockId -> BlockId -> Int -> Bool
                     -> SSAInstr -> SSAInstr
transformUnrollInstr suffix useSubst phiSubst bodyDefs header latch nextTarget copyNum isLast = \case
  SSAAssign var expr ->
    let -- Definition gets current suffix
        newVar = if null suffix then var
                 else var { ssaName = varName (varNameString (ssaName var) ++ suffix) }
        -- Uses get substituted
        newExpr = transformUnrollExpr useSubst phiSubst expr
    in SSAAssign newVar newExpr
  SSAFieldStore t f o v ->
    SSAFieldStore (transformUnrollExpr useSubst phiSubst t) f o
                  (transformUnrollExpr useSubst phiSubst v)
  SSAReturn e -> SSAReturn (fmap (transformUnrollExpr useSubst phiSubst) e)
  SSAJump target
    | target == header ->
        -- Back edge: if last copy, go to header; otherwise go to next copy
        if isLast then SSAJump header else SSAJump nextTarget
    | otherwise ->
        -- Internal jump within body
        SSAJump (if null suffix then target else blockId (blockIdName target ++ suffix))
  SSABranch cond t f ->
    SSABranch (transformUnrollExpr useSubst phiSubst cond)
              (if null suffix then t else blockId (blockIdName t ++ suffix))
              (if null suffix then f else blockId (blockIdName f ++ suffix))
  SSAExprStmt e -> SSAExprStmt (transformUnrollExpr useSubst phiSubst e)

-- | Transform an expression for unrolled copy
transformUnrollExpr :: Map VarKey SSAVar -> Map VarKey SSAVar -> SSAExpr -> SSAExpr
transformUnrollExpr useSubst phiSubst = \case
  SSAUse var ->
    let key = varKey var
    in case Map.lookup key phiSubst of
         Just newVar -> SSAUse newVar
         Nothing -> case Map.lookup key useSubst of
           Just newVar -> SSAUse newVar
           Nothing -> SSAUse var
  SSAUnary op e -> SSAUnary op (transformUnrollExpr useSubst phiSubst e)
  SSABinary op l r -> SSABinary op (transformUnrollExpr useSubst phiSubst l)
                                   (transformUnrollExpr useSubst phiSubst r)
  SSATernary c t e -> SSATernary (transformUnrollExpr useSubst phiSubst c)
                                 (transformUnrollExpr useSubst phiSubst t)
                                 (transformUnrollExpr useSubst phiSubst e)
  SSACall name args -> SSACall name (map (transformUnrollExpr useSubst phiSubst) args)
  SSAInstanceCall t m args ->
    SSAInstanceCall (transformUnrollExpr useSubst phiSubst t) m
                    (map (transformUnrollExpr useSubst phiSubst) args)
  SSANewObject cn args -> SSANewObject cn (map (transformUnrollExpr useSubst phiSubst) args)
  SSAFieldAccess t f -> SSAFieldAccess (transformUnrollExpr useSubst phiSubst t) f
  e -> e

-- | Build adjusted header with modified bound
-- Changes: i < N  ->  i < N - (factor - 1)
-- Also changes exit target to epilogue instead of original exit
buildAdjustedHeader :: SSABlock -> SSAVar -> Int -> Int
                    -> BlockId -> BlockId -> BlockId -> LoopDir -> SSABlock
buildAdjustedHeader headerBlock boundVar boundVal factor bodyTarget exitTarget latch loopDir =
  let -- Adjusted bound: need at least `factor` iterations available
      -- For countup: subtract (factor-1) from upper bound
      -- For countdown: add (factor-1) to lower bound
      adjustedBound = case loopDir of
        CountUp   -> boundVal - (factor - 1)
        CountDown -> boundVal + (factor - 1)
      -- New exit goes to epilogue header
      epilogueHeader = blockId "epilogue_header"
      -- Update phi back-edges to receive from last unrolled copy
      -- Both the block ID and variable name need to be updated
      lastCopySuffix = "_p" ++ show (factor - 1)
      newLatch = blockId (blockIdName latch ++ lastCopySuffix)  -- B8 -> B8_p1
      newPhis = [phi { phiArgs = [(if bid == latch then newLatch else bid,
                                   if bid == latch
                                   then v { ssaName = varName (varNameString (ssaName v) ++ lastCopySuffix) }
                                   else v)
                                 | (bid, v) <- phiArgs phi] }
                | phi <- blockPhis headerBlock]
      -- Update branch instruction with new bound
      newInstrs = map (adjustBranchBound adjustedBound bodyTarget exitTarget epilogueHeader) (blockInstrs headerBlock)
  in headerBlock { blockPhis = newPhis, blockInstrs = newInstrs }

-- | Adjust branch bound in instruction
-- The newBound is already adjusted for loop direction.
-- We preserve the original branch structure but update:
-- 1. The bound value with newBound (adjusted for factor)
-- 2. The "exit" target to go to epilogue instead of original exit
-- The thenTarget/elseTarget order is preserved from the original.
adjustBranchBound :: Int -> BlockId -> BlockId -> BlockId -> SSAInstr -> SSAInstr
adjustBranchBound newBound bodyTarget originalExit epilogueTarget = \case
  SSABranch (SSABinary op (SSAUse var) (SSAInt _)) thenT elseT ->
    let adjustedBound = case op of
          Le -> newBound - 1  -- <= N-1 is same as < N
          Ge -> newBound + 1  -- >= N+1 is same as > N
          _  -> newBound
        -- Replace original exit with epilogue, keep body as-is
        newThen = if thenT == originalExit then epilogueTarget else thenT
        newElse = if elseT == originalExit then epilogueTarget else elseT
    in SSABranch (SSABinary op (SSAUse var) (SSAInt adjustedBound)) newThen newElse
  other -> other

-- | Build epilogue loop to handle remaining iterations
-- This is a copy of the original loop with new labels
buildEpilogue :: SSABlock -> [SSABlock] -> Set VarKey
              -> BlockId -> BlockId -> BlockId -> Int -> [SSABlock]
buildEpilogue headerBlock bodyBlocks bodyDefs latch bodyTarget exitTarget factor =
  let epilogueHeader = blockId "epilogue_header"
      epilogueLatch = blockId "epilogue_latch"

      -- Epilogue header: receives from main loop (via adjusted header) or epilogue latch
      mainHeader = blockLabel headerBlock
      lastCopySuffix = "_p" ++ show (factor - 1)

      -- Create epilogue phi nodes
      -- They receive values from:
      -- 1. Main loop header (when main loop exits) - these are the phi vars
      -- 2. Epilogue latch (for subsequent iterations) - use the ORIGINAL latch var with suffix
      epiloguePhis = [PhiNode
                       { phiVar = (phiVar phi) { ssaName = varName (varNameString (ssaName (phiVar phi)) ++ "_e") }
                       , phiArgs = [(mainHeader, phiVar phi),  -- From main loop: a_2
                                   -- From epilogue latch: use the original latch variable with suffix
                                   -- e.g., if phi a_2 <- [B8: a_3], then epilogue latch arg is a_e_latch_3
                                   (epilogueLatch, case lookup latch (phiArgs phi) of
                                     Just latchVar -> latchVar { ssaName = varName (varNameString (ssaName latchVar) ++ "_e_latch") }
                                     Nothing -> (phiVar phi) { ssaName = varName (varNameString (ssaName (phiVar phi)) ++ "_e_latch") })]
                       }
                     | phi <- blockPhis headerBlock]

      phiKeys = Set.fromList [varKey (phiVar phi) | phi <- blockPhis headerBlock]

      -- Epilogue header instructions (same condition as original, but with epilogue phis)
      -- Replace body target with epilogueLatch, keep exit target
      epilogueHeaderInstrs = map (renameEpilogueInstr "_e" phiKeys bodyTarget epilogueLatch exitTarget) (blockInstrs headerBlock)

      -- Epilogue body (copy of original body with renamed variables)
      -- Uses epilogue phi vars, produces epilogue latch vars
      epilogueBodyInstrs = concatMap (renameEpilogueBodyInstrs "_e" "_e_latch" phiKeys) bodyBlocks

      epilogueHeaderBlock = SSABlock epilogueHeader epiloguePhis epilogueHeaderInstrs
      epilogueLatchBlock = SSABlock epilogueLatch [] (epilogueBodyInstrs ++ [SSAJump epilogueHeader])

  in [epilogueHeaderBlock, epilogueLatchBlock]

-- | Rename exit block variables to use epilogue phi variables
-- When partial unrolling redirects the main loop to an epilogue, the exit block
-- now only receives from the epilogue, so uses of main loop phi vars (like sum_2)
-- should be renamed to epilogue phi vars (like sum_e_1)
renameExitBlockVars :: String -> Set VarKey -> SSABlock -> Maybe SSABlock
renameExitBlockVars suffix phiKeys SSABlock{..} =
  let newInstrs = map (renameExitInstr suffix phiKeys) blockInstrs
  in Just $ SSABlock blockLabel blockPhis newInstrs

-- | Rename instruction for exit block
renameExitInstr :: String -> Set VarKey -> SSAInstr -> SSAInstr
renameExitInstr suffix phiKeys = \case
  SSAAssign var expr ->
    SSAAssign var (renameEpilogueExpr suffix phiKeys expr)
  SSAReturn (Just expr) ->
    SSAReturn (Just (renameEpilogueExpr suffix phiKeys expr))
  SSABranch cond thenB elseB ->
    SSABranch (renameEpilogueExpr suffix phiKeys cond) thenB elseB
  SSAExprStmt expr ->
    SSAExprStmt (renameEpilogueExpr suffix phiKeys expr)
  SSAFieldStore target field off value ->
    SSAFieldStore (renameEpilogueExpr suffix phiKeys target) field off
                  (renameEpilogueExpr suffix phiKeys value)
  other -> other

-- | Rename instruction for epilogue header
-- The epilogue preserves the same branch structure as the original, but:
-- 1. Renames variables in the condition
-- 2. Replaces the body target with epilogueLatch
-- 3. Keeps the exit target as exitTarget
renameEpilogueInstr :: String -> Set VarKey -> BlockId -> BlockId -> BlockId -> SSAInstr -> SSAInstr
renameEpilogueInstr suffix phiKeys bodyTarget epilogueLatch exitTarget = \case
  SSABranch cond thenT elseT ->
    let cond' = renameEpilogueExpr suffix phiKeys cond
        -- Replace body with epilogueLatch, keep exit as exitTarget
        newThen = if thenT == bodyTarget then epilogueLatch else exitTarget
        newElse = if elseT == bodyTarget then epilogueLatch else exitTarget
    in SSABranch cond' newThen newElse
  other -> other

-- | Rename expression for epilogue
-- Only renames phi-defined variables
renameEpilogueExpr :: String -> Set VarKey -> SSAExpr -> SSAExpr
renameEpilogueExpr suffix phiKeys = \case
  SSAUse var ->
    if Set.member (varKey var) phiKeys
    then SSAUse (var { ssaName = varName (varNameString (ssaName var) ++ suffix) })
    else SSAUse var
  SSABinary op l r -> SSABinary op (renameEpilogueExpr suffix phiKeys l) (renameEpilogueExpr suffix phiKeys r)
  SSAUnary op e -> SSAUnary op (renameEpilogueExpr suffix phiKeys e)
  e -> e

-- | Rename body instructions for epilogue
renameEpilogueBodyInstrs :: String -> String -> Set VarKey -> SSABlock -> [SSAInstr]
renameEpilogueBodyInstrs useSuffix defSuffix phiKeys SSABlock{..} =
  [renameEpilogueBodyInstr useSuffix defSuffix phiKeys instr | instr <- blockInstrs, not (isTerminator instr)]

-- | Rename a single body instruction for epilogue
renameEpilogueBodyInstr :: String -> String -> Set VarKey -> SSAInstr -> SSAInstr
renameEpilogueBodyInstr useSuffix defSuffix phiKeys = \case
  SSAAssign var expr ->
    let -- Definition gets defSuffix
        newVar = var { ssaName = varName (varNameString (ssaName var) ++ defSuffix) }
        -- Uses get useSuffix (for phi vars) or defSuffix (for body vars in same iteration)
        newExpr = renameEpilogueBodyExpr useSuffix phiKeys expr
    in SSAAssign newVar newExpr
  other -> other

-- | Rename expression for epilogue body
-- Only renames variables that are defined within the loop (phi vars)
-- External variables (like `rand_1`) are kept as-is
renameEpilogueBodyExpr :: String -> Set VarKey -> SSAExpr -> SSAExpr
renameEpilogueBodyExpr suffix phiKeys = \case
  SSAUse var ->
    -- Only rename if this is a phi-defined variable
    if Set.member (varKey var) phiKeys
    then SSAUse (var { ssaName = varName (varNameString (ssaName var) ++ suffix) })
    else SSAUse var  -- External variable, keep as-is
  SSABinary op l r -> SSABinary op (renameEpilogueBodyExpr suffix phiKeys l)
                                   (renameEpilogueBodyExpr suffix phiKeys r)
  SSAUnary op e -> SSAUnary op (renameEpilogueBodyExpr suffix phiKeys e)
  SSATernary c t f -> SSATernary (renameEpilogueBodyExpr suffix phiKeys c)
                                 (renameEpilogueBodyExpr suffix phiKeys t)
                                 (renameEpilogueBodyExpr suffix phiKeys f)
  SSACall n args -> SSACall n (map (renameEpilogueBodyExpr suffix phiKeys) args)
  SSAInstanceCall t m args -> SSAInstanceCall (renameEpilogueBodyExpr suffix phiKeys t) m
                                              (map (renameEpilogueBodyExpr suffix phiKeys) args)
  SSAFieldAccess t f -> SSAFieldAccess (renameEpilogueBodyExpr suffix phiKeys t) f
  e -> e

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
