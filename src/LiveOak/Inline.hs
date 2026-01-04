{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RecordWildCards #-}

-- | Function Inlining Optimization.
-- Replaces function calls with the function body, eliminating call overhead
-- and enabling further optimizations.
--
-- Currently supports inlining of single-block functions (getters, setters,
-- simple computations). Multi-block functions are not inlined.
module LiveOak.Inline
  ( -- * Inlining
    inlineFunctions
  , InlineResult(..)

    -- * Inlining Decisions
  , shouldInline
  , InlineHeuristics(..)
  , defaultHeuristics
  ) where

import LiveOak.SSATypes

import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.List (foldl')

--------------------------------------------------------------------------------
-- Types
--------------------------------------------------------------------------------

-- | Inlining heuristics configuration
data InlineHeuristics = InlineHeuristics
  { maxInlineSize :: !Int           -- ^ Maximum instruction count to inline
  , maxInlineDepth :: !Int          -- ^ Maximum nesting depth for inlining
  , inlineThreshold :: !Int         -- ^ Cost threshold for inlining decision
  , alwaysInlineSize :: !Int        -- ^ Always inline if smaller than this
  , neverInlineRecursive :: !Bool   -- ^ Never inline recursive functions
  } deriving (Show)

-- | Default inlining heuristics
defaultHeuristics :: InlineHeuristics
defaultHeuristics = InlineHeuristics
  { maxInlineSize = 50              -- Max 50 instructions
  , maxInlineDepth = 3              -- Max 3 levels of inlining
  , inlineThreshold = 100           -- Cost threshold
  , alwaysInlineSize = 5            -- Always inline tiny functions
  , neverInlineRecursive = True     -- Don't inline recursive calls
  }

-- | Result of inlining pass
data InlineResult = InlineResult
  { inlineOptProgram :: !SSAProgram   -- ^ Program with inlined functions
  , inlineCount :: !Int               -- ^ Number of call sites inlined
  , inlinedFunctions :: ![String]     -- ^ Names of inlined functions
  } deriving (Show)

-- | Method info for inlining decisions
data MethodInfo = MethodInfo
  { miName :: !String
  , miClassName :: !String
  , miSize :: !Int                    -- ^ Instruction count
  , miCallCount :: !Int               -- ^ Number of call sites
  , miIsRecursive :: !Bool            -- ^ Calls itself?
  , miBlocks :: ![SSABlock]           -- ^ Method blocks
  , miParams :: ![SSAVar]             -- ^ Parameters
  } deriving (Show)

--------------------------------------------------------------------------------
-- Inlining Analysis
--------------------------------------------------------------------------------

-- | Analyze a program to collect method information
analyzeProgram :: SSAProgram -> Map String MethodInfo
analyzeProgram (SSAProgram classes) =
  Map.fromList $ concatMap analyzeClass classes
  where
    analyzeClass cls =
      [(fullName cls m, analyzeMethod cls m) | m <- ssaClassMethods cls]

    fullName cls m = ssaClassName cls ++ "_" ++ methodNameString (ssaMethodName m)

    analyzeMethod cls m =
      let blocks = ssaMethodBlocks m
          size = sum [length (blockInstrs b) + length (blockPhis b) | b <- blocks]
          calls = countCalls blocks
          isRec = isRecursive (ssaClassName cls) (methodNameString (ssaMethodName m)) blocks
      in MethodInfo
        { miName = methodNameString (ssaMethodName m)
        , miClassName = ssaClassName cls
        , miSize = size
        , miCallCount = calls
        , miIsRecursive = isRec
        , miBlocks = blocks
        , miParams = ssaMethodParams m
        }

-- | Count call sites in blocks
countCalls :: [SSABlock] -> Int
countCalls blocks = sum [countBlockCalls b | b <- blocks]
  where
    countBlockCalls SSABlock{..} = sum [countInstrCalls i | i <- blockInstrs]

    countInstrCalls = \case
      SSAAssign _ expr -> countExprCalls expr
      SSAReturn (Just expr) -> countExprCalls expr
      SSAExprStmt expr -> countExprCalls expr
      _ -> 0

    countExprCalls = \case
      SSACall _ _ -> 1
      SSAInstanceCall _ _ _ -> 1
      SSAUnary _ e -> countExprCalls e
      SSABinary _ l r -> countExprCalls l + countExprCalls r
      SSATernary c t e -> countExprCalls c + countExprCalls t + countExprCalls e
      _ -> 0

-- | Check if a method is recursive
isRecursive :: String -> String -> [SSABlock] -> Bool
isRecursive className methodName =
  any (blockIsRecursive className methodName)
  where
    blockIsRecursive cn mn SSABlock{..} =
      any (instrIsRecursive cn mn) blockInstrs

    instrIsRecursive cn mn = \case
      SSAAssign _ expr -> exprIsRecursive cn mn expr
      SSAReturn (Just expr) -> exprIsRecursive cn mn expr
      SSAExprStmt expr -> exprIsRecursive cn mn expr
      _ -> False

    exprIsRecursive cn mn = \case
      SSACall name _ -> name == cn ++ "_" ++ mn || name == mn
      SSAInstanceCall _ method _ -> method == mn
      SSAUnary _ e -> exprIsRecursive cn mn e
      SSABinary _ l r -> exprIsRecursive cn mn l || exprIsRecursive cn mn r
      SSATernary c t e -> exprIsRecursive cn mn c || exprIsRecursive cn mn t || exprIsRecursive cn mn e
      _ -> False

--------------------------------------------------------------------------------
-- Inlining Decisions
--------------------------------------------------------------------------------

-- | Decide whether to inline a function
shouldInline :: InlineHeuristics -> MethodInfo -> Bool
shouldInline h info
  -- Never inline recursive functions (if configured)
  | neverInlineRecursive h && miIsRecursive info = False
  -- Always inline tiny functions
  | miSize info <= alwaysInlineSize h = True
  -- Don't inline large functions
  | miSize info > maxInlineSize h = False
  -- Use cost/benefit analysis
  | otherwise = inlineBenefit info > 0

-- | Calculate inlining benefit (positive = should inline)
inlineBenefit :: MethodInfo -> Int
inlineBenefit info =
  let -- Benefit: eliminate call overhead (estimated at 10 instructions)
      callOverhead = 10
      benefit = miCallCount info * callOverhead
      -- Cost: code size increase
      cost = (miCallCount info - 1) * miSize info  -- -1 because we keep one copy
  in benefit - cost

--------------------------------------------------------------------------------
-- Inlining Transformation
--------------------------------------------------------------------------------

-- | Inline functions in a program
inlineFunctions :: InlineHeuristics -> SSAProgram -> InlineResult
inlineFunctions heuristics prog@(SSAProgram classes) =
  let methodInfos = analyzeProgram prog
      -- Find methods to inline
      toInline = Map.filter (shouldInline heuristics) methodInfos
      -- Perform inlining
      (optimized, count) = inlineInProgram toInline classes
  in InlineResult
    { inlineOptProgram = SSAProgram optimized
    , inlineCount = count
    , inlinedFunctions = Map.keys toInline
    }

-- | Inline calls in program
inlineInProgram :: Map String MethodInfo -> [SSAClass] -> ([SSAClass], Int)
inlineInProgram toInline classes =
  let results = map (inlineInClass toInline) classes
  in (map fst results, sum (map snd results))

-- | Inline calls in a class
inlineInClass :: Map String MethodInfo -> SSAClass -> (SSAClass, Int)
inlineInClass toInline cls =
  let results = map (inlineInMethod toInline) (ssaClassMethods cls)
      methods' = map fst results
      count = sum (map snd results)
  in (cls { ssaClassMethods = methods' }, count)

-- | Inline calls in a method
inlineInMethod :: Map String MethodInfo -> SSAMethod -> (SSAMethod, Int)
inlineInMethod toInline method =
  let (blocks', count) = inlineInBlocks toInline 0 (ssaMethodBlocks method)
  in (method { ssaMethodBlocks = blocks' }, count)

-- | Inline calls in blocks
inlineInBlocks :: Map String MethodInfo -> Int -> [SSABlock] -> ([SSABlock], Int)
inlineInBlocks toInline labelCounter blocks =
  let (accRev, count) = foldl' inlineBlock ([], 0) blocks
  in (reverse accRev, count)
  where
    inlineBlock (acc, count) block =
      let (block', newBlocks, c) = inlineBlockCalls toInline labelCounter block
          -- Prepend in reverse order: newBlocks then block'
      in (reverse newBlocks ++ (block' : acc), count + c)

-- | Inline calls in a single block
inlineBlockCalls :: Map String MethodInfo -> Int -> SSABlock -> (SSABlock, [SSABlock], Int)
inlineBlockCalls toInline labelCounter block@SSABlock{..} =
  let (instrsRev, blocksRev, count) = foldl' inlineInstr ([], [], 0) blockInstrs
  in (block { blockInstrs = reverse instrsRev }, reverse blocksRev, count)
  where
    inlineInstr (acc, blocks, count) instr =
      case findInlineableCall toInline instr of
        Just (methodInfo, resultVar, args) ->
          -- Inline this call
          let (inlinedInstrs, newBlocks') = inlineCall methodInfo resultVar args labelCounter
              -- Prepend inlined instructions in reverse order
          in (reverse inlinedInstrs ++ acc, reverse newBlocks' ++ blocks, count + 1)
        Nothing ->
          (instr : acc, blocks, count)

-- | Find an inlineable call in an instruction
findInlineableCall :: Map String MethodInfo -> SSAInstr -> Maybe (MethodInfo, Maybe SSAVar, [SSAExpr])
findInlineableCall toInline = \case
  SSAAssign var (SSACall name args) ->
    case Map.lookup name toInline of
      Just info -> Just (info, Just var, args)
      Nothing -> Nothing
  SSAExprStmt (SSACall name args) ->
    case Map.lookup name toInline of
      Just info -> Just (info, Nothing, args)
      Nothing -> Nothing
  _ -> Nothing

-- | Inline a single call
-- For simple functions (single block or straightforward control flow),
-- we inline by replacing the call with parameter assignments + body + return handling
inlineCall :: MethodInfo -> Maybe SSAVar -> [SSAExpr] -> Int -> ([SSAInstr], [SSABlock])
inlineCall info resultVar args _labelCounter =
  case miBlocks info of
    -- Simple case: single block function (getters, setters, simple computations)
    [SSABlock{..}] ->
      let -- Create parameter assignments (with unique names to avoid conflicts)
          paramAssigns = zipWith (mkParamAssign _labelCounter) (miParams info) args
          -- Create a substitution map from original params to inlined params
          paramSubst = Map.fromList
            [(ssaName p, inlineParamName _labelCounter p) | p <- miParams info]
          -- Transform body instructions, substituting params and handling returns
          bodyInstrs = concatMap (transformInstr paramSubst resultVar) blockInstrs
      in (paramAssigns ++ bodyInstrs, [])

    -- Multi-block functions: for now, don't inline (would need proper CFG merging)
    _ -> ([], [])  -- Return empty to skip inlining
  where
    mkParamAssign counter param arg =
      let newName = inlineParamName counter param
          newVar = SSAVar newName (ssaVersion param) (ssaVarType param)
      in SSAAssign newVar arg

    inlineParamName counter param =
      varName ("__inline_" ++ show counter ++ "_" ++ varNameString (ssaName param))

-- | Transform an instruction for inlining
-- - Substitute parameter references with inlined parameter names
-- - Convert returns to assignments (if resultVar is provided)
transformInstr :: Map VarName VarName -> Maybe SSAVar -> SSAInstr -> [SSAInstr]
transformInstr subst resultVar = \case
  -- Return with value: assign to result variable
  SSAReturn (Just expr) ->
    case resultVar of
      Just rv -> [SSAAssign rv (substExpr subst expr)]
      Nothing -> []  -- Void context, discard return value

  -- Return without value: nothing to do
  SSAReturn Nothing -> []

  -- Jump/Branch: skip (we're flattening into a single block)
  SSAJump _ -> []
  SSABranch {} -> []

  -- Regular instructions: substitute parameters
  SSAAssign var expr ->
    [SSAAssign (substVar subst var) (substExpr subst expr)]
  SSAFieldStore target field idx val ->
    [SSAFieldStore (substExpr subst target) field idx (substExpr subst val)]
  SSAExprStmt expr ->
    [SSAExprStmt (substExpr subst expr)]

-- | Substitute variable names in a variable
substVar :: Map VarName VarName -> SSAVar -> SSAVar
substVar subst var =
  case Map.lookup (ssaName var) subst of
    Just newName -> var { ssaName = newName }
    Nothing -> var

-- | Substitute variable names in an expression
substExpr :: Map VarName VarName -> SSAExpr -> SSAExpr
substExpr subst = \case
  SSAUse var -> SSAUse (substVar subst var)
  SSAUnary op e -> SSAUnary op (substExpr subst e)
  SSABinary op l r -> SSABinary op (substExpr subst l) (substExpr subst r)
  SSATernary c t e -> SSATernary (substExpr subst c) (substExpr subst t) (substExpr subst e)
  SSACall n args -> SSACall n (map (substExpr subst) args)
  SSAInstanceCall t m args -> SSAInstanceCall (substExpr subst t) m (map (substExpr subst) args)
  SSANewObject cn args -> SSANewObject cn (map (substExpr subst) args)
  SSAFieldAccess t f -> SSAFieldAccess (substExpr subst t) f
  other -> other
