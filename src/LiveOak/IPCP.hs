{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RecordWildCards #-}

-- | Interprocedural Constant Propagation.
-- Propagates constants across method boundaries.
--
-- == Algorithm
-- 1. Build a call graph
-- 2. For each call site, analyze constant arguments
-- 3. Specialize methods for constant arguments when beneficial
-- 4. Propagate return values that are always constant
--
module LiveOak.IPCP
  ( -- * Interprocedural Constant Propagation
    propagateIPConstants
  , IPCPResult(..)

    -- * Call Graph
  , CallGraph(..)
  , buildCallGraph
  , CallSite(..)

    -- * Analysis
  , MethodConstInfo(..)
  , analyzeMethodConstants
  ) where

import LiveOak.SSATypes
import LiveOak.Ast (BinaryOp(..), UnaryOp(..))

import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Set (Set)
import qualified Data.Set as Set
import Data.List (foldl')
import Data.Maybe (mapMaybe, catMaybes)

--------------------------------------------------------------------------------
-- Types
--------------------------------------------------------------------------------

-- | IPCP result
data IPCPResult = IPCPResult
  { ipcpOptProgram :: !SSAProgram
  , ipcpPropagated :: !Int           -- ^ Number of constants propagated
  , ipcpSpecialized :: !Int          -- ^ Number of methods specialized
  } deriving (Show)

-- | Call site information
data CallSite = CallSite
  { csCallerClass :: !String
  , csCallerMethod :: !String
  , csCalleeMethod :: !String
  , csCalleeClass :: !(Maybe String)  -- ^ Nothing for static calls
  , csArguments :: ![SSAExpr]
  , csBlockId :: !BlockId
  } deriving (Show)

-- | Call graph
data CallGraph = CallGraph
  { cgCallSites :: ![CallSite]
  , cgCallers :: !(Map String [CallSite])    -- ^ Callee -> call sites calling it
  , cgCallees :: !(Map String [String])      -- ^ Caller -> methods it calls
  } deriving (Show)

-- | Constant value lattice
data ConstValue
  = CVTop                           -- ^ Unknown
  | CVConst !SSAExpr                -- ^ Known constant
  | CVBottom                        -- ^ Conflicting values (not constant)
  deriving (Eq, Show)

-- | Per-method constant information
data MethodConstInfo = MethodConstInfo
  { mciParamConsts :: ![ConstValue]  -- ^ Constants for each parameter
  , mciReturnConst :: !ConstValue    -- ^ Return value constant
  } deriving (Eq, Show)

--------------------------------------------------------------------------------
-- Call Graph Construction
--------------------------------------------------------------------------------

-- | Build call graph from program
buildCallGraph :: SSAProgram -> CallGraph
buildCallGraph (SSAProgram classes) =
  let allSites = concatMap classCallSites classes
      callers = foldl' addCaller Map.empty allSites
      callees = foldl' addCallee Map.empty allSites
  in CallGraph
    { cgCallSites = allSites
    , cgCallers = callers
    , cgCallees = callees
    }
  where
    addCaller m site =
      Map.insertWith (++) (csCalleeMethod site) [site] m
    addCallee m site =
      let key = csCallerClass site ++ "_" ++ csCallerMethod site
      in Map.insertWith (++) key [csCalleeMethod site] m

-- | Collect call sites from a class
classCallSites :: SSAClass -> [CallSite]
classCallSites cls =
  concatMap (methodCallSites (ssaClassName cls)) (ssaClassMethods cls)

-- | Collect call sites from a method
methodCallSites :: String -> SSAMethod -> [CallSite]
methodCallSites className method =
  concatMap (blockCallSites className (methodNameString (ssaMethodName method)))
            (ssaMethodBlocks method)

-- | Collect call sites from a block
blockCallSites :: String -> String -> SSABlock -> [CallSite]
blockCallSites className methodName SSABlock{..} =
  mapMaybe (instrCallSite className methodName blockLabel) blockInstrs

-- | Extract call site from instruction
instrCallSite :: String -> String -> BlockId -> SSAInstr -> Maybe CallSite
instrCallSite className methodName bid = \case
  SSAAssign _ (SSACall name args) ->
    Just $ CallSite className methodName name Nothing args bid
  SSAAssign _ (SSAInstanceCall target method args) ->
    Just $ CallSite className methodName method (Just $ inferClass target) args bid
  SSAExprStmt (SSACall name args) ->
    Just $ CallSite className methodName name Nothing args bid
  SSAExprStmt (SSAInstanceCall target method args) ->
    Just $ CallSite className methodName method (Just $ inferClass target) args bid
  _ -> Nothing
  where
    inferClass SSAThis = className
    inferClass _ = "Unknown"

--------------------------------------------------------------------------------
-- Constant Analysis
--------------------------------------------------------------------------------

-- | Analyze constants for all methods
analyzeAllConstants :: SSAProgram -> CallGraph -> Map String MethodConstInfo
analyzeAllConstants (SSAProgram classes) cg =
  let initial = Map.fromList [(fullName cls m, initConstInfo m)
                             | cls <- classes, m <- ssaClassMethods cls]
      -- Iterate until fixed point
      final = iterateAnalysis cg initial
  in final
  where
    fullName cls m = ssaClassName cls ++ "_" ++ methodNameString (ssaMethodName m)

    initConstInfo m = MethodConstInfo
      { mciParamConsts = replicate (length (ssaMethodParams m)) CVTop
      , mciReturnConst = CVTop
      }

-- | Iterate constant analysis
iterateAnalysis :: CallGraph -> Map String MethodConstInfo -> Map String MethodConstInfo
iterateAnalysis cg state = iterate' 20 state
  where
    iterate' 0 s = s
    iterate' n s =
      let s' = oneIteration cg s
      in if s' == state then s' else iterate' (n-1) s'

-- | One iteration of constant propagation
oneIteration :: CallGraph -> Map String MethodConstInfo -> Map String MethodConstInfo
oneIteration cg state = Map.mapWithKey (updateMethod cg state) state

-- | Update constant info for a method
updateMethod :: CallGraph -> Map String MethodConstInfo -> String -> MethodConstInfo -> MethodConstInfo
updateMethod cg state methodKey info =
  let -- Get all call sites calling this method
      callSites = Map.findWithDefault [] methodKey (cgCallers cg)
      -- Compute new parameter constants (meet of all call site arguments)
      newParamConsts = computeParamConsts callSites (length (mciParamConsts info))
  in info { mciParamConsts = newParamConsts }

-- | Compute parameter constants from call sites
computeParamConsts :: [CallSite] -> Int -> [ConstValue]
computeParamConsts [] n = replicate n CVTop
computeParamConsts sites n =
  [meetAll [evalArg (csArguments s !! i) | s <- sites, i < length (csArguments s)]
  | i <- [0..n-1]]
  where
    meetAll [] = CVTop
    meetAll xs = foldl1 meetConst xs

-- | Meet two constant values
meetConst :: ConstValue -> ConstValue -> ConstValue
meetConst CVTop y = y
meetConst x CVTop = x
meetConst CVBottom _ = CVBottom
meetConst _ CVBottom = CVBottom
meetConst (CVConst e1) (CVConst e2)
  | e1 == e2 = CVConst e1
  | otherwise = CVBottom

-- | Evaluate an argument expression to a constant
evalArg :: SSAExpr -> ConstValue
evalArg (SSAInt n) = CVConst (SSAInt n)
evalArg (SSABool b) = CVConst (SSABool b)
evalArg (SSAStr s) = CVConst (SSAStr s)
evalArg SSANull = CVConst SSANull
evalArg _ = CVTop

--------------------------------------------------------------------------------
-- Constant Propagation
--------------------------------------------------------------------------------

-- | Propagate interprocedural constants
propagateIPConstants :: SSAProgram -> IPCPResult
propagateIPConstants prog@(SSAProgram classes) =
  let cg = buildCallGraph prog
      constInfo = analyzeAllConstants prog cg
      -- Apply constant propagation
      (optimized, propCount) = propagateConstants constInfo classes
  in IPCPResult
    { ipcpOptProgram = SSAProgram optimized
    , ipcpPropagated = propCount
    , ipcpSpecialized = 0  -- Specialization not implemented yet
    }

-- | Propagate constants to methods
propagateConstants :: Map String MethodConstInfo -> [SSAClass] -> ([SSAClass], Int)
propagateConstants constInfo classes =
  let results = map (propagateClassConstants constInfo) classes
  in (map fst results, sum (map snd results))

-- | Propagate constants in a class
propagateClassConstants :: Map String MethodConstInfo -> SSAClass -> (SSAClass, Int)
propagateClassConstants constInfo cls =
  let results = map (propagateMethodConstants constInfo (ssaClassName cls)) (ssaClassMethods cls)
      methods' = map fst results
      count = sum (map snd results)
  in (cls { ssaClassMethods = methods' }, count)

-- | Propagate constants in a method
propagateMethodConstants :: Map String MethodConstInfo -> String -> SSAMethod -> (SSAMethod, Int)
propagateMethodConstants constInfo className method =
  let key = className ++ "_" ++ methodNameString (ssaMethodName method)
      info = Map.findWithDefault (MethodConstInfo [] CVTop) key constInfo
      -- Build substitution map from constant parameters
      paramSubst = buildParamSubst (ssaMethodParams method) (mciParamConsts info)
      -- Apply substitution to blocks
      (blocks', count) = substituteBlocks paramSubst (ssaMethodBlocks method)
  in (method { ssaMethodBlocks = blocks' }, count)

-- | Build substitution map from parameters and their constant values
buildParamSubst :: [SSAVar] -> [ConstValue] -> Map VarKey SSAExpr
buildParamSubst params consts = Map.fromList $ catMaybes
  [case c of
     CVConst e -> Just ((ssaName p, ssaVersion p), e)
     _ -> Nothing
  | (p, c) <- zip params consts]

-- | Substitute constants in blocks
substituteBlocks :: Map VarKey SSAExpr -> [SSABlock] -> ([SSABlock], Int)
substituteBlocks subst blocks =
  let results = map (substituteBlock subst) blocks
  in (map fst results, sum (map snd results))

-- | Substitute constants in a block
substituteBlock :: Map VarKey SSAExpr -> SSABlock -> (SSABlock, Int)
substituteBlock subst block@SSABlock{..} =
  let (instrs', counts) = unzip $ map (substituteInstr subst) blockInstrs
      (phis', phiCounts) = unzip $ map (substitutePhi subst) blockPhis
  in (block { blockInstrs = instrs', blockPhis = phis' }, sum counts + sum phiCounts)

-- | Substitute constants in an instruction
substituteInstr :: Map VarKey SSAExpr -> SSAInstr -> (SSAInstr, Int)
substituteInstr subst = \case
  SSAAssign var expr ->
    let (expr', count) = substituteExpr subst expr
    in (SSAAssign var expr', count)
  SSAFieldStore target field idx value ->
    let (target', c1) = substituteExpr subst target
        (value', c2) = substituteExpr subst value
    in (SSAFieldStore target' field idx value', c1 + c2)
  SSAReturn (Just expr) ->
    let (expr', count) = substituteExpr subst expr
    in (SSAReturn (Just expr'), count)
  SSABranch cond thenB elseB ->
    let (cond', count) = substituteExpr subst cond
    in (SSABranch cond' thenB elseB, count)
  SSAExprStmt expr ->
    let (expr', count) = substituteExpr subst expr
    in (SSAExprStmt expr', count)
  other -> (other, 0)

-- | Substitute constants in a phi node
substitutePhi :: Map VarKey SSAExpr -> PhiNode -> (PhiNode, Int)
substitutePhi subst phi@PhiNode{..} =
  let results = [(bid, v, countSubst v) | (bid, v) <- phiArgs]
      args' = [(bid, v) | (bid, v, _) <- results]
      totalCount = sum [c | (_, _, c) <- results]
  in (phi { phiArgs = args' }, totalCount)
  where
    countSubst v = case Map.lookup (ssaName v, ssaVersion v) subst of
      Just _ -> 1  -- Would substitute if we could
      Nothing -> 0

-- | Substitute constants in an expression
substituteExpr :: Map VarKey SSAExpr -> SSAExpr -> (SSAExpr, Int)
substituteExpr subst = \case
  SSAUse var ->
    case Map.lookup (ssaName var, ssaVersion var) subst of
      Just expr -> (expr, 1)
      Nothing -> (SSAUse var, 0)
  SSAUnary op e ->
    let (e', count) = substituteExpr subst e
    in (SSAUnary op e', count)
  SSABinary op l r ->
    let (l', c1) = substituteExpr subst l
        (r', c2) = substituteExpr subst r
    in (SSABinary op l' r', c1 + c2)
  SSATernary c t e ->
    let (c', cc) = substituteExpr subst c
        (t', ct) = substituteExpr subst t
        (e', ce) = substituteExpr subst e
    in (SSATernary c' t' e', cc + ct + ce)
  SSACall n args ->
    let results = map (substituteExpr subst) args
    in (SSACall n (map fst results), sum (map snd results))
  SSAInstanceCall target m args ->
    let (target', ct) = substituteExpr subst target
        results = map (substituteExpr subst) args
    in (SSAInstanceCall target' m (map fst results), ct + sum (map snd results))
  SSANewObject cn args ->
    let results = map (substituteExpr subst) args
    in (SSANewObject cn (map fst results), sum (map snd results))
  SSAFieldAccess target field ->
    let (target', count) = substituteExpr subst target
    in (SSAFieldAccess target' field, count)
  other -> (other, 0)

--------------------------------------------------------------------------------
-- Method Analysis
--------------------------------------------------------------------------------

-- | Analyze a method for constant propagation opportunities
analyzeMethodConstants :: SSAMethod -> MethodConstInfo
analyzeMethodConstants method =
  let returnConst = analyzeReturnConstant (ssaMethodBlocks method)
  in MethodConstInfo
    { mciParamConsts = replicate (length (ssaMethodParams method)) CVTop
    , mciReturnConst = returnConst
    }

-- | Analyze return value for constant
analyzeReturnConstant :: [SSABlock] -> ConstValue
analyzeReturnConstant blocks =
  let returnValues = concatMap blockReturnValues blocks
  in foldl' meetConst CVTop (map evalArg returnValues)
  where
    blockReturnValues SSABlock{..} = mapMaybe instrReturnValue blockInstrs
    instrReturnValue (SSAReturn (Just e)) = Just e
    instrReturnValue _ = Nothing
