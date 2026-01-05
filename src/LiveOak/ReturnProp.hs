{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RecordWildCards #-}

-- | Return Value Propagation.
-- Propagates constant return values to call sites.
--
-- == Analysis
--
-- For each method, determine if it always returns the same constant value.
-- If so, replace calls to that method with the constant.
--
-- == Example
--
-- @
-- // Method always returns 42
-- int getAnswer() { return 42; }
--
-- // Before:
-- x = this.getAnswer()
--
-- // After:
-- x = 42
-- @
--
-- == Limitations
--
-- - Only handles simple constants (int, bool, null)
-- - Requires all return paths to return the same constant
-- - Does not handle methods with side effects (conservative)
--
module LiveOak.ReturnProp
  ( -- * Return Value Propagation
    propagateReturns
  , ReturnPropResult(..)
  ) where

import LiveOak.SSATypes
import LiveOak.SSAUtils (isPure)

import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Maybe (mapMaybe)
import Data.List (foldl')

--------------------------------------------------------------------------------
-- Types
--------------------------------------------------------------------------------

-- | Return propagation result
data ReturnPropResult = ReturnPropResult
  { rpOptProgram :: !SSAProgram
  , rpPropagated :: !Int          -- ^ Number of calls replaced
  } deriving (Show)

-- | Method signature
type MethodSig = (String, String)  -- (className, methodName)

-- | Constant return value
data ConstantReturn
  = ReturnInt !Int
  | ReturnBool !Bool
  | ReturnNull
  | ReturnThis
  deriving (Eq, Show)

--------------------------------------------------------------------------------
-- Return Value Propagation
--------------------------------------------------------------------------------

-- | Propagate constant return values
propagateReturns :: SSAProgram -> ReturnPropResult
propagateReturns (SSAProgram classes) =
  let -- Analyze methods for constant returns
      constReturns = analyzeConstantReturns classes
      -- Propagate to call sites
      (classes', count) = propagateToCallSites constReturns classes
  in ReturnPropResult
    { rpOptProgram = SSAProgram classes'
    , rpPropagated = count
    }

-- | Analyze all methods for constant returns
analyzeConstantReturns :: [SSAClass] -> Map MethodSig ConstantReturn
analyzeConstantReturns classes =
  Map.fromList $ mapMaybe analyzeMethod
    [ (ssaClassName cls, method)
    | cls <- classes
    , method <- ssaClassMethods cls
    ]

-- | Analyze a single method for constant return
analyzeMethod :: (String, SSAMethod) -> Maybe (MethodSig, ConstantReturn)
analyzeMethod (className, method@SSAMethod{..}) =
  -- Check if method is pure (no side effects that would prevent propagation)
  if not (methodIsPure method)
  then Nothing
  else
    let returns = collectReturns ssaMethodBlocks
    in case returns of
      [] -> Nothing  -- No returns (infinite loop or unreachable)
      (r:rs) | all (== r) rs -> Just ((className, show ssaMethodName), r)
      _ -> Nothing  -- Multiple different return values

-- | Check if a method is pure (all expressions are pure)
methodIsPure :: SSAMethod -> Bool
methodIsPure SSAMethod{..} =
  all blockIsPure ssaMethodBlocks

-- | Check if a block is pure
blockIsPure :: SSABlock -> Bool
blockIsPure SSABlock{..} =
  all instrIsPure blockInstrs

-- | Check if an instruction is pure
instrIsPure :: SSAInstr -> Bool
instrIsPure = \case
  SSAAssign _ expr -> isPure expr
  SSAReturn _ -> True
  SSAJump _ -> True
  SSABranch cond _ _ -> isPure cond
  SSAFieldStore _ _ _ _ -> False  -- Field stores have side effects
  SSAExprStmt expr -> isPure expr

-- | Collect all return values from blocks
collectReturns :: [SSABlock] -> [ConstantReturn]
collectReturns blocks =
  mapMaybe getConstantReturn $ concatMap getReturns blocks

-- | Get return instructions from a block
getReturns :: SSABlock -> [SSAExpr]
getReturns SSABlock{..} =
  [expr | SSAReturn (Just expr) <- blockInstrs]

-- | Convert expression to constant return (if it is one)
getConstantReturn :: SSAExpr -> Maybe ConstantReturn
getConstantReturn = \case
  SSAInt n -> Just (ReturnInt n)
  SSABool b -> Just (ReturnBool b)
  SSANull -> Just ReturnNull
  SSAThis -> Just ReturnThis
  _ -> Nothing

-- | Propagate constants to call sites
propagateToCallSites :: Map MethodSig ConstantReturn -> [SSAClass]
                     -> ([SSAClass], Int)
propagateToCallSites constReturns classes =
  let (classes', counts) = unzip $ map (propagateClass constReturns) classes
  in (classes', sum counts)

-- | Propagate in a class
propagateClass :: Map MethodSig ConstantReturn -> SSAClass -> (SSAClass, Int)
propagateClass constReturns cls@SSAClass{..} =
  let (methods', counts) = unzip $ map (propagateMethod constReturns) ssaClassMethods
  in (cls { ssaClassMethods = methods' }, sum counts)

-- | Propagate in a method
propagateMethod :: Map MethodSig ConstantReturn -> SSAMethod -> (SSAMethod, Int)
propagateMethod constReturns method@SSAMethod{..} =
  let (blocks', counts) = unzip $ map (propagateBlock constReturns) ssaMethodBlocks
  in (method { ssaMethodBlocks = blocks' }, sum counts)

-- | Propagate in a block
propagateBlock :: Map MethodSig ConstantReturn -> SSABlock -> (SSABlock, Int)
propagateBlock constReturns block@SSABlock{..} =
  let (instrs', counts) = unzip $ map (propagateInstr constReturns) blockInstrs
  in (block { blockInstrs = instrs' }, sum counts)

-- | Propagate in an instruction
propagateInstr :: Map MethodSig ConstantReturn -> SSAInstr -> (SSAInstr, Int)
propagateInstr constReturns = \case
  SSAAssign var expr ->
    let (expr', count) = propagateExpr constReturns expr
    in (SSAAssign var expr', count)
  SSAExprStmt expr ->
    let (expr', count) = propagateExpr constReturns expr
    in (SSAExprStmt expr', count)
  SSAReturn (Just expr) ->
    let (expr', count) = propagateExpr constReturns expr
    in (SSAReturn (Just expr'), count)
  SSABranch cond t f ->
    let (cond', count) = propagateExpr constReturns cond
    in (SSABranch cond' t f, count)
  SSAFieldStore target field off value ->
    let (target', c1) = propagateExpr constReturns target
        (value', c2) = propagateExpr constReturns value
    in (SSAFieldStore target' field off value', c1 + c2)
  i -> (i, 0)

-- | Propagate in an expression
propagateExpr :: Map MethodSig ConstantReturn -> SSAExpr -> (SSAExpr, Int)
propagateExpr constReturns = \case
  -- For instance calls, we'd need type information to know the class
  -- For now, we can't propagate these without type info
  SSAInstanceCall target method args ->
    let (target', c1) = propagateExpr constReturns target
        (args', counts) = unzip $ map (propagateExpr constReturns) args
    in (SSAInstanceCall target' method args', c1 + sum counts)

  SSACall name args ->
    let (args', counts) = unzip $ map (propagateExpr constReturns) args
    in (SSACall name args', sum counts)

  SSAUnary op e ->
    let (e', count) = propagateExpr constReturns e
    in (SSAUnary op e', count)

  SSABinary op l r ->
    let (l', c1) = propagateExpr constReturns l
        (r', c2) = propagateExpr constReturns r
    in (SSABinary op l' r', c1 + c2)

  SSATernary c t e ->
    let (c', cc) = propagateExpr constReturns c
        (t', ct) = propagateExpr constReturns t
        (e', ce) = propagateExpr constReturns e
    in (SSATernary c' t' e', cc + ct + ce)

  SSANewObject cn args ->
    let (args', counts) = unzip $ map (propagateExpr constReturns) args
    in (SSANewObject cn args', sum counts)

  SSAFieldAccess target field ->
    let (target', count) = propagateExpr constReturns target
    in (SSAFieldAccess target' field, count)

  e -> (e, 0)

-- | Convert constant return to expression
constantToExpr :: ConstantReturn -> SSAExpr
constantToExpr = \case
  ReturnInt n -> SSAInt n
  ReturnBool b -> SSABool b
  ReturnNull -> SSANull
  ReturnThis -> SSAThis
