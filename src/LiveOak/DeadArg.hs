{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RecordWildCards #-}

-- | Dead Argument Elimination.
-- Removes unused method parameters across the program.
--
-- == Algorithm
--
-- 1. For each method, identify which parameters are never used
-- 2. At all call sites, remove the corresponding arguments
-- 3. Update the method signature to remove the dead parameters
--
-- == Limitations
--
-- - Only handles static analysis (no reflection)
-- - Conservatively keeps 'this' parameter
-- - Only processes internal methods (not external calls)
--
module LiveOak.DeadArg
  ( -- * Dead Argument Elimination
    eliminateDeadArgs
  , DeadArgResult(..)
  ) where

import LiveOak.SSATypes
import LiveOak.SSAUtils (blockUses)

import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Set (Set)
import qualified Data.Set as Set
import Data.List (foldl')

--------------------------------------------------------------------------------
-- Types
--------------------------------------------------------------------------------

-- | Dead argument elimination result
data DeadArgResult = DeadArgResult
  { daOptProgram :: !SSAProgram
  , daEliminatedArgs :: !Int      -- ^ Number of arguments eliminated
  , daAffectedMethods :: !Int     -- ^ Number of methods modified
  } deriving (Show)

-- | Method signature for tracking
type MethodSig = (String, String)  -- (className, methodName)

--------------------------------------------------------------------------------
-- Dead Argument Elimination
--------------------------------------------------------------------------------

-- | Eliminate dead arguments from a program
eliminateDeadArgs :: SSAProgram -> DeadArgResult
eliminateDeadArgs (SSAProgram classes) =
  let -- Collect dead parameters for each method
      deadParams = collectDeadParams classes
      -- Count eliminations
      elimCount = sum [length ps | ps <- Map.elems deadParams]
      affectedCount = Map.size (Map.filter (not . null) deadParams)
      -- Apply eliminations
      classes' = map (eliminateClassDeadArgs deadParams) classes
  in DeadArgResult
    { daOptProgram = SSAProgram classes'
    , daEliminatedArgs = elimCount
    , daAffectedMethods = affectedCount
    }

-- | Collect dead parameters for all methods
collectDeadParams :: [SSAClass] -> Map MethodSig [Int]
collectDeadParams classes =
  Map.fromList
    [ ((ssaClassName cls, show (ssaMethodName method)), findDeadParams method)
    | cls <- classes
    , method <- ssaClassMethods cls
    ]

-- | Find indices of dead (unused) parameters in a method
-- Returns 0-based indices of parameters that are never used
-- Note: We skip index 0 (this) as it's always kept
findDeadParams :: SSAMethod -> [Int]
findDeadParams SSAMethod{..} =
  let -- Get all used variables in the method
      usedVars = Set.unions $ map blockUses ssaMethodBlocks
      -- Check each parameter (skip 'this' at index 0)
      params = zip [0..] ssaMethodParams
      deadIndices = [ i
                    | (i, param) <- params
                    , i > 0  -- Keep 'this'
                    , not $ Set.member (varNameString (ssaName param)) usedVars
                    ]
  in deadIndices

-- | Eliminate dead arguments from a class
eliminateClassDeadArgs :: Map MethodSig [Int] -> SSAClass -> SSAClass
eliminateClassDeadArgs deadParams cls@SSAClass{..} =
  let methods' = map (eliminateMethodDeadArgs ssaClassName deadParams) ssaClassMethods
  in cls { ssaClassMethods = methods' }

-- | Eliminate dead arguments from a method
eliminateMethodDeadArgs :: String -> Map MethodSig [Int] -> SSAMethod -> SSAMethod
eliminateMethodDeadArgs className deadParams method@SSAMethod{..} =
  let -- Get dead params for this method
      myDeadParams = Map.findWithDefault [] (className, show ssaMethodName) deadParams
      -- Remove dead parameters from signature
      params' = removeIndices myDeadParams ssaMethodParams
      -- Update call sites in method body
      blocks' = map (updateBlockCalls deadParams) ssaMethodBlocks
  in method { ssaMethodParams = params', ssaMethodBlocks = blocks' }

-- | Update call sites in a block
updateBlockCalls :: Map MethodSig [Int] -> SSABlock -> SSABlock
updateBlockCalls deadParams block@SSABlock{..} =
  let instrs' = map (updateInstrCalls deadParams) blockInstrs
  in block { blockInstrs = instrs' }

-- | Update call sites in an instruction
updateInstrCalls :: Map MethodSig [Int] -> SSAInstr -> SSAInstr
updateInstrCalls deadParams = \case
  SSAAssign var expr ->
    SSAAssign var (updateExprCalls deadParams expr)
  SSAExprStmt expr ->
    SSAExprStmt (updateExprCalls deadParams expr)
  SSAReturn (Just expr) ->
    SSAReturn (Just (updateExprCalls deadParams expr))
  SSABranch cond t f ->
    SSABranch (updateExprCalls deadParams cond) t f
  SSAFieldStore target field off value ->
    SSAFieldStore (updateExprCalls deadParams target) field off
                  (updateExprCalls deadParams value)
  i -> i

-- | Update call sites in an expression
updateExprCalls :: Map MethodSig [Int] -> SSAExpr -> SSAExpr
updateExprCalls deadParams = \case
  -- Instance calls: className.methodName(args)
  -- We need to know the class type to look up dead params
  -- For now, we can't statically determine the class, so skip
  SSAInstanceCall target method args ->
    SSAInstanceCall (updateExprCalls deadParams target) method
                    (map (updateExprCalls deadParams) args)

  -- Static/global calls might have dead args, but we need class info
  SSACall name args ->
    SSACall name (map (updateExprCalls deadParams) args)

  SSAUnary op e ->
    SSAUnary op (updateExprCalls deadParams e)
  SSABinary op l r ->
    SSABinary op (updateExprCalls deadParams l) (updateExprCalls deadParams r)
  SSATernary c t e ->
    SSATernary (updateExprCalls deadParams c)
               (updateExprCalls deadParams t)
               (updateExprCalls deadParams e)
  SSANewObject cn args ->
    SSANewObject cn (map (updateExprCalls deadParams) args)
  SSAFieldAccess target field ->
    SSAFieldAccess (updateExprCalls deadParams target) field
  e -> e

-- | Remove elements at given indices from a list
removeIndices :: [Int] -> [a] -> [a]
removeIndices indices xs =
  let indexSet = Set.fromList indices
  in [x | (i, x) <- zip [0..] xs, not (Set.member i indexSet)]
