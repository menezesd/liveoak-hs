{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RecordWildCards #-}

-- | Null Check Elimination.
-- Removes redundant null checks using dataflow analysis.
--
-- == Analysis
--
-- Track "known non-null" variables:
-- - After successful field access: target is non-null
-- - After successful method call: receiver is non-null
-- - After new object creation: result is non-null
-- - After null check branch: variable is non-null in the non-null branch
--
-- == Optimizations
--
-- 1. Remove redundant null checks on known non-null values
-- 2. Simplify branches where condition is always true/false
--
module LiveOak.NullCheck
  ( -- * Null Check Elimination
    eliminateNullChecks
  , eliminateNullChecksMethod
  , NullCheckResult(..)
  ) where

import LiveOak.SSATypes
import LiveOak.Ast (BinaryOp(..))

import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Set (Set)
import qualified Data.Set as Set
import Data.List (foldl')

--------------------------------------------------------------------------------
-- Types
--------------------------------------------------------------------------------

-- | Null check elimination result
data NullCheckResult = NullCheckResult
  { ncOptBlocks :: ![SSABlock]
  , ncEliminated :: !Int          -- ^ Number of checks eliminated
  } deriving (Show)

-- | Nullability status
data NullStatus
  = NonNull       -- ^ Definitely not null
  | MaybeNull     -- ^ Could be null
  | IsNull        -- ^ Definitely null
  deriving (Eq, Show)

--------------------------------------------------------------------------------
-- Null Check Elimination
--------------------------------------------------------------------------------

-- | Eliminate null checks in blocks
eliminateNullChecks :: [SSABlock] -> NullCheckResult
eliminateNullChecks blocks =
  let -- First pass: collect known non-null variables
      nonNullVars = collectNonNullVars blocks
      -- Second pass: eliminate redundant checks
      (optimized, count) = unzip $ map (eliminateBlockNullChecks nonNullVars) blocks
  in NullCheckResult
    { ncOptBlocks = optimized
    , ncEliminated = sum count
    }

-- | Eliminate null checks in a method
eliminateNullChecksMethod :: SSAMethod -> NullCheckResult
eliminateNullChecksMethod method =
  let -- Parameters are potentially null (unless we do interprocedural analysis)
      -- 'this' is never null
      initialNonNull = Set.singleton (varName "this", 0)
      -- Collect non-null info
      nonNullVars = collectNonNullVarsWithInit initialNonNull (ssaMethodBlocks method)
      -- Eliminate checks
      (optimized, count) = unzip $ map (eliminateBlockNullChecks nonNullVars) (ssaMethodBlocks method)
  in NullCheckResult
    { ncOptBlocks = optimized
    , ncEliminated = sum count
    }

-- | Collect all definitely non-null variables
collectNonNullVars :: [SSABlock] -> Set VarKey
collectNonNullVars = collectNonNullVarsWithInit Set.empty

-- | Collect non-null variables with initial set
collectNonNullVarsWithInit :: Set VarKey -> [SSABlock] -> Set VarKey
collectNonNullVarsWithInit initial blocks =
  foldl' collectBlockNonNull initial blocks

-- | Collect non-null variables from a block
collectBlockNonNull :: Set VarKey -> SSABlock -> Set VarKey
collectBlockNonNull nonNull SSABlock{..} =
  foldl' collectInstrNonNull nonNull blockInstrs

-- | Collect non-null info from an instruction
collectInstrNonNull :: Set VarKey -> SSAInstr -> Set VarKey
collectInstrNonNull nonNull = \case
  -- New object is never null
  SSAAssign var (SSANewObject _ _) ->
    Set.insert (ssaName var, ssaVersion var) nonNull

  -- 'this' is never null
  SSAAssign var SSAThis ->
    Set.insert (ssaName var, ssaVersion var) nonNull

  -- Field access implies target is non-null (or would have crashed)
  SSAAssign _ (SSAFieldAccess target _) ->
    case target of
      SSAUse v -> Set.insert (ssaName v, ssaVersion v) nonNull
      SSAThis -> nonNull  -- Already non-null
      _ -> nonNull

  -- Instance call implies receiver is non-null
  SSAAssign _ (SSAInstanceCall target _ _) ->
    case target of
      SSAUse v -> Set.insert (ssaName v, ssaVersion v) nonNull
      SSAThis -> nonNull
      _ -> nonNull

  -- Field store implies target is non-null
  SSAFieldStore target _ _ _ ->
    case target of
      SSAUse v -> Set.insert (ssaName v, ssaVersion v) nonNull
      SSAThis -> nonNull
      _ -> nonNull

  -- Expression statement with instance call
  SSAExprStmt (SSAInstanceCall target _ _) ->
    case target of
      SSAUse v -> Set.insert (ssaName v, ssaVersion v) nonNull
      SSAThis -> nonNull
      _ -> nonNull

  _ -> nonNull

-- | Eliminate null checks in a block
eliminateBlockNullChecks :: Set VarKey -> SSABlock -> (SSABlock, Int)
eliminateBlockNullChecks nonNull block@SSABlock{..} =
  let (instrs', counts) = unzip $ map (eliminateInstrNullCheck nonNull) blockInstrs
  in (block { blockInstrs = instrs' }, sum counts)

-- | Eliminate null check in an instruction
eliminateInstrNullCheck :: Set VarKey -> SSAInstr -> (SSAInstr, Int)
eliminateInstrNullCheck nonNull instr = case instr of
  -- Check for null comparisons in assignments
  SSAAssign var expr ->
    let (expr', count) = simplifyNullCheck nonNull expr
    in (SSAAssign var expr', count)

  -- Check for null comparisons in branches
  SSABranch cond thenB elseB ->
    case analyzeNullCheck nonNull cond of
      Just True -> (SSAJump thenB, 1)   -- Condition always true
      Just False -> (SSAJump elseB, 1)  -- Condition always false
      Nothing ->
        let (cond', count) = simplifyNullCheck nonNull cond
        in (SSABranch cond' thenB elseB, count)

  _ -> (instr, 0)

-- | Analyze if a null check is always true or false
analyzeNullCheck :: Set VarKey -> SSAExpr -> Maybe Bool
analyzeNullCheck nonNull = \case
  -- x != null where x is known non-null -> true
  SSABinary Ne (SSAUse var) SSANull ->
    if Set.member (ssaName var, ssaVersion var) nonNull
    then Just True
    else Nothing

  SSABinary Ne SSANull (SSAUse var) ->
    if Set.member (ssaName var, ssaVersion var) nonNull
    then Just True
    else Nothing

  -- x == null where x is known non-null -> false
  SSABinary Eq (SSAUse var) SSANull ->
    if Set.member (ssaName var, ssaVersion var) nonNull
    then Just False
    else Nothing

  SSABinary Eq SSANull (SSAUse var) ->
    if Set.member (ssaName var, ssaVersion var) nonNull
    then Just False
    else Nothing

  -- this != null -> always true
  SSABinary Ne SSAThis SSANull -> Just True
  SSABinary Ne SSANull SSAThis -> Just True

  -- this == null -> always false
  SSABinary Eq SSAThis SSANull -> Just False
  SSABinary Eq SSANull SSAThis -> Just False

  _ -> Nothing

-- | Simplify null check expression
simplifyNullCheck :: Set VarKey -> SSAExpr -> (SSAExpr, Int)
simplifyNullCheck nonNull expr = case analyzeNullCheck nonNull expr of
  Just True -> (SSABool True, 1)
  Just False -> (SSABool False, 1)
  Nothing -> (expr, 0)
