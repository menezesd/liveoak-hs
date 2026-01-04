{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RecordWildCards #-}

-- | AST-level dataflow optimizations that don't require SSA.
-- Includes lightweight null-check elimination and value range pruning.
module LiveOak.DataFlow.AST
  ( optimizeASTDataFlow
  , eliminateNullChecks
  , eliminateImpossibleBranches
  ) where

import LiveOak.Ast

import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Maybe (fromMaybe)
import Data.Set (Set)
import qualified Data.Set as Set

-- | Run the AST dataflow passes in sequence.
optimizeASTDataFlow :: Program -> Program
optimizeASTDataFlow =
    eliminateNullChecks
  . eliminateImpossibleBranches

--------------------------------------------------------------------------------
-- Null Check Elimination
--------------------------------------------------------------------------------

-- | Set of variables known to be non-null.
type NonNullSet = Set String

-- | Eliminate redundant null checks by tracking non-null values.
eliminateNullChecks :: Program -> Program
eliminateNullChecks (Program classes) = Program (map nceClass classes)

nceClass :: ClassDecl -> ClassDecl
nceClass cls@ClassDecl{..} = cls { classMethods = map nceMethod classMethods }

nceMethod :: MethodDecl -> MethodDecl
nceMethod m@MethodDecl{..} =
  let (body', _) = nceStmt Set.empty methodBody
  in m { methodBody = body' }

-- | Eliminate null checks in a statement.
nceStmt :: NonNullSet -> Stmt -> (Stmt, NonNullSet)
nceStmt nonNull = \case
  Block stmts pos ->
    let (stmts', nonNull') = nceStmts nonNull stmts
    in (Block stmts' pos, nonNull')

  VarDecl name vt initOpt pos ->
    let initOpt' = nceExpr nonNull <$> initOpt
        -- If initialized with non-null value, mark as non-null
        nonNull' = case initOpt' of
          Just e | isKnownNonNull e -> Set.insert name nonNull
          Just (NullLit _) -> Set.delete name nonNull
          _ -> nonNull
    in (VarDecl name vt initOpt' pos, nonNull')

  Assign name value pos ->
    let value' = nceExpr nonNull value
        nonNull' = if isKnownNonNull value'
                   then Set.insert name nonNull
                   else Set.delete name nonNull
    in (Assign name value' pos, nonNull')

  FieldAssign target field offset value pos ->
    (FieldAssign (nceExpr nonNull target) field offset (nceExpr nonNull value) pos, nonNull)

  Return valueOpt pos ->
    (Return (nceExpr nonNull <$> valueOpt) pos, nonNull)

  If cond th el pos ->
    let cond' = nceExpr nonNull cond
        -- If condition is null check, we know more in branches
        (thNonNull, elNonNull) = case cond' of
          Binary Ne (Var v _) (NullLit _) _ -> (Set.insert v nonNull, nonNull)
          Binary Eq (Var v _) (NullLit _) _ -> (nonNull, Set.insert v nonNull)
          _ -> (nonNull, nonNull)
        (th', _) = nceStmt thNonNull th
        (el', _) = nceStmt elNonNull el
    in (If cond' th' el' pos, nonNull)  -- Conservative: clear knowledge after if

  While cond body pos ->
    let cond' = nceExpr nonNull cond
        (body', _) = nceStmt Set.empty body  -- Conservative in loops
    in (While cond' body' pos, Set.empty)

  Break pos -> (Break pos, nonNull)
  ExprStmt expr pos -> (ExprStmt (nceExpr nonNull expr) pos, nonNull)

-- | Process statements for null check elimination.
nceStmts :: NonNullSet -> [Stmt] -> ([Stmt], NonNullSet)
nceStmts nonNull [] = ([], nonNull)
nceStmts nonNull (s:ss) =
  let (s', nonNull') = nceStmt nonNull s
      (ss', nonNull'') = nceStmts nonNull' ss
  in (s':ss', nonNull'')

-- | Eliminate null checks in an expression.
nceExpr :: NonNullSet -> Expr -> Expr
nceExpr nonNull = \case
  -- Eliminate redundant null checks
  Binary Eq (Var v _) (NullLit _) pos | v `Set.member` nonNull ->
    BoolLit False pos  -- Known non-null, so v == null is false
  Binary Ne (Var v _) (NullLit _) pos | v `Set.member` nonNull ->
    BoolLit True pos   -- Known non-null, so v != null is true
  Binary Eq (NullLit _) (Var v _) pos | v `Set.member` nonNull ->
    BoolLit False pos
  Binary Ne (NullLit _) (Var v _) pos | v `Set.member` nonNull ->
    BoolLit True pos

  -- Recurse
  Binary op l r pos -> Binary op (nceExpr nonNull l) (nceExpr nonNull r) pos
  Unary op e pos -> Unary op (nceExpr nonNull e) pos
  Ternary c t e pos -> Ternary (nceExpr nonNull c) (nceExpr nonNull t) (nceExpr nonNull e) pos
  Call name args pos -> Call name (map (nceExpr nonNull) args) pos
  InstanceCall target method args pos ->
    InstanceCall (nceExpr nonNull target) method (map (nceExpr nonNull) args) pos
  NewObject cn args pos -> NewObject cn (map (nceExpr nonNull) args) pos
  FieldAccess target field pos -> FieldAccess (nceExpr nonNull target) field pos
  e -> e

-- | Check if an expression is known to be non-null.
isKnownNonNull :: Expr -> Bool
isKnownNonNull = \case
  IntLit _ _ -> True
  BoolLit _ _ -> True
  StrLit _ _ -> True
  This _ -> True
  NewObject _ _ _ -> True  -- new objects are never null
  _ -> False

--------------------------------------------------------------------------------
-- Value Range Analysis
--------------------------------------------------------------------------------

-- | Value range: [lower, upper] bounds for integers
data Range = Range
  { rangeLower :: Maybe Int  -- Nothing = negative infinity
  , rangeUpper :: Maybe Int  -- Nothing = positive infinity
  } deriving (Eq, Show)

-- | Full range (unknown)
fullRange :: Range
fullRange = Range Nothing Nothing

-- | Exact value range
exactRange :: Int -> Range
exactRange n = Range (Just n) (Just n)

-- | Map from variable to its known range
type RangeMap = Map String Range

-- | Eliminate branches that are impossible based on value range analysis.
-- Tracks integer ranges through assignments and conditions.
eliminateImpossibleBranches :: Program -> Program
eliminateImpossibleBranches (Program classes) = Program (map rangeClass classes)

rangeClass :: ClassDecl -> ClassDecl
rangeClass cls@ClassDecl{..} = cls { classMethods = map rangeMethod classMethods }

rangeMethod :: MethodDecl -> MethodDecl
rangeMethod m@MethodDecl{..} =
  let (body', _) = rangeStmt Map.empty methodBody
  in m { methodBody = body' }

-- | Analyze ranges and eliminate impossible branches
rangeStmt :: RangeMap -> Stmt -> (Stmt, RangeMap)
rangeStmt ranges = \case
  Block stmts pos ->
    let (stmts', ranges') = rangeStmts ranges stmts
    in (Block stmts' pos, ranges')

  VarDecl name vt initOpt pos ->
    let initOpt' = rangeExpr ranges <$> initOpt
        -- Track the range of the initialized value
        ranges' = case initOpt' of
          Just (IntLit n _) -> Map.insert name (exactRange n) ranges
          Just (Binary Add (Var v _) (IntLit n _) _) ->
            case Map.lookup v ranges of
              Just (Range (Just lo) (Just hi)) ->
                Map.insert name (Range (Just (lo + n)) (Just (hi + n))) ranges
              _ -> Map.delete name ranges
          _ -> Map.delete name ranges
    in (VarDecl name vt initOpt' pos, ranges')

  Assign name value pos ->
    let value' = rangeExpr ranges value
        ranges0 = Map.delete name ranges
        ranges' = case value' of
          IntLit n _ -> Map.insert name (exactRange n) ranges0
          Binary Add (Var v _) (IntLit n _) _ | v == name ->
            case Map.lookup name ranges of
              Just (Range (Just lo) (Just hi)) ->
                Map.insert name (Range (Just (lo + n)) (Just (hi + n))) ranges0
              Just (Range (Just lo) Nothing) | n >= 0 ->
                Map.insert name (Range (Just (lo + n)) Nothing) ranges0
              _ -> ranges0
          Var v _ -> case Map.lookup v ranges of
            Just r -> Map.insert name r ranges0
            Nothing -> ranges0
          _ -> ranges0
    in (Assign name value' pos, ranges')

  FieldAssign target field offset value pos ->
    (FieldAssign (rangeExpr ranges target) field offset (rangeExpr ranges value) pos, ranges)

  Return valueOpt pos ->
    (Return (rangeExpr ranges <$> valueOpt) pos, ranges)

  If cond th el pos ->
    let cond' = rangeExpr ranges cond
    in case evalCondition ranges cond' of
      Just True ->
        let (th', _) = rangeStmt ranges th
        in (th', ranges)  -- Condition always true
      Just False ->
        let (el', _) = rangeStmt ranges el
        in (el', ranges) -- Condition always false
      Nothing ->
        -- Refine ranges for each branch based on condition
        let (thRanges, elRanges) = refineRanges ranges cond'
            (th', _) = rangeStmt thRanges th
            (el', _) = rangeStmt elRanges el
        in (If cond' th' el' pos, ranges)  -- Conservative: don't extend ranges after if

  While cond body pos ->
    let cond' = rangeExpr ranges cond
        -- Variables modified in the loop may have any value after the first iteration.
        modifiedVars = findModifiedVars body
        bodyRanges = foldr Map.delete ranges modifiedVars
        -- Refine ranges based on condition (only applies to unmodified vars)
        (bodyRanges', _) = refineRanges bodyRanges cond'
        (body', _) = rangeStmt bodyRanges' body
    in (While cond' body' pos, Map.empty)  -- Conservative after loop

  Break pos -> (Break pos, ranges)
  ExprStmt expr pos -> (ExprStmt (rangeExpr ranges expr) pos, ranges)

-- | Process statements with range tracking
rangeStmts :: RangeMap -> [Stmt] -> ([Stmt], RangeMap)
rangeStmts ranges [] = ([], ranges)
rangeStmts ranges (s:ss) =
  let (s', ranges') = rangeStmt ranges s
      (ss', ranges'') = rangeStmts ranges' ss
  in (s':ss', ranges'')

-- | Find all variables that are assigned (modified) in a statement
findModifiedVars :: Stmt -> [String]
findModifiedVars = \case
  Block stmts _ -> concatMap findModifiedVars stmts
  VarDecl name _ _ _ -> [name]  -- Declaration counts as modification
  Assign name _ _ -> [name]
  FieldAssign _ _ _ _ _ -> []  -- Field assigns don't modify local vars
  Return _ _ -> []
  If _ th el _ -> findModifiedVars th ++ findModifiedVars el
  While _ body _ -> findModifiedVars body
  Break _ -> []
  ExprStmt _ _ -> []

-- | Apply range info to expression
-- Note: We intentionally don't replace variables with constants here.
rangeExpr :: RangeMap -> Expr -> Expr
rangeExpr _ = id  -- Range info is only used for branch elimination

-- | Evaluate a condition to a constant if possible
evalCondition :: RangeMap -> Expr -> Maybe Bool
evalCondition ranges = \case
  BoolLit b _ -> Just b

  -- x < n: if x's upper bound < n, always true; if x's lower bound >= n, always false
  Binary Lt (Var name _) (IntLit n _) _ ->
    case Map.lookup name ranges of
      Just (Range _ (Just hi)) | hi < n -> Just True   -- upper < n means always true
      Just (Range (Just lo) _) | lo >= n -> Just False -- lower >= n means always false
      _ -> Nothing

  -- x <= n: if upper <= n, always true; if lower > n, always false
  Binary Le (Var name _) (IntLit n _) _ ->
    case Map.lookup name ranges of
      Just (Range _ (Just hi)) | hi <= n -> Just True
      Just (Range (Just lo) _) | lo > n -> Just False
      _ -> Nothing

  -- x > n: if lower > n, always true; if upper <= n, always false
  Binary Gt (Var name _) (IntLit n _) _ ->
    case Map.lookup name ranges of
      Just (Range (Just lo) _) | lo > n -> Just True
      Just (Range _ (Just hi)) | hi <= n -> Just False
      _ -> Nothing

  -- x >= n: if lower >= n, always true; if upper < n, always false
  Binary Ge (Var name _) (IntLit n _) _ ->
    case Map.lookup name ranges of
      Just (Range (Just lo) _) | lo >= n -> Just True
      Just (Range _ (Just hi)) | hi < n -> Just False
      _ -> Nothing

  -- x == n: if range is exactly n, always true; if n is outside range, always false
  Binary Eq (Var name _) (IntLit n _) _ ->
    case Map.lookup name ranges of
      Just (Range (Just lo) (Just hi)) | lo == hi && lo == n -> Just True
      Just (Range (Just lo) _) | lo > n -> Just False
      Just (Range _ (Just hi)) | hi < n -> Just False
      _ -> Nothing

  -- x != n: if n is outside range, always true; if range is exactly n, always false
  Binary Ne (Var name _) (IntLit n _) _ ->
    case Map.lookup name ranges of
      Just (Range (Just lo) (Just hi)) | lo == hi && lo == n -> Just False
      Just (Range (Just lo) _) | lo > n -> Just True
      Just (Range _ (Just hi)) | hi < n -> Just True
      _ -> Nothing

  _ -> Nothing

-- | Refine ranges based on condition being true (for then branch) or false (for else branch)
refineRanges :: RangeMap -> Expr -> (RangeMap, RangeMap)
refineRanges ranges = \case
  -- x < n: then branch has x in [lo, n-1], else branch has x in [n, hi]
  Binary Lt (Var name _) (IntLit n _) _ ->
    let current = Map.findWithDefault fullRange name ranges
        thenRange = current { rangeUpper = Just (min (fromMaybe (n - 1) (rangeUpper current)) (n - 1)) }
        elseRange = current { rangeLower = Just (max (fromMaybe n (rangeLower current)) n) }
    in (Map.insert name thenRange ranges, Map.insert name elseRange ranges)

  -- x <= n: then has [lo, n], else has [n+1, hi]
  Binary Le (Var name _) (IntLit n _) _ ->
    let current = Map.findWithDefault fullRange name ranges
        thenRange = current { rangeUpper = Just (min (fromMaybe n (rangeUpper current)) n) }
        elseRange = current { rangeLower = Just (max (fromMaybe (n + 1) (rangeLower current)) (n + 1)) }
    in (Map.insert name thenRange ranges, Map.insert name elseRange ranges)

  -- x > n: then has [n+1, hi], else has [lo, n]
  Binary Gt (Var name _) (IntLit n _) _ ->
    let current = Map.findWithDefault fullRange name ranges
        thenRange = current { rangeLower = Just (max (fromMaybe (n + 1) (rangeLower current)) (n + 1)) }
        elseRange = current { rangeUpper = Just (min (fromMaybe n (rangeUpper current)) n) }
    in (Map.insert name thenRange ranges, Map.insert name elseRange ranges)

  -- x >= n: then has [n, hi], else has [lo, n-1]
  Binary Ge (Var name _) (IntLit n _) _ ->
    let current = Map.findWithDefault fullRange name ranges
        thenRange = current { rangeLower = Just (max (fromMaybe n (rangeLower current)) n) }
        elseRange = current { rangeUpper = Just (min (fromMaybe (n - 1) (rangeUpper current)) (n - 1)) }
    in (Map.insert name thenRange ranges, Map.insert name elseRange ranges)

  -- x == n: then has [n, n], else keeps current range (can't narrow much)
  Binary Eq (Var name _) (IntLit n _) _ ->
    (Map.insert name (exactRange n) ranges, ranges)

  -- x != n: then keeps range, else has [n, n]
  Binary Ne (Var name _) (IntLit n _) _ ->
    (ranges, Map.insert name (exactRange n) ranges)

  -- For other conditions, don't refine
  _ -> (ranges, ranges)
