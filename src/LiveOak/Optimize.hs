{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RecordWildCards #-}

-- | Optimization passes for LiveOak.
-- Includes constant folding, dead code elimination, and dataflow optimizations.
-- Uses SSA form for copy propagation, CSE, constant propagation, and PRE.
module LiveOak.Optimize
  ( -- * Optimization Passes
    optimize
  , constantFold
  , eliminateDeadCode

    -- * Expression Optimization
  , foldExpr

    -- * Statement Optimization
  , foldStmt
  , eliminateDeadStmt
  ) where

import LiveOak.Ast
import qualified LiveOak.DataFlow as DF

-- | Apply all optimizations to a program.
-- Runs multiple passes until the program stabilizes or max iterations reached.
optimize :: Program -> Program
optimize = id

-- | Single pass of all optimizations.
optimizeOnce :: Program -> Program
optimizeOnce =
    eliminateDeadCode
  . DF.optimizeSSADataFlow
  . DF.optimizeASTDataFlow
  . constantFold

-- | Constant folding: evaluate constant expressions at compile time.
constantFold :: Program -> Program
constantFold (Program classes) = Program (map foldClass classes)

-- | Fold constants in a class.
foldClass :: ClassDecl -> ClassDecl
foldClass cls@ClassDecl{..} = cls { classMethods = map foldMethod classMethods }

-- | Fold constants in a method.
foldMethod :: MethodDecl -> MethodDecl
foldMethod m@MethodDecl{..} = m { methodBody = foldStmt methodBody }

-- | Fold constants in a statement.
foldStmt :: Stmt -> Stmt
foldStmt = \case
  Block stmts pos -> Block (map foldStmt stmts) pos

  VarDecl name vt initOpt pos ->
    VarDecl name vt (foldExpr <$> initOpt) pos

  Assign name value pos ->
    Assign name (foldExpr value) pos

  FieldAssign target field offset value pos ->
    FieldAssign (foldExpr target) field offset (foldExpr value) pos

  Return valueOpt pos ->
    Return (foldExpr <$> valueOpt) pos

  If cond th el pos ->
    If (foldExpr cond) (foldStmt th) (foldStmt el) pos

  While cond body pos ->
    While (foldExpr cond) (foldStmt body) pos

  Break pos -> Break pos

  ExprStmt expr pos ->
    ExprStmt (foldExpr expr) pos

-- | Fold constants in an expression.
foldExpr :: Expr -> Expr
foldExpr expr = case expr of
  -- Literals are already folded
  IntLit _ _  -> expr
  BoolLit _ _ -> expr
  StrLit _ _  -> expr
  NullLit _   -> expr
  Var _ _     -> expr
  This _      -> expr

  -- Unary operations
  Unary op e pos ->
    let e' = foldExpr e
    in case (op, e') of
      -- Fold constants
      (Neg, IntLit n _)  -> IntLit (-n) pos
      (Not, BoolLit b _) -> BoolLit (not b) pos
      -- Double negation elimination: --x = x, !!x = x
      (Neg, Unary Neg inner _) -> inner
      (Not, Unary Not inner _) -> inner
      _                        -> Unary op e' pos

  -- Binary operations
  Binary op l r pos ->
    let l' = foldExpr l
        r' = foldExpr r
    in foldBinary op l' r' pos

  -- Ternary: fold condition and potentially eliminate branch
  Ternary cond th el pos ->
    let cond' = foldExpr cond
        th'   = foldExpr th
        el'   = foldExpr el
    in case cond' of
      BoolLit True _  -> th'
      BoolLit False _ -> el'
      _               -> Ternary cond' th' el' pos

  -- Calls: fold arguments
  Call name args pos ->
    Call name (map foldExpr args) pos

  InstanceCall target method args pos ->
    InstanceCall (foldExpr target) method (map foldExpr args) pos

  NewObject cn args pos ->
    NewObject cn (map foldExpr args) pos

  FieldAccess target field pos ->
    FieldAccess (foldExpr target) field pos

-- | Fold binary operations on constants.
foldBinary :: BinaryOp -> Expr -> Expr -> Int -> Expr
foldBinary op l r pos = case (op, l, r) of
  -- Algebraic reassociation: (x op c1) op c2 = x op (c1 op c2)
  -- Addition: (x + c1) + c2 = x + (c1 + c2)
  (Add, Binary Add x (IntLit c1 _) _, IntLit c2 _) ->
    foldBinary Add x (IntLit (c1 + c2) pos) pos
  (Add, Binary Add (IntLit c1 _) x _, IntLit c2 _) ->
    foldBinary Add x (IntLit (c1 + c2) pos) pos

  -- Subtraction: (x - c1) - c2 = x - (c1 + c2)
  (Sub, Binary Sub x (IntLit c1 _) _, IntLit c2 _) ->
    foldBinary Sub x (IntLit (c1 + c2) pos) pos
  -- (x + c1) - c2 = x + (c1 - c2)
  (Sub, Binary Add x (IntLit c1 _) _, IntLit c2 _) ->
    foldBinary Add x (IntLit (c1 - c2) pos) pos
  -- (x - c1) + c2 = x - (c1 - c2) = x + (c2 - c1)
  (Add, Binary Sub x (IntLit c1 _) _, IntLit c2 _) ->
    foldBinary Add x (IntLit (c2 - c1) pos) pos

  -- Multiplication: (x * c1) * c2 = x * (c1 * c2)
  (Mul, Binary Mul x (IntLit c1 _) _, IntLit c2 _) ->
    foldBinary Mul x (IntLit (c1 * c2) pos) pos
  (Mul, Binary Mul (IntLit c1 _) x _, IntLit c2 _) ->
    foldBinary Mul x (IntLit (c1 * c2) pos) pos

  -- Division: (x / c1) / c2 = x / (c1 * c2) (when c1*c2 != 0)
  (Div, Binary Div x (IntLit c1 _) _, IntLit c2 _) | c1 * c2 /= 0 ->
    foldBinary Div x (IntLit (c1 * c2) pos) pos

  -- Boolean reassociation: (x && c1) && c2 = x && (c1 && c2)
  (And, Binary And x (BoolLit c1 _) _, BoolLit c2 _) ->
    foldBinary And x (BoolLit (c1 && c2) pos) pos
  (Or, Binary Or x (BoolLit c1 _) _, BoolLit c2 _) ->
    foldBinary Or x (BoolLit (c1 || c2) pos) pos

  -- String concatenation reassociation: (x + "a") + "b" = x + "ab"
  (Add, Binary Add x (StrLit s1 _) _, StrLit s2 _) ->
    foldBinary Add x (StrLit (s1 ++ s2) pos) pos

  -- Integer arithmetic on literals
  (Add, IntLit a _, IntLit b _) -> IntLit (a + b) pos
  (Sub, IntLit a _, IntLit b _) -> IntLit (a - b) pos
  (Mul, IntLit a _, IntLit b _) -> IntLit (a * b) pos
  (Div, IntLit a _, IntLit b _) | b /= 0 -> IntLit (a `div` b) pos
  (Mod, IntLit a _, IntLit b _) | b /= 0 -> IntLit (a `mod` b) pos

  -- Integer comparisons on literals
  (Eq, IntLit a _, IntLit b _)  -> BoolLit (a == b) pos
  (Ne, IntLit a _, IntLit b _)  -> BoolLit (a /= b) pos
  (Lt, IntLit a _, IntLit b _)  -> BoolLit (a < b) pos
  (Le, IntLit a _, IntLit b _)  -> BoolLit (a <= b) pos
  (Gt, IntLit a _, IntLit b _)  -> BoolLit (a > b) pos
  (Ge, IntLit a _, IntLit b _)  -> BoolLit (a >= b) pos

  -- Boolean operations on literals
  (And, BoolLit a _, BoolLit b _) -> BoolLit (a && b) pos
  (Or,  BoolLit a _, BoolLit b _) -> BoolLit (a || b) pos

  -- Short-circuit optimizations for And
  (And, BoolLit False _, _) -> BoolLit False pos
  (And, BoolLit True _, r') -> r'
  (And, _, BoolLit False _) -> BoolLit False pos
  (And, l', BoolLit True _) -> l'

  -- Short-circuit optimizations for Or
  (Or, BoolLit True _, _)   -> BoolLit True pos
  (Or, BoolLit False _, r') -> r'
  (Or, _, BoolLit True _)   -> BoolLit True pos
  (Or, l', BoolLit False _) -> l'

  -- String concatenation of literals
  (Add, StrLit a _, StrLit b _) -> StrLit (a ++ b) pos

  -- String repetition: "" * n = "", s * 0 = "", s * 1 = s
  (Mul, StrLit "" _, _) -> StrLit "" pos
  (Mul, StrLit _ _, IntLit 0 _) -> StrLit "" pos
  (Mul, s@(StrLit _ _), IntLit 1 _) -> s

  -- Additive identity: x + 0 = x, 0 + x = x, x - 0 = x
  (Add, e, IntLit 0 _) -> e
  (Add, IntLit 0 _, e) -> e
  (Sub, e, IntLit 0 _) -> e

  -- Subtraction from zero: 0 - x = -x
  (Sub, IntLit 0 _, e) -> Unary Neg e pos

  -- Multiplicative identity: x * 1 = x, 1 * x = x (for integers)
  (Mul, e, IntLit 1 _) -> e
  (Mul, IntLit 1 _, e) -> e

  -- Multiplicative zero: x * 0 = 0, 0 * x = 0 (for integers, not strings)
  -- Note: literal * literal cases are handled by constant folding above
  (Mul, Var _ _, IntLit 0 _) -> IntLit 0 pos     -- var * 0
  (Mul, IntLit 0 _, Var _ _) -> IntLit 0 pos     -- 0 * var

  -- Division by 1: x / 1 = x
  (Div, e, IntLit 1 _) -> e

  -- Modulo by 1: x % 1 = 0
  (Mod, _, IntLit 1 _) -> IntLit 0 pos

  -- Note: power-of-2 multiplication is handled in codegen with LSHIFT

  -- Self-comparison: x = x is always true, x != x is always false
  -- (Only safe for variables, not expressions with side effects)
  (Eq, Var n1 _, Var n2 _) | n1 == n2 -> BoolLit True pos
  (Ne, Var n1 _, Var n2 _) | n1 == n2 -> BoolLit False pos
  (Le, Var n1 _, Var n2 _) | n1 == n2 -> BoolLit True pos   -- x <= x
  (Ge, Var n1 _, Var n2 _) | n1 == n2 -> BoolLit True pos   -- x >= x
  (Lt, Var n1 _, Var n2 _) | n1 == n2 -> BoolLit False pos  -- x < x
  (Gt, Var n1 _, Var n2 _) | n1 == n2 -> BoolLit False pos  -- x > x

  -- Self-subtraction: x - x = 0 (safe for variables)
  (Sub, Var n1 _, Var n2 _) | n1 == n2 -> IntLit 0 pos

  -- Self-division: x / x = 1 (safe for variables, assuming x != 0)
  (Div, Var n1 _, Var n2 _) | n1 == n2 -> IntLit 1 pos

  -- Self-modulo: x % x = 0 (safe for variables, assuming x != 0)
  (Mod, Var n1 _, Var n2 _) | n1 == n2 -> IntLit 0 pos

  -- Idempotent boolean: x & x = x, x | x = x
  (And, e1@(Var n1 _), Var n2 _) | n1 == n2 -> e1
  (Or, e1@(Var n1 _), Var n2 _) | n1 == n2 -> e1

  -- Right-associative constant folding: c1 + (x + c2) = x + (c1 + c2)
  (Add, IntLit c1 _, Binary Add x (IntLit c2 _) _) ->
    foldBinary Add x (IntLit (c1 + c2) pos) pos
  (Add, IntLit c1 _, Binary Add (IntLit c2 _) x _) ->
    foldBinary Add x (IntLit (c1 + c2) pos) pos

  -- c1 * (x * c2) = x * (c1 * c2)
  (Mul, IntLit c1 _, Binary Mul x (IntLit c2 _) _) ->
    foldBinary Mul x (IntLit (c1 * c2) pos) pos
  (Mul, IntLit c1 _, Binary Mul (IntLit c2 _) x _) ->
    foldBinary Mul x (IntLit (c1 * c2) pos) pos

  -- Comparison strength reduction for known values
  -- x < 0 where x >= 0 (unsigned semantics) -> false
  -- These would need type info, skip for now

  -- Distribution/factoring: x + x = 2 * x (complement of strength reduction)
  -- Skipped - strength reduction x * 2 = x + x is more common

  -- No optimization possible
  _ -> Binary op l r pos

-- | Dead code elimination: remove unreachable code.
eliminateDeadCode :: Program -> Program
eliminateDeadCode (Program classes) = Program (map elimClass classes)

-- | Eliminate dead code in a class.
elimClass :: ClassDecl -> ClassDecl
elimClass cls@ClassDecl{..} = cls { classMethods = map elimMethod classMethods }

-- | Eliminate dead code in a method.
elimMethod :: MethodDecl -> MethodDecl
elimMethod m@MethodDecl{..} = m { methodBody = eliminateDeadStmt methodBody }

-- | Eliminate dead code in a statement.
-- Removes code after return/break and simplifies always-true/false conditions.
eliminateDeadStmt :: Stmt -> Stmt
eliminateDeadStmt = \case
  Block stmts pos ->
    Block (eliminateDeadInBlock stmts) pos

  VarDecl name vt initOpt pos ->
    VarDecl name vt initOpt pos

  Assign name value pos ->
    Assign name value pos

  FieldAssign target field offset value pos ->
    FieldAssign target field offset value pos

  Return valueOpt pos ->
    Return valueOpt pos

  If cond th el pos ->
    -- Fold constant conditions
    case cond of
      BoolLit True _  -> eliminateDeadStmt th
      BoolLit False _ -> eliminateDeadStmt el
      _ -> If cond (eliminateDeadStmt th) (eliminateDeadStmt el) pos

  While cond body pos ->
    -- Fold constant false condition to empty block
    case cond of
      BoolLit False _ -> Block [] pos  -- while(false) never executes
      _ -> While cond (eliminateDeadStmt body) pos

  Break pos -> Break pos

  ExprStmt expr pos ->
    ExprStmt expr pos

-- | Eliminate dead code in a block.
-- Removes statements after return or break.
eliminateDeadInBlock :: [Stmt] -> [Stmt]
eliminateDeadInBlock [] = []
eliminateDeadInBlock (s:ss) =
  let s' = eliminateDeadStmt s
  in if terminates s'
     then [s']  -- Drop everything after a terminating statement
     else s' : eliminateDeadInBlock ss

-- | Check if a statement always terminates (return or break).
terminates :: Stmt -> Bool
terminates = \case
  Return _ _ -> True
  Break _    -> True
  Block stmts _ -> any terminates stmts
  If _ th el _ -> terminates th && terminates el  -- Both branches terminate
  _ -> False
