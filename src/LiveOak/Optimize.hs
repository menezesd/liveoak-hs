{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RecordWildCards #-}

-- | Optimization passes for LiveOak.
-- Includes constant folding and dead code elimination.
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

-- | Apply all optimizations to a program.
optimize :: Program -> Program
optimize = eliminateDeadCode . constantFold

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
      (Neg, IntLit n _)  -> IntLit (-n) pos
      (Not, BoolLit b _) -> BoolLit (not b) pos
      _                  -> Unary op e' pos

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
  -- Integer arithmetic
  (Add, IntLit a _, IntLit b _) -> IntLit (a + b) pos
  (Sub, IntLit a _, IntLit b _) -> IntLit (a - b) pos
  (Mul, IntLit a _, IntLit b _) -> IntLit (a * b) pos
  (Div, IntLit a _, IntLit b _) | b /= 0 -> IntLit (a `div` b) pos
  (Mod, IntLit a _, IntLit b _) | b /= 0 -> IntLit (a `mod` b) pos

  -- Integer comparisons
  (Eq, IntLit a _, IntLit b _)  -> BoolLit (a == b) pos
  (Ne, IntLit a _, IntLit b _)  -> BoolLit (a /= b) pos
  (Lt, IntLit a _, IntLit b _)  -> BoolLit (a < b) pos
  (Le, IntLit a _, IntLit b _)  -> BoolLit (a <= b) pos
  (Gt, IntLit a _, IntLit b _)  -> BoolLit (a > b) pos
  (Ge, IntLit a _, IntLit b _)  -> BoolLit (a >= b) pos

  -- Boolean operations
  (And, BoolLit a _, BoolLit b _) -> BoolLit (a && b) pos
  (Or,  BoolLit a _, BoolLit b _) -> BoolLit (a || b) pos

  -- Short-circuit optimizations
  (And, BoolLit False _, _) -> BoolLit False pos
  (And, BoolLit True _, r') -> r'
  (And, _, BoolLit False _) -> BoolLit False pos
  (And, l', BoolLit True _) -> l'

  (Or, BoolLit True _, _)   -> BoolLit True pos
  (Or, BoolLit False _, r') -> r'
  (Or, _, BoolLit True _)   -> BoolLit True pos
  (Or, l', BoolLit False _) -> l'

  -- String concatenation of literals
  (Add, StrLit a _, StrLit b _) -> StrLit (a ++ b) pos

  -- Identity operations: x + 0 = x, x * 1 = x, etc.
  (Add, e, IntLit 0 _) -> e
  (Add, IntLit 0 _, e) -> e
  (Sub, e, IntLit 0 _) -> e
  (Mul, e, IntLit 1 _) -> e
  (Mul, IntLit 1 _, e) -> e
  (Mul, _, IntLit 0 _) -> IntLit 0 pos
  (Mul, IntLit 0 _, _) -> IntLit 0 pos
  (Div, e, IntLit 1 _) -> e

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
