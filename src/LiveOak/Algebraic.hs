{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RecordWildCards #-}

-- | Algebraic Simplifications.
-- Applies algebraic identities to simplify expressions.
--
-- == Simplifications
--
-- Additive identities:
-- - @x + 0 = 0 + x = x@
-- - @x - 0 = x@
-- - @x - x = 0@
--
-- Multiplicative identities:
-- - @x * 1 = 1 * x = x@
-- - @x * 0 = 0 * x = 0@
-- - @x / 1 = x@
-- - @x % 1 = 0@
--
-- Boolean identities:
-- - @x && true = x@
-- - @x && false = false@
-- - @x || true = true@
-- - @x || false = x@
-- - @!(!x) = x@
--
-- Comparison identities:
-- - @x == x = true@ (for non-floating-point)
-- - @x != x = false@
-- - @x < x = false@
-- - @x <= x = true@
--
module LiveOak.Algebraic
  ( -- * Algebraic Simplification
    simplifyAlgebraic
  , simplifyAlgebraicMethod
  , AlgebraicResult(..)
  ) where

import LiveOak.SSATypes
import LiveOak.Ast (BinaryOp(..), UnaryOp(..))

--------------------------------------------------------------------------------
-- Types
--------------------------------------------------------------------------------

-- | Algebraic simplification result
data AlgebraicResult = AlgebraicResult
  { arOptBlocks :: ![SSABlock]
  , arSimplified :: !Int          -- ^ Number of expressions simplified
  } deriving (Show)

--------------------------------------------------------------------------------
-- Algebraic Simplification
--------------------------------------------------------------------------------

-- | Simplify algebraic expressions in blocks
simplifyAlgebraic :: [SSABlock] -> AlgebraicResult
simplifyAlgebraic blocks =
  let (optimized, counts) = unzip $ map simplifyBlock blocks
  in AlgebraicResult
    { arOptBlocks = optimized
    , arSimplified = sum counts
    }

-- | Simplify algebraic expressions in a method
simplifyAlgebraicMethod :: SSAMethod -> AlgebraicResult
simplifyAlgebraicMethod method =
  simplifyAlgebraic (ssaMethodBlocks method)

-- | Simplify a block
simplifyBlock :: SSABlock -> (SSABlock, Int)
simplifyBlock block@SSABlock{..} =
  let (instrs', counts) = unzip $ map simplifyInstr blockInstrs
  in (block { blockInstrs = instrs' }, sum counts)

-- | Simplify an instruction
simplifyInstr :: SSAInstr -> (SSAInstr, Int)
simplifyInstr = \case
  SSAAssign var expr ->
    let (expr', count) = simplifyExpr expr
    in (SSAAssign var expr', count)

  SSABranch cond thenB elseB ->
    let (cond', count) = simplifyExpr cond
    in case cond' of
      SSABool True -> (SSAJump thenB, count + 1)
      SSABool False -> (SSAJump elseB, count + 1)
      _ -> (SSABranch cond' thenB elseB, count)

  SSAReturn (Just expr) ->
    let (expr', count) = simplifyExpr expr
    in (SSAReturn (Just expr'), count)

  SSAReturn Nothing -> (SSAReturn Nothing, 0)

  SSAFieldStore target field idx expr ->
    let (expr', count) = simplifyExpr expr
    in (SSAFieldStore target field idx expr', count)

  SSAExprStmt expr ->
    let (expr', count) = simplifyExpr expr
    in (SSAExprStmt expr', count)

  instr -> (instr, 0)

-- | Simplify an expression
simplifyExpr :: SSAExpr -> (SSAExpr, Int)
simplifyExpr expr = case expr of
  -- Binary operations
  SSABinary op left right ->
    let (left', c1) = simplifyExpr left
        (right', c2) = simplifyExpr right
        (result, c3) = simplifyBinary op left' right'
    in (result, c1 + c2 + c3)

  -- Unary operations
  SSAUnary op operand ->
    let (operand', c1) = simplifyExpr operand
        (result, c2) = simplifyUnary op operand'
    in (result, c1 + c2)

  -- Recursively simplify nested expressions
  SSAInstanceCall target method args ->
    let (args', counts) = unzip $ map simplifyExpr args
    in (SSAInstanceCall target method args', sum counts)

  SSACall name args ->
    let (args', counts) = unzip $ map simplifyExpr args
    in (SSACall name args', sum counts)

  SSANewObject cls args ->
    let (args', counts) = unzip $ map simplifyExpr args
    in (SSANewObject cls args', sum counts)

  -- Terminals - no simplification
  _ -> (expr, 0)

-- | Simplify a binary operation
simplifyBinary :: BinaryOp -> SSAExpr -> SSAExpr -> (SSAExpr, Int)
simplifyBinary op left right = case op of
  -- Addition identities
  Add -> case (left, right) of
    (SSAInt 0, _) -> (right, 1)           -- 0 + x = x
    (_, SSAInt 0) -> (left, 1)            -- x + 0 = x
    _ -> (SSABinary op left right, 0)

  -- Subtraction identities
  Sub -> case (left, right) of
    (_, SSAInt 0) -> (left, 1)            -- x - 0 = x
    _ | sameVar left right -> (SSAInt 0, 1) -- x - x = 0
    _ -> (SSABinary op left right, 0)

  -- Multiplication identities
  Mul -> case (left, right) of
    (SSAInt 1, _) -> (right, 1)           -- 1 * x = x
    (_, SSAInt 1) -> (left, 1)            -- x * 1 = x
    (SSAInt 0, _) -> (SSAInt 0, 1)        -- 0 * x = 0
    (_, SSAInt 0) -> (SSAInt 0, 1)        -- x * 0 = 0
    (SSAInt (-1), _) -> (SSAUnary Neg right, 1)  -- -1 * x = -x
    (_, SSAInt (-1)) -> (SSAUnary Neg left, 1)   -- x * -1 = -x
    _ -> (SSABinary op left right, 0)

  -- Division identities
  Div -> case (left, right) of
    (_, SSAInt 1) -> (left, 1)            -- x / 1 = x
    (SSAInt 0, _) -> (SSAInt 0, 1)        -- 0 / x = 0 (assume x != 0)
    _ | sameVar left right -> (SSAInt 1, 1) -- x / x = 1 (assume x != 0)
    _ -> (SSABinary op left right, 0)

  -- Modulo identities
  Mod -> case (left, right) of
    (_, SSAInt 1) -> (SSAInt 0, 1)        -- x % 1 = 0
    (SSAInt 0, _) -> (SSAInt 0, 1)        -- 0 % x = 0
    _ | sameVar left right -> (SSAInt 0, 1) -- x % x = 0 (assume x != 0)
    _ -> (SSABinary op left right, 0)

  -- Logical AND identities
  And -> case (left, right) of
    (SSABool True, _) -> (right, 1)       -- true && x = x
    (_, SSABool True) -> (left, 1)        -- x && true = x
    (SSABool False, _) -> (SSABool False, 1)  -- false && x = false
    (_, SSABool False) -> (SSABool False, 1)  -- x && false = false
    _ | sameVar left right -> (left, 1)   -- x && x = x
    _ -> (SSABinary op left right, 0)

  -- Logical OR identities
  Or -> case (left, right) of
    (SSABool False, _) -> (right, 1)      -- false || x = x
    (_, SSABool False) -> (left, 1)       -- x || false = x
    (SSABool True, _) -> (SSABool True, 1)   -- true || x = true
    (_, SSABool True) -> (SSABool True, 1)   -- x || true = true
    _ | sameVar left right -> (left, 1)   -- x || x = x
    _ -> (SSABinary op left right, 0)

  -- Equality identities
  Eq -> case (left, right) of
    _ | sameVar left right -> (SSABool True, 1)  -- x == x = true
    (SSANull, SSANull) -> (SSABool True, 1)
    (SSABool b1, SSABool b2) -> (SSABool (b1 == b2), 1)
    (SSAInt n1, SSAInt n2) -> (SSABool (n1 == n2), 1)
    _ -> (SSABinary op left right, 0)

  -- Not-equal identities
  Ne -> case (left, right) of
    _ | sameVar left right -> (SSABool False, 1)  -- x != x = false
    (SSANull, SSANull) -> (SSABool False, 1)
    (SSABool b1, SSABool b2) -> (SSABool (b1 /= b2), 1)
    (SSAInt n1, SSAInt n2) -> (SSABool (n1 /= n2), 1)
    _ -> (SSABinary op left right, 0)

  -- Less-than identities
  Lt -> case (left, right) of
    _ | sameVar left right -> (SSABool False, 1)  -- x < x = false
    (SSAInt n1, SSAInt n2) -> (SSABool (n1 < n2), 1)
    _ -> (SSABinary op left right, 0)

  -- Less-than-or-equal identities
  Le -> case (left, right) of
    _ | sameVar left right -> (SSABool True, 1)  -- x <= x = true
    (SSAInt n1, SSAInt n2) -> (SSABool (n1 <= n2), 1)
    _ -> (SSABinary op left right, 0)

  -- Greater-than identities
  Gt -> case (left, right) of
    _ | sameVar left right -> (SSABool False, 1)  -- x > x = false
    (SSAInt n1, SSAInt n2) -> (SSABool (n1 > n2), 1)
    _ -> (SSABinary op left right, 0)

  -- Greater-than-or-equal identities
  Ge -> case (left, right) of
    _ | sameVar left right -> (SSABool True, 1)  -- x >= x = true
    (SSAInt n1, SSAInt n2) -> (SSABool (n1 >= n2), 1)
    _ -> (SSABinary op left right, 0)

-- | Simplify a unary operation
simplifyUnary :: UnaryOp -> SSAExpr -> (SSAExpr, Int)
simplifyUnary op operand = case op of
  -- Double negation
  Neg -> case operand of
    SSAUnary Neg inner -> (inner, 1)      -- -(-x) = x
    SSAInt n -> (SSAInt (-n), 1)          -- -n = constant
    _ -> (SSAUnary op operand, 0)

  -- Double logical not
  Not -> case operand of
    SSAUnary Not inner -> (inner, 1)      -- !(!x) = x
    SSABool b -> (SSABool (not b), 1)     -- !true = false, !false = true
    _ -> (SSAUnary op operand, 0)

-- | Check if two expressions refer to the same variable
sameVar :: SSAExpr -> SSAExpr -> Bool
sameVar (SSAUse v1) (SSAUse v2) =
  ssaName v1 == ssaName v2 && ssaVersion v1 == ssaVersion v2
sameVar SSAThis SSAThis = True
sameVar _ _ = False
