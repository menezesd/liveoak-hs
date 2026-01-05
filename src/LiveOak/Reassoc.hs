{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RecordWildCards #-}

-- | Expression Reassociation.
-- Reorders associative/commutative expressions to enable more optimizations.
--
-- == Transformations
--
-- 1. **Constant grouping**: Group constants together for folding
--    @(a + 1) + 2 -> a + (1 + 2) -> a + 3@
--
-- 2. **Variable grouping**: Group same variables for strength reduction
--    @a + a -> 2 * a@
--
-- 3. **Canonical ordering**: Put constants on the right
--    @1 + a -> a + 1@
--
-- == Associative Operations
--
-- - Addition (+)
-- - Multiplication (*)
-- - Bitwise AND (&)
-- - Bitwise OR (|)
-- - Bitwise XOR (^)
-- - Logical AND (&&)
-- - Logical OR (||)
--
module LiveOak.Reassoc
  ( -- * Reassociation
    reassociate
  , reassociateMethod
  , ReassocResult(..)
  ) where

import LiveOak.SSATypes
import LiveOak.Ast (BinaryOp(..))

import Data.List (partition, sortBy)
import Data.Ord (comparing)

--------------------------------------------------------------------------------
-- Types
--------------------------------------------------------------------------------

-- | Reassociation result
data ReassocResult = ReassocResult
  { rrOptBlocks :: ![SSABlock]
  , rrReassociated :: !Int          -- ^ Number of expressions reassociated
  } deriving (Show)

--------------------------------------------------------------------------------
-- Reassociation
--------------------------------------------------------------------------------

-- | Reassociate expressions in blocks
reassociate :: [SSABlock] -> ReassocResult
reassociate blocks =
  let (optimized, counts) = unzip $ map reassocBlock blocks
  in ReassocResult
    { rrOptBlocks = optimized
    , rrReassociated = sum counts
    }

-- | Reassociate expressions in a method
reassociateMethod :: SSAMethod -> ReassocResult
reassociateMethod method =
  reassociate (ssaMethodBlocks method)

-- | Reassociate a block
reassocBlock :: SSABlock -> (SSABlock, Int)
reassocBlock block@SSABlock{..} =
  let (instrs', counts) = unzip $ map reassocInstr blockInstrs
  in (block { blockInstrs = instrs' }, sum counts)

-- | Reassociate an instruction
reassocInstr :: SSAInstr -> (SSAInstr, Int)
reassocInstr = \case
  SSAAssign var expr ->
    let (expr', count) = reassocExpr expr
    in (SSAAssign var expr', count)

  SSABranch cond thenB elseB ->
    let (cond', count) = reassocExpr cond
    in (SSABranch cond' thenB elseB, count)

  SSAReturn (Just expr) ->
    let (expr', count) = reassocExpr expr
    in (SSAReturn (Just expr'), count)

  SSAReturn Nothing -> (SSAReturn Nothing, 0)

  SSAFieldStore target field idx expr ->
    let (expr', count) = reassocExpr expr
    in (SSAFieldStore target field idx expr', count)

  instr -> (instr, 0)

-- | Reassociate an expression
reassocExpr :: SSAExpr -> (SSAExpr, Int)
reassocExpr expr = case expr of
  SSABinary op left right | isAssociative op ->
    let (left', c1) = reassocExpr left
        (right', c2) = reassocExpr right
        (result, c3) = reassocBinary op left' right'
    in (result, c1 + c2 + c3)

  SSABinary op left right ->
    let (left', c1) = reassocExpr left
        (right', c2) = reassocExpr right
    in (SSABinary op left' right', c1 + c2)

  SSAUnary op operand ->
    let (operand', c) = reassocExpr operand
    in (SSAUnary op operand', c)

  _ -> (expr, 0)

-- | Check if an operation is associative
isAssociative :: BinaryOp -> Bool
isAssociative = \case
  Add -> True
  Mul -> True
  And -> True
  Or  -> True
  _   -> False

-- | Check if an operation is commutative
isCommutative :: BinaryOp -> Bool
isCommutative = \case
  Add -> True
  Mul -> True
  And -> True
  Or  -> True
  Eq  -> True
  Ne  -> True
  _   -> False

-- | Reassociate a binary expression
reassocBinary :: BinaryOp -> SSAExpr -> SSAExpr -> (SSAExpr, Int)
reassocBinary op left right =
  -- Flatten the expression tree
  let operands = flatten op left ++ flatten op right
      -- Partition into constants and non-constants
      (consts, vars) = partition isConstant operands
      -- Sort variables for canonical ordering
      sortedVars = sortBy (comparing exprOrd) vars
  in case (consts, sortedVars) of
    -- All constants - fold them
    (cs@(_:_:_), []) ->
      let folded = foldConstants op cs
      in (folded, 1)

    -- Multiple constants with variables - fold constants first
    (cs@(_:_:_), v:vs) ->
      let folded = foldConstants op cs
          result = buildTree op (v : vs ++ [folded])
      in (result, 1)

    -- Single constant and variables - put constant on right
    ([c], v:vs) ->
      let result = buildTree op (v : vs ++ [c])
      in if isConstant right
         then (result, 0)  -- Already in canonical form
         else (result, 1)

    -- No constants - check for same variables
    ([], _) ->
      let (grouped, count) = groupSameVars op sortedVars
          result = buildTree op grouped
      in (result, count)

    -- Just rebuild
    _ -> (SSABinary op left right, 0)

-- | Flatten an expression tree for an associative operation
flatten :: BinaryOp -> SSAExpr -> [SSAExpr]
flatten op (SSABinary op' left right) | op == op' =
  flatten op left ++ flatten op right
flatten _ expr = [expr]

-- | Check if an expression is a constant
isConstant :: SSAExpr -> Bool
isConstant (SSAInt _) = True
isConstant (SSABool _) = True
isConstant _ = False

-- | Ordering for expressions (for canonical form)
exprOrd :: SSAExpr -> (Int, String, Int)
exprOrd (SSAUse var) = (0, show (ssaName var), ssaVersion var)
exprOrd SSAThis = (1, "this", 0)
exprOrd (SSAInt n) = (2, "", fromIntegral n)
exprOrd (SSABool b) = (3, "", if b then 1 else 0)
exprOrd _ = (4, "", 0)

-- | Fold constants together
foldConstants :: BinaryOp -> [SSAExpr] -> SSAExpr
foldConstants op consts = case op of
  Add -> SSAInt $ sum [n | SSAInt n <- consts]
  Mul -> SSAInt $ product [n | SSAInt n <- consts]
  And -> SSABool $ and [b | SSABool b <- consts]
  Or  -> SSABool $ or [b | SSABool b <- consts]
  _   -> head consts  -- Shouldn't happen

-- | Build a tree from a list of operands
buildTree :: BinaryOp -> [SSAExpr] -> SSAExpr
buildTree _ [e] = e
buildTree op (e:es) = SSABinary op e (buildTree op es)
buildTree _ [] = error "buildTree: empty list"

-- | Group same variables (e.g., a + a -> 2 * a)
groupSameVars :: BinaryOp -> [SSAExpr] -> ([SSAExpr], Int)
groupSameVars Add exprs = groupAddition exprs
groupSameVars _ exprs = (exprs, 0)

-- | Group same variables in addition (a + a -> 2 * a)
groupAddition :: [SSAExpr] -> ([SSAExpr], Int)
groupAddition [] = ([], 0)
groupAddition [e] = ([e], 0)
groupAddition (e:es) =
  let (same, different) = partition (sameExpr e) es
      count = length same + 1  -- +1 for e itself
      (rest, restCount) = groupAddition different
  in if count > 1
     then (SSABinary Mul (SSAInt (fromIntegral count)) e : rest, 1 + restCount)
     else (e : rest, restCount)
  where
    sameExpr (SSAUse v1) (SSAUse v2) =
      ssaName v1 == ssaName v2 && ssaVersion v1 == ssaVersion v2
    sameExpr SSAThis SSAThis = True
    sameExpr _ _ = False
