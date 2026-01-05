{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RecordWildCards #-}

-- | Shared SSA Utilities.
-- Common helper functions for traversing and analyzing SSA constructs.
module LiveOak.SSAUtils
  ( -- * Variable Uses
    exprUses
  , instrUses
  , blockUses
  , phiUses

    -- * Variable Definitions
  , instrDefs
  , blockDefs

    -- * Expression Predicates
  , isPure
  , isSimple
  , isConstant
  , hasSideEffects

    -- * Expression Traversal
  , mapExpr
  , foldExpr
  , exprSize
  , containsVar
  , collectVarKeys

    -- * Expression Substitution
  , substVar
  , substVars

    -- * Instruction Utilities
  , mapInstrExprs
  , substVarsInInstr
  , instrExprs

    -- * Block Utilities
  , blockMapFromList
  , BlockMap

    -- * Fixed-Point Iteration
  , fixedPointWithLimit
  ) where

import LiveOak.SSATypes

import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Set (Set)
import qualified Data.Set as Set

--------------------------------------------------------------------------------
-- Block Utilities
--------------------------------------------------------------------------------

-- | Type alias for block maps
type BlockMap = Map BlockId SSABlock

-- | Build a block map from a list of blocks
-- This is a common pattern used across optimization modules.
blockMapFromList :: [SSABlock] -> BlockMap
blockMapFromList blocks = Map.fromList [(blockLabel b, b) | b <- blocks]

--------------------------------------------------------------------------------
-- Variable Uses
--------------------------------------------------------------------------------

-- | Get all variables used in an expression
exprUses :: SSAExpr -> Set String
exprUses = \case
  SSAUse var -> Set.singleton (varNameString (ssaName var))
  SSAUnary _ e -> exprUses e
  SSABinary _ l r -> exprUses l `Set.union` exprUses r
  SSATernary c t e -> exprUses c `Set.union` exprUses t `Set.union` exprUses e
  SSACall _ args -> Set.unions (map exprUses args)
  SSAInstanceCall target _ args ->
    exprUses target `Set.union` Set.unions (map exprUses args)
  SSANewObject _ args -> Set.unions (map exprUses args)
  SSAFieldAccess target _ -> exprUses target
  _ -> Set.empty

-- | Get all variables used in an instruction
instrUses :: SSAInstr -> Set String
instrUses = \case
  SSAAssign _ expr -> exprUses expr
  SSAReturn (Just expr) -> exprUses expr
  SSAReturn Nothing -> Set.empty
  SSAJump _ -> Set.empty
  SSABranch cond _ _ -> exprUses cond
  SSAFieldStore target _ _ value -> exprUses target `Set.union` exprUses value
  SSAExprStmt expr -> exprUses expr

-- | Get all variables used in a phi node
phiUses :: PhiNode -> Set String
phiUses PhiNode{..} = Set.fromList [varNameString (ssaName v) | (_, v) <- phiArgs]

-- | Get all variables used in a block (including phi nodes)
blockUses :: SSABlock -> Set String
blockUses SSABlock{..} = Set.unions $
  map phiUses blockPhis ++ map instrUses blockInstrs

--------------------------------------------------------------------------------
-- Variable Definitions
--------------------------------------------------------------------------------

-- | Get the variable defined by an instruction (if any)
instrDefs :: SSAInstr -> Set String
instrDefs = \case
  SSAAssign var _ -> Set.singleton (varNameString (ssaName var))
  _ -> Set.empty

-- | Get all variables defined in a block (phi nodes + instructions)
blockDefs :: SSABlock -> Set String
blockDefs SSABlock{..} = Set.fromList $
  [varNameString (ssaName (phiVar phi)) | phi <- blockPhis] ++
  [varNameString (ssaName var) | SSAAssign var _ <- blockInstrs]

--------------------------------------------------------------------------------
-- Expression Predicates
--------------------------------------------------------------------------------

-- | Check if an expression is pure (no side effects)
isPure :: SSAExpr -> Bool
isPure = \case
  SSAInt _ -> True
  SSABool _ -> True
  SSAStr _ -> True
  SSANull -> True
  SSAThis -> True
  SSAUse _ -> True
  SSAUnary _ e -> isPure e
  SSABinary _ l r -> isPure l && isPure r
  SSATernary c t e -> isPure c && isPure t && isPure e
  SSAFieldAccess _ _ -> True  -- Reading a field is pure
  SSACall _ _ -> False        -- Calls may have side effects
  SSAInstanceCall _ _ _ -> False
  SSANewObject _ _ -> False   -- Allocation is a side effect

-- | Check if an expression is simple (leaf or single operation)
isSimple :: SSAExpr -> Bool
isSimple = \case
  SSAInt _ -> True
  SSABool _ -> True
  SSAStr _ -> True
  SSANull -> True
  SSAThis -> True
  SSAUse _ -> True
  SSAUnary _ e -> isLeaf e
  SSABinary _ l r -> isLeaf l && isLeaf r
  _ -> False
  where
    isLeaf = \case
      SSAInt _ -> True
      SSABool _ -> True
      SSAStr _ -> True
      SSANull -> True
      SSAThis -> True
      SSAUse _ -> True
      _ -> False

--------------------------------------------------------------------------------
-- Fixed-Point Iteration
--------------------------------------------------------------------------------

-- | Apply a function repeatedly until a fixed point is reached or
-- the iteration limit is exceeded. Useful for optimization passes
-- that need to run until no more changes occur.
--
-- @
-- -- Run optimization up to 3 times or until stable:
-- optimized = fixedPointWithLimit 3 optimizePass input
-- @
fixedPointWithLimit :: Eq a => Int -> (a -> a) -> a -> a
fixedPointWithLimit 0 _ x = x  -- Max iterations reached
fixedPointWithLimit n f x =
  let x' = f x
  in if x' == x then x else fixedPointWithLimit (n - 1) f x'

--------------------------------------------------------------------------------
-- Expression Traversal
--------------------------------------------------------------------------------

-- | Map a function over all sub-expressions in an expression
mapExpr :: (SSAExpr -> SSAExpr) -> SSAExpr -> SSAExpr
mapExpr f = go
  where
    go expr = f $ case expr of
      SSAUnary op e -> SSAUnary op (go e)
      SSABinary op l r -> SSABinary op (go l) (go r)
      SSATernary c t e -> SSATernary (go c) (go t) (go e)
      SSACall n args -> SSACall n (map go args)
      SSAInstanceCall t m args -> SSAInstanceCall (go t) m (map go args)
      SSANewObject cn args -> SSANewObject cn (map go args)
      SSAFieldAccess t field -> SSAFieldAccess (go t) field
      e -> e  -- Leaves (literals, uses) unchanged

-- | Fold over all sub-expressions in an expression
foldExpr :: (a -> SSAExpr -> a) -> a -> SSAExpr -> a
foldExpr f acc expr = case expr of
  SSAUnary _ e -> f (foldExpr f acc e) expr
  SSABinary _ l r -> f (foldExpr f (foldExpr f acc l) r) expr
  SSATernary c t e -> f (foldExpr f (foldExpr f (foldExpr f acc c) t) e) expr
  SSACall _ args -> f (foldl (foldExpr f) acc args) expr
  SSAInstanceCall t _ args -> f (foldl (foldExpr f) (foldExpr f acc t) args) expr
  SSANewObject _ args -> f (foldl (foldExpr f) acc args) expr
  SSAFieldAccess t _ -> f (foldExpr f acc t) expr
  e -> f acc e

-- | Substitute a variable with an expression in an expression
substVar :: VarKey -> SSAExpr -> SSAExpr -> SSAExpr
substVar target replacement = mapExpr $ \case
  SSAUse v | (ssaName v, ssaVersion v) == target -> replacement
  e -> e

-- | Substitute multiple variables at once
substVars :: Map VarKey SSAExpr -> SSAExpr -> SSAExpr
substVars substs = mapExpr $ \case
  SSAUse v -> case Map.lookup (ssaName v, ssaVersion v) substs of
    Just repl -> repl
    Nothing -> SSAUse v
  e -> e

--------------------------------------------------------------------------------
-- Expression Properties
--------------------------------------------------------------------------------

-- | Check if expression is a constant (literal)
isConstant :: SSAExpr -> Bool
isConstant = \case
  SSAInt _ -> True
  SSABool _ -> True
  SSAStr _ -> True
  SSANull -> True
  _ -> False

-- | Check if expression has any side effects when executed
hasSideEffects :: SSAExpr -> Bool
hasSideEffects = not . isPure

-- | Get the size (number of nodes) of an expression tree
exprSize :: SSAExpr -> Int
exprSize = foldExpr (\acc _ -> acc + 1) 0

-- | Check if expression contains a specific variable
containsVar :: VarKey -> SSAExpr -> Bool
containsVar key = foldExpr check False
  where
    check found (SSAUse v) = found || (ssaName v, ssaVersion v) == key
    check found _ = found

-- | Collect all variables used in an expression (with versions)
collectVarKeys :: SSAExpr -> Set VarKey
collectVarKeys = foldExpr collect Set.empty
  where
    collect acc (SSAUse v) = Set.insert (ssaName v, ssaVersion v) acc
    collect acc _ = acc

--------------------------------------------------------------------------------
-- Instruction Utilities
--------------------------------------------------------------------------------

-- | Map a function over expressions in an instruction
mapInstrExprs :: (SSAExpr -> SSAExpr) -> SSAInstr -> SSAInstr
mapInstrExprs f = \case
  SSAAssign v e -> SSAAssign v (f e)
  SSAReturn (Just e) -> SSAReturn (Just (f e))
  SSABranch c t el -> SSABranch (f c) t el
  SSAFieldStore t fld off v -> SSAFieldStore (f t) fld off (f v)
  SSAExprStmt e -> SSAExprStmt (f e)
  i -> i  -- Other instructions unchanged

-- | Substitute variables in an instruction
substVarsInInstr :: Map VarKey SSAExpr -> SSAInstr -> SSAInstr
substVarsInInstr substs = mapInstrExprs (substVars substs)

-- | Get all expressions in an instruction
instrExprs :: SSAInstr -> [SSAExpr]
instrExprs = \case
  SSAAssign _ e -> [e]
  SSAReturn (Just e) -> [e]
  SSAReturn Nothing -> []
  SSAJump _ -> []
  SSABranch c _ _ -> [c]
  SSAFieldStore t _ _ v -> [t, v]
  SSAExprStmt e -> [e]
