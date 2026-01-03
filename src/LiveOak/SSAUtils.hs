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
  , exprVars
  ) where

import LiveOak.SSATypes

import Data.Set (Set)
import qualified Data.Set as Set

--------------------------------------------------------------------------------
-- Variable Uses
--------------------------------------------------------------------------------

-- | Get all variables used in an expression
exprUses :: SSAExpr -> Set String
exprUses = \case
  SSAUse var -> Set.singleton (ssaName var)
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
phiUses PhiNode{..} = Set.fromList [ssaName v | (_, v) <- phiArgs]

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
  SSAAssign var _ -> Set.singleton (ssaName var)
  _ -> Set.empty

-- | Get all variables defined in a block (phi nodes + instructions)
blockDefs :: SSABlock -> Set String
blockDefs SSABlock{..} = Set.fromList $
  [ssaName (phiVar phi) | phi <- blockPhis] ++
  [ssaName var | SSAAssign var _ <- blockInstrs]

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

-- | Get all variables mentioned in an expression (same as exprUses, alias for clarity)
exprVars :: SSAExpr -> Set String
exprVars = exprUses
