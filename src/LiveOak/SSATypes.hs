{-# LANGUAGE LambdaCase #-}

-- | SSA type definitions for LiveOak.
-- This module is separate to avoid circular dependencies with CFG.
module LiveOak.SSATypes
  ( -- * SSA Types
    SSAProgram(..)
  , SSAClass(..)
  , SSAMethod(..)
  , SSABlock(..)
  , SSAInstr(..)
  , SSAExpr(..)
  , PhiNode(..)
  , SSAVar(..)
  ) where

import LiveOak.Ast (UnaryOp, BinaryOp, ReturnSig)
import LiveOak.Types (ValueType)

--------------------------------------------------------------------------------
-- SSA Types
--------------------------------------------------------------------------------

-- | SSA variable with version number
data SSAVar = SSAVar
  { ssaName :: !String     -- ^ Original variable name
  , ssaVersion :: !Int     -- ^ Version number (0 = original)
  , ssaVarType :: !(Maybe ValueType)  -- ^ Type (if known, e.g., for parameters)
  } deriving (Eq, Ord, Show)

-- | Phi node: selects value based on predecessor block
data PhiNode = PhiNode
  { phiVar :: !SSAVar                    -- ^ Variable being defined
  , phiArgs :: ![(String, SSAVar)]       -- ^ (predecessor label, value)
  } deriving (Eq, Show)

-- | SSA expression
data SSAExpr
  = SSAInt !Int
  | SSABool !Bool
  | SSAStr !String
  | SSANull
  | SSAUse !SSAVar                      -- ^ Use of SSA variable
  | SSAThis
  | SSAUnary !UnaryOp !SSAExpr
  | SSABinary !BinaryOp !SSAExpr !SSAExpr
  | SSATernary !SSAExpr !SSAExpr !SSAExpr
  | SSACall !String ![SSAExpr]
  | SSAInstanceCall !SSAExpr !String ![SSAExpr]
  | SSANewObject !String ![SSAExpr]
  | SSAFieldAccess !SSAExpr !String
  deriving (Eq, Show)

-- | SSA instruction
data SSAInstr
  = SSAAssign !SSAVar !SSAExpr          -- ^ x_n = expr
  | SSAFieldStore !SSAExpr !String !Int !SSAExpr  -- ^ target.field = value
  | SSAReturn !(Maybe SSAExpr)
  | SSAJump !String                     -- ^ Unconditional jump
  | SSABranch !SSAExpr !String !String  -- ^ Conditional branch (cond, true, false)
  | SSAExprStmt !SSAExpr                -- ^ Expression for side effects
  deriving (Eq, Show)

-- | Basic block in SSA form
data SSABlock = SSABlock
  { blockLabel :: !String
  , blockPhis :: ![PhiNode]             -- ^ Phi functions at block start
  , blockInstrs :: ![SSAInstr]          -- ^ Instructions (non-phi)
  } deriving (Eq, Show)

-- | Method in SSA form
data SSAMethod = SSAMethod
  { ssaMethodClassName :: !String       -- ^ Containing class name
  , ssaMethodName :: !String
  , ssaMethodParams :: ![SSAVar]        -- ^ Parameters as SSA vars (version 0)
  , ssaMethodReturnSig :: !ReturnSig    -- ^ Return signature
  , ssaMethodBlocks :: ![SSABlock]      -- ^ Basic blocks
  , ssaEntryBlock :: !String            -- ^ Entry block label
  } deriving (Eq, Show)

-- | Class in SSA form
data SSAClass = SSAClass
  { ssaClassName :: !String
  , ssaClassFields :: ![(String, ValueType)]  -- ^ Field declarations
  , ssaClassMethods :: ![SSAMethod]
  } deriving (Eq, Show)

-- | Program in SSA form
data SSAProgram = SSAProgram
  { ssaClasses :: ![SSAClass]
  } deriving (Eq, Show)
