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
  , BlockId
  , blockId
  , blockIdName
  , SSAVar(..)
  , VarName
  , varName
  , varNameString
  , MethodName
  , methodNameFromString
  , methodNameString

    -- * Variable Key
  , VarKey
  , varKey
  , varFromKey
  ) where

import LiveOak.Ast (UnaryOp, BinaryOp, ReturnSig)
import LiveOak.Types (ValueType)

--------------------------------------------------------------------------------
-- SSA Types
--------------------------------------------------------------------------------

-- | Block identifier.
newtype BlockId = BlockId String deriving (Eq, Ord)

instance Show BlockId where
  show = blockIdName

blockId :: String -> BlockId
blockId = BlockId

blockIdName :: BlockId -> String
blockIdName (BlockId name) = name

-- | Variable name.
newtype VarName = VarName String deriving (Eq, Ord)

instance Show VarName where
  show = varNameString

varName :: String -> VarName
varName = VarName

varNameString :: VarName -> String
varNameString (VarName name) = name

-- | Method name.
newtype MethodName = MethodName String deriving (Eq, Ord)

instance Show MethodName where
  show = methodNameString

methodNameFromString :: String -> MethodName
methodNameFromString = MethodName

methodNameString :: MethodName -> String
methodNameString (MethodName name) = name

-- | SSA variable with version number
data SSAVar = SSAVar
  { ssaName :: !VarName    -- ^ Original variable name
  , ssaVersion :: !Int     -- ^ Version number (0 = original)
  , ssaVarType :: !(Maybe ValueType)  -- ^ Type (if known, e.g., for parameters)
  } deriving (Eq, Ord, Show)

-- | Phi node: selects value based on predecessor block
data PhiNode = PhiNode
  { phiVar :: !SSAVar                    -- ^ Variable being defined
  , phiArgs :: ![(BlockId, SSAVar)]      -- ^ (predecessor label, value)
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
  | SSAJump !BlockId                    -- ^ Unconditional jump
  | SSABranch !SSAExpr !BlockId !BlockId  -- ^ Conditional branch (cond, true, false)
  | SSAExprStmt !SSAExpr                -- ^ Expression for side effects
  deriving (Eq, Show)

-- | Basic block in SSA form
data SSABlock = SSABlock
  { blockLabel :: !BlockId
  , blockPhis :: ![PhiNode]             -- ^ Phi functions at block start
  , blockInstrs :: ![SSAInstr]          -- ^ Instructions (non-phi)
  } deriving (Eq, Show)

-- | Method in SSA form
data SSAMethod = SSAMethod
  { ssaMethodClassName :: !String       -- ^ Containing class name
  , ssaMethodName :: !MethodName
  , ssaMethodParams :: ![SSAVar]        -- ^ Parameters as SSA vars (version 0)
  , ssaMethodReturnSig :: !ReturnSig    -- ^ Return signature
  , ssaMethodBlocks :: ![SSABlock]      -- ^ Basic blocks
  , ssaEntryBlock :: !BlockId           -- ^ Entry block label
  } deriving (Eq, Show)

-- | Class in SSA form
data SSAClass = SSAClass
  { ssaClassName :: !String
  , ssaClassFields :: ![(String, ValueType)]  -- ^ Field declarations
  , ssaClassMethods :: ![SSAMethod]
  } deriving (Eq, Show)

-- | Program in SSA form
newtype SSAProgram = SSAProgram
  { ssaClasses :: [SSAClass]
  } deriving (Eq, Show)

--------------------------------------------------------------------------------
-- Variable Key
--------------------------------------------------------------------------------

-- | A key for identifying SSA variables (name, version)
type VarKey = (VarName, Int)

-- | Create a VarKey from an SSAVar
varKey :: SSAVar -> VarKey
varKey v = (ssaName v, ssaVersion v)

-- | Create an SSAVar from a VarKey (with no type info)
varFromKey :: VarKey -> SSAVar
varFromKey (name, version) = SSAVar name version Nothing
