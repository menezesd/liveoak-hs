{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RecordWildCards #-}

-- | Type inference for SSA expressions.
-- Infers types by analyzing SSA structure and using symbol table information.
module LiveOak.SSATypeInfer
  ( -- * Type Inference
    inferSSAExprType
  , inferSSAExprClass
  , TypeEnv
  , buildTypeEnv
  , getVarType
  ) where

import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Maybe (fromMaybe)

import LiveOak.SSATypes
import LiveOak.Types (ValueType(..), Type(..), ofPrimitive, ofObject, typeClassName)
import LiveOak.Symbol (ProgramSymbols, lookupClass, lookupField, lookupProgramMethod, csFieldOrder, vsType, msReturnType)
import LiveOak.Ast (UnaryOp(..), BinaryOp(..))
import qualified LiveOak.Ast as Ast

--------------------------------------------------------------------------------
-- Type Environment
--------------------------------------------------------------------------------

-- | Type environment: tracks types of SSA variables
type TypeEnv = Map (String, Int) ValueType

-- | Build a type environment from SSA blocks
-- Takes the class name to handle 'this' references
buildTypeEnv :: [SSABlock] -> ProgramSymbols -> String -> TypeEnv
buildTypeEnv blocks syms className =
  Map.unions $ map (buildBlockTypeEnv syms className) blocks

-- | Build type environment for a single block
buildBlockTypeEnv :: ProgramSymbols -> String -> SSABlock -> TypeEnv
buildBlockTypeEnv syms className SSABlock{..} =
  let phiTypes = Map.fromList [(varKey (phiVar phi), inferVarType (phiVar phi)) | phi <- blockPhis, varHasType (phiVar phi)]
      instrTypes = Map.unions $ map (buildInstrTypeEnv syms className) blockInstrs
  in Map.union phiTypes instrTypes

-- | Build type environment from a single instruction
buildInstrTypeEnv :: ProgramSymbols -> String -> SSAInstr -> TypeEnv
buildInstrTypeEnv syms className = \case
  SSAAssign var expr ->
    let exprType = case expr of
          SSAThis -> Just (ofObject className)  -- 'this' has type of current class
          _ -> inferSSAExprType syms Map.empty expr
    in case exprType of
         Just t -> Map.singleton (varKey var) t
         Nothing -> if varHasType var
                    then Map.singleton (varKey var) (inferVarType var)
                    else Map.empty
  _ -> Map.empty

-- | Get variable key for type environment
varKey :: SSAVar -> (String, Int)
varKey v = (ssaName v, ssaVersion v)

-- | Check if variable has type annotation
varHasType :: SSAVar -> Bool
varHasType v = case ssaVarType v of
  Just _ -> True
  Nothing -> False

-- | Get type from variable (requires varHasType to be True)
inferVarType :: SSAVar -> ValueType
inferVarType v = fromMaybe (ofPrimitive TInt) (ssaVarType v)

-- | Look up variable type in environment
getVarType :: TypeEnv -> SSAVar -> Maybe ValueType
getVarType env var =
  case ssaVarType var of
    Just t -> Just t
    Nothing -> Map.lookup (varKey var) env

--------------------------------------------------------------------------------
-- Expression Type Inference
--------------------------------------------------------------------------------

-- | Infer the type of an SSA expression
inferSSAExprType :: ProgramSymbols -> TypeEnv -> SSAExpr -> Maybe ValueType
inferSSAExprType syms env = \case
  SSAInt _ -> Just (ofPrimitive TInt)
  SSABool _ -> Just (ofPrimitive TBool)
  SSAStr _ -> Just (ofPrimitive TString)
  SSANull -> Nothing  -- Null has no specific type until assigned
  SSAThis -> Nothing  -- Need class context
  SSAUse var -> getVarType env var

  SSAUnary op e -> do
    t <- inferSSAExprType syms env e
    case op of
      Neg -> if t == ofPrimitive TInt then Just (ofPrimitive TInt) else Nothing
      Not -> if t == ofPrimitive TBool then Just (ofPrimitive TBool) else Nothing

  SSABinary op l r -> do
    lt <- inferSSAExprType syms env l
    rt <- inferSSAExprType syms env r
    inferBinaryType op lt rt

  SSATernary cond _t e -> do
    -- Ternary returns type of branches (assume both have same type)
    _ct <- inferSSAExprType syms env cond
    inferSSAExprType syms env e

  SSACall name _args ->
    -- Would need to resolve function return type from symbol table
    -- For now, assume int
    Just (ofPrimitive TInt)

  SSAInstanceCall target method _args -> do
    targetClass <- inferSSAExprClass syms env target
    case lookupProgramMethod targetClass method syms of
      Just ms -> case msReturnType ms of
        Just retType -> Just retType
        Nothing -> Nothing
      Nothing -> Nothing

  SSANewObject className _args ->
    Just (ofObject className)

  SSAFieldAccess target field -> do
    targetClass <- inferSSAExprClass syms env target
    case lookupClass targetClass syms of
      Just cs -> case lookupField field cs of
        Just vs -> Just (vsType vs)
        Nothing -> Nothing
      Nothing -> Nothing

-- | Infer the class name of an SSA expression
inferSSAExprClass :: ProgramSymbols -> TypeEnv -> SSAExpr -> Maybe String
inferSSAExprClass syms env expr = do
  vt <- inferSSAExprType syms env expr
  typeClassName vt

-- | Infer type of binary operation
inferBinaryType :: BinaryOp -> ValueType -> ValueType -> Maybe ValueType
inferBinaryType op lt rt =
  case op of
    -- Arithmetic: int op int -> int
    Add | lt == ofPrimitive TInt && rt == ofPrimitive TInt -> Just (ofPrimitive TInt)
    Sub | lt == ofPrimitive TInt && rt == ofPrimitive TInt -> Just (ofPrimitive TInt)
    Mul | lt == ofPrimitive TInt && rt == ofPrimitive TInt -> Just (ofPrimitive TInt)
    Div | lt == ofPrimitive TInt && rt == ofPrimitive TInt -> Just (ofPrimitive TInt)
    Mod | lt == ofPrimitive TInt && rt == ofPrimitive TInt -> Just (ofPrimitive TInt)

    -- Comparison: int op int -> bool
    Lt | lt == ofPrimitive TInt && rt == ofPrimitive TInt -> Just (ofPrimitive TBool)
    Le | lt == ofPrimitive TInt && rt == ofPrimitive TInt -> Just (ofPrimitive TBool)
    Gt | lt == ofPrimitive TInt && rt == ofPrimitive TInt -> Just (ofPrimitive TBool)
    Ge | lt == ofPrimitive TInt && rt == ofPrimitive TInt -> Just (ofPrimitive TBool)

    -- Equality: any op any -> bool (if same type)
    Eq -> Just (ofPrimitive TBool)
    Ne -> Just (ofPrimitive TBool)

    -- Logical: bool op bool -> bool
    And | lt == ofPrimitive TBool && rt == ofPrimitive TBool -> Just (ofPrimitive TBool)
    Or | lt == ofPrimitive TBool && rt == ofPrimitive TBool -> Just (ofPrimitive TBool)

    _ -> Nothing
