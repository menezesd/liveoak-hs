{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RecordWildCards #-}

-- | Type inference for SSA expressions.
-- Infers types by analyzing SSA structure and using symbol table information.
module LiveOak.SSATypeInfer
  ( -- * Type Inference
    inferSSAExprType
  , inferSSAExprTypeWithClass
  , inferSSAExprClass
  , inferSSAExprClassWithCtx
  , TypeEnv
  , buildTypeEnv
  , getVarType
  ) where

import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Maybe (fromMaybe)
import Data.List (foldl')

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

-- | Build a type environment from SSA blocks using a small fixed-point pass.
-- Seeds with parameter and annotated variable types, then iterates until no change.
buildTypeEnv :: [SSABlock] -> ProgramSymbols -> String -> [SSAVar] -> TypeEnv
buildTypeEnv blocks syms className params = go seedEnv
  where
    seedEnv =
      let paramEnv = Map.fromList [(varKey v, inferVarType v) | v <- params, varHasType v]
          phiEnv = Map.fromList
            [ (varKey (phiVar phi), inferVarType (phiVar phi))
            | block <- blocks
            , phi <- blockPhis block
            , varHasType (phiVar phi)
            ]
      in Map.union paramEnv phiEnv

    go env =
      let env' = foldl' (buildBlockEnv env) env blocks
      in if env' == env then env else go env'

    buildBlockEnv env acc SSABlock{..} =
      foldl' (buildInstrEnv env) acc blockInstrs

    buildInstrEnv env acc = \case
      SSAAssign var expr ->
        -- Use class context to properly resolve 'this' and field accesses
        let exprType = inferSSAExprTypeWithClass (Just className) syms env expr
        in case exprType of
             Just t -> Map.insert (varKey var) t acc
             Nothing -> if varHasType var
                        then Map.insert (varKey var) (inferVarType var) acc
                        else acc
      _ -> acc

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

-- | Infer the type of an SSA expression (with class context for 'this')
-- The optional String is the current class name for resolving 'this'
inferSSAExprType :: ProgramSymbols -> TypeEnv -> SSAExpr -> Maybe ValueType
inferSSAExprType = inferSSAExprTypeWithClass Nothing

-- | Infer the type of an SSA expression with an explicit class context
inferSSAExprTypeWithClass :: Maybe String -> ProgramSymbols -> TypeEnv -> SSAExpr -> Maybe ValueType
inferSSAExprTypeWithClass classCtx syms env = \case
  SSAInt _ -> Just (ofPrimitive TInt)
  SSABool _ -> Just (ofPrimitive TBool)
  SSAStr _ -> Just (ofPrimitive TString)
  SSANull -> Nothing  -- Null has no specific type until assigned
  SSAThis -> ofObject <$> classCtx  -- Use class context if available
  SSAUse var -> getVarType env var

  SSAUnary op e -> do
    t <- inferSSAExprTypeWithClass classCtx syms env e
    case op of
      Neg | t == ofPrimitive TInt    -> Just (ofPrimitive TInt)
          | t == ofPrimitive TString -> Just (ofPrimitive TString)
          | otherwise                -> Nothing
      Not | t == ofPrimitive TBool   -> Just (ofPrimitive TBool)
          | otherwise                -> Nothing

  SSABinary op l r -> do
    lt <- inferSSAExprTypeWithClass classCtx syms env l
    rt <- inferSSAExprTypeWithClass classCtx syms env r
    inferBinaryType op lt rt

  SSATernary cond t e -> do
    _ct <- inferSSAExprTypeWithClass classCtx syms env cond
    tt <- inferSSAExprTypeWithClass classCtx syms env t
    et <- inferSSAExprTypeWithClass classCtx syms env e
    if tt == et then Just tt else Nothing

  SSACall name _args ->
    -- Would need to resolve function return type from symbol table
    -- For now, assume int
    Just (ofPrimitive TInt)

  SSAInstanceCall target method _args -> do
    targetClass <- inferSSAExprClassWithCtx classCtx syms env target
    case lookupProgramMethod targetClass method syms of
      Just ms -> case msReturnType ms of
        Just retType -> Just retType
        Nothing -> Nothing
      Nothing -> Nothing

  SSANewObject className _args ->
    Just (ofObject className)

  SSAFieldAccess target field -> do
    targetClass <- inferSSAExprClassWithCtx classCtx syms env target
    case lookupClass targetClass syms of
      Just cs -> case lookupField field cs of
        Just vs -> Just (vsType vs)
        Nothing -> Nothing
      Nothing -> Nothing

-- | Infer the class name of an SSA expression (without class context)
inferSSAExprClass :: ProgramSymbols -> TypeEnv -> SSAExpr -> Maybe String
inferSSAExprClass = inferSSAExprClassWithCtx Nothing

-- | Infer the class name of an SSA expression (with class context)
inferSSAExprClassWithCtx :: Maybe String -> ProgramSymbols -> TypeEnv -> SSAExpr -> Maybe String
inferSSAExprClassWithCtx classCtx syms env expr = do
  vt <- inferSSAExprTypeWithClass classCtx syms env expr
  typeClassName vt

-- | Infer type of binary operation
inferBinaryType :: BinaryOp -> ValueType -> ValueType -> Maybe ValueType
inferBinaryType op lt rt =
  case op of
    -- Arithmetic: int op int -> int
    Add | lt == ofPrimitive TInt && rt == ofPrimitive TInt -> Just (ofPrimitive TInt)
    Add | lt == ofPrimitive TString && rt == ofPrimitive TString -> Just (ofPrimitive TString)
    Add | lt == ofPrimitive TString && rt == ofPrimitive TInt -> Just (ofPrimitive TString)
    Add | lt == ofPrimitive TInt && rt == ofPrimitive TString -> Just (ofPrimitive TString)
    Sub | lt == ofPrimitive TInt && rt == ofPrimitive TInt -> Just (ofPrimitive TInt)
    Mul | lt == ofPrimitive TInt && rt == ofPrimitive TInt -> Just (ofPrimitive TInt)
    Div | lt == ofPrimitive TInt && rt == ofPrimitive TInt -> Just (ofPrimitive TInt)
    Mod | lt == ofPrimitive TInt && rt == ofPrimitive TInt -> Just (ofPrimitive TInt)

    -- Comparison: int op int -> bool
    Lt | lt == ofPrimitive TInt && rt == ofPrimitive TInt -> Just (ofPrimitive TBool)
    Le | lt == ofPrimitive TInt && rt == ofPrimitive TInt -> Just (ofPrimitive TBool)
    Gt | lt == ofPrimitive TInt && rt == ofPrimitive TInt -> Just (ofPrimitive TBool)
    Ge | lt == ofPrimitive TInt && rt == ofPrimitive TInt -> Just (ofPrimitive TBool)
    -- String comparisons: string op string -> bool
    Lt | lt == ofPrimitive TString && rt == ofPrimitive TString -> Just (ofPrimitive TBool)
    Le | lt == ofPrimitive TString && rt == ofPrimitive TString -> Just (ofPrimitive TBool)
    Gt | lt == ofPrimitive TString && rt == ofPrimitive TString -> Just (ofPrimitive TBool)
    Ge | lt == ofPrimitive TString && rt == ofPrimitive TString -> Just (ofPrimitive TBool)

    -- Equality: any op any -> bool (if same type)
    Eq -> Just (ofPrimitive TBool)
    Ne -> Just (ofPrimitive TBool)

    -- Logical: bool op bool -> bool
    And | lt == ofPrimitive TBool && rt == ofPrimitive TBool -> Just (ofPrimitive TBool)
    Or | lt == ofPrimitive TBool && rt == ofPrimitive TBool -> Just (ofPrimitive TBool)

    _ -> Nothing
