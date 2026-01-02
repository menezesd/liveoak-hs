{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RecordWildCards #-}

-- | Warning analysis for LiveOak.
-- Detects unused variables and other potential issues.
module LiveOak.Warnings
  ( -- * Warning Collection
    collectWarnings
  , collectMethodWarnings
  ) where

import Data.Set (Set)
import qualified Data.Set as Set

import LiveOak.Ast
import LiveOak.Symbol
import LiveOak.Diag (Warning(..))

-- | Collect all warnings for a program.
collectWarnings :: Program -> ProgramSymbols -> [Warning]
collectWarnings (Program classes) syms =
  concatMap (collectClassWarnings syms) classes

-- | Collect warnings for a class.
collectClassWarnings :: ProgramSymbols -> ClassDecl -> [Warning]
collectClassWarnings syms cls@ClassDecl{..} =
  concatMap (collectMethodWarnings syms cls) classMethods

-- | Collect warnings for a method.
collectMethodWarnings :: ProgramSymbols -> ClassDecl -> MethodDecl -> [Warning]
collectMethodWarnings syms cls MethodDecl{..} =
  unusedLocalWarnings ++ unusedParamWarnings
  where
    -- Get method symbol
    maybeMs = do
      cs <- lookupClass (className cls) syms
      lookupMethod methodName cs

    -- Collect all variable uses in the method body
    usedVars = collectUsedVars methodBody

    -- Check for unused local variables
    unusedLocalWarnings = case maybeMs of
      Nothing -> []
      Just ms ->
        [ UnusedVariable (vsName vs) (vsLine vs) (vsColumn vs)
        | vs <- msLocals ms
        , not (vsName vs `Set.member` usedVars)
        ]

    -- Check for unused parameters (excluding 'this')
    unusedParamWarnings = case maybeMs of
      Nothing -> []
      Just ms ->
        [ UnusedVariable (vsName vs) (vsLine vs) (vsColumn vs)
        | vs <- msParams ms
        , vsName vs /= "this"  -- 'this' is always implicitly used
        , not (vsName vs `Set.member` usedVars)
        ]

-- | Collect all variable names used in a statement.
collectUsedVars :: Stmt -> Set String
collectUsedVars = \case
  Block stmts _ ->
    Set.unions (map collectUsedVars stmts)

  VarDecl _ _ initOpt _ ->
    maybe Set.empty collectUsedVarsExpr initOpt

  Assign name value _ ->
    -- The variable being assigned to counts as a use for this analysis
    Set.insert name $ collectUsedVarsExpr value

  FieldAssign target _ _ value _ ->
    collectUsedVarsExpr target `Set.union` collectUsedVarsExpr value

  Return valueOpt _ ->
    maybe Set.empty collectUsedVarsExpr valueOpt

  If cond th el _ ->
    collectUsedVarsExpr cond `Set.union`
    collectUsedVars th `Set.union`
    collectUsedVars el

  While cond body _ ->
    collectUsedVarsExpr cond `Set.union` collectUsedVars body

  Break _ -> Set.empty

  ExprStmt expr _ ->
    collectUsedVarsExpr expr

-- | Collect all variable names used in an expression.
collectUsedVarsExpr :: Expr -> Set String
collectUsedVarsExpr = \case
  IntLit _ _   -> Set.empty
  BoolLit _ _  -> Set.empty
  StrLit _ _   -> Set.empty
  NullLit _    -> Set.empty
  This _       -> Set.singleton "this"

  Var name _ -> Set.singleton name

  Unary _ expr _ ->
    collectUsedVarsExpr expr

  Binary _ left right _ ->
    collectUsedVarsExpr left `Set.union` collectUsedVarsExpr right

  Ternary cond th el _ ->
    collectUsedVarsExpr cond `Set.union`
    collectUsedVarsExpr th `Set.union`
    collectUsedVarsExpr el

  Call _ args _ ->
    Set.unions (map collectUsedVarsExpr args)

  InstanceCall target _ args _ ->
    collectUsedVarsExpr target `Set.union`
    Set.unions (map collectUsedVarsExpr args)

  NewObject _ args _ ->
    Set.unions (map collectUsedVarsExpr args)

  FieldAccess target _ _ ->
    collectUsedVarsExpr target
