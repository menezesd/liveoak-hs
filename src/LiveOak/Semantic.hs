{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RecordWildCards #-}

-- | Semantic analysis for LiveOak.
-- Performs type checking and validation on the AST.
module LiveOak.Semantic
  ( -- * Semantic Checking
    checkProgram
  , checkProgramCollectErrors
  , checkMethod
  , checkStmt
  , checkExpr

    -- * Type Inference
  , inferType
  , inferClassName
  ) where

import Control.Monad (when, unless, forM_, zipWithM_)

import LiveOak.Types
import LiveOak.Ast
import LiveOak.Symbol
import LiveOak.Diag

-- | Context for semantic checking.
data CheckCtx = CheckCtx
  { ctxMethod  :: MethodSymbol
  , ctxSymbols :: ProgramSymbols
  }

-- | Check an entire program (stops at first error).
checkProgram :: Program -> ProgramSymbols -> Result ()
checkProgram (Program classes) syms = do
  -- Check entry point exists
  case getEntrypoint syms of
    Nothing -> resolveErr "Missing Main.main entry point" 0 0
    Just ms -> do
      when (expectedUserArgs ms > 0) $
        syntaxErr "Main.main must not have parameters" 0 0
  -- Check all methods
  forM_ classes $ \cls ->
    forM_ (classMethods cls) $ \method ->
      checkMethod method syms

-- | Check an entire program, collecting all errors instead of stopping at first.
checkProgramCollectErrors :: Program -> ProgramSymbols -> [Diag]
checkProgramCollectErrors (Program classes) syms =
  entryPointErrors ++ methodErrors
  where
    -- Check entry point
    entryPointErrors = case getEntrypoint syms of
      Nothing -> [ResolveError "Missing Main.main entry point" 0 0]
      Just ms ->
        [SyntaxError "Main.main must not have parameters" 0 0 |
          expectedUserArgs ms > 0]

    -- Check all methods and collect errors
    methodErrors = concatMap checkClass classes

    checkClass cls = concatMap (checkMethodErrors syms) (classMethods cls)

-- | Check a method and return list of errors (empty if valid).
checkMethodErrors :: ProgramSymbols -> MethodDecl -> [Diag]
checkMethodErrors syms method@MethodDecl{..} =
  case checkMethod method syms of
    Left diag -> [diag]
    Right ()  -> []

-- | Check a single method.
checkMethod :: MethodDecl -> ProgramSymbols -> Result ()
checkMethod MethodDecl{..} syms = do
  -- Look up method symbol
  cs <- fromMaybe (ResolveError ("Unknown class: " ++ methodClassName) 0 0)
          (lookupClass methodClassName syms)
  ms <- fromMaybe (ResolveError ("Unknown method: " ++ methodName) 0 0)
          (lookupMethod methodName cs)
  let ctx = CheckCtx ms syms
  -- Check body
  checkStmt ctx methodBody
  -- Check return coverage for non-void methods
  when (methodReturnSig /= Void) $ do
    unless (returnsOnAllPaths methodBody) $
      syntaxErr "Non-void method must return on all paths" (stmtPos methodBody) 0

-- | Conservative check whether a statement guarantees a return on all paths.
returnsOnAllPaths :: Stmt -> Bool
returnsOnAllPaths = \case
  Return _ _    -> True
  Block stmts _ -> go stmts
    where
      go [] = False
      go (s:ss) = returnsOnAllPaths s || go ss
  If _ th el _  -> returnsOnAllPaths th && returnsOnAllPaths el
  _             -> False

-- | Check a statement.
checkStmt :: CheckCtx -> Stmt -> Result ()
checkStmt ctx@CheckCtx{..} = \case
  Block stmts _ ->
    mapM_ (checkStmt ctx) stmts

  VarDecl _name vtOpt initOpt pos -> do
    case initOpt of
      Nothing -> ok ()
      Just initExpr -> do
        checkExpr ctx initExpr
        case vtOpt of
          Nothing -> ok ()
          Just expectedVt -> checkAssignable ctx expectedVt initExpr pos

  Assign name value pos -> do
    checkExpr ctx value
    case lookupVarOrField ctx name of
      Just vs -> checkAssignable ctx (vsType vs) value pos
      Nothing -> resolveErr ("Undeclared variable: " ++ name) pos 0

  FieldAssign target field _ value pos -> do
    checkExpr ctx target
    checkExpr ctx value
    case target of
      NullLit _ -> syntaxErr ("Null dereference in field assignment: " ++ field) pos 0
      _ -> do
        targetCn <- inferClassName ctx target
        case targetCn of
          Nothing -> resolveErr ("Field " ++ field ++ " not found") pos 0
          Just cn -> case lookupClass cn ctxSymbols of
            Nothing -> resolveErr ("Unknown class: " ++ cn) pos 0
            Just cs -> case lookupField field cs of
              Nothing -> resolveErr ("Field " ++ field ++ " not found in class " ++ cn) pos 0
              Just fv -> checkAssignable ctx (vsType fv) value pos

  Return valueOpt pos -> do
    let retSig = getReturnSig ctxMethod
    case (valueOpt, retSig) of
      (Nothing, Void) -> ok ()
      (Nothing, _)    -> typeErr "Non-void method must return a value" pos 0
      (Just _, Void)  -> typeErr "Void method should not return a value" pos 0
      (Just expr, RetPrim t) -> do
        checkExpr ctx expr
        exprT <- inferType ctx expr
        unless (exprT == Just t) $
          typeErr "Return type mismatch" pos 0
      (Just expr, RetObj cn) -> do
        checkExpr ctx expr
        case expr of
          NullLit _ -> ok ()  -- null is valid for object return
          _ -> do
            exprCn <- inferClassName ctx expr
            unless (exprCn == Just cn) $
              typeErr "Return object type mismatch" pos 0

  If cond thenB elseB pos -> do
    checkExpr ctx cond
    condT <- inferType ctx cond
    unless (condT == Just TBool) $
      typeErr "If condition must be bool" pos 0
    checkStmt ctx thenB
    checkStmt ctx elseB

  While cond body pos -> do
    checkExpr ctx cond
    condT <- inferType ctx cond
    unless (condT == Just TBool) $
      typeErr "While condition must be bool" pos 0
    checkStmt ctx body

  Break _ -> ok ()

  ExprStmt expr _ -> checkExpr ctx expr

-- | Check assignability of an expression to a value type.
checkAssignable :: CheckCtx -> ValueType -> Expr -> Int -> Result ()
checkAssignable ctx expected expr pos = case expected of
  ObjectRefType _ -> case expr of
    NullLit _ -> ok ()  -- null is assignable to any object type
    _ -> do
      exprCn <- inferClassName ctx expr
      let expectedCn = typeClassName expected
      unless (exprCn == expectedCn) $
        typeErr "Object type mismatch in assignment" pos 0
  PrimitiveType t -> do
    exprT <- inferType ctx expr
    unless (exprT == Just t) $
      typeErr "Type mismatch in assignment" pos 0

-- | Check an expression.
checkExpr :: CheckCtx -> Expr -> Result ()
checkExpr ctx@CheckCtx{..} = \case
  IntLit _ _  -> ok ()
  BoolLit _ _ -> ok ()
  StrLit _ _  -> ok ()
  NullLit _   -> ok ()
  This _      -> ok ()

  Var name pos ->
    case lookupVarOrField ctx name of
      Just _  -> ok ()
      Nothing -> resolveErr ("Undeclared variable: " ++ name) pos 0

  Unary _ expr _ -> checkExpr ctx expr

  Binary _ left right _ -> do
    checkExpr ctx left
    checkExpr ctx right

  Ternary cond thenE elseE _pos -> do
    checkExpr ctx cond
    condT <- inferType ctx cond
    unless (condT == Just TBool) $
      typeErr "Ternary condition must be bool" (exprPos cond) 0
    checkExpr ctx thenE
    checkExpr ctx elseE

  Call name args pos -> do
    className <- currentThisClassName ctx pos
    _ <- checkMethodCall ctx className name args pos
    ok ()

  InstanceCall target method args pos -> do
    case target of
      This _ -> syntaxErr "Explicit this.method() is not allowed" pos 0
      NullLit _ -> syntaxErr "Null dereference in instance call" pos 0
      InstanceCall _ _ _ _ -> syntaxErr "Method chaining is not allowed" pos 0
      FieldAccess _ _ _ -> syntaxErr "Method chaining is not allowed" pos 0
      _ -> ok ()
    checkExpr ctx target
    targetCn <- inferClassName ctx target
    case targetCn of
      Nothing -> resolveErr "Cannot determine class for instance method call" pos 0
      Just cn -> do
        _ <- checkMethodCall ctx cn method args pos
        ok ()

  NewObject _ args _ -> mapM_ (checkExpr ctx) args

  FieldAccess target field pos -> do
    case target of
      NullLit _ -> syntaxErr ("Null dereference in field access: " ++ field) pos 0
      _ -> ok ()
    checkExpr ctx target
    targetCn <- inferClassName ctx target
    case targetCn of
      Nothing -> resolveErr ("Unknown field: " ++ field) pos 0
      Just cn -> case lookupClass cn ctxSymbols of
        Nothing -> resolveErr ("Unknown class: " ++ cn) pos 0
        Just cs -> case lookupField field cs of
          Nothing -> resolveErr ("Field " ++ field ++ " not found in class " ++ cn) pos 0
          Just _ -> ok ()

-- | Infer the primitive type of an expression (if primitive).
inferType :: CheckCtx -> Expr -> Result (Maybe Type)
inferType ctx@CheckCtx{..} = \case
  IntLit _ _  -> ok (Just TInt)
  BoolLit _ _ -> ok (Just TBool)
  StrLit _ _  -> ok (Just TString)
  NullLit _   -> ok Nothing  -- null has no primitive type

  Var name _ -> case lookupVarOrField ctx name of
    Just vs -> ok $ primitiveType (vsType vs)
    Nothing -> ok Nothing

  This _ -> ok Nothing  -- 'this' is an object

  Unary Neg expr _  -> do
    t <- inferType ctx expr
    ok $ case t of
      Just TString -> Just TString
      _            -> Just TInt
  Unary Not _ _  -> ok (Just TBool)

  Binary op left right _ -> case op of
    -- Add can be integer addition or string concatenation
    Add -> do
      leftT <- inferType ctx left
      rightT <- inferType ctx right
      ok $ if leftT == Just TString || rightT == Just TString
             then Just TString
             else Just TInt
    Sub -> ok (Just TInt)
    Mul -> do
      leftT <- inferType ctx left
      rightT <- inferType ctx right
      ok $ if leftT == Just TString || rightT == Just TString
             then Just TString
             else Just TInt
    Div -> ok (Just TInt)
    Mod -> ok (Just TInt)
    And -> ok (Just TBool)
    Or  -> ok (Just TBool)
    Eq  -> ok (Just TBool)
    Ne  -> ok (Just TBool)
    Lt  -> ok (Just TBool)
    Le  -> ok (Just TBool)
    Gt  -> ok (Just TBool)
    Ge  -> ok (Just TBool)
    Concat -> ok (Just TString)

  Ternary _ thenE elseE _ -> do
    thenT <- inferType ctx thenE
    elseT <- inferType ctx elseE
    ok $ if thenT == elseT then thenT else Nothing

  Call name _ pos -> do
    className <- currentThisClassName ctx pos
    case lookupProgramMethod className name ctxSymbols of
      Nothing -> ok Nothing
      Just ms -> ok $ primitiveType =<< msReturnType ms

  InstanceCall target method _ _ -> do
    targetCn <- inferClassName ctx target
    case targetCn of
      Nothing -> ok Nothing
      Just cn -> case lookupProgramMethod cn method ctxSymbols of
        Nothing -> ok Nothing
        Just ms -> ok $ primitiveType =<< msReturnType ms

  NewObject _ _ _ -> ok Nothing  -- object type

  FieldAccess target field _ -> do
    targetCn <- inferClassName ctx target
    case targetCn of
      Nothing -> ok Nothing
      Just cn -> case lookupClass cn ctxSymbols of
        Nothing -> ok Nothing
        Just cs -> case lookupField field cs of
          Nothing -> ok Nothing
          Just vs -> ok $ primitiveType (vsType vs)

-- | Infer the class name of an expression (if object type).
inferClassName :: CheckCtx -> Expr -> Result (Maybe String)
inferClassName ctx@CheckCtx{..} = \case
  NullLit _ -> ok Nothing

  This _ -> case lookupVar "this" ctxMethod of
    Just vs -> ok $ typeClassName (vsType vs)
    Nothing -> ok Nothing

  Var name _ -> case lookupVarOrField ctx name of
    Just vs -> ok $ typeClassName (vsType vs)
    Nothing -> ok Nothing

  NewObject cn _ _ -> ok (Just cn)

  Call name _ pos -> do
    className <- currentThisClassName ctx pos
    case lookupProgramMethod className name ctxSymbols of
      Nothing -> ok Nothing
      Just ms -> ok $ typeClassName =<< msReturnType ms

  InstanceCall target method _ _ -> do
    targetCn <- inferClassName ctx target
    case targetCn of
      Nothing -> ok Nothing
      Just cn -> case lookupProgramMethod cn method ctxSymbols of
        Nothing -> ok Nothing
        Just ms -> ok $ typeClassName =<< msReturnType ms

  FieldAccess target field _ -> do
    targetCn <- inferClassName ctx target
    case targetCn of
      Nothing -> ok Nothing
      Just cn -> case lookupClass cn ctxSymbols of
        Nothing -> ok Nothing
        Just cs -> case lookupField field cs of
          Nothing -> ok Nothing
          Just vs -> ok $ typeClassName (vsType vs)

  Ternary _ thenE elseE _ -> do
    thenCn <- inferClassName ctx thenE
    elseCn <- inferClassName ctx elseE
    ok $ case (thenCn, elseCn) of
      (Just cn1, Just cn2) | cn1 == cn2 -> Just cn1
      (Just cn, Nothing) -> Just cn
      (Nothing, Just cn) -> Just cn
      _ -> Nothing

  _ -> ok Nothing  -- primitives and operators don't have class names

-- | Get the class name of 'this' for the current method context.
currentThisClassName :: CheckCtx -> Int -> Result String
currentThisClassName CheckCtx{..} pos = case lookupVar "this" ctxMethod of
  Just vs -> case typeClassName (vsType vs) of
    Just cn -> ok cn
    Nothing -> resolveErr "Cannot resolve 'this' type" pos 0
  Nothing -> resolveErr "Cannot resolve 'this' type" pos 0

-- | Resolve a method call and validate argument compatibility.
checkMethodCall :: CheckCtx -> String -> String -> [Expr] -> Int -> Result MethodSymbol
checkMethodCall ctx@CheckCtx{..} className methodName args pos = do
  mapM_ (checkExpr ctx) args
  cs <- fromMaybe (ResolveError ("Unknown class: " ++ className) pos 0)
          (lookupClass className ctxSymbols)
  ms <- fromMaybe (ResolveError ("Unknown method: " ++ className ++ "." ++ methodName) pos 0)
          (lookupMethod methodName cs)
  let expected = expectedUserArgs ms
  when (length args /= expected) $
    syntaxErr (className ++ "." ++ methodName ++ " expects " ++ show expected ++ " arguments") pos 0
  let params = drop 1 (msParams ms)  -- drop implicit 'this'
  zipWithM_ (\p a -> checkAssignable ctx (vsType p) a pos) params args
  ok ms

--------------------------------------------------------------------------------
-- Lookup Helpers
--------------------------------------------------------------------------------

-- | Look up a variable or field by name.
-- First checks local variables/parameters, then fields of 'this'.
lookupVarOrField :: CheckCtx -> String -> Maybe VarSymbol
lookupVarOrField CheckCtx{..} name =
  case lookupVar name ctxMethod of
    Just vs -> Just vs
    Nothing -> lookupThisField ctxMethod ctxSymbols name

-- | Look up a field on 'this' object.
lookupThisField :: MethodSymbol -> ProgramSymbols -> String -> Maybe VarSymbol
lookupThisField method syms fieldName = do
  thisVs <- lookupVar "this" method
  cn <- typeClassName (vsType thisVs)
  cs <- lookupClass cn syms
  lookupField fieldName cs
