{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE OverloadedStrings #-}

-- | Code generation for LiveOak.
-- Generates SAM (Stack Abstract Machine) assembly from the AST.
module LiveOak.Codegen
  ( -- * Code Generation
    generateCode
  , emitProgram

    -- * Code Generation Monad
  , Codegen
  , runCodegen

    -- * Labels
  , Label (..)
  , freshLabel
  , methodLabel
  ) where

import Control.Monad (forM_, when)
import Control.Monad.State.Strict
import Control.Monad.Reader
import Control.Monad.Except
import Data.Text (Text)
import qualified Data.Text as T
import Data.Text.Lazy.Builder (Builder)
import qualified Data.Text.Lazy.Builder as B
import qualified Data.Text.Lazy as TL

import LiveOak.Types
import LiveOak.Ast
import LiveOak.Symbol
import LiveOak.Diag (Diag, Result)
import qualified LiveOak.Diag as D
import LiveOak.StringRuntime

-- | A label in SAM assembly.
newtype Label = Label { labelName :: Text }
  deriving (Eq, Show)

-- | Code generation state.
data CodegenState = CodegenState
  { cgLabelCounter :: !Int        -- ^ Counter for generating unique labels
  , cgCode         :: !Builder    -- ^ Accumulated code
  }

-- | Code generation context (read-only).
data CodegenCtx = CodegenCtx
  { cgSymbols     :: !ProgramSymbols   -- ^ Program symbols
  , cgMethod      :: !(Maybe MethodSymbol)  -- ^ Current method (if any)
  , cgLoopLabels  :: ![Label]          -- ^ Stack of loop end labels for break
  , cgReturnLabel :: !(Maybe Label)    -- ^ Return epilogue label
  }

-- | Code generation monad.
type Codegen a = ReaderT CodegenCtx (StateT CodegenState (Either Diag)) a

-- | Run the code generation monad.
runCodegen :: ProgramSymbols -> Codegen a -> Result (a, Text)
runCodegen syms action = do
  let ctx = CodegenCtx
        { cgSymbols = syms
        , cgMethod = Nothing
        , cgLoopLabels = []
        , cgReturnLabel = Nothing
        }
      st = CodegenState
        { cgLabelCounter = 0
        , cgCode = mempty
        }
  (result, finalState) <- runStateT (runReaderT action ctx) st
  let code = TL.toStrict $ B.toLazyText $ cgCode finalState
  return (result, code)

-- | Generate code for a program.
generateCode :: Program -> ProgramSymbols -> Result Text
generateCode prog syms = do
  (_, code) <- runCodegen syms (emitProgram prog)
  return code

-- | Emit the entire program.
emitProgram :: Program -> Codegen ()
emitProgram (Program classes) = do
  -- Emit program preamble (allocate Main, call Main.main)
  emitPreamble
  -- Emit all methods
  forM_ classes $ \cls ->
    forM_ (classMethods cls) $ \method ->
      emitMethod cls method
  -- Emit string runtime
  emit emitStringRuntime

-- | Emit program preamble.
emitPreamble :: Codegen ()
emitPreamble = do
  syms <- asks cgSymbols
  let mainFields = case lookupClass "Main" syms of
        Just cs -> length (csFieldOrder cs)
        Nothing -> 0
  -- Allocate Main object
  emit $ "PUSHIMM " <> tshow mainFields <> "\n"
  emit "MALLOC\n"
  -- Prepare return slot and 'this'
  emit "PUSHIMM 0\n"  -- return slot
  emit "SWAP\n"       -- place 'this' below return slot
  -- Call Main.main
  let mainLabel = methodLabel "Main" "main"
  emit "LINK\n"
  emit $ "JSR " <> labelName mainLabel <> "\n"
  emit "UNLINK\n"
  emit "ADDSP -1\n"   -- pop arg
  emit "ADDSP -1\n"   -- pop return slot
  emit "STOP\n"

-- | Emit a method.
emitMethod :: ClassDecl -> MethodDecl -> Codegen ()
emitMethod cls MethodDecl{..} = do
  syms <- asks cgSymbols
  -- Look up method symbol
  ms <- case lookupProgramMethod (className cls) methodName syms of
    Just m  -> return m
    Nothing -> throwError $ D.ResolveError ("Unknown method: " ++ methodName) 0 0

  -- Emit method label
  let label = methodLabel (className cls) methodName
  emit "\n"
  emit $ labelName label <> ":\n"

  -- Method prologue
  let nLocals = numLocals ms
  emit "LINK\n"
  when (nLocals > 0) $
    emit $ "ADDSP " <> tshow nLocals <> "\n"

  -- Generate return label
  retLabel <- freshLabel "return"

  -- Emit body with updated context
  let ctx' c = c { cgMethod = Just ms, cgReturnLabel = Just retLabel }
  local ctx' $ emitStmt methodBody

  -- For void methods, ensure return value
  when (methodReturnSig == Void) $ do
    emit "PUSHIMM 0\n"

  -- Return epilogue
  emit $ labelName retLabel <> ":\n"
  when (nLocals > 0) $
    emit $ "ADDSP " <> tshow (-nLocals) <> "\n"
  emit "UNLINK\n"
  emit "RST\n"

-- | Emit a statement.
emitStmt :: Stmt -> Codegen ()
emitStmt = \case
  Block stmts _ ->
    forM_ stmts emitStmt

  VarDecl _ _ initOpt _ -> case initOpt of
    Nothing   -> emit "PUSHIMM 0\n"  -- default initialize to 0/null
    Just expr -> emitExpr expr

  Assign name value _ -> do
    loc <- resolveVar name
    case loc of
      LocalVar addr -> do
        emitExpr value
        emit $ "STOREOFF " <> tshow addr <> "\n"
      FieldVar off -> do
        -- Emit this.field = value
        thisAddr <- getVarAddress "this"
        emit $ "PUSHOFF " <> tshow thisAddr <> "\n"
        emit $ "PUSHIMM " <> tshow off <> "\n"
        emit "ADD\n"
        emitExpr value
        emit "STOREIND\n"

  FieldAssign target _field offset value _ -> do
    emitExpr target    -- push target address
    emit $ "PUSHIMM " <> tshow offset <> "\n"
    emit "ADD\n"       -- target + offset
    emitExpr value
    emit "STOREIND\n"

  Return valueOpt _ -> do
    case valueOpt of
      Nothing   -> emit "PUSHIMM 0\n"
      Just expr -> emitExpr expr
    retLabel <- asks cgReturnLabel
    case retLabel of
      Just lbl -> emit $ "JUMP " <> labelName lbl <> "\n"
      Nothing  -> throwError $ D.ResolveError "Return outside method" 0 0

  If cond thenBranch elseBranch _ -> do
    elseLabel <- freshLabel "else"
    endLabel <- freshLabel "endif"
    emitExpr cond
    emit "ISNIL\n"
    emit $ "JUMPC " <> labelName elseLabel <> "\n"
    emitStmt thenBranch
    emit $ "JUMP " <> labelName endLabel <> "\n"
    emit $ labelName elseLabel <> ":\n"
    emitStmt elseBranch
    emit $ labelName endLabel <> ":\n"

  While cond body _ -> do
    startLabel <- freshLabel "while"
    endLabel <- freshLabel "endwhile"
    emit $ labelName startLabel <> ":\n"
    emitExpr cond
    emit "ISNIL\n"
    emit $ "JUMPC " <> labelName endLabel <> "\n"
    -- Push end label for break
    local (\c -> c { cgLoopLabels = endLabel : cgLoopLabels c }) $
      emitStmt body
    emit $ "JUMP " <> labelName startLabel <> "\n"
    emit $ labelName endLabel <> ":\n"

  Break _ -> do
    loopLabels <- asks cgLoopLabels
    case loopLabels of
      []    -> throwError $ D.SyntaxError "break outside loop" 0 0
      (l:_) -> emit $ "JUMP " <> labelName l <> "\n"

  ExprStmt expr _ -> do
    emitExpr expr
    emit "ADDSP -1\n"  -- discard result

-- | Emit an expression.
emitExpr :: Expr -> Codegen ()
emitExpr = \case
  IntLit n _ ->
    emit $ "PUSHIMM " <> tshow n <> "\n"

  BoolLit b _ ->
    emit $ "PUSHIMM " <> (if b then "1" else "0") <> "\n"

  StrLit s _ ->
    emit $ "PUSHIMMSTR \"" <> T.pack (escapeString s) <> "\"\n"

  NullLit _ ->
    emit "PUSHIMM 0\n"

  Var name _ -> do
    loc <- resolveVar name
    case loc of
      LocalVar addr -> emit $ "PUSHOFF " <> tshow addr <> "\n"
      FieldVar off -> do
        -- Emit this.field access
        thisAddr <- getVarAddress "this"
        emit $ "PUSHOFF " <> tshow thisAddr <> "\n"
        emit $ "PUSHIMM " <> tshow off <> "\n"
        emit "ADD\n"
        emit "PUSHIND\n"

  This _ -> do
    addr <- getVarAddress "this"
    emit $ "PUSHOFF " <> tshow addr <> "\n"

  Unary op expr _ -> do
    emitExpr expr
    case op of
      Neg -> do
        emit "PUSHIMM 0\n"
        emit "SWAP\n"
        emit "SUB\n"
      Not -> do
        emit "ISNIL\n"  -- 0 becomes 1, non-0 becomes 0

  Binary op left right _ -> do
    -- Handle short-circuit for And/Or
    case op of
      And -> emitShortCircuitAnd left right
      Or  -> emitShortCircuitOr left right
      _   -> do
        emitExpr left
        emitExpr right
        emitBinaryOp op

  Ternary cond thenExpr elseExpr _ -> do
    falseLabel <- freshLabel "ternary_false"
    endLabel <- freshLabel "ternary_end"
    emitExpr cond
    emit "ISNIL\n"
    emit $ "JUMPC " <> labelName falseLabel <> "\n"
    emitExpr thenExpr
    emit $ "JUMP " <> labelName endLabel <> "\n"
    emit $ labelName falseLabel <> ":\n"
    emitExpr elseExpr
    emit $ labelName endLabel <> ":\n"

  Call method args _ -> do
    -- Push return slot
    emit "PUSHIMM 0\n"
    -- Push this (current method's this)
    addr <- getVarAddress "this"
    emit $ "PUSHOFF " <> tshow addr <> "\n"
    -- Push arguments
    forM_ args emitExpr
    -- Call
    let nArgs = length args + 1  -- +1 for 'this'
    emit "LINK\n"
    emit $ "JSR " <> T.pack method <> "\n"
    emit "UNLINK\n"
    emit $ "ADDSP " <> tshow (-nArgs) <> "\n"
    -- Result is now on TOS (return slot)

  InstanceCall target method args _ -> do
    -- Push return slot
    emit "PUSHIMM 0\n"
    -- Push target (becomes 'this' for callee)
    emitExpr target
    -- Push arguments
    forM_ args emitExpr
    -- Determine the class of target to find method label
    targetClass <- inferTargetClass target
    let fullMethod = case targetClass of
          Just cn -> methodLabel cn method
          Nothing -> Label (T.pack method)
    let nArgs = length args + 1
    emit "LINK\n"
    emit $ "JSR " <> labelName fullMethod <> "\n"
    emit "UNLINK\n"
    emit $ "ADDSP " <> tshow (-nArgs) <> "\n"

  NewObject clsName args _ -> do
    syms <- asks cgSymbols
    let nFields = case lookupClass clsName syms of
          Just cs -> length (csFieldOrder cs)
          Nothing -> 1
    -- Allocate object
    emit $ "PUSHIMM " <> tshow nFields <> "\n"
    emit "MALLOC\n"
    -- Check if constructor exists
    let hasConstructor = case lookupClass clsName syms of
          Just cs -> case lookupMethod clsName cs of
            Just _  -> True
            Nothing -> False
          Nothing -> False
    when hasConstructor $ do
      -- Call constructor
      emit "DUP\n"              -- save object reference
      emit "PUSHIMM 0\n"        -- return slot
      emit "SWAP\n"             -- [obj, 0, obj]
      forM_ args emitExpr
      let ctorLabel = methodLabel clsName clsName
      let nArgs = length args + 1
      emit "LINK\n"
      emit $ "JSR " <> labelName ctorLabel <> "\n"
      emit "UNLINK\n"
      emit $ "ADDSP " <> tshow (-nArgs) <> "\n"
      emit "ADDSP -1\n"         -- pop return slot

  FieldAccess target field _ -> do
    emitExpr target
    -- Look up field offset
    syms <- asks cgSymbols
    targetClass <- inferTargetClass target
    let offset = case targetClass of
          Just cn -> case lookupClass cn syms of
            Just cs -> case fieldOffset field cs of
              Just off -> off
              Nothing  -> 0
            Nothing -> 0
          Nothing -> 0
    emit $ "PUSHIMM " <> tshow offset <> "\n"
    emit "ADD\n"
    emit "PUSHIND\n"

-- | Emit short-circuit AND.
emitShortCircuitAnd :: Expr -> Expr -> Codegen ()
emitShortCircuitAnd left right = do
  falseLabel <- freshLabel "and_false"
  endLabel <- freshLabel "and_end"
  emitExpr left
  emit "ISNIL\n"
  emit $ "JUMPC " <> labelName falseLabel <> "\n"
  emitExpr right
  emit "ISNIL\n"
  emit $ "JUMPC " <> labelName falseLabel <> "\n"
  emit "PUSHIMM 1\n"
  emit $ "JUMP " <> labelName endLabel <> "\n"
  emit $ labelName falseLabel <> ":\n"
  emit "PUSHIMM 0\n"
  emit $ labelName endLabel <> ":\n"

-- | Emit short-circuit OR.
emitShortCircuitOr :: Expr -> Expr -> Codegen ()
emitShortCircuitOr left right = do
  trueLabel <- freshLabel "or_true"
  falseLabel <- freshLabel "or_false"
  endLabel <- freshLabel "or_end"
  emitExpr left
  emit "ISNIL\n"
  emit $ "JUMPC " <> labelName trueLabel <> "_check\n"
  emit "PUSHIMM 1\n"
  emit $ "JUMP " <> labelName endLabel <> "\n"
  emit $ labelName trueLabel <> "_check:\n"
  emitExpr right
  emit "ISNIL\n"
  emit $ "JUMPC " <> labelName falseLabel <> "\n"
  emit "PUSHIMM 1\n"
  emit $ "JUMP " <> labelName endLabel <> "\n"
  emit $ labelName falseLabel <> ":\n"
  emit "PUSHIMM 0\n"
  emit $ labelName endLabel <> ":\n"

-- | Emit a binary operator instruction.
emitBinaryOp :: BinaryOp -> Codegen ()
emitBinaryOp = \case
  Add -> emit "ADD\n"
  Sub -> emit "SUB\n"
  Mul -> emit "TIMES\n"
  Div -> emit "DIV\n"
  Mod -> emit "MOD\n"
  And -> emit "AND\n"
  Or  -> emit "OR\n"
  Eq  -> emit "EQUAL\n"
  Lt  -> emit "LESS\n"
  Gt  -> emit "GREATER\n"
  Ne  -> do
    emit "EQUAL\n"
    emit "ISNIL\n"
  Le  -> do
    emit "GREATER\n"
    emit "ISNIL\n"
  Ge  -> do
    emit "LESS\n"
    emit "ISNIL\n"
  Concat -> do
    emit "LINK\n"
    emit $ "JSR " <> strConcatLabel <> "\n"
    emit "UNLINK\n"
    emit "ADDSP -2\n"

-- | Variable location: either a local/param (stack offset) or a field.
data VarLocation
  = LocalVar Int    -- ^ Stack offset
  | FieldVar Int    -- ^ Field offset (requires 'this' access)
  deriving (Eq, Show)

-- | Resolve a variable name to its location.
resolveVar :: String -> Codegen VarLocation
resolveVar name = do
  maybeMethod <- asks cgMethod
  syms <- asks cgSymbols
  case maybeMethod of
    Nothing -> throwError $ D.ResolveError ("No method context for variable: " ++ name) 0 0
    Just ms -> case lookupVar name ms of
      Just vs -> return $ LocalVar $ stackAddress (numParams ms) vs
      Nothing -> do
        -- Check if it's a field of 'this'
        case lookupVar "this" ms of
          Just thisVs -> case typeClassName (vsType thisVs) of
            Just cn -> case lookupClass cn syms of
              Just cs -> case fieldOffset name cs of
                Just off -> return $ FieldVar off
                Nothing  -> throwError $ D.ResolveError ("Undeclared variable: " ++ name) 0 0
              Nothing -> throwError $ D.ResolveError ("Undeclared variable: " ++ name) 0 0
            Nothing -> throwError $ D.ResolveError ("Undeclared variable: " ++ name) 0 0
          Nothing -> throwError $ D.ResolveError ("Undeclared variable: " ++ name) 0 0

-- | Get the stack address of a variable (for locals/params only).
getVarAddress :: String -> Codegen Int
getVarAddress name = do
  loc <- resolveVar name
  case loc of
    LocalVar addr -> return addr
    FieldVar _    -> throwError $ D.ResolveError ("Expected local variable: " ++ name) 0 0

-- | Infer the class of an expression target.
inferTargetClass :: Expr -> Codegen (Maybe String)
inferTargetClass = \case
  This _ -> do
    maybeMethod <- asks cgMethod
    case maybeMethod of
      Just ms -> case lookupVar "this" ms of
        Just vs -> return $ typeClassName (vsType vs)
        Nothing -> return Nothing
      Nothing -> return Nothing

  Var name _ -> do
    maybeMethod <- asks cgMethod
    case maybeMethod of
      Just ms -> case lookupVar name ms of
        Just vs -> return $ typeClassName (vsType vs)
        Nothing -> return Nothing
      Nothing -> return Nothing

  NewObject cn _ _ -> return (Just cn)

  FieldAccess target field _ -> do
    targetCn <- inferTargetClass target
    syms <- asks cgSymbols
    case targetCn of
      Nothing -> return Nothing
      Just cn -> case lookupClass cn syms of
        Nothing -> return Nothing
        Just cs -> case lookupField field cs of
          Nothing -> return Nothing
          Just vs -> return $ typeClassName (vsType vs)

  InstanceCall target method _ _ -> do
    targetCn <- inferTargetClass target
    syms <- asks cgSymbols
    case targetCn of
      Nothing -> return Nothing
      Just cn -> case lookupProgramMethod cn method syms of
        Nothing -> return Nothing
        Just ms -> return $ typeClassName =<< msReturnType ms

  _ -> return Nothing

-- | Generate a fresh label.
freshLabel :: Text -> Codegen Label
freshLabel prefix = do
  n <- gets cgLabelCounter
  modify $ \s -> s { cgLabelCounter = n + 1 }
  return $ Label $ prefix <> "_" <> tshow n

-- | Generate a method label.
methodLabel :: String -> String -> Label
methodLabel className methodName =
  Label $ T.pack className <> "_" <> T.pack methodName

-- | Emit code to the output.
emit :: Text -> Codegen ()
emit t = modify $ \s -> s { cgCode = cgCode s <> B.fromText t }

-- | Show as Text.
tshow :: Show a => a -> Text
tshow = T.pack . show

-- | Escape a string for SAM.
escapeString :: String -> String
escapeString = concatMap escapeChar
  where
    escapeChar '\\' = "\\\\"
    escapeChar '"'  = "\\\""
    escapeChar '\n' = "\\n"
    escapeChar '\t' = "\\t"
    escapeChar '\r' = "\\r"
    escapeChar c    = [c]
