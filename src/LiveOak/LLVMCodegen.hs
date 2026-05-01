{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE OverloadedStrings #-}

-- | LLVM IR code generation from SSA form.
-- Emits textual LLVM IR (.ll) that can be compiled with clang or llc.
--
-- Design: uses alloca + load/store for all variables (clang -O0 style).
-- LLVM's mem2reg pass promotes these to SSA registers automatically.
-- This avoids the need for register allocation, liveness analysis,
-- or explicit LLVM phi instructions for CFG-level merges.
module LiveOak.LLVMCodegen
  ( generateLLVMFromSSA
  ) where

import Control.Monad (forM, forM_, when)
import Control.Monad.State.Strict
import Control.Monad.Reader
import Control.Monad.Except
import Data.Text (Text)
import qualified Data.Text as T
import Data.Text.Lazy.Builder (Builder)
import qualified Data.Text.Lazy.Builder as B
import qualified Data.Text.Lazy as TL
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Data.List (foldl', sort)
import Data.Char (isDigit)
import Data.Maybe (fromMaybe, isJust)

import LiveOak.Ast (UnaryOp(..), BinaryOp(..))
import LiveOak.SSATypes
import LiveOak.CFG
import LiveOak.MapUtils (lookupList)
import LiveOak.Symbol (ProgramSymbols(..), MethodSymbol, lookupClass,
                       csFieldOrder, lookupMethod, fieldOffset, numParams,
                       numLocals, msParams, msLocals, vsName)
import LiveOak.Diag (Diag, Result)
import qualified LiveOak.Diag as D
import LiveOak.SSATypeInfer (TypeEnv, buildTypeEnv, inferSSAExprClassWithCtx, inferSSAExprTypeWithClass)
import LiveOak.Types (ValueType(..), Type(..))

--------------------------------------------------------------------------------
-- Code Generation Types
--------------------------------------------------------------------------------

data LLVMCodegenState = LLVMCodegenState
  { lcgTempCounter  :: !Int
  , lcgLabelCounter :: !Int
  , lcgCode         :: !Builder
  , lcgStrings      :: ![(Text, Text)]       -- ^ (label, content) for .rodata
  , lcgCurrentBlock :: !Text                -- ^ Current LLVM block label (for phi)
  }

data LLVMCodegenCtx = LLVMCodegenCtx
  { lcgSymbols    :: !ProgramSymbols
  , lcgClassName  :: !String
  , lcgMethodName :: !String
  , lcgMethodSym  :: !MethodSymbol
  , lcgCFG        :: !CFG
  , lcgPhiCopies  :: !(Map BlockId [(BlockId, String, String)])
  , lcgTypeEnv    :: !TypeEnv
  }

type LLVMCodegen a = ReaderT LLVMCodegenCtx (StateT LLVMCodegenState (Either Diag)) a

--------------------------------------------------------------------------------
-- Entry Point
--------------------------------------------------------------------------------

-- | Generate LLVM IR from an SSA program
generateLLVMFromSSA :: SSAProgram -> ProgramSymbols -> Result Text
generateLLVMFromSSA (SSAProgram classes) syms = do
  -- Generate method definitions
  methodCodes <- forM classes $ \cls ->
    forM (ssaClassMethods cls) $ \method ->
      generateMethodLLVM syms (ssaClassName cls) method

  let methods = T.intercalate "\n" (concat methodCodes)

  return $ T.intercalate "\n"
    [ emitModuleHeader
    , emitExternalDecls
    , emitStringConstants (collectAllStrings classes)
    , emitRuntime
    , methods
    , emitEntryPoint syms
    ]

-- | Collect all string literals from the program (for global constants)
collectAllStrings :: [SSAClass] -> [(Text, String)]
collectAllStrings classes =
  let strs = concatMap classStrings classes
      numbered = zip [0..] strs
  in [(".str." <> tshow i, s) | (i, s) <- numbered]
  where
    classStrings cls = concatMap methodStrings (ssaClassMethods cls)
    methodStrings m = concatMap blockStrings (ssaMethodBlocks m)
    blockStrings SSABlock{..} = concatMap instrStrings blockInstrs
    instrStrings = \case
      SSAAssign _ expr -> exprStrings expr
      SSAFieldStore _ _ _ expr -> exprStrings expr
      SSAReturn (Just expr) -> exprStrings expr
      SSAExprStmt expr -> exprStrings expr
      _ -> []
    exprStrings = \case
      SSAStr s -> [s]
      SSAUnary _ e -> exprStrings e
      SSABinary _ l r -> exprStrings l ++ exprStrings r
      SSATernary c t e -> exprStrings c ++ exprStrings t ++ exprStrings e
      SSACall _ args -> concatMap exprStrings args
      SSAInstanceCall obj _ args -> exprStrings obj ++ concatMap exprStrings args
      SSANewObject _ args -> concatMap exprStrings args
      SSAFieldAccess obj _ -> exprStrings obj
      _ -> []

--------------------------------------------------------------------------------
-- Module Structure
--------------------------------------------------------------------------------

emitModuleHeader :: Text
emitModuleHeader = T.unlines
  [ "; LiveOak LLVM IR output"
  , ""
  ]

emitExternalDecls :: Text
emitExternalDecls = T.unlines
  [ "; External declarations"
  , "declare ptr @malloc(i64)"
  , "declare ptr @memset(ptr, i32, i64)"
  , "declare ptr @strcpy(ptr, ptr)"
  , "declare ptr @strcat(ptr, ptr)"
  , "declare i64 @strlen(ptr)"
  , "declare i32 @strcmp(ptr, ptr)"
  , "declare i32 @printf(ptr, ...)"
  , "declare void @exit(i32) noreturn"
  , ""
  ]

emitStringConstants :: [(Text, String)] -> Text
emitStringConstants [] = ""
emitStringConstants strs = T.unlines $
  ["; String constants"] ++
  [ "@" <> label <> " = private unnamed_addr constant ["
    <> tshow (length s + 1) <> " x i8] c\"" <> escapeStrLLVM (T.pack s) <> "\\00\""
  | (label, s) <- strs
  ] ++ [""]

emitEntryPoint :: ProgramSymbols -> Text
emitEntryPoint syms =
  let mainFields = case lookupClass "Main" syms of
        Just cs -> length (csFieldOrder cs)
        Nothing -> 0
      size = max 8 (mainFields * 8)
  in T.unlines
    [ ""
    , "; Program entry point"
    , "define i32 @main() {"
    , "  %obj = call ptr @malloc(i64 " <> tshow size <> ")"
    , "  call ptr @memset(ptr %obj, i32 0, i64 " <> tshow size <> ")"
    , "  %this = ptrtoint ptr %obj to i64"
    , "  %result = call i64 @Main_main(i64 %this)"
    , "  %exit_code = trunc i64 %result to i32"
    , "  ret i32 %exit_code"
    , "}"
    ]

--------------------------------------------------------------------------------
-- Runtime Functions (defined in LLVM IR)
--------------------------------------------------------------------------------

emitRuntime :: Text
emitRuntime = T.unlines
  [ "; Runtime support"
  , "@.fmt.int = private unnamed_addr constant [4 x i8] c\"%ld\\00\""
  , "@.fmt.str = private unnamed_addr constant [3 x i8] c\"%s\\00\""
  , "@.fmt.nl  = private unnamed_addr constant [2 x i8] c\"\\0A\\00\""
  , "@.str.true  = private unnamed_addr constant [5 x i8] c\"true\\00\""
  , "@.str.false = private unnamed_addr constant [6 x i8] c\"false\\00\""
  , ""
  , runtimeStrConcat
  , runtimeStrRepeat
  , runtimeStrReverse
  , runtimeStrCompare
  , runtimeStrLength
  , runtimePrintInt
  , runtimePrintString
  , runtimePrintBool
  , runtimePrintNewline
  ]

runtimeStrConcat :: Text
runtimeStrConcat = T.unlines
  [ "define i64 @__str_concat(i64 %s1.int, i64 %s2.int) {"
  , "  %s1 = inttoptr i64 %s1.int to ptr"
  , "  %s2 = inttoptr i64 %s2.int to ptr"
  , "  %len1 = call i64 @strlen(ptr %s1)"
  , "  %len2 = call i64 @strlen(ptr %s2)"
  , "  %total = add i64 %len1, %len2"
  , "  %total1 = add i64 %total, 1"
  , "  %buf = call ptr @malloc(i64 %total1)"
  , "  call ptr @strcpy(ptr %buf, ptr %s1)"
  , "  call ptr @strcat(ptr %buf, ptr %s2)"
  , "  %result = ptrtoint ptr %buf to i64"
  , "  ret i64 %result"
  , "}"
  ]

runtimeStrRepeat :: Text
runtimeStrRepeat = T.unlines
  [ "define i64 @__str_repeat(i64 %s.int, i64 %n) {"
  , "entry:"
  , "  %s = inttoptr i64 %s.int to ptr"
  , "  %cmp = icmp sle i64 %n, 0"
  , "  br i1 %cmp, label %empty, label %positive"
  , "empty:"
  , "  %ebuf = call ptr @malloc(i64 1)"
  , "  store i8 0, ptr %ebuf"
  , "  %eres = ptrtoint ptr %ebuf to i64"
  , "  ret i64 %eres"
  , "positive:"
  , "  %len = call i64 @strlen(ptr %s)"
  , "  %total = mul i64 %len, %n"
  , "  %total1 = add i64 %total, 1"
  , "  %buf = call ptr @malloc(i64 %total1)"
  , "  store i8 0, ptr %buf"
  , "  br label %loop"
  , "loop:"
  , "  %i = phi i64 [0, %positive], [%i.next, %loop]"
  , "  call ptr @strcat(ptr %buf, ptr %s)"
  , "  %i.next = add i64 %i, 1"
  , "  %done = icmp sge i64 %i.next, %n"
  , "  br i1 %done, label %exit, label %loop"
  , "exit:"
  , "  %result = ptrtoint ptr %buf to i64"
  , "  ret i64 %result"
  , "}"
  ]

runtimeStrReverse :: Text
runtimeStrReverse = T.unlines
  [ "define i64 @__str_reverse(i64 %s.int) {"
  , "entry:"
  , "  %s = inttoptr i64 %s.int to ptr"
  , "  %len = call i64 @strlen(ptr %s)"
  , "  %buf.sz = add i64 %len, 1"
  , "  %buf = call ptr @malloc(i64 %buf.sz)"
  , "  %null.ptr = getelementptr i8, ptr %buf, i64 %len"
  , "  store i8 0, ptr %null.ptr"
  , "  br label %loop"
  , "loop:"
  , "  %j = phi i64 [0, %entry], [%j.next, %loop]"
  , "  %i = sub i64 %len, 1"
  , "  %ri = sub i64 %i, %j"
  , "  %src = getelementptr i8, ptr %s, i64 %ri"
  , "  %ch = load i8, ptr %src"
  , "  %dst = getelementptr i8, ptr %buf, i64 %j"
  , "  store i8 %ch, ptr %dst"
  , "  %j.next = add i64 %j, 1"
  , "  %done = icmp sge i64 %j.next, %len"
  , "  br i1 %done, label %exit, label %loop"
  , "exit:"
  , "  %result = ptrtoint ptr %buf to i64"
  , "  ret i64 %result"
  , "}"
  ]

runtimeStrCompare :: Text
runtimeStrCompare = T.unlines
  [ "define i64 @__str_compare(i64 %s1.int, i64 %s2.int) {"
  , "  %s1 = inttoptr i64 %s1.int to ptr"
  , "  %s2 = inttoptr i64 %s2.int to ptr"
  , "  %r32 = call i32 @strcmp(ptr %s1, ptr %s2)"
  , "  %result = sext i32 %r32 to i64"
  , "  ret i64 %result"
  , "}"
  ]

runtimeStrLength :: Text
runtimeStrLength = T.unlines
  [ "define i64 @__str_length(i64 %s.int) {"
  , "  %s = inttoptr i64 %s.int to ptr"
  , "  %result = call i64 @strlen(ptr %s)"
  , "  ret i64 %result"
  , "}"
  ]

runtimePrintInt :: Text
runtimePrintInt = T.unlines
  [ "define void @__print_int(i64 %n) {"
  , "  call i32 (ptr, ...) @printf(ptr @.fmt.int, i64 %n)"
  , "  ret void"
  , "}"
  ]

runtimePrintString :: Text
runtimePrintString = T.unlines
  [ "define void @__print_string(i64 %s.int) {"
  , "  %s = inttoptr i64 %s.int to ptr"
  , "  call i32 (ptr, ...) @printf(ptr @.fmt.str, ptr %s)"
  , "  ret void"
  , "}"
  ]

runtimePrintBool :: Text
runtimePrintBool = T.unlines
  [ "define void @__print_bool(i64 %b) {"
  , "entry:"
  , "  %cmp = icmp ne i64 %b, 0"
  , "  br i1 %cmp, label %t, label %f"
  , "t:"
  , "  call i32 (ptr, ...) @printf(ptr @.fmt.str, ptr @.str.true)"
  , "  ret void"
  , "f:"
  , "  call i32 (ptr, ...) @printf(ptr @.fmt.str, ptr @.str.false)"
  , "  ret void"
  , "}"
  ]

runtimePrintNewline :: Text
runtimePrintNewline = T.unlines
  [ "define void @__print_newline() {"
  , "  call i32 (ptr, ...) @printf(ptr @.fmt.nl)"
  , "  ret void"
  , "}"
  ]

--------------------------------------------------------------------------------
-- Method Code Generation
--------------------------------------------------------------------------------

generateMethodLLVM :: ProgramSymbols -> String -> SSAMethod -> Result Text
generateMethodLLVM syms clsName method@SSAMethod{..} = do
  let cfg = buildCFG method
      methodNameStr = methodNameString ssaMethodName

  methodSymbol <- case lookupClass clsName syms >>= lookupMethod methodNameStr of
    Just ms -> return ms
    Nothing -> D.resolveErr ("Unknown method symbol for " ++ clsName ++ "." ++ methodNameStr) 0 0

  let phiCopies = computePhiCopies cfg ssaMethodBlocks
      typeEnv = buildTypeEnv ssaMethodBlocks syms ssaMethodClassName ssaMethodParams

      ctx = LLVMCodegenCtx
        { lcgSymbols = syms
        , lcgClassName = clsName
        , lcgMethodName = methodNameStr
        , lcgMethodSym = methodSymbol
        , lcgCFG = cfg
        , lcgPhiCopies = phiCopies
        , lcgTypeEnv = typeEnv
        }

      initState = LLVMCodegenState
        { lcgTempCounter = 0
        , lcgLabelCounter = 0
        , lcgCode = mempty
        , lcgStrings = []
        , lcgCurrentBlock = "prologue"
        }

  (_, finalState) <- runStateT (runReaderT (emitMethodLLVM method) ctx) initState
  let code = TL.toStrict $ B.toLazyText $ lcgCode finalState
      -- Emit method-local string constants before the method
      strConsts = if null (lcgStrings finalState)
                  then ""
                  else T.unlines
                    [ "@" <> lbl <> " = private unnamed_addr constant ["
                      <> tshow (T.length s + 1) <> " x i8] c\""
                      <> escapeStrLLVM s <> "\\00\""
                    | (lbl, s) <- reverse (lcgStrings finalState)
                    ]
  return $ strConsts <> code

emitMethodLLVM :: SSAMethod -> LLVMCodegen ()
emitMethodLLVM SSAMethod{..} = do
  clsName <- asks lcgClassName
  methodSym <- asks lcgMethodSym
  let label = T.pack clsName <> "_" <> T.pack (methodNameString ssaMethodName)
      params = msParams methodSym

  -- Function signature: all params are i64
  let paramList = T.intercalate ", "
        [ "i64 %" <> T.pack (vsName p) <> ".param"
        | p <- params
        ]
  emit $ "\ndefine i64 @" <> label <> "(" <> paramList <> ") {\n"
  emit "prologue:\n"

  -- Allocas for all variables
  let allVarBases = collectAllVars ssaMethodBlocks
      paramNames = Set.fromList $ map vsName params
      localNames = Set.fromList $ map vsName (msLocals methodSym)
      allBases = Set.unions [paramNames, localNames, allVarBases]
  forM_ (Set.toList allBases) $ \name ->
    emit $ "  %" <> T.pack name <> ".addr = alloca i64\n"

  -- Store parameters to allocas
  forM_ params $ \p -> do
    let name = vsName p
    emit $ "  store i64 %" <> T.pack name <> ".param, ptr %" <> T.pack name <> ".addr\n"

  -- Branch to entry CFG block
  let entryName = T.pack $ blockIdName ssaEntryBlock
  emit $ "  br label %" <> entryName <> "\n"

  -- Emit blocks in reverse postorder
  cfg <- asks lcgCFG
  let blockOrder = reversePostorder cfg
  forM_ blockOrder $ \bid ->
    forM_ (getBlock cfg bid) emitBlock

  emit "}\n"

collectAllVars :: [SSABlock] -> Set.Set String
collectAllVars blocks = Set.unions $ map blockVars blocks
  where
    blockVars SSABlock{..} =
      Set.unions $ map phiVars blockPhis ++ map instrVars blockInstrs
    phiVars PhiNode{..} = Set.singleton (ssaVarBase phiVar)
    instrVars (SSAAssign var _) = Set.singleton (ssaVarBase var)
    instrVars _ = Set.empty

ssaVarBase :: SSAVar -> String
ssaVarBase v = varNameString (ssaName v)

ssaVarStr :: SSAVar -> String
ssaVarStr v = varNameString (ssaName v) ++ "_" ++ show (ssaVersion v)

--------------------------------------------------------------------------------
-- Block Code Generation
--------------------------------------------------------------------------------

emitBlock :: CFGBlock -> LLVMCodegen ()
emitBlock CFGBlock{..} = do
  let label = T.pack (blockIdName cfgBlockId)
  emit $ label <> ":\n"
  modify $ \s -> s { lcgCurrentBlock = label }

  -- Phi copies are handled at predecessor exits, NOT here.
  -- (In alloca approach, phis are implicit via stores.)

  forM_ cfgInstrs emitInstr
  emitTerminator cfgBlockId cfgTerm

emitInstr :: SSAInstr -> LLVMCodegen ()
emitInstr = \case
  SSAAssign var expr -> do
    val <- emitExpr expr
    let baseName = ssaVarBase var
    emit $ "  store i64 " <> val <> ", ptr %" <> T.pack baseName <> ".addr\n"

  SSAFieldStore target _field off value -> do
    objVal <- emitExpr target
    valVal <- emitExpr value
    objPtr <- freshTemp
    emit $ "  " <> objPtr <> " = inttoptr i64 " <> objVal <> " to ptr\n"
    fldPtr <- freshTemp
    emit $ "  " <> fldPtr <> " = getelementptr i8, ptr " <> objPtr <> ", i64 " <> tshow (off * 8) <> "\n"
    emit $ "  store i64 " <> valVal <> ", ptr " <> fldPtr <> "\n"

  SSAReturn exprOpt -> do
    case exprOpt of
      Just expr -> do
        val <- emitExpr expr
        emit $ "  ret i64 " <> val <> "\n"
      Nothing ->
        emit "  ret i64 0\n"

  SSAJump _ -> return ()
  SSABranch _ _ _ -> return ()

  SSAExprStmt expr -> do
    _ <- emitExpr expr
    return ()

emitTerminator :: BlockId -> Terminator -> LLVMCodegen ()
emitTerminator currentBlock term = do
  phiCopies <- asks lcgPhiCopies
  let copies = lookupList currentBlock phiCopies

  case term of
    TermJump target -> do
      let targetCopies = [(d, s) | (t, d, s) <- copies, t == target]
      emitPhiCopies targetCopies
      emit $ "  br label %" <> T.pack (blockIdName target) <> "\n"

    TermBranch cond thenBlock elseBlock -> do
      condVal <- emitExpr cond
      condBool <- freshTemp
      emit $ "  " <> condBool <> " = icmp ne i64 " <> condVal <> ", 0\n"

      let thenCopies = [(d, s) | (t, d, s) <- copies, t == thenBlock]
          elseCopies = [(d, s) | (t, d, s) <- copies, t == elseBlock]

      if null thenCopies && null elseCopies
        then
          emit $ "  br i1 " <> condBool
            <> ", label %" <> T.pack (blockIdName thenBlock)
            <> ", label %" <> T.pack (blockIdName elseBlock) <> "\n"
        else do
          thenCopyLbl <- freshLabel "then.copy"
          elseCopyLbl <- freshLabel "else.copy"
          emit $ "  br i1 " <> condBool
            <> ", label %" <> thenCopyLbl
            <> ", label %" <> elseCopyLbl <> "\n"

          emit $ thenCopyLbl <> ":\n"
          modify $ \s -> s { lcgCurrentBlock = thenCopyLbl }
          emitPhiCopies thenCopies
          emit $ "  br label %" <> T.pack (blockIdName thenBlock) <> "\n"

          emit $ elseCopyLbl <> ":\n"
          modify $ \s -> s { lcgCurrentBlock = elseCopyLbl }
          emitPhiCopies elseCopies
          emit $ "  br label %" <> T.pack (blockIdName elseBlock) <> "\n"

    TermReturn exprOpt -> do
      case exprOpt of
        Just (SSACall name args) -> do
          val <- emitTailCall name args
          emit $ "  ret i64 " <> val <> "\n"
        Just (SSAInstanceCall target method args) -> do
          val <- emitInstanceCallExpr target method args
          emit $ "  ret i64 " <> val <> "\n"
        Just expr -> do
          val <- emitExpr expr
          emit $ "  ret i64 " <> val <> "\n"
        Nothing ->
          emit "  ret i64 0\n"

--------------------------------------------------------------------------------
-- Expression Code Generation (result returned as LLVM value text)
--------------------------------------------------------------------------------

emitExpr :: SSAExpr -> LLVMCodegen Text
emitExpr = \case
  SSAInt n -> return $ tshow n

  SSABool b -> return $ if b then "1" else "0"

  SSAStr s -> do
    strLabel <- addString (T.pack s)
    tmp <- freshTemp
    emit $ "  " <> tmp <> " = ptrtoint ptr @" <> strLabel <> " to i64\n"
    return tmp

  SSANull -> return "0"

  SSAUse var -> do
    tmp <- freshTemp
    let baseName = ssaVarBase var
    emit $ "  " <> tmp <> " = load i64, ptr %" <> T.pack baseName <> ".addr\n"
    return tmp

  SSAThis -> do
    tmp <- freshTemp
    emit $ "  " <> tmp <> " = load i64, ptr %this.addr\n"
    return tmp

  SSAUnary op e -> do
    val <- emitExpr e
    case op of
      Neg -> do
        tmp <- freshTemp
        emit $ "  " <> tmp <> " = sub i64 0, " <> val <> "\n"
        return tmp
      Not -> do
        t1 <- freshTemp
        emit $ "  " <> t1 <> " = icmp eq i64 " <> val <> ", 0\n"
        t2 <- freshTemp
        emit $ "  " <> t2 <> " = zext i1 " <> t1 <> " to i64\n"
        return t2

  SSABinary op l r -> do
    case op of
      And -> emitShortCircuitAnd l r
      Or  -> emitShortCircuitOr l r
      _ -> do
        syms <- asks lcgSymbols
        typeEnv <- asks lcgTypeEnv
        clsName <- asks lcgClassName
        let isStr = isStringTyped syms typeEnv clsName l
                 || isStringTyped syms typeEnv clsName r
        if isStr
          then emitStringBinaryOp op l r
          else emitBinaryOp op l r

  SSATernary cond thenE elseE -> do
    condVal <- emitExpr cond
    condBool <- freshTemp
    emit $ "  " <> condBool <> " = icmp ne i64 " <> condVal <> ", 0\n"

    thenLbl <- freshLabel "tern.then"
    elseLbl <- freshLabel "tern.else"
    mergeLbl <- freshLabel "tern.merge"

    emit $ "  br i1 " <> condBool <> ", label %" <> thenLbl <> ", label %" <> elseLbl <> "\n"

    emit $ thenLbl <> ":\n"
    modify $ \s -> s { lcgCurrentBlock = thenLbl }
    thenVal <- emitExpr thenE
    thenExit <- gets lcgCurrentBlock
    emit $ "  br label %" <> mergeLbl <> "\n"

    emit $ elseLbl <> ":\n"
    modify $ \s -> s { lcgCurrentBlock = elseLbl }
    elseVal <- emitExpr elseE
    elseExit <- gets lcgCurrentBlock
    emit $ "  br label %" <> mergeLbl <> "\n"

    emit $ mergeLbl <> ":\n"
    modify $ \s -> s { lcgCurrentBlock = mergeLbl }
    result <- freshTemp
    emit $ "  " <> result <> " = phi i64 [" <> thenVal <> ", %" <> thenExit
      <> "], [" <> elseVal <> ", %" <> elseExit <> "]\n"
    return result

  SSACall name args ->
    emitStaticCall name args

  SSAInstanceCall target method args ->
    emitInstanceCallExpr target method args

  SSANewObject cn args ->
    emitNewObject cn args

  SSAFieldAccess target field ->
    emitFieldAccess target field

--------------------------------------------------------------------------------
-- Binary Operations
--------------------------------------------------------------------------------

emitBinaryOp :: BinaryOp -> SSAExpr -> SSAExpr -> LLVMCodegen Text
emitBinaryOp op l r = do
  lv <- emitExpr l
  rv <- emitExpr r
  case op of
    Add -> binInstr "add" lv rv
    Sub -> binInstr "sub" lv rv
    Mul -> binInstr "mul" lv rv
    Div -> binInstr "sdiv" lv rv
    Mod -> binInstr "srem" lv rv

    Eq  -> cmpInstr "eq" lv rv
    Ne  -> cmpInstr "ne" lv rv
    Lt  -> cmpInstr "slt" lv rv
    Le  -> cmpInstr "sle" lv rv
    Gt  -> cmpInstr "sgt" lv rv
    Ge  -> cmpInstr "sge" lv rv

    And -> binInstr "and" lv rv
    Or  -> binInstr "or" lv rv

    Concat -> do
      tmp <- freshTemp
      emit $ "  " <> tmp <> " = call i64 @__str_concat(i64 " <> lv <> ", i64 " <> rv <> ")\n"
      return tmp
  where
    binInstr instr lv rv = do
      tmp <- freshTemp
      emit $ "  " <> tmp <> " = " <> instr <> " i64 " <> lv <> ", " <> rv <> "\n"
      return tmp

    cmpInstr pred' lv rv = do
      t1 <- freshTemp
      emit $ "  " <> t1 <> " = icmp " <> pred' <> " i64 " <> lv <> ", " <> rv <> "\n"
      t2 <- freshTemp
      emit $ "  " <> t2 <> " = zext i1 " <> t1 <> " to i64\n"
      return t2

emitStringBinaryOp :: BinaryOp -> SSAExpr -> SSAExpr -> LLVMCodegen Text
emitStringBinaryOp op l r = do
  lv <- emitExpr l
  rv <- emitExpr r
  case op of
    Add -> do
      tmp <- freshTemp
      emit $ "  " <> tmp <> " = call i64 @__str_concat(i64 " <> lv <> ", i64 " <> rv <> ")\n"
      return tmp
    _ | op `elem` [Eq, Ne, Lt, Le, Gt, Ge] -> do
      -- inttoptr both
      lptr <- freshTemp
      emit $ "  " <> lptr <> " = inttoptr i64 " <> lv <> " to ptr\n"
      rptr <- freshTemp
      emit $ "  " <> rptr <> " = inttoptr i64 " <> rv <> " to ptr\n"
      cmpR <- freshTemp
      emit $ "  " <> cmpR <> " = call i32 @strcmp(ptr " <> lptr <> ", ptr " <> rptr <> ")\n"
      let pred' = case op of
            Eq -> "eq"; Ne -> "ne"; Lt -> "slt"; Le -> "sle"; Gt -> "sgt"; Ge -> "sge"
            _ -> "eq"
      t1 <- freshTemp
      emit $ "  " <> t1 <> " = icmp " <> pred' <> " i32 " <> cmpR <> ", 0\n"
      t2 <- freshTemp
      emit $ "  " <> t2 <> " = zext i1 " <> t1 <> " to i64\n"
      return t2
    _ -> emitBinaryOp op l r

isStringTyped :: ProgramSymbols -> TypeEnv -> String -> SSAExpr -> Bool
isStringTyped syms typeEnv clsName expr = case expr of
  SSAStr _ -> True
  SSABinary Concat _ _ -> True
  _ -> case inferSSAExprTypeWithClass (Just clsName) syms typeEnv expr of
    Just (PrimitiveType TString) -> True
    _ -> False

--------------------------------------------------------------------------------
-- Short-Circuit AND/OR
--------------------------------------------------------------------------------

emitShortCircuitAnd :: SSAExpr -> SSAExpr -> LLVMCodegen Text
emitShortCircuitAnd l r = do
  lv <- emitExpr l
  lBool <- freshTemp
  emit $ "  " <> lBool <> " = icmp ne i64 " <> lv <> ", 0\n"

  rhsLbl <- freshLabel "and.rhs"
  doneLbl <- freshLabel "and.done"
  lExit <- gets lcgCurrentBlock
  emit $ "  br i1 " <> lBool <> ", label %" <> rhsLbl <> ", label %" <> doneLbl <> "\n"

  emit $ rhsLbl <> ":\n"
  modify $ \s -> s { lcgCurrentBlock = rhsLbl }
  rv <- emitExpr r
  rBool <- freshTemp
  emit $ "  " <> rBool <> " = icmp ne i64 " <> rv <> ", 0\n"
  rExit <- gets lcgCurrentBlock
  emit $ "  br label %" <> doneLbl <> "\n"

  emit $ doneLbl <> ":\n"
  modify $ \s -> s { lcgCurrentBlock = doneLbl }
  resBool <- freshTemp
  emit $ "  " <> resBool <> " = phi i1 [false, %" <> lExit <> "], [" <> rBool <> ", %" <> rExit <> "]\n"
  result <- freshTemp
  emit $ "  " <> result <> " = zext i1 " <> resBool <> " to i64\n"
  return result

emitShortCircuitOr :: SSAExpr -> SSAExpr -> LLVMCodegen Text
emitShortCircuitOr l r = do
  lv <- emitExpr l
  lBool <- freshTemp
  emit $ "  " <> lBool <> " = icmp ne i64 " <> lv <> ", 0\n"

  rhsLbl <- freshLabel "or.rhs"
  doneLbl <- freshLabel "or.done"
  lExit <- gets lcgCurrentBlock
  emit $ "  br i1 " <> lBool <> ", label %" <> doneLbl <> ", label %" <> rhsLbl <> "\n"

  emit $ rhsLbl <> ":\n"
  modify $ \s -> s { lcgCurrentBlock = rhsLbl }
  rv <- emitExpr r
  rBool <- freshTemp
  emit $ "  " <> rBool <> " = icmp ne i64 " <> rv <> ", 0\n"
  rExit <- gets lcgCurrentBlock
  emit $ "  br label %" <> doneLbl <> "\n"

  emit $ doneLbl <> ":\n"
  modify $ \s -> s { lcgCurrentBlock = doneLbl }
  resBool <- freshTemp
  emit $ "  " <> resBool <> " = phi i1 [true, %" <> lExit <> "], [" <> rBool <> ", %" <> rExit <> "]\n"
  result <- freshTemp
  emit $ "  " <> result <> " = zext i1 " <> resBool <> " to i64\n"
  return result

--------------------------------------------------------------------------------
-- Function Calls
--------------------------------------------------------------------------------

emitStaticCall :: String -> [SSAExpr] -> LLVMCodegen Text
emitStaticCall name args = do
  argVals <- mapM emitExpr args
  thisVal <- emitExpr SSAThis
  clsName <- asks lcgClassName
  syms <- asks lcgSymbols
  let methodLabel = case lookupClass clsName syms >>= lookupMethod name of
        Just _  -> T.pack clsName <> "_" <> T.pack name
        Nothing -> T.pack name
      argList = T.intercalate ", " $
        ("i64 " <> thisVal) : map (\a -> "i64 " <> a) argVals
  tmp <- freshTemp
  emit $ "  " <> tmp <> " = call i64 @" <> methodLabel <> "(" <> argList <> ")\n"
  return tmp

emitTailCall :: String -> [SSAExpr] -> LLVMCodegen Text
emitTailCall name args = do
  argVals <- mapM emitExpr args
  thisVal <- emitExpr SSAThis
  clsName <- asks lcgClassName
  syms <- asks lcgSymbols
  let methodLabel = case lookupClass clsName syms >>= lookupMethod name of
        Just _  -> T.pack clsName <> "_" <> T.pack name
        Nothing -> T.pack name
      argList = T.intercalate ", " $
        ("i64 " <> thisVal) : map (\a -> "i64 " <> a) argVals
  tmp <- freshTemp
  emit $ "  " <> tmp <> " = tail call i64 @" <> methodLabel <> "(" <> argList <> ")\n"
  return tmp

emitInstanceCallExpr :: SSAExpr -> String -> [SSAExpr] -> LLVMCodegen Text
emitInstanceCallExpr target method args = do
  targetVal <- emitExpr target
  argVals <- mapM emitExpr args
  syms <- asks lcgSymbols
  typeEnv <- asks lcgTypeEnv
  className <- asks lcgClassName
  let methodLabel = case target of
        SSAThis -> T.pack className <> "_" <> T.pack method
        _ -> case inferSSAExprClassWithCtx (Just className) syms typeEnv target of
               Just cn -> T.pack cn <> "_" <> T.pack method
               Nothing -> T.pack className <> "_" <> T.pack method
      argList = T.intercalate ", " $
        ("i64 " <> targetVal) : map (\a -> "i64 " <> a) argVals
  tmp <- freshTemp
  emit $ "  " <> tmp <> " = call i64 @" <> methodLabel <> "(" <> argList <> ")\n"
  return tmp

emitNewObject :: String -> [SSAExpr] -> LLVMCodegen Text
emitNewObject cn args = do
  syms <- asks lcgSymbols
  cs <- case lookupClass cn syms of
    Just cs -> return cs
    Nothing -> throwError $ D.ResolveError ("Unknown class: " ++ cn) 0 0

  let nFields = length (csFieldOrder cs)
      size = max 8 (nFields * 8)
      hasCtor = isJust (lookupMethod cn cs)

  rawPtr <- freshTemp
  emit $ "  " <> rawPtr <> " = call ptr @malloc(i64 " <> tshow size <> ")\n"

  when (nFields > 0) $
    emit $ "  call ptr @memset(ptr " <> rawPtr <> ", i32 0, i64 " <> tshow size <> ")\n"

  objVal <- freshTemp
  emit $ "  " <> objVal <> " = ptrtoint ptr " <> rawPtr <> " to i64\n"

  when hasCtor $ do
    argVals <- mapM emitExpr args
    let argList = T.intercalate ", " $
          ("i64 " <> objVal) : map (\a -> "i64 " <> a) argVals
        ctorLabel = T.pack cn <> "_" <> T.pack cn
    emit $ "  call i64 @" <> ctorLabel <> "(" <> argList <> ")\n"

  return objVal

emitFieldAccess :: SSAExpr -> String -> LLVMCodegen Text
emitFieldAccess target field = do
  objVal <- emitExpr target
  syms <- asks lcgSymbols
  typeEnv <- asks lcgTypeEnv
  className <- asks lcgClassName

  let targetClass = case target of
        SSAThis -> Just className
        _ -> inferSSAExprClassWithCtx (Just className) syms typeEnv target
      offset = fromMaybe 0 $ do
        cn <- targetClass
        cs <- lookupClass cn syms
        fieldOffset field cs

  objPtr <- freshTemp
  emit $ "  " <> objPtr <> " = inttoptr i64 " <> objVal <> " to ptr\n"
  fldPtr <- freshTemp
  emit $ "  " <> fldPtr <> " = getelementptr i8, ptr " <> objPtr <> ", i64 " <> tshow (offset * 8) <> "\n"
  result <- freshTemp
  emit $ "  " <> result <> " = load i64, ptr " <> fldPtr <> "\n"
  return result

--------------------------------------------------------------------------------
-- Phi Copy Handling (alloca-based parallel copy)
--------------------------------------------------------------------------------

emitPhiCopies :: [(String, String)] -> LLVMCodegen ()
emitPhiCopies copies = do
  -- Filter out same-variable copies (no-ops with allocas)
  let effective = filter (\(d, s) -> extractBaseName d /= extractBaseName s) copies
  when (not $ null effective) $ do
    -- Phase 1: Load all sources
    vals <- forM effective $ \(_dest, src) -> do
      let srcBase = extractBaseName src
      tmp <- freshTemp
      emit $ "  " <> tmp <> " = load i64, ptr %" <> T.pack srcBase <> ".addr\n"
      return tmp
    -- Phase 2: Store to destinations
    forM_ (zip effective vals) $ \((dest, _src), val) -> do
      let destBase = extractBaseName dest
      emit $ "  store i64 " <> val <> ", ptr %" <> T.pack destBase <> ".addr\n"

computePhiCopies :: CFG -> [SSABlock] -> Map BlockId [(BlockId, String, String)]
computePhiCopies cfg blocks =
  let phiCopyList = concatMap (blockPhiCopies' cfg) blocks
  in foldl' addCopy Map.empty phiCopyList
  where
    addCopy m (srcBlock, targetBlock, destVar, srcVar) =
      Map.insertWith (++) srcBlock [(targetBlock, destVar, srcVar)] m

blockPhiCopies' :: CFG -> SSABlock -> [(BlockId, BlockId, String, String)]
blockPhiCopies' _cfg SSABlock{..} =
  [ (predBlock, blockLabel, ssaVarStr (phiVar phi), ssaVarStr srcVar)
  | phi <- blockPhis
  , (predBlock, srcVar) <- phiArgs phi
  ]

--------------------------------------------------------------------------------
-- Utilities
--------------------------------------------------------------------------------

emit :: Text -> LLVMCodegen ()
emit t = modify $ \s -> s { lcgCode = lcgCode s <> B.fromText t }

freshTemp :: LLVMCodegen Text
freshTemp = do
  n <- gets lcgTempCounter
  modify $ \s -> s { lcgTempCounter = n + 1 }
  return $ "%t" <> T.pack (show n)

freshLabel :: Text -> LLVMCodegen Text
freshLabel prefix = do
  n <- gets lcgLabelCounter
  modify $ \s -> s { lcgLabelCounter = n + 1 }
  return $ prefix <> "." <> T.pack (show n)

addString :: Text -> LLVMCodegen Text
addString content = do
  clsName <- asks lcgClassName
  methName <- asks lcgMethodName
  n <- gets lcgLabelCounter
  modify $ \s -> s { lcgLabelCounter = n + 1 }
  let label = ".str." <> T.pack clsName <> "." <> T.pack methName <> "." <> T.pack (show n)
  modify $ \s -> s { lcgStrings = (label, content) : lcgStrings s }
  return label

extractBaseName :: String -> String
extractBaseName name =
  case break (== '_') (reverse name) of
    (versionRev, '_':baseRev)
      | not (null versionRev) && all isDigit versionRev -> reverse baseRev
    _ -> name

tshow :: Show a => a -> Text
tshow = T.pack . show

escapeStrLLVM :: Text -> Text
escapeStrLLVM = T.concatMap escape
  where
    escape '"'  = "\\22"
    escape '\\' = "\\5C"
    escape '\n' = "\\0A"
    escape '\t' = "\\09"
    escape '\r' = "\\0D"
    escape c    = T.singleton c
