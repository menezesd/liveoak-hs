{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE OverloadedStrings #-}

-- | SSA-based code generation for LiveOak.
-- Generates SAM assembly directly from CFG/SSA form without lossy conversion.
module LiveOak.SSACodegen
  ( -- * Code Generation
    generateFromSSA
  , generateMethodFromCFG
  ) where

import Control.Monad (forM, forM_, when, unless)
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
import Data.Maybe (isJust)

import LiveOak.Ast (UnaryOp(..), BinaryOp(..))
import LiveOak.SSATypes
import LiveOak.CFG
import LiveOak.Symbol (ProgramSymbols(..), MethodSymbol, VarSymbol, lookupClass, lookupField, csFieldOrder, lookupMethod, fieldOffset, csName, numParams, numLocals, msName, msParams, msLocals, vsName, vsType, stackAddress)
import LiveOak.Diag (Diag, Result)
import qualified LiveOak.Diag as D
import LiveOak.StringRuntime (emitStringRuntime, strConcatLabel, strReverseLabel, strRepeatLabel, strCompareLabel)
import LiveOak.SSATypeInfer (TypeEnv, buildTypeEnv, inferSSAExprClass, inferSSAExprClassWithCtx, inferSSAExprType)
import LiveOak.Types (ValueType(..), Type(..), ofPrimitive)

--------------------------------------------------------------------------------
-- Code Generation Types
--------------------------------------------------------------------------------

-- | Code generation state
data SSACodegenState = SSACodegenState
  { scgLabelCounter :: !Int
  , scgCode :: !Builder
  , scgVarSlots :: !(Map String Int)  -- ^ Stack slot for each SSA variable
  }

-- | Code generation context
data SSACodegenCtx = SSACodegenCtx
  { scgSymbols :: !ProgramSymbols
  , scgClassName :: !String
  , scgMethodName :: !String
  , scgMethodSymbol :: !MethodSymbol
  , scgCFG :: !CFG
  , scgPhiCopies :: !(Map BlockId [(BlockId, String, String)])
    -- ^ For each block, copies to insert before jump: (target, destVar, srcVar)
  , scgTypeEnv :: !TypeEnv
    -- ^ Type environment for inferring expression types
  , scgReturnSlotOffset :: !Int        -- ^ Offset of return slot relative to FBR
  , scgLocalCount :: !Int              -- ^ Number of locals to allocate
  }

type SSACodegen a = ReaderT SSACodegenCtx (StateT SSACodegenState (Either Diag)) a

--------------------------------------------------------------------------------
-- Code Generation Entry Points
--------------------------------------------------------------------------------

-- | Generate SAM code from an SSA program
generateFromSSA :: SSAProgram -> ProgramSymbols -> Result Text
generateFromSSA (SSAProgram classes) syms = do
  -- Generate preamble
  let preamble = generatePreamble syms

  -- Generate all methods
  codes <- forM classes $ \cls ->
    forM (ssaClassMethods cls) $ \method ->
      generateMethodSSA syms (ssaClassName cls) method

  -- Generate string runtime
  let stringRuntime = generateStringRuntime

  return $ T.intercalate "\n" [preamble, T.intercalate "\n" (concat codes), stringRuntime]

-- | Generate program preamble (allocate Main, call Main.main, STOP)
generatePreamble :: ProgramSymbols -> Text
generatePreamble syms =
  let mainFields = case lookupClass "Main" syms of
        Just cs -> length (csFieldOrder cs)
        Nothing -> 0
  in T.unlines
    [ "PUSHIMM " <> tshow mainFields
    , "MALLOC"
    , "PUSHIMM 0"
    , "SWAP"
    , "LINK"
    , "JSR Main_main"
    , "UNLINK"
    , "ADDSP -1"
    , "STOP"
    ]

-- | Generate string runtime functions
generateStringRuntime :: Text
generateStringRuntime = emitStringRuntime

-- | Generate SAM code for a single method from its CFG
generateMethodFromCFG :: ProgramSymbols -> String -> SSAMethod -> Result Text
generateMethodFromCFG = generateMethodSSA

--------------------------------------------------------------------------------
-- Method Code Generation
--------------------------------------------------------------------------------

-- | Generate code for a method using its CFG
generateMethodSSA :: ProgramSymbols -> String -> SSAMethod -> Result Text
generateMethodSSA syms clsName method@SSAMethod{..} = do
  let cfg = buildCFG method
  methodSymbol <- case lookupClass clsName syms >>= lookupMethod ssaMethodName of
    Just ms -> return ms
    Nothing -> D.resolveErr ("Unknown method symbol for " ++ clsName ++ "." ++ ssaMethodName) 0 0

  -- Compute phi copies to insert in predecessor blocks
  let phiCopies = computePhiCopies cfg (ssaMethodBlocks)

      -- Build type environment for this method
      typeEnv = buildTypeEnv ssaMethodBlocks syms ssaMethodClassName ssaMethodParams

      totalParams = numParams methodSymbol
      returnSlotOffset = -(3 + totalParams)
      paramSlots = Map.fromList
        [ (vsName v, stackAddress totalParams v)
        | v <- msParams methodSymbol
        ]
      baseLocalSlots = Map.fromList
        [ (vsName v, stackAddress totalParams v)
        | v <- msLocals methodSymbol
        ]
      baseLocalCount = numLocals methodSymbol

      allVars = collectAllVars ssaMethodBlocks
      baseNames = Set.fromList (Map.keys paramSlots ++ Map.keys baseLocalSlots)
      extraVars = sort $ Set.toList $ Set.difference allVars baseNames
      extraSlots = Map.fromList $ zip extraVars [baseLocalCount + 1 ..]

      varSlots = Map.unions [paramSlots, baseLocalSlots, extraSlots]
      localCount = baseLocalCount + length extraVars

      ctx = SSACodegenCtx
        { scgSymbols = syms
        , scgClassName = clsName
        , scgMethodName = ssaMethodName
        , scgMethodSymbol = methodSymbol
        , scgCFG = cfg
        , scgPhiCopies = phiCopies
        , scgTypeEnv = typeEnv
        , scgReturnSlotOffset = returnSlotOffset
        , scgLocalCount = localCount
        }

      initState = SSACodegenState
        { scgLabelCounter = 0
        , scgCode = mempty
        , scgVarSlots = varSlots
        }

  (_, finalState) <- runStateT (runReaderT (emitMethodCFG method) ctx) initState
  return $ TL.toStrict $ B.toLazyText $ scgCode finalState

-- | Emit a method using CFG
emitMethodCFG :: SSAMethod -> SSACodegen ()
emitMethodCFG SSAMethod{..} = do
  clsName <- asks scgClassName
  currentMs <- asks scgMethodSymbol

  -- Emit method label
  let label = T.pack clsName <> "_" <> T.pack ssaMethodName
  emit $ "\n" <> label <> ":\n"

  -- Method prologue
  emit "LINK\n"

  -- Allocate space for local variables
  localCount <- asks scgLocalCount
  when (localCount > 0) $
    emit $ "ADDSP " <> tshow localCount <> "\n"

  -- Tail-call entry point (after prologue)
  cls <- asks scgClassName
  meth <- asks scgMethodName
  let tcoLabel = methodTCOLabelText cls meth
  emit $ tcoLabel <> ":\n"

  cfg <- asks scgCFG

  -- Emit blocks in reverse postorder
  let blockOrder = reversePostorder cfg
  forM_ blockOrder $ \blockId ->
    case getBlock cfg blockId of
      Just block -> emitBlock block
      Nothing -> return ()

  -- Method epilogue (return label)
  emit $ label <> "_return:\n"
  -- Pop local variables before unlinking (they're still on stack after ADDSP allocations)
  when (localCount > 0) $
    emit $ "ADDSP " <> tshow (-localCount) <> "\n"
  emit "UNLINK\n"
  emit "RST\n"

-- | Collect all variable names from blocks
collectAllVars :: [SSABlock] -> Set.Set String
collectAllVars blocks = Set.unions $ map blockVars blocks
  where
    blockVars SSABlock{..} =
      Set.unions $ map phiVars blockPhis ++ map instrVars blockInstrs

    phiVars PhiNode{..} = Set.singleton (ssaName phiVar)

    instrVars (SSAAssign var _) = Set.singleton (ssaName var)
    instrVars _ = Set.empty

--------------------------------------------------------------------------------
-- Block Code Generation
--------------------------------------------------------------------------------

-- | Emit a single block
emitBlock :: CFGBlock -> SSACodegen ()
emitBlock CFGBlock{..} = do
  -- Emit block label
  blockLabel <- blockLabelText cfgBlockId
  emit $ blockLabel <> ":\n"

  -- Emit phi node copies (from predecessors that jump here)
  -- Note: actual phi copies are inserted in predecessor terminators
  -- Here we just need to load the correct value

  -- Emit instructions
  forM_ cfgInstrs emitInstr

  -- Emit terminator with phi copies
  emitTerminator cfgBlockId cfgTerm

-- | Emit an SSA instruction
emitInstr :: SSAInstr -> SSACodegen ()
emitInstr = \case
  SSAAssign var expr -> do
    emitSSAExpr expr
    slot <- getVarSlot (ssaName var)
    emit $ "STOREOFF " <> tshow slot <> "\n"

  SSAFieldStore target _field off value -> do
    emitSSAExpr target
    emit $ "PUSHIMM " <> tshow off <> "\n"
    emit "ADD\n"
    emitSSAExpr value
    emit "STOREIND\n"

  SSAReturn exprOpt -> do
    returnSlot <- asks scgReturnSlotOffset
    case exprOpt of
      Just expr -> emitSSAExpr expr
      Nothing -> emit "PUSHIMM 0\n"
    -- Store in return slot (value stays on stack)
    emit $ "STOREOFF " <> tshow returnSlot <> "\n"

  SSAJump _ -> return ()  -- Handled by terminator

  SSABranch _ _ _ -> return ()  -- Handled by terminator

  SSAExprStmt expr -> do
    emitSSAExpr expr
    emit "ADDSP -1\n"  -- Discard result

-- | Emit a block terminator
emitTerminator :: BlockId -> Terminator -> SSACodegen ()
emitTerminator currentBlock term = do
  -- Get phi copies to insert before this jump
  phiCopies <- asks scgPhiCopies
  let copies = Map.findWithDefault [] currentBlock phiCopies

  case term of
    TermJump target -> do
      -- Insert phi copies for the target block
      forM_ [(d, s) | (t, d, s) <- copies, t == target] $ \(dest, src) -> do
        srcSlot <- getVarSlot src
        destSlot <- getVarSlot dest
        emit $ "PUSHOFF " <> tshow srcSlot <> "\n"
        emit $ "STOREOFF " <> tshow destSlot <> "\n"
      targetLabel <- blockLabelText target
      emit $ "JUMP " <> targetLabel <> "\n"

    TermBranch cond thenBlock elseBlock -> do
      emitSSAExpr cond
      -- Condition expression produces a boolean (0=false, 1=true)
      -- JUMPC jumps if top of stack is non-zero (true)
      -- We want to jump to elseBlock if condition is FALSE, so invert with ISNIL
      emit "ISNIL\n"
      -- JUMPC pops the condition value. If false, jump to elseCopyLabel to perform phi copies.
      elseCopyLabel <- freshLabel "else_copies"
      emit $ "JUMPC " <> elseCopyLabel <> "\n"
      -- True branch: perform phi copies for thenBlock before jumping.
      forM_ [(d, s) | (t, d, s) <- copies, t == thenBlock] $ \(dest, src) -> do
        srcSlot <- getVarSlot src
        destSlot <- getVarSlot dest
        emit $ "PUSHOFF " <> tshow srcSlot <> "\n"
        emit $ "STOREOFF " <> tshow destSlot <> "\n"
      thenLabel <- blockLabelText thenBlock
      emit $ "JUMP " <> thenLabel <> "\n"
      -- False branch: perform phi copies for elseBlock before jumping there.
      emit $ elseCopyLabel <> ":\n"
      forM_ [(d, s) | (t, d, s) <- copies, t == elseBlock] $ \(dest, src) -> do
        srcSlot <- getVarSlot src
        destSlot <- getVarSlot dest
        emit $ "PUSHOFF " <> tshow srcSlot <> "\n"
        emit $ "STOREOFF " <> tshow destSlot <> "\n"
      elseLabel <- blockLabelText elseBlock
      emit $ "JUMP " <> elseLabel <> "\n"

    TermReturn exprOpt -> do
      returnSlot <- asks scgReturnSlotOffset
      handled <- case exprOpt of
        Just expr -> emitTailCallIfPossible expr
        Nothing -> return False
      unless handled $ do
        case exprOpt of
          Just expr -> do
            emitSSAExpr expr
            emit $ "STOREOFF " <> tshow returnSlot <> "\n"
          Nothing -> do
            emit "PUSHIMM 0\n"
            emit $ "STOREOFF " <> tshow returnSlot <> "\n"
        clsName <- asks scgClassName
        methName <- asks scgMethodName
        let retLabel = T.pack clsName <> "_" <> T.pack methName <> "_return"
        emit $ "JUMP " <> retLabel <> "\n"

-- | Attempt tail-call optimization in a return. Returns True if handled.
-- Temporarily disable SSA TCO to stabilize stack correctness.
emitTailCallIfPossible :: SSAExpr -> SSACodegen Bool
emitTailCallIfPossible _ = return False

-- | Emit a tail call by rewriting params/this in-place and jumping to TCO label.
emitTailCallSSA :: MethodSymbol -> String -> MethodSymbol -> [SSAExpr] -> Maybe SSAExpr -> SSACodegen ()
emitTailCallSSA _ _ _ _ _ = return ()  -- currently unused (TCO disabled)

-- | Find a method in all classes (used as fallback when type inference fails)
-- Returns the first class that has a method with the given name
findMethodInClasses :: ProgramSymbols -> String -> Maybe String
findMethodInClasses syms methodName =
  let classes = Map.elems (psClasses syms)
      classesWithMethod = filter hasMethod classes
      hasMethod cs = isJust (lookupMethod methodName cs)
  in case classesWithMethod of
       (cs:_) -> Just (csName cs)
       [] -> Nothing

-- | Clean up leftover values from expression evaluation
-- After an expression result is consumed (e.g., via STOREOFF), clean up
-- any temporary values left on the stack (like method call arguments)
-- Note: Only top-level method calls leave garbage; sub-expressions are consumed
emitExprCleanup :: SSAExpr -> SSACodegen ()
emitExprCleanup = \case
  SSACall _ args -> emit $ "ADDSP " <> tshow (negate $ length args + 1) <> "\n"
  SSAInstanceCall _ _ args -> emit $ "ADDSP " <> tshow (negate $ length args + 1) <> "\n"
  _ -> return ()  -- Other expressions don't leave garbage on stack

--------------------------------------------------------------------------------
-- Expression Code Generation
--------------------------------------------------------------------------------

-- | Emit an SSA expression
emitSSAExpr :: SSAExpr -> SSACodegen ()
emitSSAExpr = \case
  SSAInt n ->
    emit $ "PUSHIMM " <> tshow n <> "\n"

  SSABool b ->
    emit $ "PUSHIMM " <> (if b then "1" else "0") <> "\n"

  SSAStr s ->
    emit $ "PUSHIMMSTR \"" <> T.pack (escapeString s) <> "\"\n"

  SSANull ->
    emit "PUSHIMM 0\n"

  SSAUse var -> do
    slot <- getVarSlot (ssaName var)
    emit $ "PUSHOFF " <> tshow slot <> "\n"

  SSAThis -> do
    slot <- getVarSlot "this"
    emit $ "PUSHOFF " <> tshow slot <> "\n"

  SSAUnary op e -> do
    syms <- asks scgSymbols
    typeEnv <- asks scgTypeEnv
    let exprType = inferSSAExprType syms typeEnv e
    emitSSAExpr e
    case op of
      Neg -> do
        case exprType of
          Just t | t == ofPrimitive TString -> emitSSAStringReverse
          _ -> do
            emit "PUSHIMM 0\n"
            emit "SWAP\n"
            emit "SUB\n"
      Not ->
        emit "ISNIL\n"

  SSABinary op l r -> do
    syms <- asks scgSymbols
    typeEnv <- asks scgTypeEnv
    methSym <- asks scgMethodSymbol
    clsName <- asks scgClassName
    let lType = inferSSAExprType syms typeEnv l
        rType = inferSSAExprType syms typeEnv r
    case stringBinaryEmitterSSA syms methSym clsName typeEnv op lType rType l r of
      Just emitter -> emitter
      Nothing -> case op of
        And -> emitShortCircuitAnd l r
        Or  -> emitShortCircuitOr l r
        Concat -> do
          emitSSAExpr l
          emitSSAExpr r
          emitSSAStringConcat
        _ -> do
          emitSSAExpr l
          emitSSAExpr r
          emitBinaryOp op

  SSATernary cond thenE elseE -> do
    elseLabel <- freshLabel "else"
    endLabel <- freshLabel "endif"
    emitSSAExpr cond
    emit "ISNIL\n"
    emit $ "JUMPC " <> elseLabel <> "\n"
    emitSSAExpr thenE
    emit $ "JUMP " <> endLabel <> "\n"
    emit $ elseLabel <> ":\n"
    emitSSAExpr elseE
    emit $ endLabel <> ":\n"

  SSACall name args -> do
    -- Push return slot
    emit "PUSHIMM 0\n"
    -- Push implicit 'this'
    thisSlot <- getVarSlot "this"
    emit $ "PUSHOFF " <> tshow thisSlot <> "\n"
    -- Push arguments
    forM_ args emitSSAExpr
    -- Call
    emit "LINK\n"
    clsName <- asks scgClassName
    syms <- asks scgSymbols
    let methodLabel = case lookupClass clsName syms >>= lookupMethod name of
          Just _ -> T.pack clsName <> "_" <> T.pack name
          Nothing -> T.pack name  -- Fallback
    emit $ "JSR " <> methodLabel <> "\n"
    emit "UNLINK\n"
    -- Clean up arguments: after UNLINK, stack is [return_value, this, args...]
    -- We want to keep return_value (at bottom) and pop this+args (on top)
    let nArgs = length args + 1  -- +1 for 'this'
    emit $ "ADDSP " <> tshow (negate nArgs) <> "\n"

  SSAInstanceCall target method args -> do
    emit "PUSHIMM 0\n"  -- Return slot
    emitSSAExpr target   -- Push 'this'
    forM_ args emitSSAExpr
    emit "LINK\n"
    -- Infer target class type and use qualified method name
    syms <- asks scgSymbols
    typeEnv <- asks scgTypeEnv
    className <- asks scgClassName
    let methodLabel = case target of
          SSAThis -> T.pack className <> "_" <> T.pack method  -- 'this' is current class
          _ -> case inferSSAExprClassWithCtx (Just className) syms typeEnv target of
                 Just cn -> T.pack cn <> "_" <> T.pack method
                 Nothing ->
                   -- Fallback: search all classes for this method
                   case findMethodInClasses syms method of
                     Just cn -> T.pack cn <> "_" <> T.pack method
                     Nothing -> T.pack method  -- Last resort: bare name
    emit $ "JSR " <> methodLabel <> "\n"
    emit "UNLINK\n"
    -- Clean up arguments: after UNLINK, stack is [return_value, this, args...]
    -- We want to keep return_value (at bottom) and pop this+args (on top)
    let nArgs = length args + 1  -- +1 for 'this'
    emit $ "ADDSP " <> tshow (negate nArgs) <> "\n"

  SSANewObject cn args -> do
    syms <- asks scgSymbols
    let nFields = case lookupClass cn syms of
          Just cs -> length (csFieldOrder cs)
          Nothing -> 1
        hasCtor = maybe False (isJust . lookupMethod cn) (lookupClass cn syms)
    -- Allocate object (heap initialized to 0)
    emit $ "PUSHIMM " <> tshow nFields <> "\n"
    emit "MALLOC\n"
    -- Call constructor if present
    when hasCtor $ do
      emit "DUP\n"       -- keep object for caller
      emit "PUSHIMM 0\n" -- return slot
      emit "SWAP\n"      -- place obj below return slot
      forM_ args emitSSAExpr
      let ctorLabel = T.pack cn <> "_" <> T.pack cn
          nArgs = length args + 1  -- +1 for 'this'
      emit "LINK\n"
      emit $ "JSR " <> ctorLabel <> "\n"
      emit "UNLINK\n"
      emit $ "ADDSP " <> tshow (negate nArgs) <> "\n"
      emit "ADDSP -1\n"  -- pop return slot

  SSAFieldAccess target field -> do
    -- Emit target expression
    emitSSAExpr target
    -- Infer target class and look up field offset
    syms <- asks scgSymbols
    typeEnv <- asks scgTypeEnv
    className <- asks scgClassName
    let targetClass = case target of
          SSAThis -> Just className  -- Use current class for 'this'
          _ -> inferSSAExprClassWithCtx (Just className) syms typeEnv target
        offset = case targetClass of
          Just cn -> case lookupClass cn syms of
            Just cs -> case fieldOffset field cs of
              Just off -> off
              Nothing -> 0  -- Field not found, default to 0
            Nothing -> 0  -- Class not found, default to 0
          Nothing -> 0  -- Can't infer type, default to 0
    emit $ "PUSHIMM " <> tshow offset <> "\n"
    emit "ADD\n"
    emit "PUSHIND\n"

-- | Emit a binary operation
emitBinaryOp :: BinaryOp -> SSACodegen ()
emitBinaryOp = \case
  Add -> emit "ADD\n"
  Sub -> emit "SUB\n"
  Mul -> emit "TIMES\n"
  Div -> emit "DIV\n"
  Mod -> emit "MOD\n"
  Eq  -> emit "EQUAL\n"
  Ne  -> do emit "EQUAL\n"; emit "ISNIL\n"
  Lt  -> emit "LESS\n"
  Le  -> do emit "GREATER\n"; emit "ISNIL\n"
  Gt  -> emit "GREATER\n"
  Ge  -> do emit "LESS\n"; emit "ISNIL\n"
  And -> emit "AND\n"
  Or  -> emit "OR\n"
  Concat -> emit "ADD\n"  -- String concatenation uses ADD in SAM

-- | Short-circuit AND for SSA expressions
emitShortCircuitAnd :: SSAExpr -> SSAExpr -> SSACodegen ()
emitShortCircuitAnd l r = do
  falseLabel <- freshLabel "and_false"
  endLabel <- freshLabel "and_end"
  emitSSAExpr l
  emit "ISNIL\n"
  emit $ "JUMPC " <> falseLabel <> "\n"
  emitSSAExpr r
  emit "ISNIL\n"
  emit $ "JUMPC " <> falseLabel <> "\n"
  emit "PUSHIMM 1\n"
  emit $ "JUMP " <> endLabel <> "\n"
  emit $ falseLabel <> ":\n"
  emit "PUSHIMM 0\n"
  emit $ endLabel <> ":\n"

-- | Short-circuit OR for SSA expressions
emitShortCircuitOr :: SSAExpr -> SSAExpr -> SSACodegen ()
emitShortCircuitOr l r = do
  trueLabel <- freshLabel "or_true"
  falseLabel <- freshLabel "or_false"
  endLabel <- freshLabel "or_end"
  emitSSAExpr l
  emit "ISNIL\n"
  emit $ "JUMPC " <> trueLabel <> "_check\n"
  emit "PUSHIMM 1\n"
  emit $ "JUMP " <> endLabel <> "\n"
  emit $ trueLabel <> "_check:\n"
  emitSSAExpr r
  emit "ISNIL\n"
  emit $ "JUMPC " <> falseLabel <> "\n"
  emit "PUSHIMM 1\n"
  emit $ "JUMP " <> endLabel <> "\n"
  emit $ falseLabel <> ":\n"
  emit "PUSHIMM 0\n"
  emit $ endLabel <> ":\n"

-- | Choose string-aware emitter when either operand is a string.
stringBinaryEmitterSSA :: ProgramSymbols -> MethodSymbol -> String -> TypeEnv -> BinaryOp -> Maybe ValueType -> Maybe ValueType -> SSAExpr -> SSAExpr -> Maybe (SSACodegen ())
stringBinaryEmitterSSA syms methSym currentClass tenv op lType rType l r
  | isString && op `elem` [Eq, Ne, Lt, Gt] = Just $ do
      emitSSAExpr l
      emitSSAExpr r
      emitSSAStringCompare op
  | isString && op == Add = Just $ do
      emitSSAExpr l
      emitSSAExpr r
      emitSSAStringConcat
  | lType == Just (ofPrimitive TString) && rType == Just (ofPrimitive TInt) =
      Just $ do
        emitSSAExpr l
        emitSSAExpr r
        emitSSAStringRepeat False
  | lType == Just (ofPrimitive TInt) && rType == Just (ofPrimitive TString) =
      Just $ do
        emitSSAExpr l
        emitSSAExpr r
        emitSSAStringRepeat True
  | otherwise = Nothing
  where
    isString =
      lType == Just (ofPrimitive TString)
        || rType == Just (ofPrimitive TString)
        || isStringLiteral l || isStringLiteral r
        || isConcatExpr l || isConcatExpr r
        || isStringVarUse l || isStringVarUse r
        || isStringFieldUse l || isStringFieldUse r

    isStringLiteral = \case
      SSAStr _ -> True
      _ -> False

    isConcatExpr = \case
      SSABinary Add l1 r1 ->
        let lt' = inferSSAExprType syms tenv l1
            rt' = inferSSAExprType syms tenv r1
        in lt' == Just (ofPrimitive TString) || rt' == Just (ofPrimitive TString) || isStringLiteral l1 || isStringLiteral r1
      _ -> False

    isStringVarUse = \case
      SSAUse v ->
        case inferSSAExprType syms tenv (SSAUse v) of
          Just t -> t == ofPrimitive TString
          Nothing -> lookupVarType (ssaName v)
      _ -> False

    isStringFieldUse = \case
      SSAFieldAccess target field ->
        let targetClass = case target of
              SSAThis -> Just currentClass
              _ -> inferSSAExprClassWithCtx (Just currentClass) syms tenv target
        in case targetClass of
             Just cn -> case lookupClass cn syms >>= lookupField field of
               Just vs -> vsType vs == ofPrimitive TString
               Nothing -> False
             Nothing -> False
      _ -> False

    lookupVarType name =
      let paramType = [vsType vs | vs <- msParams methSym, vsName vs == name]
          localType = [vsType vs | vs <- msLocals methSym, vsName vs == name]
          candidate = paramType ++ localType
      in case candidate of
           (t:_) -> t == ofPrimitive TString
           _ -> False

-- | Emit string comparison using runtime helper.
emitSSAStringCompare :: BinaryOp -> SSACodegen ()
emitSSAStringCompare op = do
  emit "LINK\n"
  emit $ "JSR " <> strCompareLabel <> "\n"
  emit "UNLINK\n"
  emit "ADDSP -1\n"
  case op of
    Eq -> do
      emit "PUSHIMM 0\n"
      emit "EQUAL\n"
    Ne -> do
      emit "PUSHIMM 0\n"
      emit "EQUAL\n"
      emit "ISNIL\n"
    Lt -> do
      emit "PUSHIMM -1\n"
      emit "EQUAL\n"
    Gt -> do
      emit "PUSHIMM 1\n"
      emit "EQUAL\n"
    _ -> return ()

-- | Emit string concatenation using runtime helper.
emitSSAStringConcat :: SSACodegen ()
emitSSAStringConcat = do
  emit "LINK\n"
  emit $ "JSR " <> strConcatLabel <> "\n"
  emit "UNLINK\n"
  emit "ADDSP -1\n"

-- | Emit string repetition (string * int).
emitSSAStringRepeat :: Bool -> SSACodegen ()
emitSSAStringRepeat swapOperands = do
  when swapOperands $ emit "SWAP\n"
  emit "LINK\n"
  emit $ "JSR " <> strRepeatLabel <> "\n"
  emit "UNLINK\n"
  emit "ADDSP -1\n"

-- | Emit string reverse (~str).
emitSSAStringReverse :: SSACodegen ()
emitSSAStringReverse = do
  emit "LINK\n"
  emit $ "JSR " <> strReverseLabel <> "\n"
  emit "UNLINK\n"

--------------------------------------------------------------------------------
-- Phi Node Handling
--------------------------------------------------------------------------------

-- | Compute phi copies that need to be inserted in predecessor blocks
-- Returns: Map from source block -> [(target block, dest var, src var)]
computePhiCopies :: CFG -> [SSABlock] -> Map BlockId [(BlockId, String, String)]
computePhiCopies cfg blocks =
  let -- For each block with phi nodes, add copies to predecessors
      phiCopyList = concatMap (blockPhiCopies cfg) blocks
      -- Group by source block
  in foldl' addCopy Map.empty phiCopyList
  where
    addCopy m (srcBlock, targetBlock, destVar, srcVar) =
      Map.insertWith (++) srcBlock [(targetBlock, destVar, srcVar)] m

-- | Get phi copies for a block
blockPhiCopies :: CFG -> SSABlock -> [(BlockId, BlockId, String, String)]
blockPhiCopies _cfg SSABlock{..} =
  [ (predBlock, blockLabel, ssaName (phiVar phi), ssaName srcVar)
  | phi <- blockPhis
  , (predBlock, srcVar) <- phiArgs phi
  ]

--------------------------------------------------------------------------------
-- Utilities
--------------------------------------------------------------------------------

-- | Emit code
emit :: Text -> SSACodegen ()
emit t = modify $ \s -> s { scgCode = scgCode s <> B.fromText t }

-- | Generate predictable TCO entry label.
methodTCOLabelText :: String -> String -> Text
methodTCOLabelText clsName methName = T.pack clsName <> "_" <> T.pack methName <> "_tco"

-- | Generate a method-specific prefix for block labels.
methodLabelPrefixText :: SSACodegen Text
methodLabelPrefixText = do
  cls <- asks scgClassName
  meth <- asks scgMethodName
  return $ T.pack cls <> "_" <> T.pack meth

-- | Qualify a block label with the current method to avoid collisions.
blockLabelText :: BlockId -> SSACodegen Text
blockLabelText bid = do
  prefix <- methodLabelPrefixText
  return $ prefix <> "__" <> T.pack bid

-- | Generate a fresh label
freshLabel :: Text -> SSACodegen Text
freshLabel prefix = do
  st <- get
  let n = scgLabelCounter st
  put st { scgLabelCounter = n + 1 }
  methodPrefix <- methodLabelPrefixText
  return $ methodPrefix <> "_" <> prefix <> "_" <> T.pack (show n)

-- | Get stack slot for a variable
getVarSlot :: String -> SSACodegen Int
getVarSlot name = do
  slots <- gets scgVarSlots
  case Map.lookup name slots of
    Just slot -> return slot
    Nothing -> throwError $ D.ResolveError ("Unknown variable: " ++ name) 0 0

-- | Convert to text
tshow :: Show a => a -> Text
tshow = T.pack . show

-- | Escape a string for SAM
escapeString :: String -> String
escapeString = concatMap escape
  where
    escape '"' = "\\\""
    escape '\\' = "\\\\"
    escape '\n' = "\\n"
    escape '\t' = "\\t"
    escape c = [c]
