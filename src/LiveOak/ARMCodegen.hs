{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE OverloadedStrings #-}

-- | AArch64 code generation from SSA form.
-- Generates GAS (GNU Assembler) syntax for Linux AArch64.
module LiveOak.ARMCodegen
  ( -- * Code Generation
    generateARMFromSSA
  , generateMethodARM
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
import Data.Bits (countTrailingZeros, popCount, (.&.), shiftR)

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
import LiveOak.ARM (ARMReg(..), regName)
import LiveOak.ARMRuntime (emitARMRuntime)
import qualified LiveOak.ARM as ARM
import LiveOak.X86Liveness (computeLiveness, buildIntervals)
import LiveOak.ARMRegAlloc (RegAllocation(..), VarLocation(..), allocateRegisters, getVarLocation, usedCalleeRegs)

--------------------------------------------------------------------------------
-- Code Generation Types
--------------------------------------------------------------------------------

-- | Code generation state
data ARMCodegenState = ARMCodegenState
  { acgLabelCounter :: !Int
  , acgCode :: !Builder
  , acgVarSlots :: !(Map String Int)  -- ^ Stack slot offset for each SSA variable (relative to FP)
  , acgFrameSize :: !Int              -- ^ Total frame size (for alignment)
  , acgStrings :: ![(Text, Text)]     -- ^ String literals: (label, content)
  }

-- | Code generation context
data ARMCodegenCtx = ARMCodegenCtx
  { acgSymbols :: !ProgramSymbols
  , acgClassName :: !String
  , acgMethodName :: !String
  , acgMethodSymbol :: !MethodSymbol
  , acgCFG :: !CFG
  , acgPhiCopies :: !(Map BlockId [(BlockId, String, String)])
  , acgTypeEnv :: !TypeEnv
  , acgLocalCount :: !Int
  , acgRegAlloc :: !RegAllocation           -- ^ Register allocation result
  }

type ARMCodegen a = ReaderT ARMCodegenCtx (StateT ARMCodegenState (Either Diag)) a

--------------------------------------------------------------------------------
-- Code Generation Entry Points
--------------------------------------------------------------------------------

-- | Generate AArch64 assembly from an SSA program
generateARMFromSSA :: SSAProgram -> ProgramSymbols -> Result Text
generateARMFromSSA (SSAProgram classes) syms = do
  let dataSection = generateDataSection

  -- Generate text section with all methods
  codes <- forM classes $ \cls ->
    forM (ssaClassMethods cls) $ \method ->
      generateMethodARM syms (ssaClassName cls) method

  -- Generate runtime support
  let runtime = T.unlines $ map ARM.instrText emitARMRuntime

  -- Generate entry point
  let entryPoint = generateEntryPoint syms

  return $ T.intercalate "\n"
    [ dataSection
    , ".text"
    , T.intercalate "\n" (concat codes)
    , runtime
    , entryPoint
    ]

-- | Generate the .data section
generateDataSection :: Text
generateDataSection = T.unlines
  [ ".section .data"
  , ""
  ]

-- | Generate program entry point
generateEntryPoint :: ProgramSymbols -> Text
generateEntryPoint syms =
  let mainFields = case lookupClass "Main" syms of
        Just cs -> length (csFieldOrder cs)
        Nothing -> 0
  in T.unlines
    [ ""
    , "// Program entry point"
    , ".globl main"
    , "main:"
    , "    stp x29, x30, [sp, #-16]!"
    , "    mov x29, sp"
    , ""
    , "    // Allocate Main object"
    , "    mov x0, #" <> tshow (mainFields * 8)
    , "    bl malloc"
    , ""
    , "    // Call Main.main (object pointer already in x0)"
    , "    bl Main_main"
    , ""
    , "    // Exit with return value (already in x0)"
    , "    bl exit"
    ]

--------------------------------------------------------------------------------
-- Method Code Generation
--------------------------------------------------------------------------------

-- | Generate AArch64 code for a single method
generateMethodARM :: ProgramSymbols -> String -> SSAMethod -> Result Text
generateMethodARM syms clsName method@SSAMethod{..} = do
  let cfg = buildCFG method
      methodNameStr = methodNameString ssaMethodName

  methodSymbol <- case lookupClass clsName syms >>= lookupMethod methodNameStr of
    Just ms -> return ms
    Nothing -> D.resolveErr ("Unknown method symbol for " ++ clsName ++ "." ++ methodNameStr) 0 0

  let phiCopies = computePhiCopies cfg ssaMethodBlocks
      typeEnv = buildTypeEnv ssaMethodBlocks syms ssaMethodClassName ssaMethodParams

      -- Compute liveness and register allocation
      liveness = computeLiveness cfg
      intervals = buildIntervals cfg liveness
      regAlloc = allocateRegisters intervals

      totalParams = numParams methodSymbol
      baseLocalCount = numLocals methodSymbol

      -- Collect all SSA variable BASE names
      allVarBases = collectAllVars ssaMethodBlocks
      paramNames = Set.fromList $ map vsName (msParams methodSymbol)
      localNames = Set.fromList $ map vsName (msLocals methodSymbol)
      baseNames = Set.union paramNames localNames
      extraVars = sort $ Set.toList $ Set.difference allVarBases baseNames

      -- Assign stack slots using BASE names
      paramSlots = Map.fromList $ zip (map vsName (msParams methodSymbol)) [0..]
      localSlots = Map.fromList $ zip (map vsName (msLocals methodSymbol)) [totalParams..]
      extraSlots = Map.fromList $ zip extraVars [totalParams + baseLocalCount..]

      varSlots = Map.unions [paramSlots, localSlots, extraSlots]
      totalVars = totalParams + baseLocalCount + length extraVars

      -- Frame size: 8 bytes per variable, aligned to 16 bytes
      rawFrameSize = totalVars * 8
      frameSize = ((rawFrameSize + 15) `div` 16) * 16

      ctx = ARMCodegenCtx
        { acgSymbols = syms
        , acgClassName = clsName
        , acgMethodName = methodNameStr
        , acgMethodSymbol = methodSymbol
        , acgCFG = cfg
        , acgPhiCopies = phiCopies
        , acgTypeEnv = typeEnv
        , acgLocalCount = totalVars
        , acgRegAlloc = regAlloc
        }

      initState = ARMCodegenState
        { acgLabelCounter = 0
        , acgCode = mempty
        , acgVarSlots = varSlots
        , acgFrameSize = frameSize
        , acgStrings = []
        }

  (_, finalState) <- runStateT (runReaderT (emitMethodARM method) ctx) initState
  let code = TL.toStrict $ B.toLazyText $ acgCode finalState
      strData = if null (acgStrings finalState)
                then ""
                else T.unlines $ [".section .rodata"] ++
                     [lbl <> ":\n    .asciz \"" <> escapeStr s <> "\""
                     | (lbl, s) <- reverse (acgStrings finalState)] ++
                     [".section .text"]
  return $ code <> strData
  where
    escapeStr = T.concatMap (\c -> case c of
      '\n' -> "\\n"; '\t' -> "\\t"; '\r' -> "\\r"
      '"'  -> "\\\""; '\\' -> "\\\\"; _   -> T.singleton c)

-- | Emit AArch64 code for a method
emitMethodARM :: SSAMethod -> ARMCodegen ()
emitMethodARM SSAMethod{..} = do
  clsName <- asks acgClassName
  let label = T.pack clsName <> "_" <> T.pack (methodNameString ssaMethodName)

  -- Method label
  emit $ "\n.globl " <> label <> "\n"
  emit $ label <> ":\n"

  -- Prologue: save FP and LR
  emit "    stp x29, x30, [sp, #-16]!\n"
  emit "    mov x29, sp\n"

  -- Allocate stack frame
  frameSize <- gets acgFrameSize
  emitSubSP frameSize

  -- Save callee-saved registers that we use (in pairs for alignment)
  alloc <- asks acgRegAlloc
  let usedCallee = usedCalleeRegs alloc
  emitPushCalleeSaved usedCallee

  -- Save arguments from registers to their allocated locations
  -- AAPCS64: X0 (this), X1, X2, X3, X4, X5, X6, X7
  methodSym <- asks acgMethodSymbol
  let params = msParams methodSym
      argRegsUsed = zip params [X0, X1, X2, X3, X4, X5, X6, X7]
  forM_ argRegsUsed $ \(param, reg) -> do
    emitStoreVar reg (vsName param ++ "_0")

  -- TCO entry point (after prologue)
  let tcoLabel = label <> "_tco"
  emit $ tcoLabel <> ":\n"

  -- Emit blocks in reverse postorder
  cfg <- asks acgCFG
  let blockOrder = reversePostorder cfg
  forM_ blockOrder $ \bid ->
    forM_ (getBlock cfg bid) emitBlock

  -- Return label
  let returnLabel = label <> "_return"
  emit $ returnLabel <> ":\n"

  -- Epilogue: restore callee-saved registers in reverse order
  emitPopCalleeSaved usedCallee

  -- Restore stack pointer and frame pointer
  emitAddSP frameSize
  emit "    ldp x29, x30, [sp], #16\n"
  emit "    ret\n"

-- | Convert an SSAVar to a versioned string identifier
ssaVarStr :: SSAVar -> String
ssaVarStr v = varNameString (ssaName v) ++ "_" ++ show (ssaVersion v)

-- | Convert an SSAVar to its base name (without version)
ssaVarBase :: SSAVar -> String
ssaVarBase v = varNameString (ssaName v)

-- | Collect all variable BASE names from blocks
collectAllVars :: [SSABlock] -> Set.Set String
collectAllVars blocks = Set.unions $ map blockVars blocks
  where
    blockVars SSABlock{..} =
      Set.unions $ map phiVars blockPhis ++ map instrVars blockInstrs
    phiVars PhiNode{..} = Set.singleton (ssaVarBase phiVar)
    instrVars (SSAAssign var _) = Set.singleton (ssaVarBase var)
    instrVars _ = Set.empty

--------------------------------------------------------------------------------
-- Block Code Generation
--------------------------------------------------------------------------------

-- | Emit a single block
emitBlock :: CFGBlock -> ARMCodegen ()
emitBlock CFGBlock{..} = do
  blockLabel <- blockLabelText cfgBlockId
  emit $ blockLabel <> ":\n"
  forM_ cfgInstrs emitInstr
  emitTerminator cfgBlockId cfgTerm

-- | Emit an SSA instruction
emitInstr :: SSAInstr -> ARMCodegen ()
emitInstr = \case
  SSAAssign var expr -> do
    emitExpr expr  -- Result in X0
    emitStoreVar X0 (ssaVarStr var)

  SSAFieldStore target _field off value -> do
    emitExpr target
    emit "    str x0, [sp, #-16]!\n"  -- Save target pointer
    emitExpr value
    emit "    mov x1, x0\n"           -- Value in X1
    emit "    ldr x0, [sp], #16\n"    -- Restore target to X0
    emit $ "    str x1, [x0, #" <> tshow (off * 8) <> "]\n"

  SSAReturn exprOpt -> do
    case exprOpt of
      Just expr -> emitExpr expr  -- Result in X0
      Nothing -> emit "    mov x0, #0\n"

  SSAJump _ -> return ()  -- Handled by terminator
  SSABranch _ _ _ -> return ()  -- Handled by terminator

  SSAExprStmt expr -> do
    emitExpr expr  -- Result discarded

-- | Emit a block terminator
emitTerminator :: BlockId -> Terminator -> ARMCodegen ()
emitTerminator currentBlock term = do
  phiCopies <- asks acgPhiCopies
  let copies = lookupList currentBlock phiCopies

  case term of
    TermJump target -> do
      let targetCopies = [(d, s) | (t, d, s) <- copies, t == target]
      emitParallelCopies targetCopies
      targetLabel <- blockLabelText target
      emit $ "    b " <> targetLabel <> "\n"

    TermBranch cond thenBlock elseBlock -> do
      emitExpr cond
      thenCopyLabel <- freshLabel "then_copy"
      elseCopyLabel <- freshLabel "else_copy"

      -- Branch if zero to else
      emit $ "    cbz x0, " <> elseCopyLabel <> "\n"

      -- Then branch
      emit $ thenCopyLabel <> ":\n"
      let thenCopies = [(d, s) | (t, d, s) <- copies, t == thenBlock]
      emitParallelCopies thenCopies
      thenLabel <- blockLabelText thenBlock
      emit $ "    b " <> thenLabel <> "\n"

      -- Else branch
      emit $ elseCopyLabel <> ":\n"
      let elseCopies = [(d, s) | (t, d, s) <- copies, t == elseBlock]
      emitParallelCopies elseCopies
      elseLabel <- blockLabelText elseBlock
      emit $ "    b " <> elseLabel <> "\n"

    TermReturn exprOpt -> do
      clsName <- asks acgClassName
      methName <- asks acgMethodName
      syms <- asks acgSymbols
      typeEnv <- asks acgTypeEnv
      case exprOpt of
        -- Self-recursive tail call
        Just (SSACall name args) | name == methName -> do
          case lookupClass clsName syms >>= lookupMethod name of
            Just _ -> emitSelfTailCall args
            Nothing -> do
              let targetLabel = T.pack name
              emitCrossMethodTailCall targetLabel args

        -- Self-recursive instance call on 'this'
        Just (SSAInstanceCall SSAThis method args) | method == methName ->
          emitSelfTailCall args

        -- Cross-method static call
        Just (SSACall name args) -> do
          let targetLabel = case lookupClass clsName syms >>= lookupMethod name of
                Just _ -> T.pack clsName <> "_" <> T.pack name
                Nothing -> T.pack name
          emitCrossMethodTailCall targetLabel args

        -- Instance call: TCO to method on another object
        Just (SSAInstanceCall target method args) -> do
          let targetLabel = case target of
                SSAThis -> T.pack clsName <> "_" <> T.pack method
                _ -> case inferSSAExprClassWithCtx (Just clsName) syms typeEnv target of
                       Just cn -> T.pack cn <> "_" <> T.pack method
                       Nothing -> T.pack clsName <> "_" <> T.pack method
          emitInstanceTailCall target targetLabel args

        -- Non-call expression
        Just expr -> do
          emitExpr expr
          let retLabel = T.pack clsName <> "_" <> T.pack methName <> "_return"
          emit $ "    b " <> retLabel <> "\n"

        -- Void return
        Nothing -> do
          emit "    mov x0, #0\n"
          let retLabel = T.pack clsName <> "_" <> T.pack methName <> "_return"
          emit $ "    b " <> retLabel <> "\n"

--------------------------------------------------------------------------------
-- Expression Code Generation
--------------------------------------------------------------------------------

-- | Emit an SSA expression, result in X0
emitExpr :: SSAExpr -> ARMCodegen ()
emitExpr = \case
  SSAInt n ->
    emitLoadImm n "x0"

  SSABool b ->
    emit $ "    mov x0, #" <> (if b then "1" else "0") <> "\n"

  SSAStr s -> do
    strLabel <- freshLabel "str"
    addString strLabel (T.pack s)
    emit $ "    adrp x0, " <> strLabel <> "\n"
    emit $ "    add x0, x0, :lo12:" <> strLabel <> "\n"

  SSANull ->
    emit "    mov x0, xzr\n"

  SSAUse var -> do
    emitLoadVar (ssaVarStr var) X0

  SSAThis -> do
    emitLoadVar "this_0" X0

  SSAUnary op e -> do
    emitExpr e
    case op of
      Neg -> emit "    neg x0, x0\n"
      Not -> do
        emit "    cmp x0, #0\n"
        emit "    cset x0, eq\n"

  SSABinary op l r -> do
    case op of
      And -> emitShortCircuitAnd l r
      Or  -> emitShortCircuitOr l r
      _ -> do
        syms <- asks acgSymbols
        typeEnv <- asks acgTypeEnv
        clsName <- asks acgClassName
        let isStringExpr = isStringTyped syms typeEnv clsName l || isStringTyped syms typeEnv clsName r
        if isStringExpr
          then do
            emitExpr l
            emit "    str x0, [sp, #-16]!\n"
            emitExpr r
            emit "    mov x1, x0\n"
            emit "    ldr x0, [sp], #16\n"
            case op of
              Eq  -> emitStringCompare op
              Ne  -> emitStringCompare op
              Lt  -> emitStringCompare op
              Le  -> emitStringCompare op
              Gt  -> emitStringCompare op
              Ge  -> emitStringCompare op
              Add -> emitStringConcat
              _   -> emitBinaryOp op
          else emitOptimizedBinary op l r

  SSATernary cond thenE elseE ->
    if isSimpleExpr cond && isSimpleExpr thenE && isSimpleExpr elseE
    then emitCsel cond thenE elseE
    else do
      elseLabel <- freshLabel "else"
      endLabel <- freshLabel "endif"
      emitExpr cond
      emit $ "    cbz x0, " <> elseLabel <> "\n"
      emitExpr thenE
      emit $ "    b " <> endLabel <> "\n"
      emit $ elseLabel <> ":\n"
      emitExpr elseE
      emit $ endLabel <> ":\n"

  SSACall name args -> do
    emitStaticCall name args

  SSAInstanceCall target method args -> do
    emitInstanceCall target method args

  SSANewObject cn args -> do
    emitNewObject cn args

  SSAFieldAccess target field -> do
    emitFieldAccess target field

-- | Emit a binary operation (left in X0, right in X1, result in X0)
emitBinaryOp :: BinaryOp -> ARMCodegen ()
emitBinaryOp = \case
  Add -> emit "    add x0, x0, x1\n"
  Sub -> emit "    sub x0, x0, x1\n"
  Mul -> emit "    mul x0, x0, x1\n"

  Div -> emit "    sdiv x0, x0, x1\n"

  Mod -> do
    emit "    sdiv x2, x0, x1\n"     -- x2 = x0 / x1
    emit "    msub x0, x2, x1, x0\n" -- x0 = x0 - x2*x1

  Eq -> do
    emit "    cmp x0, x1\n"
    emit "    cset x0, eq\n"

  Ne -> do
    emit "    cmp x0, x1\n"
    emit "    cset x0, ne\n"

  Lt -> do
    emit "    cmp x0, x1\n"
    emit "    cset x0, lt\n"

  Le -> do
    emit "    cmp x0, x1\n"
    emit "    cset x0, le\n"

  Gt -> do
    emit "    cmp x0, x1\n"
    emit "    cset x0, gt\n"

  Ge -> do
    emit "    cmp x0, x1\n"
    emit "    cset x0, ge\n"

  And -> emit "    and x0, x0, x1\n"
  Or  -> emit "    orr x0, x0, x1\n"

  Concat -> do
    -- x0 = left, x1 = right (already in correct arg positions)
    emit "    bl __str_concat\n"

--------------------------------------------------------------------------------
-- Peephole-Optimized Binary Operations
--------------------------------------------------------------------------------

-- | Emit optimized binary operation with peephole patterns
emitOptimizedBinary :: BinaryOp -> SSAExpr -> SSAExpr -> ARMCodegen ()
emitOptimizedBinary op l r = case (op, l, r) of
  -- Multiply by power of 2: x * 2^n -> x << n
  (Mul, _, SSAInt n) | n > 0 && isPowerOf2 n -> do
    emitExpr l
    emit $ "    lsl x0, x0, #" <> tshow (countTrailingZeros n) <> "\n"

  (Mul, SSAInt n, _) | n > 0 && isPowerOf2 n -> do
    emitExpr r
    emit $ "    lsl x0, x0, #" <> tshow (countTrailingZeros n) <> "\n"

  -- Multiply by 3: x * 3 -> add x0, x0, x0, lsl #1
  (Mul, _, SSAInt 3) -> do
    emitExpr l
    emit "    add x0, x0, x0, lsl #1\n"

  (Mul, SSAInt 3, _) -> do
    emitExpr r
    emit "    add x0, x0, x0, lsl #1\n"

  -- Multiply by 5: x * 5 -> add x0, x0, x0, lsl #2
  (Mul, _, SSAInt 5) -> do
    emitExpr l
    emit "    add x0, x0, x0, lsl #2\n"

  (Mul, SSAInt 5, _) -> do
    emitExpr r
    emit "    add x0, x0, x0, lsl #2\n"

  -- Multiply by 9: x * 9 -> add x0, x0, x0, lsl #3
  (Mul, _, SSAInt 9) -> do
    emitExpr l
    emit "    add x0, x0, x0, lsl #3\n"

  (Mul, SSAInt 9, _) -> do
    emitExpr r
    emit "    add x0, x0, x0, lsl #3\n"

  -- Add/Sub 0: identity
  (Add, _, SSAInt 0) -> emitExpr l
  (Add, SSAInt 0, _) -> emitExpr r
  (Sub, _, SSAInt 0) -> emitExpr l

  -- Multiply by 0: result is 0
  (Mul, _, SSAInt 0) -> emit "    mov x0, xzr\n"
  (Mul, SSAInt 0, _) -> emit "    mov x0, xzr\n"

  -- Multiply by 1: identity
  (Mul, _, SSAInt 1) -> emitExpr l
  (Mul, SSAInt 1, _) -> emitExpr r

  -- Compare with 0: use cmp with zero register
  (Eq, _, SSAInt 0) -> do
    emitExpr l
    emit "    cmp x0, #0\n"
    emit "    cset x0, eq\n"

  (Eq, SSAInt 0, _) -> do
    emitExpr r
    emit "    cmp x0, #0\n"
    emit "    cset x0, eq\n"

  (Ne, _, SSAInt 0) -> do
    emitExpr l
    emit "    cmp x0, #0\n"
    emit "    cset x0, ne\n"

  (Ne, SSAInt 0, _) -> do
    emitExpr r
    emit "    cmp x0, #0\n"
    emit "    cset x0, ne\n"

  -- Add/Sub with small immediate: use immediate form
  (Add, _, SSAInt n) | n > 0 && n <= 4095 -> do
    emitExpr l
    emit $ "    add x0, x0, #" <> tshow n <> "\n"

  (Sub, _, SSAInt n) | n > 0 && n <= 4095 -> do
    emitExpr l
    emit $ "    sub x0, x0, #" <> tshow n <> "\n"

  -- Default: standard two-operand emission
  _ -> do
    emitExpr l
    emit "    str x0, [sp, #-16]!\n"   -- Push left
    emitExpr r
    emit "    mov x1, x0\n"            -- Right in X1
    emit "    ldr x0, [sp], #16\n"     -- Pop left into X0
    emitBinaryOp op

-- | Check if a number is a power of 2
isPowerOf2 :: Int -> Bool
isPowerOf2 n = n > 0 && popCount n == 1

--------------------------------------------------------------------------------
-- Conditional Select (ARM's cmov)
--------------------------------------------------------------------------------

-- | Check if an expression is simple enough for csel
isSimpleExpr :: SSAExpr -> Bool
isSimpleExpr = \case
  SSAInt _ -> True
  SSABool _ -> True
  SSANull -> True
  SSAUse _ -> True
  SSAThis -> True
  SSAFieldAccess SSAThis _ -> True
  SSAFieldAccess (SSAUse _) _ -> True
  SSAUnary _ (SSAInt _) -> True
  SSAUnary _ (SSABool _) -> True
  SSAUnary _ (SSAUse _) -> True
  _ -> False

-- | Emit conditional select: cond ? thenE : elseE
emitCsel :: SSAExpr -> SSAExpr -> SSAExpr -> ARMCodegen ()
emitCsel cond thenE elseE = do
  -- Evaluate else value
  emitExpr elseE
  emit "    str x0, [sp, #-16]!\n"   -- Save else

  -- Evaluate then value
  emitExpr thenE
  emit "    mov x1, x0\n"            -- Then in X1

  -- Evaluate condition
  emitExpr cond
  emit "    cmp x0, #0\n"

  -- Select result: if cond != 0, pick x1 (then), else pick stack (else)
  emit "    ldr x0, [sp], #16\n"     -- Else in X0
  emit "    csel x0, x1, x0, ne\n"   -- X0 = cond ? X1 : X0

-- | Check if an expression has string type
isStringTyped :: ProgramSymbols -> TypeEnv -> String -> SSAExpr -> Bool
isStringTyped syms typeEnv clsName expr = case expr of
  SSAStr _ -> True
  SSABinary Concat _ _ -> True
  _ -> case inferSSAExprTypeWithClass (Just clsName) syms typeEnv expr of
    Just (PrimitiveType TString) -> True
    _ -> False

-- | Emit string comparison (left in X0, right in X1)
emitStringCompare :: BinaryOp -> ARMCodegen ()
emitStringCompare op = do
  -- Call strcmp(left, right) - args already in x0, x1
  emit "    bl strcmp\n"
  -- strcmp returns int in w0 (32-bit)
  emit "    cmp w0, #0\n"
  case op of
    Eq -> emit "    cset x0, eq\n"
    Ne -> emit "    cset x0, ne\n"
    Lt -> emit "    cset x0, lt\n"
    Le -> emit "    cset x0, le\n"
    Gt -> emit "    cset x0, gt\n"
    Ge -> emit "    cset x0, ge\n"
    _  -> return ()

-- | Emit string concatenation (left in X0, right in X1)
emitStringConcat :: ARMCodegen ()
emitStringConcat = do
  -- Args already in correct positions
  emit "    bl __str_concat\n"

-- | Short-circuit AND
emitShortCircuitAnd :: SSAExpr -> SSAExpr -> ARMCodegen ()
emitShortCircuitAnd l r = do
  falseLabel <- freshLabel "and_false"
  endLabel <- freshLabel "and_end"
  emitExpr l
  emit $ "    cbz x0, " <> falseLabel <> "\n"
  emitExpr r
  emit $ "    cbz x0, " <> falseLabel <> "\n"
  emit "    mov x0, #1\n"
  emit $ "    b " <> endLabel <> "\n"
  emit $ falseLabel <> ":\n"
  emit "    mov x0, xzr\n"
  emit $ endLabel <> ":\n"

-- | Short-circuit OR
emitShortCircuitOr :: SSAExpr -> SSAExpr -> ARMCodegen ()
emitShortCircuitOr l r = do
  trueLabel <- freshLabel "or_true"
  endLabel <- freshLabel "or_end"
  emitExpr l
  emit $ "    cbnz x0, " <> trueLabel <> "\n"
  emitExpr r
  emit $ "    cbnz x0, " <> trueLabel <> "\n"
  emit "    mov x0, xzr\n"
  emit $ "    b " <> endLabel <> "\n"
  emit $ trueLabel <> ":\n"
  emit "    mov x0, #1\n"
  emit $ endLabel <> ":\n"

--------------------------------------------------------------------------------
-- Tail Call Optimization
--------------------------------------------------------------------------------

-- | Emit a self-recursive tail call (to same method)
emitSelfTailCall :: [SSAExpr] -> ARMCodegen ()
emitSelfTailCall args = do
  methodSym <- asks acgMethodSymbol
  let params = msParams methodSym
      explicitParams = drop 1 params
      explicitParamNames = map (\p -> vsName p ++ "_0") explicitParams

  -- Evaluate all arguments first and push on stack
  forM_ (reverse args) $ \arg -> do
    emitExpr arg
    emit "    str x0, [sp, #-16]!\n"

  -- Pop into parameter locations
  forM_ explicitParamNames $ \paramName -> do
    emit "    ldr x0, [sp], #16\n"
    emitStoreVar X0 paramName

  -- Jump to TCO entry point
  clsName <- asks acgClassName
  methName <- asks acgMethodName
  let tcoLabel = T.pack clsName <> "_" <> T.pack methName <> "_tco"
  emit $ "    b " <> tcoLabel <> "\n"

-- | Emit a cross-method tail call
emitCrossMethodTailCall :: Text -> [SSAExpr] -> ARMCodegen ()
emitCrossMethodTailCall targetLabel args = do
  -- 1. Push 'this' temporarily
  emitLoadVar "this_0" X0
  emit "    str x0, [sp, #-16]!\n"

  -- 2. Evaluate all arguments and push them
  forM_ (reverse args) $ \arg -> do
    emitExpr arg
    emit "    str x0, [sp, #-16]!\n"

  -- 3. Pop args into arg registers (X1, X2, ..., before epilogue)
  let nArgs = length args
      armArgRegs = take nArgs [X1, X2, X3, X4, X5, X6, X7]
  forM_ armArgRegs $ \reg ->
    emit $ "    ldr " <> regName reg <> ", [sp], #16\n"
  emit "    ldr x0, [sp], #16\n"  -- 'this' into X0

  -- 4. Epilogue
  alloc <- asks acgRegAlloc
  let usedCallee = usedCalleeRegs alloc
  emitPopCalleeSaved usedCallee

  frameSize <- gets acgFrameSize
  emitAddSP frameSize
  emit "    ldp x29, x30, [sp], #16\n"

  -- 5. Jump to target method
  emit $ "    b " <> targetLabel <> "\n"

-- | Emit an instance method tail call
emitInstanceTailCall :: SSAExpr -> Text -> [SSAExpr] -> ARMCodegen ()
emitInstanceTailCall target targetLabel args = do
  -- 1. Evaluate target and push
  emitExpr target
  emit "    str x0, [sp, #-16]!\n"

  -- 2. Evaluate all arguments and push
  forM_ (reverse args) $ \arg -> do
    emitExpr arg
    emit "    str x0, [sp, #-16]!\n"

  -- 3. Pop args into registers
  let nArgs = length args
      armArgRegs = take nArgs [X1, X2, X3, X4, X5, X6, X7]
  forM_ armArgRegs $ \reg ->
    emit $ "    ldr " <> regName reg <> ", [sp], #16\n"
  emit "    ldr x0, [sp], #16\n"  -- target into X0

  -- 4. Epilogue
  alloc <- asks acgRegAlloc
  let usedCallee = usedCalleeRegs alloc
  emitPopCalleeSaved usedCallee

  frameSize <- gets acgFrameSize
  emitAddSP frameSize
  emit "    ldp x29, x30, [sp], #16\n"

  -- 5. Jump to target
  emit $ "    b " <> targetLabel <> "\n"

--------------------------------------------------------------------------------
-- Function Calls
--------------------------------------------------------------------------------

-- | Emit a static method call
emitStaticCall :: String -> [SSAExpr] -> ARMCodegen ()
emitStaticCall name args = do
  -- Evaluate arguments and push on stack
  forM_ (reverse args) $ \arg -> do
    emitExpr arg
    emit "    str x0, [sp, #-16]!\n"

  -- Pop args into registers (X1, X2, X3, ...)
  let nArgs = length args
      armArgRegs = take nArgs [X1, X2, X3, X4, X5, X6, X7]
  forM_ armArgRegs $ \reg -> do
    emit $ "    ldr " <> regName reg <> ", [sp], #16\n"

  -- Load 'this' into X0
  emitLoadVar "this_0" X0

  -- Call the method
  clsName <- asks acgClassName
  syms <- asks acgSymbols
  let methodLabel = case lookupClass clsName syms >>= lookupMethod name of
        Just _ -> T.pack clsName <> "_" <> T.pack name
        Nothing -> T.pack name
  emit $ "    bl " <> methodLabel <> "\n"

-- | Emit an instance method call
emitInstanceCall :: SSAExpr -> String -> [SSAExpr] -> ARMCodegen ()
emitInstanceCall target method args = do
  -- Evaluate target (this pointer)
  emitExpr target
  emit "    str x0, [sp, #-16]!\n"  -- Save target

  -- Evaluate arguments and push them
  forM_ (reverse args) $ \arg -> do
    emitExpr arg
    emit "    str x0, [sp, #-16]!\n"

  -- Pop args into registers (X1, X2, ...)
  let nArgs = length args
      armArgRegs = take nArgs [X1, X2, X3, X4, X5, X6, X7]
  forM_ armArgRegs $ \reg -> do
    emit $ "    ldr " <> regName reg <> ", [sp], #16\n"

  -- Pop target into X0
  emit "    ldr x0, [sp], #16\n"

  -- Determine method label
  syms <- asks acgSymbols
  typeEnv <- asks acgTypeEnv
  className <- asks acgClassName
  let methodLabel = case target of
        SSAThis -> T.pack className <> "_" <> T.pack method
        _ -> case inferSSAExprClassWithCtx (Just className) syms typeEnv target of
               Just cn -> T.pack cn <> "_" <> T.pack method
               Nothing -> T.pack className <> "_" <> T.pack method

  emit $ "    bl " <> methodLabel <> "\n"

-- | Emit object allocation
emitNewObject :: String -> [SSAExpr] -> ARMCodegen ()
emitNewObject cn args = do
  syms <- asks acgSymbols
  cs <- case lookupClass cn syms of
    Just cs -> return cs
    Nothing -> throwError $ D.ResolveError ("Unknown class: " ++ cn) 0 0

  let nFields = length (csFieldOrder cs)
      hasCtor = isJust (lookupMethod cn cs)

  -- Allocate object: malloc(nFields * 8)
  emitLoadImm (nFields * 8) "x0"
  emit "    bl malloc\n"
  -- X0 = object pointer

  -- Initialize fields to 0
  when (nFields > 0) $ do
    emit "    str x0, [sp, #-16]!\n"  -- Save object pointer
    -- memset(ptr, 0, size)
    emit "    mov x1, #0\n"
    emitLoadImm (nFields * 8) "x2"
    emit "    bl memset\n"
    emit "    ldr x0, [sp], #16\n"    -- Restore object pointer

  -- Call constructor if present
  when hasCtor $ do
    emit "    str x0, [sp, #-16]!\n"  -- Save object for return

    -- Evaluate all constructor args and push
    forM_ (reverse args) $ \arg -> do
      emitExpr arg
      emit "    str x0, [sp, #-16]!\n"

    -- Pop args into registers: this in X0, args in X1, X2, ...
    let ctorArgRegs = take (length args) [X1, X2, X3, X4, X5, X6, X7]
    forM_ ctorArgRegs $ \reg -> do
      emit $ "    ldr " <> regName reg <> ", [sp], #16\n"

    -- Load 'this' from saved position
    emit "    ldr x0, [sp]\n"

    let ctorLabel = T.pack cn <> "_" <> T.pack cn
    emit $ "    bl " <> ctorLabel <> "\n"

    emit "    ldr x0, [sp], #16\n"    -- Return object pointer

-- | Emit field access
emitFieldAccess :: SSAExpr -> String -> ARMCodegen ()
emitFieldAccess target field = do
  emitExpr target  -- Object pointer in X0

  syms <- asks acgSymbols
  typeEnv <- asks acgTypeEnv
  className <- asks acgClassName

  let targetClass = case target of
        SSAThis -> Just className
        _ -> inferSSAExprClassWithCtx (Just className) syms typeEnv target

      offset = fromMaybe 0 $ do
        cn <- targetClass
        cs <- lookupClass cn syms
        fieldOffset field cs

  emit $ "    ldr x0, [x0, #" <> tshow (offset * 8) <> "]\n"

--------------------------------------------------------------------------------
-- Phi Node Handling
--------------------------------------------------------------------------------

-- | Emit parallel copies for phi nodes.
emitParallelCopies :: [(String, String)] -> ARMCodegen ()
emitParallelCopies [] = return ()
emitParallelCopies copies = do
  -- Phase 1: Push all source values
  forM_ copies $ \(_dest, src) -> do
    emitLoadVar src X0
    emit "    str x0, [sp, #-16]!\n"

  -- Phase 2: Pop values into destinations (in reverse order)
  forM_ (reverse copies) $ \(dest, _src) -> do
    emit "    ldr x0, [sp], #16\n"
    emitStoreVar X0 dest

-- | Compute phi copies
computePhiCopies :: CFG -> [SSABlock] -> Map BlockId [(BlockId, String, String)]
computePhiCopies cfg blocks =
  let phiCopyList = concatMap (blockPhiCopies cfg) blocks
  in foldl' addCopy Map.empty phiCopyList
  where
    addCopy m (srcBlock, targetBlock, destVar, srcVar) =
      Map.insertWith (++) srcBlock [(targetBlock, destVar, srcVar)] m

blockPhiCopies :: CFG -> SSABlock -> [(BlockId, BlockId, String, String)]
blockPhiCopies _cfg SSABlock{..} =
  [ (predBlock, blockLabel, ssaVarStr (phiVar phi), ssaVarStr srcVar)
  | phi <- blockPhis
  , (predBlock, srcVar) <- phiArgs phi
  ]

--------------------------------------------------------------------------------
-- Immediate Loading
--------------------------------------------------------------------------------

-- | Emit code to load an immediate value into a register
emitLoadImm :: Int -> Text -> ARMCodegen ()
emitLoadImm n reg
  | n >= 0 && n <= 65535 =
      emit $ "    mov " <> reg <> ", #" <> tshow n <> "\n"
  | n >= -65536 && n < 0 =
      emit $ "    mov " <> reg <> ", #" <> tshow n <> "\n"
  | otherwise = do
      -- Use movz + movk sequence for larger values
      let w0 = n .&. 0xFFFF
          w1 = (n `shiftR` 16) .&. 0xFFFF
          w2 = (n `shiftR` 32) .&. 0xFFFF
          w3 = (n `shiftR` 48) .&. 0xFFFF
      if n < 0
        then do
          -- For negative numbers, use literal pool
          emit $ "    ldr " <> reg <> ", =" <> tshow n <> "\n"
        else do
          emit $ "    movz " <> reg <> ", #" <> tshow w0 <> "\n"
          when (w1 /= 0) $
            emit $ "    movk " <> reg <> ", #" <> tshow w1 <> ", lsl #16\n"
          when (w2 /= 0) $
            emit $ "    movk " <> reg <> ", #" <> tshow w2 <> ", lsl #32\n"
          when (w3 /= 0) $
            emit $ "    movk " <> reg <> ", #" <> tshow w3 <> ", lsl #48\n"

--------------------------------------------------------------------------------
-- Stack Pointer Manipulation
--------------------------------------------------------------------------------

-- | Subtract from stack pointer (allocate frame)
emitSubSP :: Int -> ARMCodegen ()
emitSubSP 0 = return ()
emitSubSP n
  | n > 0 && n <= 4095 =
      emit $ "    sub sp, sp, #" <> tshow n <> "\n"
  | n > 4095 = do
      emitLoadImm n "x16"
      emit "    sub sp, sp, x16\n"
  | otherwise = return ()

-- | Add to stack pointer (deallocate frame)
emitAddSP :: Int -> ARMCodegen ()
emitAddSP 0 = return ()
emitAddSP n
  | n > 0 && n <= 4095 =
      emit $ "    add sp, sp, #" <> tshow n <> "\n"
  | n > 4095 = do
      emitLoadImm n "x16"
      emit "    add sp, sp, x16\n"
  | otherwise = return ()

--------------------------------------------------------------------------------
-- Callee-Saved Register Save/Restore
--------------------------------------------------------------------------------

-- | Push callee-saved registers (in pairs for alignment)
emitPushCalleeSaved :: [ARMReg] -> ARMCodegen ()
emitPushCalleeSaved regs = forM_ (pairUp regs) $ \case
  (r1, Just r2) ->
    emit $ "    stp " <> regName r1 <> ", " <> regName r2 <> ", [sp, #-16]!\n"
  (r1, Nothing) ->
    emit $ "    str " <> regName r1 <> ", [sp, #-16]!\n"

-- | Pop callee-saved registers (in reverse pairs)
emitPopCalleeSaved :: [ARMReg] -> ARMCodegen ()
emitPopCalleeSaved regs = forM_ (reverse $ pairUp regs) $ \case
  (r1, Just r2) ->
    emit $ "    ldp " <> regName r1 <> ", " <> regName r2 <> ", [sp], #16\n"
  (r1, Nothing) ->
    emit $ "    ldr " <> regName r1 <> ", [sp], #16\n"

-- | Pair up a list: [a,b,c,d,e] -> [(a,Just b), (c,Just d), (e,Nothing)]
pairUp :: [a] -> [(a, Maybe a)]
pairUp [] = []
pairUp [x] = [(x, Nothing)]
pairUp (x:y:rest) = (x, Just y) : pairUp rest

--------------------------------------------------------------------------------
-- Variable Access
--------------------------------------------------------------------------------

-- | Get stack slot for a variable (offset from FP)
getVarSlot :: String -> ARMCodegen Int
getVarSlot name = do
  slots <- gets acgVarSlots
  case Map.lookup name slots of
    Just slot -> return slot
    Nothing -> throwError $ D.ResolveError ("Unknown variable: " ++ name) 0 0

-- | Get the location of a variable (register or stack)
getVarLoc :: String -> ARMCodegen VarLocation
getVarLoc name = do
  alloc <- asks acgRegAlloc
  case getVarLocation name alloc of
    Just loc -> return loc
    Nothing -> do
      let baseName = extractBaseName name
      slot <- getVarSlot baseName
      return $ OnStack slot

-- | Extract base name from versioned SSA name
extractBaseName :: String -> String
extractBaseName name =
  case break (== '_') (reverse name) of
    (versionRev, '_':baseRev)
      | not (null versionRev) && all isDigit versionRev -> reverse baseRev
    _ -> name

-- | Emit load from variable location to register
emitLoadVar :: String -> ARMReg -> ARMCodegen ()
emitLoadVar name destReg = do
  loc <- getVarLoc name
  case loc of
    InReg srcReg | srcReg == destReg -> return ()
    InReg srcReg ->
      emit $ "    mov " <> regName destReg <> ", " <> regName srcReg <> "\n"
    OnStack slot -> emitLoadFromSlot slot destReg

-- | Emit store from register to variable location
emitStoreVar :: ARMReg -> String -> ARMCodegen ()
emitStoreVar srcReg name = do
  loc <- getVarLoc name
  case loc of
    InReg destReg | destReg == srcReg -> return ()
    InReg destReg ->
      emit $ "    mov " <> regName destReg <> ", " <> regName srcReg <> "\n"
    OnStack slot -> emitStoreToSlot srcReg slot

-- | Load from a stack slot (FP-relative) into a register
emitLoadFromSlot :: Int -> ARMReg -> ARMCodegen ()
emitLoadFromSlot slot destReg = do
  let offset = (slot + 1) * 8
  if offset <= 255
    then emit $ "    ldur " <> regName destReg <> ", [x29, #-" <> tshow offset <> "]\n"
    else do
      emitLoadImm offset "x16"
      emit $ "    sub x16, x29, x16\n"
      emit $ "    ldr " <> regName destReg <> ", [x16]\n"

-- | Store a register value to a stack slot (FP-relative)
emitStoreToSlot :: ARMReg -> Int -> ARMCodegen ()
emitStoreToSlot srcReg slot = do
  let offset = (slot + 1) * 8
  if offset <= 255
    then emit $ "    stur " <> regName srcReg <> ", [x29, #-" <> tshow offset <> "]\n"
    else do
      emitLoadImm offset "x16"
      emit $ "    sub x16, x29, x16\n"
      emit $ "    str " <> regName srcReg <> ", [x16]\n"

--------------------------------------------------------------------------------
-- Utilities
--------------------------------------------------------------------------------

-- | Emit text
emit :: Text -> ARMCodegen ()
emit t = modify $ \s -> s { acgCode = acgCode s <> B.fromText t }

-- | Add a string literal to be emitted in .rodata
addString :: Text -> Text -> ARMCodegen ()
addString label content = modify $ \s -> s { acgStrings = (label, content) : acgStrings s }

-- | Generate a fresh label
freshLabel :: Text -> ARMCodegen Text
freshLabel prefix = do
  st <- get
  let n = acgLabelCounter st
  put st { acgLabelCounter = n + 1 }
  clsName <- asks acgClassName
  methName <- asks acgMethodName
  return $ ".L" <> T.pack clsName <> "_" <> T.pack methName <> "_" <> prefix <> "_" <> T.pack (show n)

-- | Get block label
blockLabelText :: BlockId -> ARMCodegen Text
blockLabelText bid = do
  clsName <- asks acgClassName
  methName <- asks acgMethodName
  return $ ".L" <> T.pack clsName <> "_" <> T.pack methName <> "_" <> T.pack (blockIdName bid)

tshow :: Show a => a -> Text
tshow = T.pack . show
