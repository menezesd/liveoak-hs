{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE OverloadedStrings #-}

-- | x86_64 code generation from SSA form.
-- Generates GAS (GNU Assembler) syntax for Linux x86_64.
module LiveOak.X86Codegen
  ( -- * Code Generation
    generateX86FromSSA
  , generateMethodX86
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
import LiveOak.X86
import LiveOak.X86Runtime (emitX86Runtime)
import LiveOak.X86Liveness (computeLiveness, buildIntervals)
import LiveOak.X86RegAlloc (RegAllocation(..), VarLocation(..), allocateRegisters, getVarLocation, usedCalleeRegs)

--------------------------------------------------------------------------------
-- Code Generation Types
--------------------------------------------------------------------------------

-- | Code generation state
data X86CodegenState = X86CodegenState
  { xcgLabelCounter :: !Int
  , xcgCode :: !Builder
  , xcgVarSlots :: !(Map String Int)  -- ^ Stack slot offset for each SSA variable (relative to RBP)
  , xcgFrameSize :: !Int              -- ^ Total frame size (for alignment)
  , xcgStrings :: ![(Text, Text)]     -- ^ String literals: (label, content)
  }

-- | Code generation context
data X86CodegenCtx = X86CodegenCtx
  { xcgSymbols :: !ProgramSymbols
  , xcgClassName :: !String
  , xcgMethodName :: !String
  , xcgMethodSymbol :: !MethodSymbol
  , xcgCFG :: !CFG
  , xcgPhiCopies :: !(Map BlockId [(BlockId, String, String)])
  , xcgTypeEnv :: !TypeEnv
  , xcgLocalCount :: !Int
  , xcgRegAlloc :: !RegAllocation           -- ^ Register allocation result
  }

type X86Codegen a = ReaderT X86CodegenCtx (StateT X86CodegenState (Either Diag)) a

--------------------------------------------------------------------------------
-- Code Generation Entry Points
--------------------------------------------------------------------------------

-- | Generate x86_64 assembly from an SSA program
generateX86FromSSA :: SSAProgram -> ProgramSymbols -> Result Text
generateX86FromSSA (SSAProgram classes) syms = do
  -- Generate data section (string literals would go here)
  let dataSection = generateDataSection

  -- Generate text section with all methods
  codes <- forM classes $ \cls ->
    forM (ssaClassMethods cls) $ \method ->
      generateMethodX86 syms (ssaClassName cls) method

  -- Generate runtime support (convert instructions to text)
  let runtime = T.unlines $ map instrText emitX86Runtime

  -- Generate entry point (main)
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
    , "# Program entry point"
    , ".globl main"
    , "main:"
    , "    pushq %rbp"
    , "    movq %rsp, %rbp"
    , ""
    , "    # Allocate Main object"
    , "    movq $" <> tshow (mainFields * 8) <> ", %rdi"
    , "    call malloc"
    , ""
    , "    # Call Main.main with Main object as 'this'"
    , "    movq %rax, %rdi"
    , "    call Main_main"
    , ""
    , "    # Exit with return value"
    , "    movq %rax, %rdi"
    , "    call exit"
    ]

--------------------------------------------------------------------------------
-- Method Code Generation
--------------------------------------------------------------------------------

-- | Generate x86_64 code for a single method
generateMethodX86 :: ProgramSymbols -> String -> SSAMethod -> Result Text
generateMethodX86 syms clsName method@SSAMethod{..} = do
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

      -- Compute variable slots
      -- Parameters come in registers (System V ABI), we'll copy them to stack
      -- Locals start at -8(%rbp), -16(%rbp), etc.
      totalParams = numParams methodSymbol
      baseLocalCount = numLocals methodSymbol

      -- Collect all SSA variable BASE names (without version suffix)
      -- All versions of a variable share the same stack slot
      allVarBases = collectAllVars ssaMethodBlocks

      -- Parameter and local base names
      paramNames = Set.fromList $ map vsName (msParams methodSymbol)
      localNames = Set.fromList $ map vsName (msLocals methodSymbol)
      baseNames = Set.union paramNames localNames

      -- Extra SSA variables (not in params or locals)
      extraVars = sort $ Set.toList $ Set.difference allVarBases baseNames

      -- Assign stack slots using BASE names (all versions share same slot)
      -- Slot i means offset -(i+1)*8 from RBP
      paramSlots = Map.fromList $ zip (map vsName (msParams methodSymbol)) [0..]
      localSlots = Map.fromList $ zip (map vsName (msLocals methodSymbol)) [totalParams..]
      extraSlots = Map.fromList $ zip extraVars [totalParams + baseLocalCount..]

      varSlots = Map.unions [paramSlots, localSlots, extraSlots]
      totalVars = totalParams + baseLocalCount + length extraVars

      -- Frame size: 8 bytes per variable, aligned to 16 bytes
      rawFrameSize = totalVars * 8
      frameSize = ((rawFrameSize + 15) `div` 16) * 16

      ctx = X86CodegenCtx
        { xcgSymbols = syms
        , xcgClassName = clsName
        , xcgMethodName = methodNameStr
        , xcgMethodSymbol = methodSymbol
        , xcgCFG = cfg
        , xcgPhiCopies = phiCopies
        , xcgTypeEnv = typeEnv
        , xcgLocalCount = totalVars
        , xcgRegAlloc = regAlloc
        }

      initState = X86CodegenState
        { xcgLabelCounter = 0
        , xcgCode = mempty
        , xcgVarSlots = varSlots
        , xcgFrameSize = frameSize
        , xcgStrings = []
        }

  (_, finalState) <- runStateT (runReaderT (emitMethodX86 method) ctx) initState
  let code = TL.toStrict $ B.toLazyText $ xcgCode finalState
      -- Emit string literals in rodata section, then switch back to text
      strData = if null (xcgStrings finalState)
                then ""
                else T.unlines $ [".section .rodata"] ++
                     [lbl <> ":\n    .asciz \"" <> escapeStr s <> "\""
                     | (lbl, s) <- reverse (xcgStrings finalState)] ++
                     [".section .text"]  -- Switch back to text for next method
  return $ code <> strData
  where
    escapeStr = T.concatMap (\c -> case c of
      '\n' -> "\\n"
      '\t' -> "\\t"
      '\r' -> "\\r"
      '"'  -> "\\\""
      '\\' -> "\\\\"
      _    -> T.singleton c)

-- | Emit x86_64 code for a method
emitMethodX86 :: SSAMethod -> X86Codegen ()
emitMethodX86 SSAMethod{..} = do
  clsName <- asks xcgClassName
  let label = T.pack clsName <> "_" <> T.pack (methodNameString ssaMethodName)

  -- Method label (make global for linking)
  emit $ "\n.globl " <> label <> "\n"
  emit $ label <> ":\n"

  -- Prologue
  emit "    pushq %rbp\n"
  emit "    movq %rsp, %rbp\n"

  -- Allocate stack frame
  frameSize <- gets xcgFrameSize
  when (frameSize > 0) $
    emit $ "    subq $" <> tshow frameSize <> ", %rsp\n"

  -- Save callee-saved registers that we use
  alloc <- asks xcgRegAlloc
  let usedCallee = usedCalleeRegs alloc
  forM_ usedCallee $ \reg ->
    emit $ "    pushq " <> regName reg <> "\n"

  -- Save arguments from registers to their allocated locations
  -- System V ABI: RDI, RSI, RDX, RCX, R8, R9
  -- Parameters are stored with version 0 (initial SSA version)
  methodSym <- asks xcgMethodSymbol
  let params = msParams methodSym
      argRegsUsed = zip params [RDI, RSI, RDX, RCX, R8, R9]
  forM_ argRegsUsed $ \(param, reg) -> do
    emitStoreVar reg (vsName param ++ "_0")

  -- TCO entry point (after prologue)
  let tcoLabel = label <> "_tco"
  emit $ tcoLabel <> ":\n"

  -- Emit blocks in reverse postorder
  cfg <- asks xcgCFG
  let blockOrder = reversePostorder cfg
  forM_ blockOrder $ \bid ->
    forM_ (getBlock cfg bid) emitBlock

  -- Return label
  let returnLabel = label <> "_return"
  emit $ returnLabel <> ":\n"

  -- Epilogue: restore callee-saved registers in reverse order
  forM_ (reverse usedCallee) $ \reg ->
    emit $ "    popq " <> regName reg <> "\n"

  -- Restore stack pointer and base pointer
  when (frameSize > 0) $
    emit $ "    addq $" <> tshow frameSize <> ", %rsp\n"
  emit "    popq %rbp\n"
  emit "    ret\n"

-- | Convert an SSAVar to a versioned string identifier (matches X86Liveness.varStr)
-- Used for register allocation which tracks individual SSA versions
ssaVarStr :: SSAVar -> String
ssaVarStr v = varNameString (ssaName v) ++ "_" ++ show (ssaVersion v)

-- | Convert an SSAVar to its base name (without version)
-- Used for stack slot allocation where all versions share a slot
ssaVarBase :: SSAVar -> String
ssaVarBase v = varNameString (ssaName v)

-- | Collect all variable BASE names from blocks (for stack slot allocation)
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
emitBlock :: CFGBlock -> X86Codegen ()
emitBlock CFGBlock{..} = do
  blockLabel <- blockLabelText cfgBlockId
  emit $ blockLabel <> ":\n"

  -- Emit instructions
  forM_ cfgInstrs emitInstr

  -- Emit terminator
  emitTerminator cfgBlockId cfgTerm

-- | Emit an SSA instruction
emitInstr :: SSAInstr -> X86Codegen ()
emitInstr = \case
  SSAAssign var expr -> do
    emitExpr expr  -- Result in RAX
    emitStoreVar RAX (ssaVarStr var)

  SSAFieldStore target _field off value -> do
    emitExpr target
    emit "    pushq %rax\n"  -- Save target pointer
    emitExpr value
    emit "    popq %rcx\n"   -- Restore target to RCX
    emit $ "    movq %rax, " <> tshow (off * 8) <> "(%rcx)\n"

  SSAReturn exprOpt -> do
    case exprOpt of
      Just expr -> emitExpr expr  -- Result in RAX
      Nothing -> emit "    xorq %rax, %rax\n"  -- Return 0

  SSAJump _ -> return ()  -- Handled by terminator

  SSABranch _ _ _ -> return ()  -- Handled by terminator

  SSAExprStmt expr -> do
    emitExpr expr  -- Result discarded

-- | Emit a block terminator
emitTerminator :: BlockId -> Terminator -> X86Codegen ()
emitTerminator currentBlock term = do
  phiCopies <- asks xcgPhiCopies
  let copies = lookupList currentBlock phiCopies

  case term of
    TermJump target -> do
      -- Insert phi copies using parallel copy semantics
      let targetCopies = [(d, s) | (t, d, s) <- copies, t == target]
      emitParallelCopies targetCopies
      targetLabel <- blockLabelText target
      emit $ "    jmp " <> targetLabel <> "\n"

    TermBranch cond thenBlock elseBlock -> do
      emitExpr cond
      emit "    testq %rax, %rax\n"

      -- Generate labels for phi copy blocks
      thenCopyLabel <- freshLabel "then_copy"
      elseCopyLabel <- freshLabel "else_copy"

      -- Jump to else if zero
      emit $ "    jz " <> elseCopyLabel <> "\n"

      -- Then branch copies using parallel copy semantics
      emit $ thenCopyLabel <> ":\n"
      let thenCopies = [(d, s) | (t, d, s) <- copies, t == thenBlock]
      emitParallelCopies thenCopies
      thenLabel <- blockLabelText thenBlock
      emit $ "    jmp " <> thenLabel <> "\n"

      -- Else branch copies using parallel copy semantics
      emit $ elseCopyLabel <> ":\n"
      let elseCopies = [(d, s) | (t, d, s) <- copies, t == elseBlock]
      emitParallelCopies elseCopies
      elseLabel <- blockLabelText elseBlock
      emit $ "    jmp " <> elseLabel <> "\n"

    TermReturn exprOpt -> do
      clsName <- asks xcgClassName
      methName <- asks xcgMethodName
      syms <- asks xcgSymbols
      typeEnv <- asks xcgTypeEnv
      case exprOpt of
        -- Self-recursive tail call: same method in same class
        Just (SSACall name args) | name == methName -> do
          case lookupClass clsName syms >>= lookupMethod name of
            Just _ -> emitSelfTailCall args
            Nothing -> do
              -- Not a method in this class, use cross-method TCO
              let targetLabel = T.pack name
              emitCrossMethodTailCall targetLabel args

        -- Self-recursive instance call on 'this'
        Just (SSAInstanceCall SSAThis method args) | method == methName ->
          emitSelfTailCall args

        -- Cross-method static call: TCO to different method
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

        -- Non-call expression: evaluate and return
        Just expr -> do
          emitExpr expr
          let retLabel = T.pack clsName <> "_" <> T.pack methName <> "_return"
          emit $ "    jmp " <> retLabel <> "\n"

        -- Void return
        Nothing -> do
          emit "    xorq %rax, %rax\n"
          let retLabel = T.pack clsName <> "_" <> T.pack methName <> "_return"
          emit $ "    jmp " <> retLabel <> "\n"

--------------------------------------------------------------------------------
-- Expression Code Generation
--------------------------------------------------------------------------------

-- | Emit an SSA expression, result in RAX
emitExpr :: SSAExpr -> X86Codegen ()
emitExpr = \case
  SSAInt n ->
    emit $ "    movq $" <> tshow n <> ", %rax\n"

  SSABool b ->
    emit $ "    movq $" <> (if b then "1" else "0") <> ", %rax\n"

  SSAStr s -> do
    -- Emit string as a static label in .rodata section
    strLabel <- freshLabel "str"
    addString strLabel (T.pack s)
    emit $ "    leaq " <> strLabel <> "(%rip), %rax\n"

  SSANull ->
    emit "    xorq %rax, %rax\n"

  SSAUse var -> do
    emitLoadVar (ssaVarStr var) RAX

  SSAThis -> do
    emitLoadVar "this_0" RAX

  SSAUnary op e -> do
    emitExpr e
    case op of
      Neg -> emit "    negq %rax\n"
      Not -> do
        emit "    testq %rax, %rax\n"
        emit "    sete %al\n"
        emit "    movzbl %al, %eax\n"

  SSABinary op l r -> do
    case op of
      And -> emitShortCircuitAnd l r
      Or  -> emitShortCircuitOr l r
      _ -> do
        emitExpr l
        emit "    pushq %rax\n"
        emitExpr r
        emit "    movq %rax, %rcx\n"  -- Right operand in RCX
        emit "    popq %rax\n"        -- Left operand in RAX
        -- Check if this is a string operation using type inference
        syms <- asks xcgSymbols
        typeEnv <- asks xcgTypeEnv
        clsName <- asks xcgClassName
        let isStringExpr = isStringTyped syms typeEnv clsName l || isStringTyped syms typeEnv clsName r
        if isStringExpr
          then case op of
            Eq -> emitStringCompare op
            Ne -> emitStringCompare op
            Lt -> emitStringCompare op
            Le -> emitStringCompare op
            Gt -> emitStringCompare op
            Ge -> emitStringCompare op
            Add -> emitStringConcat  -- String concatenation uses Add
            _ -> emitBinaryOp op
          else emitBinaryOp op

  SSATernary cond thenE elseE -> do
    elseLabel <- freshLabel "else"
    endLabel <- freshLabel "endif"
    emitExpr cond
    emit "    testq %rax, %rax\n"
    emit $ "    jz " <> elseLabel <> "\n"
    emitExpr thenE
    emit $ "    jmp " <> endLabel <> "\n"
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

-- | Emit a binary operation (operands: RAX op RCX, result in RAX)
emitBinaryOp :: BinaryOp -> X86Codegen ()
emitBinaryOp = \case
  Add -> emit "    addq %rcx, %rax\n"
  Sub -> emit "    subq %rcx, %rax\n"
  Mul -> emit "    imulq %rcx, %rax\n"

  Div -> do
    emit "    cqo\n"              -- Sign-extend RAX into RDX:RAX
    emit "    idivq %rcx\n"       -- RAX = quotient

  Mod -> do
    emit "    cqo\n"
    emit "    idivq %rcx\n"
    emit "    movq %rdx, %rax\n"  -- RDX = remainder

  Eq -> do
    emit "    cmpq %rcx, %rax\n"
    emit "    sete %al\n"
    emit "    movzbl %al, %eax\n"

  Ne -> do
    emit "    cmpq %rcx, %rax\n"
    emit "    setne %al\n"
    emit "    movzbl %al, %eax\n"

  Lt -> do
    emit "    cmpq %rcx, %rax\n"
    emit "    setl %al\n"
    emit "    movzbl %al, %eax\n"

  Le -> do
    emit "    cmpq %rcx, %rax\n"
    emit "    setle %al\n"
    emit "    movzbl %al, %eax\n"

  Gt -> do
    emit "    cmpq %rcx, %rax\n"
    emit "    setg %al\n"
    emit "    movzbl %al, %eax\n"

  Ge -> do
    emit "    cmpq %rcx, %rax\n"
    emit "    setge %al\n"
    emit "    movzbl %al, %eax\n"

  And -> emit "    andq %rcx, %rax\n"
  Or  -> emit "    orq %rcx, %rax\n"

  Concat -> do
    -- String concatenation: call runtime helper
    emit "    movq %rax, %rdi\n"
    emit "    movq %rcx, %rsi\n"
    emit "    call __str_concat\n"

-- | Check if an expression has string type using type inference
isStringTyped :: ProgramSymbols -> TypeEnv -> String -> SSAExpr -> Bool
isStringTyped syms typeEnv clsName expr = case expr of
  SSAStr _ -> True
  SSABinary Concat _ _ -> True
  _ -> case inferSSAExprTypeWithClass (Just clsName) syms typeEnv expr of
    Just (PrimitiveType TString) -> True
    _ -> False

-- | Emit string comparison (left in RAX, right in RCX)
emitStringCompare :: BinaryOp -> X86Codegen ()
emitStringCompare op = do
  -- Call strcmp(left, right)
  emit "    movq %rax, %rdi\n"
  emit "    movq %rcx, %rsi\n"
  emit "    call strcmp\n"
  -- strcmp returns int (32-bit): <0 if left<right, 0 if equal, >0 if left>right
  -- Use 32-bit test since strcmp returns 32-bit int
  emit "    testl %eax, %eax\n"
  case op of
    Eq -> do
      emit "    sete %al\n"
      emit "    movzbl %al, %eax\n"
    Ne -> do
      emit "    setne %al\n"
      emit "    movzbl %al, %eax\n"
    Lt -> do
      emit "    setl %al\n"
      emit "    movzbl %al, %eax\n"
    Le -> do
      emit "    setle %al\n"
      emit "    movzbl %al, %eax\n"
    Gt -> do
      emit "    setg %al\n"
      emit "    movzbl %al, %eax\n"
    Ge -> do
      emit "    setge %al\n"
      emit "    movzbl %al, %eax\n"
    _ -> return ()

-- | Emit string concatenation (left in RAX, right in RCX)
emitStringConcat :: X86Codegen ()
emitStringConcat = do
  emit "    movq %rax, %rdi\n"
  emit "    movq %rcx, %rsi\n"
  emit "    call __str_concat\n"
  -- Result is in RAX

-- | Short-circuit AND
emitShortCircuitAnd :: SSAExpr -> SSAExpr -> X86Codegen ()
emitShortCircuitAnd l r = do
  falseLabel <- freshLabel "and_false"
  endLabel <- freshLabel "and_end"
  emitExpr l
  emit "    testq %rax, %rax\n"
  emit $ "    jz " <> falseLabel <> "\n"
  emitExpr r
  emit "    testq %rax, %rax\n"
  emit $ "    jz " <> falseLabel <> "\n"
  emit "    movq $1, %rax\n"
  emit $ "    jmp " <> endLabel <> "\n"
  emit $ falseLabel <> ":\n"
  emit "    xorq %rax, %rax\n"
  emit $ endLabel <> ":\n"

-- | Short-circuit OR
emitShortCircuitOr :: SSAExpr -> SSAExpr -> X86Codegen ()
emitShortCircuitOr l r = do
  trueLabel <- freshLabel "or_true"
  endLabel <- freshLabel "or_end"
  emitExpr l
  emit "    testq %rax, %rax\n"
  emit $ "    jnz " <> trueLabel <> "\n"
  emitExpr r
  emit "    testq %rax, %rax\n"
  emit $ "    jnz " <> trueLabel <> "\n"
  emit "    xorq %rax, %rax\n"
  emit $ "    jmp " <> endLabel <> "\n"
  emit $ trueLabel <> ":\n"
  emit "    movq $1, %rax\n"
  emit $ endLabel <> ":\n"

--------------------------------------------------------------------------------
-- Tail Call Optimization
--------------------------------------------------------------------------------

-- | Emit a self-recursive tail call (to same method)
-- Note: args from SSACall does NOT include 'this', which stays the same
emitSelfTailCall :: [SSAExpr] -> X86Codegen ()
emitSelfTailCall args = do
  methodSym <- asks xcgMethodSymbol
  let params = msParams methodSym
      -- Parameters include 'this' at the front - skip it since we keep same 'this'
      explicitParams = drop 1 params
      -- Parameters have version 0 (initial SSA version)
      explicitParamNames = map (\p -> vsName p ++ "_0") explicitParams

  -- Evaluate all arguments first and push them on stack
  -- This prevents clobbering parameters before we're done reading them
  forM_ (reverse args) $ \arg -> do
    emitExpr arg
    emit "    pushq %rax\n"

  -- Pop into parameter locations (in correct order)
  forM_ explicitParamNames $ \paramName -> do
    emit "    popq %rax\n"
    emitStoreVar RAX paramName

  -- Jump to TCO entry point (after prologue)
  clsName <- asks xcgClassName
  methName <- asks xcgMethodName
  let tcoLabel = T.pack clsName <> "_" <> T.pack methName <> "_tco"
  emit $ "    jmp " <> tcoLabel <> "\n"

-- | Emit a cross-method tail call (to different method, same class)
-- This is for calls like "return foo(args)" where foo is a method in the same class
--
-- Stack order fix: We must pop args into arg registers BEFORE doing the epilogue,
-- because the epilogue pops callee-saved regs which are below the args on the stack.
emitCrossMethodTailCall :: Text -> [SSAExpr] -> X86Codegen ()
emitCrossMethodTailCall targetLabel args = do
  -- 1. Push 'this' temporarily
  emitLoadVar "this_0" RAX
  emit "    pushq %rax\n"

  -- 2. Evaluate all arguments and push them temporarily
  forM_ (reverse args) $ \arg -> do
    emitExpr arg
    emit "    pushq %rax\n"

  -- 3. Pop args into arg registers NOW (before epilogue)
  -- Args go in RSI, RDX, RCX, R8, R9; 'this' goes in RDI
  let nArgs = length args
      argRegsX86 = take nArgs [RSI, RDX, RCX, R8, R9]
  forM_ argRegsX86 $ \reg ->
    emit $ "    popq " <> regName reg <> "\n"
  emit "    popq %rdi\n"  -- 'this' into RDI

  -- 4. Now do epilogue - args are safe in caller-saved arg registers
  alloc <- asks xcgRegAlloc
  let usedCallee = usedCalleeRegs alloc
  forM_ (reverse usedCallee) $ \reg ->
    emit $ "    popq " <> regName reg <> "\n"

  frameSize <- gets xcgFrameSize
  when (frameSize > 0) $
    emit $ "    addq $" <> tshow frameSize <> ", %rsp\n"
  emit "    popq %rbp\n"

  -- 5. Jump to target method (return address is on top of stack)
  emit $ "    jmp " <> targetLabel <> "\n"

-- | Emit an instance method tail call (to different object)
-- Same stack ordering fix as emitCrossMethodTailCall.
emitInstanceTailCall :: SSAExpr -> Text -> [SSAExpr] -> X86Codegen ()
emitInstanceTailCall target targetLabel args = do
  -- 1. Evaluate target and push temporarily
  emitExpr target
  emit "    pushq %rax\n"

  -- 2. Evaluate all arguments and push them temporarily
  forM_ (reverse args) $ \arg -> do
    emitExpr arg
    emit "    pushq %rax\n"

  -- 3. Pop args into arg registers NOW (before epilogue)
  let nArgs = length args
      argRegsX86 = take nArgs [RSI, RDX, RCX, R8, R9]
  forM_ argRegsX86 $ \reg ->
    emit $ "    popq " <> regName reg <> "\n"
  emit "    popq %rdi\n"  -- target into RDI

  -- 4. Now do epilogue - args are safe in caller-saved arg registers
  alloc <- asks xcgRegAlloc
  let usedCallee = usedCalleeRegs alloc
  forM_ (reverse usedCallee) $ \reg ->
    emit $ "    popq " <> regName reg <> "\n"

  frameSize <- gets xcgFrameSize
  when (frameSize > 0) $
    emit $ "    addq $" <> tshow frameSize <> ", %rsp\n"
  emit "    popq %rbp\n"

  -- 5. Jump to target method
  emit $ "    jmp " <> targetLabel <> "\n"

--------------------------------------------------------------------------------
-- Function Calls
--------------------------------------------------------------------------------

-- | Emit a static method call
emitStaticCall :: String -> [SSAExpr] -> X86Codegen ()
emitStaticCall name args = do
  -- Evaluate arguments in reverse order and push on stack
  -- This ensures they come off in the right order for registers
  forM_ (reverse args) $ \arg -> do
    emitExpr arg
    emit "    pushq %rax\n"

  -- Pop args into registers (args go in RSI, RDX, RCX, R8, R9)
  let nArgs = length args
      argRegsX86 = take nArgs [RSI, RDX, RCX, R8, R9]
  forM_ argRegsX86 $ \reg -> do
    emit $ "    popq " <> regName reg <> "\n"

  -- Load 'this' as first argument into RDI
  emitLoadVar "this_0" RDI

  -- Call the method
  clsName <- asks xcgClassName
  syms <- asks xcgSymbols
  let methodLabel = case lookupClass clsName syms >>= lookupMethod name of
        Just _ -> T.pack clsName <> "_" <> T.pack name
        Nothing -> T.pack name
  emit $ "    call " <> methodLabel <> "\n"
  -- Result is in RAX

-- | Emit an instance method call
emitInstanceCall :: SSAExpr -> String -> [SSAExpr] -> X86Codegen ()
emitInstanceCall target method args = do
  -- Evaluate target (this pointer)
  emitExpr target
  emit "    pushq %rax\n"  -- Save target

  -- Evaluate arguments in reverse order and push them
  -- This ensures they come off the stack in the right order for registers
  forM_ (reverse args) $ \arg -> do
    emitExpr arg
    emit "    pushq %rax\n"

  -- Pop args into registers (first 5 args go in RSI, RDX, RCX, R8, R9)
  let nArgs = length args
      argRegsX86 = take nArgs [RSI, RDX, RCX, R8, R9]
  forM_ argRegsX86 $ \reg -> do
    emit $ "    popq " <> regName reg <> "\n"

  -- Pop target into RDI
  emit "    popq %rdi\n"

  -- Determine method label
  syms <- asks xcgSymbols
  typeEnv <- asks xcgTypeEnv
  className <- asks xcgClassName
  let methodLabel = case target of
        SSAThis -> T.pack className <> "_" <> T.pack method
        _ -> case inferSSAExprClassWithCtx (Just className) syms typeEnv target of
               Just cn -> T.pack cn <> "_" <> T.pack method
               Nothing -> T.pack className <> "_" <> T.pack method

  emit $ "    call " <> methodLabel <> "\n"

-- | Emit object allocation
emitNewObject :: String -> [SSAExpr] -> X86Codegen ()
emitNewObject cn args = do
  syms <- asks xcgSymbols
  cs <- case lookupClass cn syms of
    Just cs -> return cs
    Nothing -> throwError $ D.ResolveError ("Unknown class: " ++ cn) 0 0

  let nFields = length (csFieldOrder cs)
      hasCtor = isJust (lookupMethod cn cs)

  -- Allocate object: malloc(nFields * 8)
  emit $ "    movq $" <> tshow (nFields * 8) <> ", %rdi\n"
  emit "    call malloc\n"
  -- RAX = object pointer

  -- Initialize fields to 0 (malloc doesn't zero memory, use calloc or memset)
  when (nFields > 0) $ do
    emit "    pushq %rax\n"  -- Save object pointer
    emit "    movq %rax, %rdi\n"
    emit "    xorq %rsi, %rsi\n"  -- 0
    emit $ "    movq $" <> tshow (nFields * 8) <> ", %rdx\n"
    emit "    call memset\n"
    emit "    popq %rax\n"  -- Restore object pointer

  -- Call constructor if present
  when hasCtor $ do
    emit "    pushq %rax\n"  -- Save object for return

    -- Evaluate all constructor args first and push them on stack
    -- This ensures arg evaluation doesn't clobber other args
    forM_ (reverse args) $ \arg -> do
      emitExpr arg
      emit "    pushq %rax\n"

    -- Pop args into registers: this in RDI, args in RSI, RDX, ...
    let ctorArgRegs = take (length args) [RSI, RDX, RCX, R8, R9]
    forM_ ctorArgRegs $ \reg -> do
      emit $ "    popq " <> regName reg <> "\n"

    -- Load 'this' from where we saved the object pointer
    -- After popping all args, object pointer is at top of stack
    emit "    movq (%rsp), %rdi\n"

    let ctorLabel = T.pack cn <> "_" <> T.pack cn
    emit $ "    call " <> ctorLabel <> "\n"

    emit "    popq %rax\n"  -- Return object pointer

-- | Emit field access
emitFieldAccess :: SSAExpr -> String -> X86Codegen ()
emitFieldAccess target field = do
  emitExpr target  -- Object pointer in RAX

  syms <- asks xcgSymbols
  typeEnv <- asks xcgTypeEnv
  className <- asks xcgClassName

  let targetClass = case target of
        SSAThis -> Just className
        _ -> inferSSAExprClassWithCtx (Just className) syms typeEnv target

      offset = fromMaybe 0 $ do
        cn <- targetClass
        cs <- lookupClass cn syms
        fieldOffset field cs

  emit $ "    movq " <> tshow (offset * 8) <> "(%rax), %rax\n"

--------------------------------------------------------------------------------
-- Phi Node Handling
--------------------------------------------------------------------------------

-- | Emit parallel copies for phi nodes.
-- Uses parallel copy semantics: all sources are read before any destination is written.
-- This avoids the "lost copy" problem where a destination overwrites a source.
emitParallelCopies :: [(String, String)] -> X86Codegen ()
emitParallelCopies [] = return ()
emitParallelCopies copies = do
  -- Phase 1: Push all source values onto the stack
  forM_ copies $ \(_dest, src) -> do
    emitLoadVar src RAX
    emit "    pushq %rax\n"

  -- Phase 2: Pop values into destinations (in reverse order)
  forM_ (reverse copies) $ \(dest, _src) -> do
    emit "    popq %rax\n"
    emitStoreVar RAX dest

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
-- Utilities
--------------------------------------------------------------------------------

-- | Emit text
emit :: Text -> X86Codegen ()
emit t = modify $ \s -> s { xcgCode = xcgCode s <> B.fromText t }

-- | Add a string literal to be emitted in .rodata
addString :: Text -> Text -> X86Codegen ()
addString label content = modify $ \s -> s { xcgStrings = (label, content) : xcgStrings s }

-- | Generate a fresh label
freshLabel :: Text -> X86Codegen Text
freshLabel prefix = do
  st <- get
  let n = xcgLabelCounter st
  put st { xcgLabelCounter = n + 1 }
  clsName <- asks xcgClassName
  methName <- asks xcgMethodName
  return $ ".L" <> T.pack clsName <> "_" <> T.pack methName <> "_" <> prefix <> "_" <> T.pack (show n)

-- | Get block label
blockLabelText :: BlockId -> X86Codegen Text
blockLabelText bid = do
  clsName <- asks xcgClassName
  methName <- asks xcgMethodName
  return $ ".L" <> T.pack clsName <> "_" <> T.pack methName <> "_" <> T.pack (blockIdName bid)

-- | Get stack slot for a variable (offset from RBP)
getVarSlot :: String -> X86Codegen Int
getVarSlot name = do
  slots <- gets xcgVarSlots
  case Map.lookup name slots of
    Just slot -> return slot
    Nothing -> throwError $ D.ResolveError ("Unknown variable: " ++ name) 0 0

-- | Get the location of a variable (register or stack)
-- Register allocation uses versioned names (like "this_0", "x_1")
-- Stack slots use base names (like "this", "x")
getVarLoc :: String -> X86Codegen VarLocation
getVarLoc name = do
  alloc <- asks xcgRegAlloc
  case getVarLocation name alloc of
    Just loc -> return loc
    Nothing -> do
      -- Fall back to stack slot using base name
      let baseName = extractBaseName name
      slot <- getVarSlot baseName
      return $ OnStack slot

-- | Extract base name from versioned SSA name (e.g., "this_0" -> "this")
extractBaseName :: String -> String
extractBaseName name =
  case break (== '_') (reverse name) of
    (versionRev, '_':baseRev)
      | not (null versionRev) && all isDigit versionRev -> reverse baseRev
    _ -> name  -- No valid version suffix, use as-is

-- | Emit load from variable location to register
emitLoadVar :: String -> X86Reg -> X86Codegen ()
emitLoadVar name destReg = do
  loc <- getVarLoc name
  case loc of
    InReg srcReg | srcReg == destReg -> return ()  -- No-op
    InReg srcReg -> emit $ "    movq " <> regName srcReg <> ", " <> regName destReg <> "\n"
    OnStack slot -> emit $ "    movq " <> tshow (-(slot + 1) * 8) <> "(%rbp), " <> regName destReg <> "\n"

-- | Emit store from register to variable location
emitStoreVar :: X86Reg -> String -> X86Codegen ()
emitStoreVar srcReg name = do
  loc <- getVarLoc name
  case loc of
    InReg destReg | destReg == srcReg -> return ()  -- No-op
    InReg destReg -> emit $ "    movq " <> regName srcReg <> ", " <> regName destReg <> "\n"
    OnStack slot -> emit $ "    movq " <> regName srcReg <> ", " <> tshow (-(slot + 1) * 8) <> "(%rbp)\n"

tshow :: Show a => a -> Text
tshow = T.pack . show
