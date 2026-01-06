{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}

-- | x86_64 instruction types and pretty-printing.
-- Generates GAS (GNU Assembler) syntax output.
module LiveOak.X86
  ( -- * Registers
    X86Reg(..)
  , regName
  , reg32Name
  , reg8Name
  , callerSavedRegs
  , calleeSavedRegs
  , argRegs

    -- * Operands
  , X86Operand(..)
  , operandText

    -- * Instructions
  , X86Instr(..)
  , instrText

    -- * Sizes
  , X86Size(..)
  , sizeSuffix
  ) where

import Data.Text (Text)
import qualified Data.Text as T

--------------------------------------------------------------------------------
-- Registers
--------------------------------------------------------------------------------

-- | x86_64 general-purpose registers
data X86Reg
  = RAX | RBX | RCX | RDX
  | RSI | RDI | RBP | RSP
  | R8  | R9  | R10 | R11
  | R12 | R13 | R14 | R15
  deriving (Eq, Ord, Show)

-- | 64-bit register name
regName :: X86Reg -> Text
regName = \case
  RAX -> "%rax"; RBX -> "%rbx"; RCX -> "%rcx"; RDX -> "%rdx"
  RSI -> "%rsi"; RDI -> "%rdi"; RBP -> "%rbp"; RSP -> "%rsp"
  R8  -> "%r8";  R9  -> "%r9";  R10 -> "%r10"; R11 -> "%r11"
  R12 -> "%r12"; R13 -> "%r13"; R14 -> "%r14"; R15 -> "%r15"

-- | 32-bit register name (for 32-bit operations)
reg32Name :: X86Reg -> Text
reg32Name = \case
  RAX -> "%eax"; RBX -> "%ebx"; RCX -> "%ecx"; RDX -> "%edx"
  RSI -> "%esi"; RDI -> "%edi"; RBP -> "%ebp"; RSP -> "%esp"
  R8  -> "%r8d"; R9  -> "%r9d"; R10 -> "%r10d"; R11 -> "%r11d"
  R12 -> "%r12d"; R13 -> "%r13d"; R14 -> "%r14d"; R15 -> "%r15d"

-- | 8-bit register name (for setcc)
reg8Name :: X86Reg -> Text
reg8Name = \case
  RAX -> "%al"; RBX -> "%bl"; RCX -> "%cl"; RDX -> "%dl"
  RSI -> "%sil"; RDI -> "%dil"; RBP -> "%bpl"; RSP -> "%spl"
  R8  -> "%r8b"; R9  -> "%r9b"; R10 -> "%r10b"; R11 -> "%r11b"
  R12 -> "%r12b"; R13 -> "%r13b"; R14 -> "%r14b"; R15 -> "%r15b"

-- | Caller-saved registers (can be clobbered by function calls)
callerSavedRegs :: [X86Reg]
callerSavedRegs = [RAX, RCX, RDX, RSI, RDI, R8, R9, R10, R11]

-- | Callee-saved registers (must be preserved across calls)
calleeSavedRegs :: [X86Reg]
calleeSavedRegs = [RBX, RBP, R12, R13, R14, R15]

-- | Argument registers (System V AMD64 ABI)
argRegs :: [X86Reg]
argRegs = [RDI, RSI, RDX, RCX, R8, R9]

--------------------------------------------------------------------------------
-- Operand Sizes
--------------------------------------------------------------------------------

-- | Operand size for instructions
data X86Size = Byte | Word | DWord | QWord
  deriving (Eq, Show)

-- | GAS suffix for operand size
sizeSuffix :: X86Size -> Text
sizeSuffix = \case
  Byte  -> "b"
  Word  -> "w"
  DWord -> "l"
  QWord -> "q"

--------------------------------------------------------------------------------
-- Operands
--------------------------------------------------------------------------------

-- | x86_64 operand
data X86Operand
  = Reg !X86Reg                    -- ^ Register: %rax
  | Imm !Int                       -- ^ Immediate: $42
  | Mem !X86Reg !Int               -- ^ Memory: offset(%reg)
  | MemIndex !X86Reg !X86Reg !Int !Int  -- ^ Indexed: offset(%base, %index, scale)
  | Label !Text                    -- ^ Label reference
  | LabelRIP !Text                 -- ^ RIP-relative: label(%rip)
  deriving (Eq, Show)

-- | Format operand as GAS syntax
operandText :: X86Operand -> Text
operandText = \case
  Reg r -> regName r
  Imm n -> "$" <> tshow n
  Mem base 0 -> "(" <> regName base <> ")"
  Mem base off -> tshow off <> "(" <> regName base <> ")"
  MemIndex base idx scale 0 ->
    "(" <> regName base <> ", " <> regName idx <> ", " <> tshow scale <> ")"
  MemIndex base idx scale off ->
    tshow off <> "(" <> regName base <> ", " <> regName idx <> ", " <> tshow scale <> ")"
  Label lbl -> lbl
  LabelRIP lbl -> lbl <> "(%rip)"

-- | Format operand as 32-bit (for movzbl destination)
operandText32 :: X86Operand -> Text
operandText32 = \case
  Reg r -> reg32Name r
  other -> operandText other

--------------------------------------------------------------------------------
-- Instructions
--------------------------------------------------------------------------------

-- | x86_64 instruction
data X86Instr
  -- Data movement
  = MOV !X86Operand !X86Operand    -- ^ mov src, dst
  | MOVZX !X86Operand !X86Operand  -- ^ movzx src, dst (zero-extend)
  | MOVSX !X86Operand !X86Operand  -- ^ movsx src, dst (sign-extend)
  | LEA !X86Operand !X86Operand    -- ^ lea src, dst (load effective address)
  | PUSH !X86Operand               -- ^ push src
  | POP !X86Operand                -- ^ pop dst
  | XCHG !X86Operand !X86Operand   -- ^ xchg src, dst

  -- Arithmetic
  | ADD !X86Operand !X86Operand    -- ^ add src, dst
  | SUB !X86Operand !X86Operand    -- ^ sub src, dst
  | IMUL !X86Operand !X86Operand   -- ^ imul src, dst (signed multiply)
  | IMUL3 !X86Operand !X86Operand !X86Operand  -- ^ imul imm, src, dst
  | IDIV !X86Operand               -- ^ idiv src (signed divide rdx:rax by src)
  | NEG !X86Operand                -- ^ neg dst (negate)
  | INC !X86Operand                -- ^ inc dst
  | DEC !X86Operand                -- ^ dec dst
  | CQO                            -- ^ sign-extend rax into rdx:rax

  -- Bitwise
  | AND !X86Operand !X86Operand    -- ^ and src, dst
  | OR !X86Operand !X86Operand     -- ^ or src, dst
  | XOR !X86Operand !X86Operand    -- ^ xor src, dst
  | NOT !X86Operand                -- ^ not dst
  | SHL !X86Operand !X86Operand    -- ^ shl count, dst (shift left)
  | SHR !X86Operand !X86Operand    -- ^ shr count, dst (shift right logical)
  | SAR !X86Operand !X86Operand    -- ^ sar count, dst (shift right arithmetic)

  -- Comparison
  | CMP !X86Operand !X86Operand    -- ^ cmp src, dst (dst - src, set flags)
  | TEST !X86Operand !X86Operand   -- ^ test src, dst (dst & src, set flags)

  -- Conditional set
  | SETE !X86Operand               -- ^ set if equal (ZF=1)
  | SETNE !X86Operand              -- ^ set if not equal (ZF=0)
  | SETL !X86Operand               -- ^ set if less (SF!=OF)
  | SETLE !X86Operand              -- ^ set if less or equal (ZF=1 or SF!=OF)
  | SETG !X86Operand               -- ^ set if greater (ZF=0 and SF=OF)
  | SETGE !X86Operand              -- ^ set if greater or equal (SF=OF)

  -- Control flow
  | JMP !X86Operand                -- ^ unconditional jump
  | JE !X86Operand                 -- ^ jump if equal
  | JNE !X86Operand                -- ^ jump if not equal
  | JL !X86Operand                 -- ^ jump if less
  | JLE !X86Operand                -- ^ jump if less or equal
  | JG !X86Operand                 -- ^ jump if greater
  | JGE !X86Operand                -- ^ jump if greater or equal
  | JZ !X86Operand                 -- ^ jump if zero (same as JE)
  | JNZ !X86Operand                -- ^ jump if not zero (same as JNE)
  | CALL !X86Operand               -- ^ call function
  | RET                            -- ^ return

  -- Directives (pseudo-instructions)
  | LABEL !Text                    -- ^ Label definition
  | GLOBAL !Text                   -- ^ .globl directive
  | SECTION !Text                  -- ^ .section directive
  | ASCII !Text                    -- ^ .ascii directive
  | ASCIZ !Text                    -- ^ .asciz directive (null-terminated)
  | QUAD !Int                      -- ^ .quad directive
  | ALIGN !Int                     -- ^ .align directive
  | COMMENT !Text                  -- ^ Comment
  deriving (Eq, Show)

-- | Format instruction as GAS syntax
instrText :: X86Instr -> Text
instrText = \case
  -- Data movement
  MOV src dst -> "    movq " <> operandText src <> ", " <> operandText dst
  MOVZX src dst -> "    movzbl " <> operandText src <> ", " <> operandText32 dst
  MOVSX src dst -> "    movslq " <> operandText src <> ", " <> operandText dst
  LEA src dst -> "    leaq " <> operandText src <> ", " <> operandText dst
  PUSH src -> "    pushq " <> operandText src
  POP dst -> "    popq " <> operandText dst
  XCHG src dst -> "    xchgq " <> operandText src <> ", " <> operandText dst

  -- Arithmetic
  ADD src dst -> "    addq " <> operandText src <> ", " <> operandText dst
  SUB src dst -> "    subq " <> operandText src <> ", " <> operandText dst
  IMUL src dst -> "    imulq " <> operandText src <> ", " <> operandText dst
  IMUL3 imm src dst -> "    imulq " <> operandText imm <> ", " <> operandText src <> ", " <> operandText dst
  IDIV src -> "    idivq " <> operandText src
  NEG dst -> "    negq " <> operandText dst
  INC dst -> "    incq " <> operandText dst
  DEC dst -> "    decq " <> operandText dst
  CQO -> "    cqo"

  -- Bitwise
  AND src dst -> "    andq " <> operandText src <> ", " <> operandText dst
  OR src dst -> "    orq " <> operandText src <> ", " <> operandText dst
  XOR src dst -> "    xorq " <> operandText src <> ", " <> operandText dst
  NOT dst -> "    notq " <> operandText dst
  SHL cnt dst -> "    shlq " <> operandText cnt <> ", " <> operandText dst
  SHR cnt dst -> "    shrq " <> operandText cnt <> ", " <> operandText dst
  SAR cnt dst -> "    sarq " <> operandText cnt <> ", " <> operandText dst

  -- Comparison
  CMP src dst -> "    cmpq " <> operandText src <> ", " <> operandText dst
  TEST src dst -> "    testq " <> operandText src <> ", " <> operandText dst

  -- Conditional set
  SETE dst -> "    sete " <> operandText dst
  SETNE dst -> "    setne " <> operandText dst
  SETL dst -> "    setl " <> operandText dst
  SETLE dst -> "    setle " <> operandText dst
  SETG dst -> "    setg " <> operandText dst
  SETGE dst -> "    setge " <> operandText dst

  -- Control flow
  JMP target -> "    jmp " <> operandText target
  JE target -> "    je " <> operandText target
  JNE target -> "    jne " <> operandText target
  JL target -> "    jl " <> operandText target
  JLE target -> "    jle " <> operandText target
  JG target -> "    jg " <> operandText target
  JGE target -> "    jge " <> operandText target
  JZ target -> "    jz " <> operandText target
  JNZ target -> "    jnz " <> operandText target
  CALL target -> "    call " <> operandText target
  RET -> "    ret"

  -- Directives
  LABEL lbl -> lbl <> ":"
  GLOBAL sym -> ".globl " <> sym
  SECTION name -> ".section " <> name
  ASCII str -> "    .ascii \"" <> escapeString str <> "\""
  ASCIZ str -> "    .asciz \"" <> escapeString str <> "\""
  QUAD n -> "    .quad " <> tshow n
  ALIGN n -> "    .align " <> tshow n
  COMMENT txt -> "    # " <> txt

--------------------------------------------------------------------------------
-- Utilities
--------------------------------------------------------------------------------

tshow :: Show a => a -> Text
tshow = T.pack . show

-- | Escape a string for GAS
escapeString :: Text -> Text
escapeString = T.concatMap escape
  where
    escape '"' = "\\\""
    escape '\\' = "\\\\"
    escape '\n' = "\\n"
    escape '\t' = "\\t"
    escape '\r' = "\\r"
    escape c = T.singleton c
