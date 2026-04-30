{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}

-- | AArch64 (ARM64) instruction types and pretty-printing.
-- Generates GAS (GNU Assembler) syntax output for Linux AArch64.
module LiveOak.ARM
  ( -- * Registers
    ARMReg(..)
  , regName
  , reg32Name
  , callerSavedRegs
  , calleeSavedRegs
  , argRegs

    -- * Conditions
  , ARMCond(..)
  , condText
  , invertCond

    -- * Operands
  , ARMOperand(..)
  , operandText

    -- * Instructions
  , ARMInstr(..)
  , instrText
  ) where

import Data.Text (Text)
import qualified Data.Text as T

--------------------------------------------------------------------------------
-- Registers
--------------------------------------------------------------------------------

-- | AArch64 general-purpose registers
data ARMReg
  = X0  | X1  | X2  | X3  | X4  | X5  | X6  | X7
  | X8  | X9  | X10 | X11 | X12 | X13 | X14 | X15
  | X16 | X17 | X18 | X19 | X20 | X21 | X22 | X23
  | X24 | X25 | X26 | X27 | X28
  | XFP  -- ^ X29, frame pointer
  | XLR  -- ^ X30, link register
  | XSP  -- ^ Stack pointer
  | XZR  -- ^ Zero register
  deriving (Eq, Ord, Show)

-- | 64-bit register name
regName :: ARMReg -> Text
regName = \case
  X0  -> "x0";  X1  -> "x1";  X2  -> "x2";  X3  -> "x3"
  X4  -> "x4";  X5  -> "x5";  X6  -> "x6";  X7  -> "x7"
  X8  -> "x8";  X9  -> "x9";  X10 -> "x10"; X11 -> "x11"
  X12 -> "x12"; X13 -> "x13"; X14 -> "x14"; X15 -> "x15"
  X16 -> "x16"; X17 -> "x17"; X18 -> "x18"; X19 -> "x19"
  X20 -> "x20"; X21 -> "x21"; X22 -> "x22"; X23 -> "x23"
  X24 -> "x24"; X25 -> "x25"; X26 -> "x26"; X27 -> "x27"
  X28 -> "x28"
  XFP -> "x29"; XLR -> "x30"; XSP -> "sp";  XZR -> "xzr"

-- | 32-bit register name (W-form)
reg32Name :: ARMReg -> Text
reg32Name = \case
  X0  -> "w0";  X1  -> "w1";  X2  -> "w2";  X3  -> "w3"
  X4  -> "w4";  X5  -> "w5";  X6  -> "w6";  X7  -> "w7"
  X8  -> "w8";  X9  -> "w9";  X10 -> "w10"; X11 -> "w11"
  X12 -> "w12"; X13 -> "w13"; X14 -> "w14"; X15 -> "w15"
  X16 -> "w16"; X17 -> "w17"; X18 -> "w18"; X19 -> "w19"
  X20 -> "w20"; X21 -> "w21"; X22 -> "w22"; X23 -> "w23"
  X24 -> "w24"; X25 -> "w25"; X26 -> "w26"; X27 -> "w27"
  X28 -> "w28"
  XFP -> "w29"; XLR -> "w30"; XSP -> "wsp"; XZR -> "wzr"

-- | Caller-saved registers (clobbered by function calls)
callerSavedRegs :: [ARMReg]
callerSavedRegs = [X0, X1, X2, X3, X4, X5, X6, X7, X8,
                   X9, X10, X11, X12, X13, X14, X15, X16, X17, X18]

-- | Callee-saved registers (must be preserved across calls)
calleeSavedRegs :: [ARMReg]
calleeSavedRegs = [X19, X20, X21, X22, X23, X24, X25, X26, X27, X28]

-- | Argument registers (AAPCS64)
argRegs :: [ARMReg]
argRegs = [X0, X1, X2, X3, X4, X5, X6, X7]

--------------------------------------------------------------------------------
-- Condition Codes
--------------------------------------------------------------------------------

-- | AArch64 condition codes
data ARMCond
  = CondEQ   -- ^ Equal (Z=1)
  | CondNE   -- ^ Not equal (Z=0)
  | CondLT   -- ^ Signed less than (N!=V)
  | CondLE   -- ^ Signed less or equal (Z=1 or N!=V)
  | CondGT   -- ^ Signed greater than (Z=0 and N=V)
  | CondGE   -- ^ Signed greater or equal (N=V)
  deriving (Eq, Show)

-- | Condition code text for assembly
condText :: ARMCond -> Text
condText = \case
  CondEQ -> "eq"; CondNE -> "ne"
  CondLT -> "lt"; CondLE -> "le"
  CondGT -> "gt"; CondGE -> "ge"

-- | Invert a condition code
invertCond :: ARMCond -> ARMCond
invertCond = \case
  CondEQ -> CondNE; CondNE -> CondEQ
  CondLT -> CondGE; CondGE -> CondLT
  CondLE -> CondGT; CondGT -> CondLE

--------------------------------------------------------------------------------
-- Operands
--------------------------------------------------------------------------------

-- | AArch64 operand
data ARMOperand
  = Reg !ARMReg                    -- ^ Register: x0
  | WReg !ARMReg                   -- ^ 32-bit register: w0
  | Imm !Int                      -- ^ Immediate: #42
  | MemOff !ARMReg !Int           -- ^ Offset: [base, #off]
  | MemPreIdx !ARMReg !Int        -- ^ Pre-indexed: [base, #off]!
  | MemPostIdx !ARMReg !Int       -- ^ Post-indexed: [base], #off
  | Label !Text                   -- ^ Label reference
  | LabelLo12 !Text              -- ^ Low 12 bits: :lo12:label
  deriving (Eq, Show)

-- | Format operand as GAS syntax
operandText :: ARMOperand -> Text
operandText = \case
  Reg r -> regName r
  WReg r -> reg32Name r
  Imm n -> "#" <> tshow n
  MemOff base 0 -> "[" <> regName base <> "]"
  MemOff base off -> "[" <> regName base <> ", #" <> tshow off <> "]"
  MemPreIdx base off -> "[" <> regName base <> ", #" <> tshow off <> "]!"
  MemPostIdx base off -> "[" <> regName base <> "], #" <> tshow off
  Label lbl -> lbl
  LabelLo12 lbl -> ":lo12:" <> lbl

--------------------------------------------------------------------------------
-- Instructions
--------------------------------------------------------------------------------

-- | AArch64 instruction
data ARMInstr
  -- Data movement
  = MOV !ARMOperand !ARMOperand              -- ^ mov dst, src
  | LDR !ARMOperand !ARMOperand              -- ^ ldr dst, addr
  | STR !ARMOperand !ARMOperand              -- ^ str src, addr
  | LDRB !ARMOperand !ARMOperand             -- ^ ldrb dst, addr (byte load)
  | STRB !ARMOperand !ARMOperand             -- ^ strb src, addr (byte store)
  | STP !ARMReg !ARMReg !ARMOperand          -- ^ stp r1, r2, addr
  | LDP !ARMReg !ARMReg !ARMOperand          -- ^ ldp r1, r2, addr
  | ADRP !ARMOperand !ARMOperand             -- ^ adrp dst, label (page address)

  -- Arithmetic
  | ADD !ARMOperand !ARMOperand !ARMOperand   -- ^ add dst, src1, src2
  | SUB !ARMOperand !ARMOperand !ARMOperand   -- ^ sub dst, src1, src2
  | MUL !ARMOperand !ARMOperand !ARMOperand   -- ^ mul dst, src1, src2
  | SDIV !ARMOperand !ARMOperand !ARMOperand  -- ^ sdiv dst, src1, src2
  | MSUB !ARMOperand !ARMOperand !ARMOperand !ARMOperand  -- ^ msub dst, m1, m2, a
  | NEG !ARMOperand !ARMOperand               -- ^ neg dst, src

  -- Bitwise
  | AND !ARMOperand !ARMOperand !ARMOperand   -- ^ and dst, src1, src2
  | ORR !ARMOperand !ARMOperand !ARMOperand   -- ^ orr dst, src1, src2
  | EOR !ARMOperand !ARMOperand !ARMOperand   -- ^ eor dst, src1, src2
  | MVN !ARMOperand !ARMOperand               -- ^ mvn dst, src (bitwise NOT)
  | LSL !ARMOperand !ARMOperand !ARMOperand   -- ^ lsl dst, src, amount
  | LSR !ARMOperand !ARMOperand !ARMOperand   -- ^ lsr dst, src, amount
  | ASR !ARMOperand !ARMOperand !ARMOperand   -- ^ asr dst, src, amount

  -- Comparison
  | CMP !ARMOperand !ARMOperand               -- ^ cmp src1, src2
  | TST !ARMOperand !ARMOperand               -- ^ tst src1, src2 (AND, discard result)
  | CSET !ARMOperand !ARMCond                 -- ^ cset dst, cond
  | CSEL !ARMOperand !ARMOperand !ARMOperand !ARMCond  -- ^ csel dst, t, f, cond

  -- Control flow
  | B !ARMOperand                             -- ^ b label (unconditional)
  | Bcond !ARMCond !ARMOperand                -- ^ b.cond label
  | CBZ !ARMOperand !ARMOperand               -- ^ cbz reg, label
  | CBNZ !ARMOperand !ARMOperand              -- ^ cbnz reg, label
  | BL !ARMOperand                            -- ^ bl label (call)
  | RET                                       -- ^ ret

  -- Directives
  | LABEL !Text                               -- ^ Label definition
  | GLOBAL !Text                              -- ^ .globl directive
  | SECTION !Text                             -- ^ .section directive
  | ASCIZ !Text                               -- ^ .asciz directive
  | XWORD !Int                                -- ^ .xword directive (64-bit)
  | ALIGN !Int                                -- ^ .align directive
  | COMMENT !Text                             -- ^ Comment
  deriving (Eq, Show)

-- | Format instruction as GAS syntax
instrText :: ARMInstr -> Text
instrText = \case
  -- Data movement
  MOV dst src -> "    mov " <> operandText dst <> ", " <> operandText src
  LDR dst addr -> "    ldr " <> operandText dst <> ", " <> operandText addr
  STR src addr -> "    str " <> operandText src <> ", " <> operandText addr
  LDRB dst addr -> "    ldrb " <> operandText dst <> ", " <> operandText addr
  STRB src addr -> "    strb " <> operandText src <> ", " <> operandText addr
  STP r1 r2 addr -> "    stp " <> regName r1 <> ", " <> regName r2 <> ", " <> operandText addr
  LDP r1 r2 addr -> "    ldp " <> regName r1 <> ", " <> regName r2 <> ", " <> operandText addr
  ADRP dst lbl -> "    adrp " <> operandText dst <> ", " <> operandText lbl

  -- Arithmetic
  ADD dst s1 s2 -> "    add " <> operandText dst <> ", " <> operandText s1 <> ", " <> operandText s2
  SUB dst s1 s2 -> "    sub " <> operandText dst <> ", " <> operandText s1 <> ", " <> operandText s2
  MUL dst s1 s2 -> "    mul " <> operandText dst <> ", " <> operandText s1 <> ", " <> operandText s2
  SDIV dst s1 s2 -> "    sdiv " <> operandText dst <> ", " <> operandText s1 <> ", " <> operandText s2
  MSUB dst m1 m2 a -> "    msub " <> operandText dst <> ", " <> operandText m1 <> ", " <> operandText m2 <> ", " <> operandText a
  NEG dst src -> "    neg " <> operandText dst <> ", " <> operandText src

  -- Bitwise
  AND dst s1 s2 -> "    and " <> operandText dst <> ", " <> operandText s1 <> ", " <> operandText s2
  ORR dst s1 s2 -> "    orr " <> operandText dst <> ", " <> operandText s1 <> ", " <> operandText s2
  EOR dst s1 s2 -> "    eor " <> operandText dst <> ", " <> operandText s1 <> ", " <> operandText s2
  MVN dst src -> "    mvn " <> operandText dst <> ", " <> operandText src
  LSL dst src amt -> "    lsl " <> operandText dst <> ", " <> operandText src <> ", " <> operandText amt
  LSR dst src amt -> "    lsr " <> operandText dst <> ", " <> operandText src <> ", " <> operandText amt
  ASR dst src amt -> "    asr " <> operandText dst <> ", " <> operandText src <> ", " <> operandText amt

  -- Comparison
  CMP s1 s2 -> "    cmp " <> operandText s1 <> ", " <> operandText s2
  TST s1 s2 -> "    tst " <> operandText s1 <> ", " <> operandText s2
  CSET dst cond -> "    cset " <> operandText dst <> ", " <> condText cond
  CSEL dst t f cond -> "    csel " <> operandText dst <> ", " <> operandText t <> ", " <> operandText f <> ", " <> condText cond

  -- Control flow
  B target -> "    b " <> operandText target
  Bcond cond target -> "    b." <> condText cond <> " " <> operandText target
  CBZ reg target -> "    cbz " <> operandText reg <> ", " <> operandText target
  CBNZ reg target -> "    cbnz " <> operandText reg <> ", " <> operandText target
  BL target -> "    bl " <> operandText target
  RET -> "    ret"

  -- Directives
  LABEL lbl -> lbl <> ":"
  GLOBAL sym -> ".globl " <> sym
  SECTION name -> ".section " <> name
  ASCIZ str -> "    .asciz \"" <> escapeString str <> "\""
  XWORD n -> "    .xword " <> tshow n
  ALIGN n -> "    .align " <> tshow n
  COMMENT txt -> "    // " <> txt

--------------------------------------------------------------------------------
-- Utilities
--------------------------------------------------------------------------------

tshow :: Show a => a -> Text
tshow = T.pack . show

-- | Escape a string for GAS
escapeString :: Text -> Text
escapeString = T.concatMap escape
  where
    escape '"'  = "\\\""
    escape '\\' = "\\\\"
    escape '\n' = "\\n"
    escape '\t' = "\\t"
    escape '\r' = "\\r"
    escape c    = T.singleton c
