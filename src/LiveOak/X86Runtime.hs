{-# LANGUAGE OverloadedStrings #-}

-- | x86_64 runtime support code.
-- Generates assembly for runtime helpers (string operations, etc.)
module LiveOak.X86Runtime
  ( emitX86Runtime
  ) where

import Data.Text (Text)
import qualified Data.Text as T

import LiveOak.X86

--------------------------------------------------------------------------------
-- Runtime Generation
--------------------------------------------------------------------------------

-- | Generate the runtime support code
emitX86Runtime :: [X86Instr]
emitX86Runtime = concat
  [ runtimeHeader
  , stringConcat
  , stringRepeat
  , stringReverse
  , stringCompare
  , stringLength
  , printInt
  , printString
  , printBool
  , printNewline
  ]

-- | Runtime header with data section
runtimeHeader :: [X86Instr]
runtimeHeader =
  [ COMMENT "Runtime support code"
  , SECTION ".data"
  , LABEL "true_str"
  , ASCIZ "true"
  , LABEL "false_str"
  , ASCIZ "false"
  , LABEL "newline_str"
  , ASCIZ "\\n"
  , LABEL "int_format"
  , ASCIZ "%ld"
  , LABEL "str_format"
  , ASCIZ "%s"
  , SECTION ".text"
  ]

--------------------------------------------------------------------------------
-- String Operations
--------------------------------------------------------------------------------

-- | String concatenation: __str_concat(char* s1, char* s2) -> char*
-- Allocates new string, copies both strings into it
stringConcat :: [X86Instr]
stringConcat =
  [ COMMENT "String concatenation"
  , GLOBAL "__str_concat"
  , LABEL "__str_concat"
  , PUSH (Reg RBP)
  , MOV (Reg RSP) (Reg RBP)
  , PUSH (Reg RBX)
  , PUSH (Reg R12)
  , PUSH (Reg R13)
  -- Save arguments
  , MOV (Reg RDI) (Reg R12)  -- s1
  , MOV (Reg RSI) (Reg R13)  -- s2
  -- Get length of s1
  , CALL (Label "strlen")
  , MOV (Reg RAX) (Reg RBX)  -- len1 in RBX
  -- Get length of s2
  , MOV (Reg R13) (Reg RDI)
  , CALL (Label "strlen")
  -- Total length = len1 + len2 + 1
  , ADD (Reg RBX) (Reg RAX)
  , INC (Reg RAX)
  -- Allocate
  , MOV (Reg RAX) (Reg RDI)
  , CALL (Label "malloc")
  , MOV (Reg RAX) (Reg RBX)  -- result in RBX
  -- Copy s1
  , MOV (Reg RBX) (Reg RDI)
  , MOV (Reg R12) (Reg RSI)
  , CALL (Label "strcpy")
  -- Concatenate s2
  , MOV (Reg RBX) (Reg RDI)
  , MOV (Reg R13) (Reg RSI)
  , CALL (Label "strcat")
  -- Return result
  , MOV (Reg RBX) (Reg RAX)
  , POP (Reg R13)
  , POP (Reg R12)
  , POP (Reg RBX)
  , POP (Reg RBP)
  , RET
  ]

-- | String repeat: __str_repeat(char* s, int n) -> char*
stringRepeat :: [X86Instr]
stringRepeat =
  [ COMMENT "String repeat"
  , GLOBAL "__str_repeat"
  , LABEL "__str_repeat"
  , PUSH (Reg RBP)
  , MOV (Reg RSP) (Reg RBP)
  , PUSH (Reg RBX)
  , PUSH (Reg R12)
  , PUSH (Reg R13)
  , PUSH (Reg R14)
  -- Save arguments
  , MOV (Reg RDI) (Reg R12)  -- s
  , MOV (Reg RSI) (Reg R13)  -- n
  -- Handle n <= 0
  , TEST (Reg R13) (Reg R13)
  , JG (Label "__str_repeat_positive")
  -- Return empty string
  , MOV (Imm 1) (Reg RDI)
  , CALL (Label "malloc")
  , MOV (Imm 0) (Mem RAX 0)
  , JMP (Label "__str_repeat_done")
  , LABEL "__str_repeat_positive"
  -- Get length of s
  , MOV (Reg R12) (Reg RDI)
  , CALL (Label "strlen")
  , MOV (Reg RAX) (Reg R14)  -- len in R14
  -- Total size = len * n + 1
  , IMUL (Reg R13) (Reg RAX)
  , INC (Reg RAX)
  , MOV (Reg RAX) (Reg RDI)
  , CALL (Label "malloc")
  , MOV (Reg RAX) (Reg RBX)  -- result in RBX
  -- Initialize result to empty
  , MOV (Imm 0) (Mem RBX 0)
  -- Loop n times
  , LABEL "__str_repeat_loop"
  , TEST (Reg R13) (Reg R13)
  , JZ (Label "__str_repeat_done")
  , MOV (Reg RBX) (Reg RDI)
  , MOV (Reg R12) (Reg RSI)
  , CALL (Label "strcat")
  , DEC (Reg R13)
  , JMP (Label "__str_repeat_loop")
  , LABEL "__str_repeat_done"
  , MOV (Reg RBX) (Reg RAX)
  , POP (Reg R14)
  , POP (Reg R13)
  , POP (Reg R12)
  , POP (Reg RBX)
  , POP (Reg RBP)
  , RET
  ]

-- | String reverse: __str_reverse(char* s) -> char*
stringReverse :: [X86Instr]
stringReverse =
  [ COMMENT "String reverse"
  , GLOBAL "__str_reverse"
  , LABEL "__str_reverse"
  , PUSH (Reg RBP)
  , MOV (Reg RSP) (Reg RBP)
  , PUSH (Reg RBX)
  , PUSH (Reg R12)
  , PUSH (Reg R13)
  -- Save argument
  , MOV (Reg RDI) (Reg R12)  -- s
  -- Get length
  , CALL (Label "strlen")
  , MOV (Reg RAX) (Reg R13)  -- len in R13
  -- Allocate len + 1 bytes
  , INC (Reg RAX)
  , MOV (Reg RAX) (Reg RDI)
  , CALL (Label "malloc")
  , MOV (Reg RAX) (Reg RBX)  -- result in RBX
  -- Copy in reverse
  , XOR (Reg RCX) (Reg RCX)  -- i = 0
  , LABEL "__str_reverse_loop"
  , CMP (Reg R13) (Reg RCX)
  , JGE (Label "__str_reverse_end")
  -- result[i] = s[len - 1 - i]
  , MOV (Reg R13) (Reg RAX)
  , DEC (Reg RAX)
  , SUB (Reg RCX) (Reg RAX)
  , MOV (Reg R12) (Reg RDX)
  , ADD (Reg RAX) (Reg RDX)
  , MOVZX (Mem RDX 0) (Reg RAX)
  , MOV (Reg RBX) (Reg RDX)
  , ADD (Reg RCX) (Reg RDX)
  , MOV (Reg RAX) (Mem RDX 0)  -- This needs byte move
  , INC (Reg RCX)
  , JMP (Label "__str_reverse_loop")
  , LABEL "__str_reverse_end"
  -- Null terminate
  , MOV (Reg RBX) (Reg RDX)
  , ADD (Reg R13) (Reg RDX)
  , MOV (Imm 0) (Mem RDX 0)
  , MOV (Reg RBX) (Reg RAX)
  , POP (Reg R13)
  , POP (Reg R12)
  , POP (Reg RBX)
  , POP (Reg RBP)
  , RET
  ]

-- | String compare: __str_compare(char* s1, char* s2) -> int
-- Returns strcmp result (0 if equal)
stringCompare :: [X86Instr]
stringCompare =
  [ COMMENT "String compare"
  , GLOBAL "__str_compare"
  , LABEL "__str_compare"
  -- Just call strcmp
  , JMP (Label "strcmp")
  ]

-- | String length: __str_length(char* s) -> int
stringLength :: [X86Instr]
stringLength =
  [ COMMENT "String length"
  , GLOBAL "__str_length"
  , LABEL "__str_length"
  -- Just call strlen
  , JMP (Label "strlen")
  ]

--------------------------------------------------------------------------------
-- Print Operations
--------------------------------------------------------------------------------

-- | Print integer: __print_int(int64_t n)
printInt :: [X86Instr]
printInt =
  [ COMMENT "Print integer"
  , GLOBAL "__print_int"
  , LABEL "__print_int"
  , PUSH (Reg RBP)
  , MOV (Reg RSP) (Reg RBP)
  -- Move n to RSI (second arg for printf)
  , MOV (Reg RDI) (Reg RSI)
  -- Load format string
  , LEA (LabelRIP "int_format") (Reg RDI)
  -- Clear RAX (no vector args)
  , XOR (Reg RAX) (Reg RAX)
  , CALL (Label "printf")
  , POP (Reg RBP)
  , RET
  ]

-- | Print string: __print_string(char* s)
printString :: [X86Instr]
printString =
  [ COMMENT "Print string"
  , GLOBAL "__print_string"
  , LABEL "__print_string"
  , PUSH (Reg RBP)
  , MOV (Reg RSP) (Reg RBP)
  -- Move s to RSI
  , MOV (Reg RDI) (Reg RSI)
  -- Load format string
  , LEA (LabelRIP "str_format") (Reg RDI)
  -- Clear RAX
  , XOR (Reg RAX) (Reg RAX)
  , CALL (Label "printf")
  , POP (Reg RBP)
  , RET
  ]

-- | Print boolean: __print_bool(int b)
printBool :: [X86Instr]
printBool =
  [ COMMENT "Print boolean"
  , GLOBAL "__print_bool"
  , LABEL "__print_bool"
  , PUSH (Reg RBP)
  , MOV (Reg RSP) (Reg RBP)
  , TEST (Reg RDI) (Reg RDI)
  , JZ (Label "__print_false")
  , LEA (LabelRIP "true_str") (Reg RSI)
  , JMP (Label "__print_bool_do")
  , LABEL "__print_false"
  , LEA (LabelRIP "false_str") (Reg RSI)
  , LABEL "__print_bool_do"
  , LEA (LabelRIP "str_format") (Reg RDI)
  , XOR (Reg RAX) (Reg RAX)
  , CALL (Label "printf")
  , POP (Reg RBP)
  , RET
  ]

-- | Print newline: __print_newline()
printNewline :: [X86Instr]
printNewline =
  [ COMMENT "Print newline"
  , GLOBAL "__print_newline"
  , LABEL "__print_newline"
  , PUSH (Reg RBP)
  , MOV (Reg RSP) (Reg RBP)
  , LEA (LabelRIP "newline_str") (Reg RSI)
  , LEA (LabelRIP "str_format") (Reg RDI)
  , XOR (Reg RAX) (Reg RAX)
  , CALL (Label "printf")
  , POP (Reg RBP)
  , RET
  ]
