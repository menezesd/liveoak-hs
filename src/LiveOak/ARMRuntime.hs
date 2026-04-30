{-# LANGUAGE OverloadedStrings #-}

-- | AArch64 runtime support code.
-- Generates assembly for runtime helpers (string operations, I/O, etc.)
module LiveOak.ARMRuntime
  ( emitARMRuntime
  ) where

import LiveOak.ARM

--------------------------------------------------------------------------------
-- Runtime Generation
--------------------------------------------------------------------------------

-- | Generate the runtime support code
emitARMRuntime :: [ARMInstr]
emitARMRuntime = concat
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
runtimeHeader :: [ARMInstr]
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
stringConcat :: [ARMInstr]
stringConcat =
  [ COMMENT "String concatenation"
  , GLOBAL "__str_concat"
  , LABEL "__str_concat"
  , STP XFP XLR (MemPreIdx XSP (-16))
  , MOV (Reg XFP) (Reg XSP)
  , STP X19 X20 (MemPreIdx XSP (-16))
  , STP X21 X22 (MemPreIdx XSP (-16))
  -- Save arguments
  , MOV (Reg X19) (Reg X0)    -- s1
  , MOV (Reg X20) (Reg X1)    -- s2
  -- Get length of s1
  , MOV (Reg X0) (Reg X19)
  , BL (Label "strlen")
  , MOV (Reg X21) (Reg X0)    -- len1 in X21
  -- Get length of s2
  , MOV (Reg X0) (Reg X20)
  , BL (Label "strlen")
  -- Total length = len1 + len2 + 1
  , ADD (Reg X0) (Reg X0) (Reg X21)
  , ADD (Reg X0) (Reg X0) (Imm 1)
  -- Allocate
  , BL (Label "malloc")
  , MOV (Reg X21) (Reg X0)    -- result in X21
  -- Copy s1
  , MOV (Reg X0) (Reg X21)
  , MOV (Reg X1) (Reg X19)
  , BL (Label "strcpy")
  -- Concatenate s2
  , MOV (Reg X0) (Reg X21)
  , MOV (Reg X1) (Reg X20)
  , BL (Label "strcat")
  -- Return result
  , MOV (Reg X0) (Reg X21)
  , LDP X21 X22 (MemPostIdx XSP 16)
  , LDP X19 X20 (MemPostIdx XSP 16)
  , LDP XFP XLR (MemPostIdx XSP 16)
  , RET
  ]

-- | String repeat: __str_repeat(char* s, int n) -> char*
stringRepeat :: [ARMInstr]
stringRepeat =
  [ COMMENT "String repeat"
  , GLOBAL "__str_repeat"
  , LABEL "__str_repeat"
  , STP XFP XLR (MemPreIdx XSP (-16))
  , MOV (Reg XFP) (Reg XSP)
  , STP X19 X20 (MemPreIdx XSP (-16))
  , STP X21 X22 (MemPreIdx XSP (-16))
  -- Save arguments
  , MOV (Reg X19) (Reg X0)    -- s
  , MOV (Reg X20) (Reg X1)    -- n
  -- Handle n <= 0
  , CMP (Reg X20) (Imm 0)
  , Bcond CondGT (Label "__str_repeat_positive")
  -- Return empty string
  , MOV (Reg X0) (Imm 1)
  , BL (Label "malloc")
  , STRB (WReg XZR) (MemOff X0 0)
  , B (Label "__str_repeat_done")
  , LABEL "__str_repeat_positive"
  -- Get length of s
  , MOV (Reg X0) (Reg X19)
  , BL (Label "strlen")
  , MOV (Reg X21) (Reg X0)    -- len in X21
  -- Total size = len * n + 1
  , MUL (Reg X0) (Reg X0) (Reg X20)
  , ADD (Reg X0) (Reg X0) (Imm 1)
  , BL (Label "malloc")
  , MOV (Reg X22) (Reg X0)    -- result in X22
  -- Initialize result to empty
  , STRB (WReg XZR) (MemOff X22 0)
  -- Loop n times
  , LABEL "__str_repeat_loop"
  , CBZ (Reg X20) (Label "__str_repeat_done2")
  , MOV (Reg X0) (Reg X22)
  , MOV (Reg X1) (Reg X19)
  , BL (Label "strcat")
  , SUB (Reg X20) (Reg X20) (Imm 1)
  , B (Label "__str_repeat_loop")
  , LABEL "__str_repeat_done2"
  , MOV (Reg X0) (Reg X22)
  , LABEL "__str_repeat_done"
  , LDP X21 X22 (MemPostIdx XSP 16)
  , LDP X19 X20 (MemPostIdx XSP 16)
  , LDP XFP XLR (MemPostIdx XSP 16)
  , RET
  ]

-- | String reverse: __str_reverse(char* s) -> char*
stringReverse :: [ARMInstr]
stringReverse =
  [ COMMENT "String reverse"
  , GLOBAL "__str_reverse"
  , LABEL "__str_reverse"
  , STP XFP XLR (MemPreIdx XSP (-16))
  , MOV (Reg XFP) (Reg XSP)
  , STP X19 X20 (MemPreIdx XSP (-16))
  , STP X21 X22 (MemPreIdx XSP (-16))
  -- Save argument
  , MOV (Reg X19) (Reg X0)    -- s
  -- Get length
  , BL (Label "strlen")
  , MOV (Reg X20) (Reg X0)    -- len in X20
  -- Allocate len + 1 bytes
  , ADD (Reg X0) (Reg X0) (Imm 1)
  , BL (Label "malloc")
  , MOV (Reg X21) (Reg X0)    -- result in X21
  -- Copy in reverse: i = 0
  , MOV (Reg X22) (Imm 0)
  , LABEL "__str_reverse_loop"
  , CMP (Reg X22) (Reg X20)
  , Bcond CondGE (Label "__str_reverse_end")
  -- result[i] = s[len - 1 - i]
  , SUB (Reg X2) (Reg X20) (Imm 1)
  , SUB (Reg X2) (Reg X2) (Reg X22)
  , LDRB (WReg X3) (MemOff X19 0)  -- placeholder: need indexed addressing
  -- Use add for indexed load
  , ADD (Reg X2) (Reg X19) (Reg X2)
  , LDRB (WReg X3) (MemOff X2 0)
  , ADD (Reg X4) (Reg X21) (Reg X22)
  , STRB (WReg X3) (MemOff X4 0)
  , ADD (Reg X22) (Reg X22) (Imm 1)
  , B (Label "__str_reverse_loop")
  , LABEL "__str_reverse_end"
  -- Null terminate
  , ADD (Reg X2) (Reg X21) (Reg X20)
  , STRB (WReg XZR) (MemOff X2 0)
  , MOV (Reg X0) (Reg X21)
  , LDP X21 X22 (MemPostIdx XSP 16)
  , LDP X19 X20 (MemPostIdx XSP 16)
  , LDP XFP XLR (MemPostIdx XSP 16)
  , RET
  ]

-- | String compare: __str_compare(char* s1, char* s2) -> int
stringCompare :: [ARMInstr]
stringCompare =
  [ COMMENT "String compare"
  , GLOBAL "__str_compare"
  , LABEL "__str_compare"
  -- Just tail-call strcmp (args already in x0, x1)
  , B (Label "strcmp")
  ]

-- | String length: __str_length(char* s) -> int
stringLength :: [ARMInstr]
stringLength =
  [ COMMENT "String length"
  , GLOBAL "__str_length"
  , LABEL "__str_length"
  -- Just tail-call strlen (arg already in x0)
  , B (Label "strlen")
  ]

--------------------------------------------------------------------------------
-- Print Operations
--------------------------------------------------------------------------------

-- | Print integer: __print_int(int64_t n)
printInt :: [ARMInstr]
printInt =
  [ COMMENT "Print integer"
  , GLOBAL "__print_int"
  , LABEL "__print_int"
  , STP XFP XLR (MemPreIdx XSP (-16))
  , MOV (Reg XFP) (Reg XSP)
  -- Move n to x1 (second arg for printf)
  , MOV (Reg X1) (Reg X0)
  -- Load format string
  , ADRP (Reg X0) (Label "int_format")
  , ADD (Reg X0) (Reg X0) (LabelLo12 "int_format")
  , BL (Label "printf")
  , LDP XFP XLR (MemPostIdx XSP 16)
  , RET
  ]

-- | Print string: __print_string(char* s)
printString :: [ARMInstr]
printString =
  [ COMMENT "Print string"
  , GLOBAL "__print_string"
  , LABEL "__print_string"
  , STP XFP XLR (MemPreIdx XSP (-16))
  , MOV (Reg XFP) (Reg XSP)
  -- Move s to x1
  , MOV (Reg X1) (Reg X0)
  -- Load format string
  , ADRP (Reg X0) (Label "str_format")
  , ADD (Reg X0) (Reg X0) (LabelLo12 "str_format")
  , BL (Label "printf")
  , LDP XFP XLR (MemPostIdx XSP 16)
  , RET
  ]

-- | Print boolean: __print_bool(int b)
printBool :: [ARMInstr]
printBool =
  [ COMMENT "Print boolean"
  , GLOBAL "__print_bool"
  , LABEL "__print_bool"
  , STP XFP XLR (MemPreIdx XSP (-16))
  , MOV (Reg XFP) (Reg XSP)
  , CBZ (Reg X0) (Label "__print_false")
  , ADRP (Reg X1) (Label "true_str")
  , ADD (Reg X1) (Reg X1) (LabelLo12 "true_str")
  , B (Label "__print_bool_do")
  , LABEL "__print_false"
  , ADRP (Reg X1) (Label "false_str")
  , ADD (Reg X1) (Reg X1) (LabelLo12 "false_str")
  , LABEL "__print_bool_do"
  , ADRP (Reg X0) (Label "str_format")
  , ADD (Reg X0) (Reg X0) (LabelLo12 "str_format")
  , BL (Label "printf")
  , LDP XFP XLR (MemPostIdx XSP 16)
  , RET
  ]

-- | Print newline: __print_newline()
printNewline :: [ARMInstr]
printNewline =
  [ COMMENT "Print newline"
  , GLOBAL "__print_newline"
  , LABEL "__print_newline"
  , STP XFP XLR (MemPreIdx XSP (-16))
  , MOV (Reg XFP) (Reg XSP)
  , ADRP (Reg X1) (Label "newline_str")
  , ADD (Reg X1) (Reg X1) (LabelLo12 "newline_str")
  , ADRP (Reg X0) (Label "str_format")
  , ADD (Reg X0) (Reg X0) (LabelLo12 "str_format")
  , BL (Label "printf")
  , LDP XFP XLR (MemPostIdx XSP 16)
  , RET
  ]
