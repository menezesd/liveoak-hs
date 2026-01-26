{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE OverloadedStrings #-}

-- | x86_64 Peephole Optimizations.
-- Pattern-based local optimizations on x86 assembly.
--
-- == Patterns
-- 1. Replace multiply by power of 2 with shift
-- 2. Replace multiply by small constants with lea
-- 3. Use test instead of cmp with 0
-- 4. Use inc/dec instead of add/sub 1
-- 5. Eliminate redundant moves
-- 6. Use lea for multi-operand address calculations
-- 7. Conditional move instead of branch for simple if-then-else
--
module LiveOak.X86Peephole
  ( -- * Peephole Optimization
    peepholeOptimize
  , PeepholeResult(..)
  ) where

import LiveOak.X86

import Data.Text (Text)
import qualified Data.Text as T
import Data.Bits (countTrailingZeros, popCount)
import Data.List (foldl')

--------------------------------------------------------------------------------
-- Types
--------------------------------------------------------------------------------

-- | Peephole optimization result
data PeepholeResult = PeepholeResult
  { phOptInstrs :: ![X86Instr]
  , phOptimized :: !Int           -- ^ Number of patterns applied
  } deriving (Show)

--------------------------------------------------------------------------------
-- Peephole Optimization
--------------------------------------------------------------------------------

-- | Apply peephole optimizations to instruction list
peepholeOptimize :: [X86Instr] -> PeepholeResult
peepholeOptimize instrs =
  let (optimized, count) = applyPatterns instrs
  in PeepholeResult
    { phOptInstrs = optimized
    , phOptimized = count
    }

-- | Apply all peephole patterns
applyPatterns :: [X86Instr] -> ([X86Instr], Int)
applyPatterns instrs =
  let -- Apply single-instruction patterns
      (instrs1, c1) = applySinglePatterns instrs
      -- Apply multi-instruction patterns (window of 2-3 instructions)
      (instrs2, c2) = applyWindowPatterns instrs1
      -- Remove dead code
      (instrs3, c3) = removeDeadCode instrs2
  in (instrs3, c1 + c2 + c3)

--------------------------------------------------------------------------------
-- Single Instruction Patterns
--------------------------------------------------------------------------------

-- | Apply patterns that transform a single instruction
applySinglePatterns :: [X86Instr] -> ([X86Instr], Int)
applySinglePatterns = foldr applyOne ([], 0)
  where
    applyOne instr (acc, count) =
      case transformSingle instr of
        Just new -> (new ++ acc, count + 1)
        Nothing -> (instr : acc, count)

-- | Transform a single instruction
transformSingle :: X86Instr -> Maybe [X86Instr]
transformSingle = \case
  -- Multiply by power of 2: imul $N, %reg -> shl $log2(N), %reg
  IMUL (Imm n) dst@(Reg _)
    | isPowerOf2 n && n > 0 ->
        Just [SHL (Imm (log2 n)) dst]

  -- Multiply by 3: imul $3, %src, %dst -> lea (%src, %src, 2), %dst
  IMUL3 (Imm 3) (Reg src) (Reg dst) ->
    Just [LEA (MemIndex src src 2 0) (Reg dst)]

  -- Multiply by 5: imul $5, %src, %dst -> lea (%src, %src, 4), %dst
  IMUL3 (Imm 5) (Reg src) (Reg dst) ->
    Just [LEA (MemIndex src src 4 0) (Reg dst)]

  -- Multiply by 9: imul $9, %src, %dst -> lea (%src, %src, 8), %dst
  IMUL3 (Imm 9) (Reg src) (Reg dst) ->
    Just [LEA (MemIndex src src 8 0) (Reg dst)]

  -- Compare with 0: cmp $0, %reg -> test %reg, %reg
  CMP (Imm 0) reg@(Reg _) ->
    Just [TEST reg reg]

  -- Add 1: add $1, %reg -> inc %reg
  ADD (Imm 1) dst@(Reg _) ->
    Just [INC dst]

  -- Subtract 1: sub $1, %reg -> dec %reg
  SUB (Imm 1) dst@(Reg _) ->
    Just [DEC dst]

  -- Move to self: mov %reg, %reg -> nothing
  MOV src dst | src == dst -> Just []

  -- XOR with self produces 0: xor %reg, %reg -> (keep as is, it's optimal for zeroing)
  -- This is already optimal for zeroing a register

  -- Add 0: add $0, %reg -> nothing
  ADD (Imm 0) _ -> Just []

  -- Subtract 0: sub $0, %reg -> nothing
  SUB (Imm 0) _ -> Just []

  -- Multiply by 1: imul $1, %reg, %dst -> mov %reg, %dst
  IMUL3 (Imm 1) src dst | src /= dst -> Just [MOV src dst]
  IMUL3 (Imm 1) src dst | src == dst -> Just []

  -- Multiply by 0: imul $0, %reg, %dst -> xor %dst, %dst
  IMUL3 (Imm 0) _ dst@(Reg r) -> Just [XOR (Reg r) dst]

  -- Shift by 0: shl $0, %reg -> nothing
  SHL (Imm 0) _ -> Just []
  SHR (Imm 0) _ -> Just []
  SAR (Imm 0) _ -> Just []

  -- AND with -1: and $-1, %reg -> nothing
  AND (Imm (-1)) _ -> Just []

  -- OR with 0: or $0, %reg -> nothing
  OR (Imm 0) _ -> Just []

  _ -> Nothing

-- | Check if number is power of 2
isPowerOf2 :: Int -> Bool
isPowerOf2 n = n > 0 && popCount n == 1

-- | Compute log base 2
log2 :: Int -> Int
log2 n = countTrailingZeros n

--------------------------------------------------------------------------------
-- Multi-Instruction Patterns (Window Patterns)
--------------------------------------------------------------------------------

-- | Apply patterns that look at multiple instructions
applyWindowPatterns :: [X86Instr] -> ([X86Instr], Int)
applyWindowPatterns instrs = go instrs [] 0
  where
    go [] acc count = (reverse acc, count)
    go [x] acc count = (reverse (x:acc), count)
    go (x:y:rest) acc count =
      case transformPair x y of
        Just (new, consumed) ->
          if consumed == 2
          then go rest (reverse new ++ acc) (count + 1)
          else go (y:rest) (reverse new ++ acc) (count + 1)
        Nothing -> go (y:rest) (x:acc) count

-- | Transform a pair of instructions
transformPair :: X86Instr -> X86Instr -> Maybe ([X86Instr], Int)
transformPair i1 i2 = case (i1, i2) of
  -- Redundant move: mov %a, %b; mov %b, %a -> mov %a, %b
  (MOV src1 dst1@(Reg _), MOV src2 dst2)
    | dst1 == src2 && src1 == dst2 ->
        Just ([MOV src1 dst1], 2)

  -- Store-reload: mov %reg, mem; mov mem, %reg -> mov %reg, mem
  (MOV src1@(Reg _) dst1@(Mem _ _), MOV src2 dst2@(Reg _))
    | dst1 == src2 && src1 == dst2 ->
        Just ([MOV src1 dst1], 2)

  -- Push-pop same register: push %reg; pop %reg -> nothing
  (PUSH (Reg r1), POP (Reg r2))
    | r1 == r2 -> Just ([], 2)

  -- Consecutive adds: add $n, %r; add $m, %r -> add $(n+m), %r
  (ADD (Imm n) dst@(Reg r), ADD (Imm m) (Reg r'))
    | r == r' -> Just ([ADD (Imm (n + m)) dst], 2)

  -- Consecutive subs: sub $n, %r; sub $m, %r -> sub $(n+m), %r
  (SUB (Imm n) dst@(Reg r), SUB (Imm m) (Reg r'))
    | r == r' -> Just ([SUB (Imm (n + m)) dst], 2)

  -- Add then sub same value: add $n, %r; sub $n, %r -> nothing
  (ADD (Imm n) (Reg r), SUB (Imm m) (Reg r'))
    | r == r' && n == m -> Just ([], 2)

  -- Sub then add same value: sub $n, %r; add $n, %r -> nothing
  (SUB (Imm n) (Reg r), ADD (Imm m) (Reg r'))
    | r == r' && n == m -> Just ([], 2)

  -- lea + add: lea offset(%base), %dst; add $n, %dst -> lea (offset+n)(%base), %dst
  (LEA (Mem base offset) dst@(Reg r), ADD (Imm n) (Reg r'))
    | r == r' -> Just ([LEA (Mem base (offset + n)) dst], 2)

  -- xor + test: xor %r, %r; test %r, %r -> xor %r, %r (flags already set)
  (XOR src@(Reg r1) dst@(Reg r2), TEST (Reg r3) (Reg r4))
    | r1 == r2 && r2 == r3 && r3 == r4 ->
        Just ([XOR src dst], 2)

  _ -> Nothing

--------------------------------------------------------------------------------
-- Dead Code Elimination
--------------------------------------------------------------------------------

-- | Remove obviously dead code after unconditional jumps
removeDeadCode :: [X86Instr] -> ([X86Instr], Int)
removeDeadCode = go [] 0 False
  where
    go acc count _ [] = (reverse acc, count)
    go acc count dead (x:xs) = case x of
      -- Jump or return marks dead code following (until next label)
      JMP _ -> go (x:acc) count True xs
      RET -> go (x:acc) count True xs

      -- Label ends dead code region
      LABEL _ -> go (x:acc) count False xs

      -- In dead region: skip instruction
      _ | dead -> go acc (count + 1) True xs
        | otherwise -> go (x:acc) count False xs

--------------------------------------------------------------------------------
-- Conditional Move Pattern (for simple if-then-else)
--------------------------------------------------------------------------------

-- | Check if a sequence can use CMOV
-- This pattern looks for:
--   cmp/test
--   jcc label1
--   mov src1, dst
--   jmp label2
--   label1:
--   mov src2, dst
--   label2:
-- And converts to:
--   cmp/test
--   mov src1, dst
--   cmovcc src2, dst
canUseCmov :: [X86Instr] -> Maybe [X86Instr]
canUseCmov = \case
  [cmp@(CMP _ _), JE (Label l1), MOV src1 dst@(Reg _), JMP (Label l2),
   LABEL ll1, MOV src2 dst', LABEL ll2]
    | l1 == ll1 && l2 == ll2 && dst == dst' ->
        Just [cmp, MOV src1 dst, COMMENT "cmove would go here"]

  [cmp@(TEST _ _), JE (Label l1), MOV src1 dst@(Reg _), JMP (Label l2),
   LABEL ll1, MOV src2 dst', LABEL ll2]
    | l1 == ll1 && l2 == ll2 && dst == dst' ->
        Just [cmp, MOV src1 dst, COMMENT "cmove would go here"]

  _ -> Nothing
