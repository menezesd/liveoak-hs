{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE OverloadedStrings #-}

-- | AArch64 Peephole Optimizations.
-- Pattern-based local optimizations on ARM assembly.
--
-- == Patterns
-- 1. Remove redundant moves (mov x0, x0)
-- 2. Remove identity add/sub with 0
-- 3. Replace cmp #0 + b.eq/b.ne with cbz/cbnz
-- 4. Eliminate redundant store-reload pairs
-- 5. Dead code after unconditional branches
--
module LiveOak.ARMPeephole
  ( -- * Peephole Optimization
    peepholeOptimize
  , PeepholeResult(..)
  ) where

import LiveOak.ARM

--------------------------------------------------------------------------------
-- Types
--------------------------------------------------------------------------------

-- | Peephole optimization result
data PeepholeResult = PeepholeResult
  { phOptInstrs :: ![ARMInstr]
  , phOptimized :: !Int           -- ^ Number of patterns applied
  } deriving (Show)

--------------------------------------------------------------------------------
-- Peephole Optimization
--------------------------------------------------------------------------------

-- | Apply peephole optimizations to instruction list
peepholeOptimize :: [ARMInstr] -> PeepholeResult
peepholeOptimize instrs =
  let (optimized, count) = applyPatterns instrs
  in PeepholeResult
    { phOptInstrs = optimized
    , phOptimized = count
    }

-- | Apply all peephole patterns
applyPatterns :: [ARMInstr] -> ([ARMInstr], Int)
applyPatterns instrs =
  let (instrs1, c1) = applySinglePatterns instrs
      (instrs2, c2) = applyWindowPatterns instrs1
      (instrs3, c3) = removeDeadCode instrs2
  in (instrs3, c1 + c2 + c3)

--------------------------------------------------------------------------------
-- Single Instruction Patterns
--------------------------------------------------------------------------------

-- | Apply patterns that transform a single instruction
applySinglePatterns :: [ARMInstr] -> ([ARMInstr], Int)
applySinglePatterns = foldr applyOne ([], 0)
  where
    applyOne instr (acc, count) =
      case transformSingle instr of
        Just new -> (new ++ acc, count + 1)
        Nothing  -> (instr : acc, count)

-- | Transform a single instruction
transformSingle :: ARMInstr -> Maybe [ARMInstr]
transformSingle = \case
  -- Move to self: mov x0, x0 -> nothing
  MOV (Reg r1) (Reg r2) | r1 == r2 -> Just []

  -- Add 0: add x0, x0, #0 -> nothing
  ADD _ (Reg _) (Imm 0) -> Just []

  -- Sub 0: sub x0, x0, #0 -> nothing
  SUB _ (Reg _) (Imm 0) -> Just []

  -- Shift by 0: nothing
  LSL _ _ (Imm 0) -> Just []
  LSR _ _ (Imm 0) -> Just []
  ASR _ _ (Imm 0) -> Just []

  -- AND with all 1s: nothing
  AND dst src (Imm (-1)) | dst == src -> Just []

  -- ORR with 0: nothing
  ORR dst src (Imm 0) | dst == src -> Just []

  _ -> Nothing

--------------------------------------------------------------------------------
-- Multi-Instruction Patterns (Window Patterns)
--------------------------------------------------------------------------------

-- | Apply patterns that look at multiple instructions
applyWindowPatterns :: [ARMInstr] -> ([ARMInstr], Int)
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
transformPair :: ARMInstr -> ARMInstr -> Maybe ([ARMInstr], Int)
transformPair i1 i2 = case (i1, i2) of
  -- cmp x0, #0; b.eq label -> cbz x0, label
  (CMP reg@(Reg _) (Imm 0), Bcond CondEQ target) ->
    Just ([CBZ reg target], 2)

  -- cmp x0, #0; b.ne label -> cbnz x0, label
  (CMP reg@(Reg _) (Imm 0), Bcond CondNE target) ->
    Just ([CBNZ reg target], 2)

  -- Redundant move pair: mov x1, x0; mov x0, x1 -> mov x1, x0
  (MOV dst1@(Reg _) src1@(Reg _), MOV dst2@(Reg _) src2@(Reg _))
    | dst1 == src2 && src1 == dst2 ->
        Just ([MOV dst1 src1], 2)

  -- Store-reload: str x0, [addr]; ldr x0, [addr] -> str x0, [addr]
  (STR src1@(Reg _) addr1@(MemOff _ _), LDR dst2@(Reg _) addr2@(MemOff _ _))
    | src1 == dst2 && addr1 == addr2 ->
        Just ([STR src1 addr1], 2)

  -- Consecutive adds: add x0, x0, #n; add x0, x0, #m -> add x0, x0, #(n+m)
  (ADD dst1@(Reg r1) (Reg s1) (Imm n), ADD (Reg r2) (Reg s2) (Imm m))
    | r1 == r2 && r1 == s1 && r2 == s2 ->
        Just ([ADD dst1 (Reg s1) (Imm (n + m))], 2)

  -- Consecutive subs: sub x0, x0, #n; sub x0, x0, #m -> sub x0, x0, #(n+m)
  (SUB dst1@(Reg r1) (Reg s1) (Imm n), SUB (Reg r2) (Reg s2) (Imm m))
    | r1 == r2 && r1 == s1 && r2 == s2 ->
        Just ([SUB dst1 (Reg s1) (Imm (n + m))], 2)

  -- Add then sub same: add x0, x0, #n; sub x0, x0, #n -> nothing
  (ADD (Reg r1) (Reg s1) (Imm n), SUB (Reg r2) (Reg s2) (Imm m))
    | r1 == r2 && r1 == s1 && r2 == s2 && n == m -> Just ([], 2)

  -- Sub then add same: sub x0, x0, #n; add x0, x0, #n -> nothing
  (SUB (Reg r1) (Reg s1) (Imm n), ADD (Reg r2) (Reg s2) (Imm m))
    | r1 == r2 && r1 == s1 && r2 == s2 && n == m -> Just ([], 2)

  _ -> Nothing

--------------------------------------------------------------------------------
-- Dead Code Elimination
--------------------------------------------------------------------------------

-- | Remove obviously dead code after unconditional branches
removeDeadCode :: [ARMInstr] -> ([ARMInstr], Int)
removeDeadCode = go [] 0 False
  where
    go acc count _ [] = (reverse acc, count)
    go acc count dead (x:xs) = case x of
      B _   -> go (x:acc) count True xs
      RET   -> go (x:acc) count True xs
      LABEL _ -> go (x:acc) count False xs
      _ | dead     -> go acc (count + 1) True xs
        | otherwise -> go (x:acc) count False xs
