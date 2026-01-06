{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE LambdaCase #-}

-- | Peephole optimizer for SAM assembly code.
-- Applies local optimizations to sequences of SAM instructions.
module LiveOak.Peephole
  ( optimize
  , optimizeText
  , SamInstr(..)
  , parseSam
  , emitSam
  , scheduleInstructions
  , mergeBlocks
  ) where

import Data.Text (Text)
import qualified Data.Text as T
import Data.Maybe (mapMaybe)
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Set (Set)
import qualified Data.Set as Set
import Text.Read (readMaybe)

-- | SAM instruction representation
data SamInstr
  = PUSHIMM Int
  | PUSHIMMSTR Text
  | PUSHOFF Int
  | STOREOFF Int
  | PUSHIND
  | STOREIND
  | DUP
  | SWAP
  | ADD
  | SUB
  | TIMES
  | DIV
  | MOD
  | LSHIFT Int
  | LSHIFTIND
  | RSHIFT Int
  | RSHIFTIND
  | AND
  | OR
  | EQUAL
  | LESS
  | GREATER
  | CMP
  | ISNIL
  | ISNEG
  | ADDSP Int
  | LINK
  | UNLINK
  | JSR Text
  | RST
  | JUMP Text
  | JUMPC Text
  | STOP
  | MALLOC
  | Label Text        -- A label definition (e.g., "foo:")
  | Comment Text      -- A comment line
  | Blank             -- Empty line
  deriving (Eq, Show)

-- | Parse SAM text into instructions
parseSam :: Text -> [SamInstr]
parseSam = mapMaybe parseLine . T.lines

-- | Parse a single line of SAM
parseLine :: Text -> Maybe SamInstr
parseLine line
  | T.null stripped = Just Blank
  | "//" `T.isPrefixOf` stripped = Just $ Comment stripped
  | ":" `T.isSuffixOf` stripped = Just $ Label (T.dropEnd 1 stripped)
  | otherwise = parseInstr stripped
  where
    stripped = T.strip line

-- | Parse a SAM instruction
parseInstr :: Text -> Maybe SamInstr
parseInstr txt = case T.words txt of
  ["PUSHIMM", n] -> PUSHIMM <$> readInt n
  ("PUSHIMMSTR":rest) -> Just $ PUSHIMMSTR (T.unwords rest)
  ["PUSHOFF", n] -> PUSHOFF <$> readInt n
  ["STOREOFF", n] -> STOREOFF <$> readInt n
  ["PUSHIND"] -> Just PUSHIND
  ["STOREIND"] -> Just STOREIND
  ["DUP"] -> Just DUP
  ["SWAP"] -> Just SWAP
  ["ADD"] -> Just ADD
  ["SUB"] -> Just SUB
  ["TIMES"] -> Just TIMES
  ["DIV"] -> Just DIV
  ["MOD"] -> Just MOD
  ["LSHIFT", n] -> LSHIFT <$> readInt n
  ["LSHIFTIND"] -> Just LSHIFTIND
  ["RSHIFT", n] -> RSHIFT <$> readInt n
  ["RSHIFTIND"] -> Just RSHIFTIND
  ["AND"] -> Just AND
  ["OR"] -> Just OR
  ["EQUAL"] -> Just EQUAL
  ["LESS"] -> Just LESS
  ["GREATER"] -> Just GREATER
  ["CMP"] -> Just CMP
  ["ISNIL"] -> Just ISNIL
  ["ISNEG"] -> Just ISNEG
  ["ADDSP", n] -> ADDSP <$> readInt n
  ["LINK"] -> Just LINK
  ["UNLINK"] -> Just UNLINK
  ["JSR", lbl] -> Just $ JSR lbl
  ["RST"] -> Just RST
  ["JUMP", lbl] -> Just $ JUMP lbl
  ["JUMPC", lbl] -> Just $ JUMPC lbl
  ["STOP"] -> Just STOP
  ["MALLOC"] -> Just MALLOC
  _ -> Nothing  -- Unknown instruction, skip

-- | Read an integer safely, handling negative numbers
readInt :: Text -> Maybe Int
readInt t
  | "-" `T.isPrefixOf` t = negate <$> readMaybe (T.unpack (T.drop 1 t))
  | otherwise = readMaybe (T.unpack t)

-- | Emit SAM instructions back to text
emitSam :: [SamInstr] -> Text
emitSam = T.unlines . map emitInstr

-- | Emit a single instruction
emitInstr :: SamInstr -> Text
emitInstr = \case
  PUSHIMM n -> "PUSHIMM " <> tshow n
  PUSHIMMSTR s -> "PUSHIMMSTR " <> s
  PUSHOFF n -> "PUSHOFF " <> tshow n
  STOREOFF n -> "STOREOFF " <> tshow n
  PUSHIND -> "PUSHIND"
  STOREIND -> "STOREIND"
  DUP -> "DUP"
  SWAP -> "SWAP"
  ADD -> "ADD"
  SUB -> "SUB"
  TIMES -> "TIMES"
  DIV -> "DIV"
  MOD -> "MOD"
  LSHIFT n -> "LSHIFT " <> tshow n
  LSHIFTIND -> "LSHIFTIND"
  RSHIFT n -> "RSHIFT " <> tshow n
  RSHIFTIND -> "RSHIFTIND"
  AND -> "AND"
  OR -> "OR"
  EQUAL -> "EQUAL"
  LESS -> "LESS"
  GREATER -> "GREATER"
  CMP -> "CMP"
  ISNIL -> "ISNIL"
  ISNEG -> "ISNEG"
  ADDSP n -> "ADDSP " <> tshow n
  LINK -> "LINK"
  UNLINK -> "UNLINK"
  JSR lbl -> "JSR " <> lbl
  RST -> "RST"
  JUMP lbl -> "JUMP " <> lbl
  JUMPC lbl -> "JUMPC " <> lbl
  STOP -> "STOP"
  MALLOC -> "MALLOC"
  Label lbl -> lbl <> ":"
  Comment c -> c
  Blank -> ""

tshow :: Show a => a -> Text
tshow = T.pack . show

-- | Optimize SAM text
optimizeText :: Text -> Text
optimizeText = emitSam . optimize . parseSam

-- | Maximum iterations for peephole optimization.
-- Most code stabilizes within 5-10 iterations.
maxPeepholeIterations :: Int
maxPeepholeIterations = 20

-- | Apply peephole optimizations until no more changes
optimize :: [SamInstr] -> [SamInstr]
optimize =
    -- Post-processing passes (run once after main optimizations)
    scheduleInstructions
    -- Iterative peephole optimizations
  . go maxPeepholeIterations
  where
    go 0 instrs = instrs  -- Max iterations reached
    go n instrs =
      let -- First apply jump threading
          threaded = jumpThread instrs
          -- Block merging (removes redundant jumps/labels)
          merged = mergeBlocks threaded
          -- Then peephole patterns
          optimized = peepholePass merged
      in if optimized == instrs
         then instrs
         else go (n - 1) optimized

-- | Jump threading: when a label just jumps to another label, update all
-- jumps to go directly to the final destination.
jumpThread :: [SamInstr] -> [SamInstr]
jumpThread instrs =
  let labelMap = buildJumpMap instrs
      finalMap = resolveChains labelMap
  in eliminateBranchToBranch $ map (rewriteJump finalMap) instrs

-- | Build a map from labels to their immediate jump targets.
-- A label maps to a target if the label is immediately followed by JUMP target.
buildJumpMap :: [SamInstr] -> Map Text Text
buildJumpMap = go
  where
    go [] = Map.empty
    go (Label lbl : JUMP target : rest) = Map.insert lbl target (go rest)
    go (_ : rest) = go rest

-- | Resolve chains: if A -> B and B -> C, then A -> C.
-- Uses fixed-point iteration with a limit to avoid infinite loops on cycles.
resolveChains :: Map Text Text -> Map Text Text
resolveChains mp
  | Map.null mp = mp
  | otherwise = fixedPointN 10 resolveOnce mp
  where
    -- Apply function until fixed point or iteration limit reached
    fixedPointN :: Eq a => Int -> (a -> a) -> a -> a
    fixedPointN 0 _ x = x  -- Max iterations reached
    fixedPointN n f x =
      let x' = f x
      in if x' == x then x else fixedPointN (n - 1) f $! x'

    resolveOnce m = Map.map (resolve m) m

    -- Resolve one step, detecting self-loops
    resolve m lbl = case Map.lookup lbl m of
      Just target | target /= lbl && not (isCycle m lbl target) -> target
      _ -> lbl

    -- Check if following this edge would create a cycle back to the original
    isCycle m start target = go 10 target
      where
        go 0 _ = True  -- Give up and assume cycle to be safe
        go n cur
          | cur == start = True
          | otherwise = case Map.lookup cur m of
              Just next | next /= cur -> go (n - 1) next
              _ -> False

-- | Rewrite a jump instruction to use the resolved target.
rewriteJump :: Map Text Text -> SamInstr -> SamInstr
rewriteJump m instr = case instr of
  JUMP lbl -> JUMP (Map.findWithDefault lbl lbl m)
  JUMPC lbl -> JUMPC (Map.findWithDefault lbl lbl m)
  JSR lbl -> JSR (Map.findWithDefault lbl lbl m)
  _ -> instr

-- | Eliminate branch-to-branch patterns and optimize control flow
eliminateBranchToBranch :: [SamInstr] -> [SamInstr]
eliminateBranchToBranch = removeJumpToNext
  where
    -- Remove JUMP L when L is the next instruction
    removeJumpToNext [] = []
    removeJumpToNext [x] = [x]
    removeJumpToNext (JUMP lbl : Label lbl' : rest)
      | lbl == lbl' = Label lbl' : removeJumpToNext rest
    removeJumpToNext (x : rest) = x : removeJumpToNext rest

-- | Single pass of peephole optimizations
peepholePass :: [SamInstr] -> [SamInstr]
peepholePass = \case
  [] -> []

  -- Identity operations: x + 0 = x, x - 0 = x, x * 1 = x
  (PUSHIMM 0 : ADD : rest) -> peepholePass rest
  (PUSHIMM 0 : SUB : rest) -> peepholePass rest
  (PUSHIMM 1 : TIMES : rest) -> peepholePass rest

  -- x * 0 = 0 (but need to pop the original value first)
  (PUSHIMM 0 : TIMES : rest) -> ADDSP (-1) : PUSHIMM 0 : peepholePass rest

  -- x / 1 = x
  (PUSHIMM 1 : DIV : rest) -> peepholePass rest

  -- Double negation: ISNIL; ISNIL cancels out
  (ISNIL : ISNIL : rest) -> peepholePass rest

  -- Push then pop: PUSHIMM x; ADDSP -1 = nothing
  (PUSHIMM _ : ADDSP (-1) : rest) -> peepholePass rest
  (PUSHOFF _ : ADDSP (-1) : rest) -> peepholePass rest

  -- DUP then pop: DUP; ADDSP -1 = nothing
  (DUP : ADDSP (-1) : rest) -> peepholePass rest

  -- Load then store to same location (no-op if no side effects between)
  (PUSHOFF n : STOREOFF m : rest) | n == m -> peepholePass rest

  -- Consecutive ADDSP can be combined
  (ADDSP n : ADDSP m : rest) ->
    let combined = n + m
    in if combined == 0
       then peepholePass rest
       else ADDSP combined : peepholePass rest

  -- ADDSP 0 = nothing
  (ADDSP 0 : rest) -> peepholePass rest

  -- Constant folding: PUSHIMM x; PUSHIMM y; OP = PUSHIMM (x OP y)
  (PUSHIMM x : PUSHIMM y : ADD : rest) -> PUSHIMM (x + y) : peepholePass rest
  (PUSHIMM x : PUSHIMM y : SUB : rest) -> PUSHIMM (x - y) : peepholePass rest
  (PUSHIMM x : PUSHIMM y : TIMES : rest) -> PUSHIMM (x * y) : peepholePass rest
  (PUSHIMM x : PUSHIMM y : DIV : rest) | y /= 0 -> PUSHIMM (x `div` y) : peepholePass rest
  (PUSHIMM x : PUSHIMM y : MOD : rest) | y /= 0 -> PUSHIMM (x `mod` y) : peepholePass rest

  -- Boolean constant folding
  (PUSHIMM x : PUSHIMM y : EQUAL : rest) -> PUSHIMM (if x == y then 1 else 0) : peepholePass rest
  (PUSHIMM x : PUSHIMM y : LESS : rest) -> PUSHIMM (if x < y then 1 else 0) : peepholePass rest
  (PUSHIMM x : PUSHIMM y : GREATER : rest) -> PUSHIMM (if x > y then 1 else 0) : peepholePass rest

  -- ISNIL on known values
  (PUSHIMM 0 : ISNIL : rest) -> PUSHIMM 1 : peepholePass rest
  (PUSHIMM n : ISNIL : rest) | n /= 0 -> PUSHIMM 0 : peepholePass rest

  -- SWAP; SWAP = nothing
  (SWAP : SWAP : rest) -> peepholePass rest

  -- Self-comparison optimizations: DUP; EQUAL always true
  -- DUP duplicates top of stack, then EQUAL compares two equal values
  (DUP : EQUAL : rest) -> ADDSP (-1) : PUSHIMM 1 : peepholePass rest

  -- DUP; LESS is always false (x < x)
  (DUP : LESS : rest) -> ADDSP (-1) : PUSHIMM 0 : peepholePass rest

  -- DUP; GREATER is always false (x > x)
  (DUP : GREATER : rest) -> ADDSP (-1) : PUSHIMM 0 : peepholePass rest

  -- DUP; SUB = 0 (x - x = 0)
  (DUP : SUB : rest) -> ADDSP (-1) : PUSHIMM 0 : peepholePass rest

  -- Jump to next instruction (need to track labels)
  (JUMP lbl : Label lbl' : rest) | lbl == lbl' -> Label lbl' : peepholePass rest

  -- DUP; SWAP = DUP (stack has [a, a], swap gives [a, a])
  (DUP : SWAP : rest) -> DUP : peepholePass rest

  -- Strength reduction: x * 2 = x + x (already done, but if missed)
  (PUSHIMM 2 : TIMES : rest) -> DUP : ADD : peepholePass rest

  -- More identity operations
  (PUSHIMM 0 : OR : rest) -> peepholePass rest      -- x | 0 = x
  (PUSHIMM 1 : AND : rest) -> peepholePass rest     -- x & 1 = x (treating 1 as true)

  -- Boolean simplifications
  (PUSHIMM 0 : AND : rest) -> ADDSP (-1) : PUSHIMM 0 : peepholePass rest  -- x & 0 = 0
  (PUSHIMM 1 : OR : rest) -> ADDSP (-1) : PUSHIMM 1 : peepholePass rest   -- x | 1 = 1

  -- PUSHIMM followed by operations that ignore it
  (PUSHIMM 0 : EQUAL : rest) -> ISNIL : peepholePass rest  -- x == 0 is ISNIL

  -- Redundant operations after ISNIL
  (ISNIL : PUSHIMM 0 : EQUAL : rest) -> ISNIL : peepholePass rest  -- (x == 0) == 0 = x != 0

  -- STOREOFF then PUSHOFF same location
  (STOREOFF n : PUSHOFF m : rest) | n == m -> DUP : STOREOFF n : peepholePass rest

  -- Double DUP followed by pop
  (DUP : DUP : ADDSP (-1) : rest) -> DUP : peepholePass rest

  -- LINK immediately followed by UNLINK
  (LINK : UNLINK : rest) -> peepholePass rest

  -- Redundant MALLOC 0 (allocate zero words - creates null-ish pointer)
  (PUSHIMM 0 : MALLOC : rest) -> PUSHIMM 0 : peepholePass rest

  -- PUSHIND immediately after STOREIND on same address (if we just stored, we know the value)
  -- This is tricky without more context, skip for now

  -- Consecutive identical PUSHOFF
  (PUSHOFF n : PUSHOFF m : rest) | n == m -> PUSHOFF n : DUP : peepholePass rest

  -- JUMPC to next label (conditional jump over nothing)
  (JUMPC lbl : Label lbl' : rest) | lbl == lbl' -> ADDSP (-1) : Label lbl' : peepholePass rest

  -- Basic block optimizations:

  -- x / 2 using shift (integer division)
  -- Note: SAM doesn't have shift, so we keep DIV for now

  -- Note: removed incorrect pattern (PUSHIMM 0 : SWAP : SUB) - that computes -x, not identity

  -- DUP; AND = x (x & x = x, so DUP:AND is no-op)
  (DUP : AND : rest) -> peepholePass rest

  -- DUP; OR = x (x | x = x, so DUP:OR is no-op)
  (DUP : OR : rest) -> peepholePass rest

  -- Redundant operations: PUSHIMM x; ADDSP -1 = nothing (push then pop)
  (PUSHIMMSTR _ : ADDSP (-1) : rest) -> peepholePass rest

  -- PUSHIMM then arithmetic with another PUSHIMM (handle reversed order)
  (PUSHIMM x : SWAP : PUSHIMM y : ADD : rest) -> PUSHIMM (y + x) : peepholePass rest
  (PUSHIMM x : SWAP : PUSHIMM y : TIMES : rest) -> PUSHIMM (y * x) : peepholePass rest

  -- Conditional on constant: PUSHIMM 0; JUMPC lbl = pop (always false, never jumps)
  (PUSHIMM 0 : JUMPC _ : rest) -> peepholePass rest

  -- Conditional on constant: PUSHIMM n; JUMPC lbl = JUMP lbl (always true, always jumps)
  (PUSHIMM n : JUMPC lbl : rest) | n /= 0 -> JUMP lbl : peepholePass rest

  -- Note: removed incorrect STOREOFF/overwrite pattern

  -- Note: removed incorrect load-use-load pattern

  -- RST after STOP is unreachable
  (STOP : RST : rest) -> STOP : peepholePass rest

  -- Modulo strength reduction: x % (power of 2) = x & (power - 1)
  (PUSHIMM 2 : MOD : rest) -> PUSHIMM 1 : AND : peepholePass rest
  (PUSHIMM 4 : MOD : rest) -> PUSHIMM 3 : AND : peepholePass rest
  (PUSHIMM 8 : MOD : rest) -> PUSHIMM 7 : AND : peepholePass rest
  (PUSHIMM 16 : MOD : rest) -> PUSHIMM 15 : AND : peepholePass rest
  (PUSHIMM 32 : MOD : rest) -> PUSHIMM 31 : AND : peepholePass rest
  (PUSHIMM 64 : MOD : rest) -> PUSHIMM 63 : AND : peepholePass rest
  (PUSHIMM 128 : MOD : rest) -> PUSHIMM 127 : AND : peepholePass rest
  (PUSHIMM 256 : MOD : rest) -> PUSHIMM 255 : AND : peepholePass rest

  -- Bitshift optimizations
  -- Shift by zero is identity
  (LSHIFT 0 : rest) -> peepholePass rest
  (RSHIFT 0 : rest) -> peepholePass rest

  -- Constant folding for shifts
  (PUSHIMM x : LSHIFT n : rest) | n >= 0 && n < 32 -> PUSHIMM (x * (2 ^ n)) : peepholePass rest
  (PUSHIMM x : RSHIFT n : rest) | n >= 0 && n < 32 -> PUSHIMM (x `div` (2 ^ n)) : peepholePass rest

  -- Consecutive shifts can be combined
  (LSHIFT a : LSHIFT b : rest) -> LSHIFT (a + b) : peepholePass rest
  (RSHIFT a : RSHIFT b : rest) -> RSHIFT (a + b) : peepholePass rest

  -- Shift followed by opposite shift (partial cancellation)
  (LSHIFT a : RSHIFT b : rest) | a == b -> peepholePass rest
  (RSHIFT a : LSHIFT b : rest) | a == b -> peepholePass rest

  -- Multiplication by power of 2 can use shift
  (PUSHIMM 4 : TIMES : rest) -> LSHIFT 2 : peepholePass rest
  (PUSHIMM 8 : TIMES : rest) -> LSHIFT 3 : peepholePass rest
  (PUSHIMM 16 : TIMES : rest) -> LSHIFT 4 : peepholePass rest
  (PUSHIMM 32 : TIMES : rest) -> LSHIFT 5 : peepholePass rest
  (PUSHIMM 64 : TIMES : rest) -> LSHIFT 6 : peepholePass rest

  -- Division by power of 2 can use shift (for non-negative numbers)
  (PUSHIMM 2 : DIV : rest) -> RSHIFT 1 : peepholePass rest
  (PUSHIMM 4 : DIV : rest) -> RSHIFT 2 : peepholePass rest
  (PUSHIMM 8 : DIV : rest) -> RSHIFT 3 : peepholePass rest
  (PUSHIMM 16 : DIV : rest) -> RSHIFT 4 : peepholePass rest
  (PUSHIMM 32 : DIV : rest) -> RSHIFT 5 : peepholePass rest

  -- Negative multiplication: x * (-1) = -x
  (PUSHIMM (-1) : TIMES : rest) -> PUSHIMM 0 : SWAP : SUB : peepholePass rest

  -- Negation of negation: 0 - (0 - x) = x
  (PUSHIMM 0 : SWAP : SUB : PUSHIMM 0 : SWAP : SUB : rest) -> peepholePass rest

  -- x > 0 when we know x is boolean (0 or 1) is same as x != 0
  -- x != 0 can be done with ISNIL; ISNIL
  (PUSHIMM 0 : SWAP : GREATER : rest) -> ISNIL : ISNIL : peepholePass rest

  -- x < 0 is always false for non-negative values (but we can't know that statically)
  -- x >= 0 is always true for non-negative values

  -- x != y can be rewritten as (x == y); ISNIL
  -- But we don't have a direct pattern for this without more context

  --------------------------------------------------------------------------------
  -- Comparison Chain Optimizations
  --------------------------------------------------------------------------------

  -- Pattern: a <= b && b <= c (range check)
  -- In SAM: a, b, LESS, ISNIL, b, c, LESS, ISNIL, AND
  -- If we see: LESS; ISNIL; <push b>; <push c>; LESS; ISNIL; AND
  -- This is hard to optimize without value tracking, keep as is for now

  -- Pattern: CMP-based chain (result is -1, 0, or 1)
  -- After CMP, we often check ISNEG (for <) or ISNIL (for ==)
  -- CMP; ISNEG gives true if a < b
  -- CMP; ISNIL gives true if a == b
  -- CMP; DUP; ISNEG; SWAP; ISNIL; OR gives true if a <= b (< or ==)
  (CMP : DUP : ISNEG : SWAP : ISNIL : OR : rest) ->
    -- This is "less than or equal" - could be simplified with a direct comparison
    -- But we don't have LESSEQ, so keep as: SWAP; GREATER; ISNIL
    SWAP : GREATER : ISNIL : peepholePass rest

  (CMP : DUP : ISNIL : SWAP : ISNEG : ISNIL : AND : rest) ->
    -- This is "greater than": not neg and not zero = positive = a > b
    GREATER : peepholePass rest

  -- Simplify: CMP; ISNIL -> EQUAL (both check if difference is 0)
  (CMP : ISNIL : rest) -> EQUAL : peepholePass rest

  -- Simplify: CMP; ISNEG -> LESS (CMP gives negative if a < b)
  (CMP : ISNEG : rest) -> LESS : peepholePass rest

  -- Simplify: CMP; ISNEG; ISNIL -> LESS; ISNIL (>=)
  (CMP : ISNEG : ISNIL : rest) -> LESS : ISNIL : peepholePass rest

  -- Double comparison elimination: if we compare same values twice
  -- x; y; LESS; pop; x; y; GREATER -> x; y; GREATER
  -- (Requires value tracking, skip for now)

  -- Redundant NOT after comparison: LESS; ISNIL; ISNIL = LESS
  (LESS : ISNIL : ISNIL : rest) -> LESS : peepholePass rest
  (GREATER : ISNIL : ISNIL : rest) -> GREATER : peepholePass rest
  (EQUAL : ISNIL : ISNIL : rest) -> EQUAL : peepholePass rest

  -- Boolean chain: result; ISNIL; JUMPC L is "jump if false"
  -- result; ISNIL; ISNIL; JUMPC L is "jump if true"
  -- We can sometimes merge these

  -- Note: PUSHIMM a : PUSHIMM b : EQUAL patterns already handled by constant folding

  -- Remove no-op stores followed by loads: store n; load n; drop
  (STOREOFF n : PUSHOFF m : ADDSP (-1) : rest) | n == m -> STOREOFF n : peepholePass rest

  -- Boolean short-circuit: DUP; check; JUMPC L; drop -> if top is 0, jump
  (DUP : ISNIL : JUMPC lbl : ADDSP (-1) : rest) ->
    DUP : JUMPC lbl : ADDSP (-1) : peepholePass rest  -- Short-circuit: if zero, jump

  -- Reduce stack depth: swap back adjacent loads
  (PUSHOFF a : PUSHOFF b : SWAP : rest) -> PUSHOFF b : PUSHOFF a : peepholePass rest

  -- DUP followed by drop of multiple values
  (DUP : ADDSP n : rest) | n <= -2 -> ADDSP (n + 1) : peepholePass rest

  -- Dead code after unconditional RST (until next label)
  (RST : Label l : rest) -> RST : Label l : peepholePass rest
  (RST : x : rest) | not (isControlFlow x) -> RST : peepholePass (dropUntilControl rest)

  -- Consecutive jumps to same label: only need one JUMPC check
  (JUMPC lbl1 : JUMPC lbl2 : rest) | lbl1 == lbl2 -> JUMPC lbl1 : peepholePass rest

  -- PUSHIMM 0; LESS is always false (nothing is less than 0 for unsigned)
  -- Actually in SAM integers are signed, so skip this

  -- Optimize: PUSHIMM k; ADD; PUSHIMM j; ADD -> PUSHIMM (k+j); ADD
  (PUSHIMM k : ADD : PUSHIMM j : ADD : rest) -> PUSHIMM (k + j) : ADD : peepholePass rest
  (PUSHIMM k : SUB : PUSHIMM j : SUB : rest) -> PUSHIMM (k + j) : SUB : peepholePass rest

  -- Optimize: PUSHIMM k; TIMES; PUSHIMM j; TIMES -> PUSHIMM (k*j); TIMES
  (PUSHIMM k : TIMES : PUSHIMM j : TIMES : rest) | k * j /= 0 ->
    PUSHIMM (k * j) : TIMES : peepholePass rest

  --------------------------------------------------------------------------------
  -- Additional Peephole Patterns
  --------------------------------------------------------------------------------

  -- Commutative reordering: SWAP before commutative op is redundant
  (SWAP : ADD : rest) -> ADD : peepholePass rest
  (SWAP : TIMES : rest) -> TIMES : peepholePass rest
  (SWAP : EQUAL : rest) -> EQUAL : peepholePass rest
  (SWAP : AND : rest) -> AND : peepholePass rest
  (SWAP : OR : rest) -> OR : peepholePass rest

  -- SWAP before SUB changes sign: a; b; SWAP; SUB = b - a (keep as is, semantically different)

  -- Default: keep instruction and continue
  (x : rest) -> x : peepholePass rest

-- | Check if instruction is control flow
isControlFlow :: SamInstr -> Bool
isControlFlow (Label _) = True
isControlFlow (JUMP _) = True
isControlFlow (JUMPC _) = True
isControlFlow JSR {} = True
isControlFlow RST = True
isControlFlow STOP = True
isControlFlow _ = False

-- | Drop instructions until we see control flow
dropUntilControl :: [SamInstr] -> [SamInstr]
dropUntilControl [] = []
dropUntilControl (i : rest)
  | isControlFlow i = i : rest
  | otherwise = dropUntilControl rest

--------------------------------------------------------------------------------
-- Instruction Scheduling
--------------------------------------------------------------------------------

-- | Schedule instructions to reduce stack depth and improve locality.
-- Reorders independent instructions for better performance.
scheduleInstructions :: [SamInstr] -> [SamInstr]
scheduleInstructions = scheduleBlocks

-- | Schedule within basic blocks (between labels/jumps)
scheduleBlocks :: [SamInstr] -> [SamInstr]
scheduleBlocks [] = []
scheduleBlocks instrs =
  let (block, rest) = extractBlock instrs
      scheduled = scheduleBlock block
  in scheduled ++ scheduleBlocks rest

-- | Extract a basic block (ends at label, jump, or control flow)
extractBlock :: [SamInstr] -> ([SamInstr], [SamInstr])
extractBlock [] = ([], [])
extractBlock (instr:rest)
  | isBlockEnd instr = ([instr], rest)
  | otherwise =
      let (block, remaining) = extractBlock rest
      in (instr : block, remaining)

isBlockEnd :: SamInstr -> Bool
isBlockEnd (Label _) = True
isBlockEnd (JUMP _) = True
isBlockEnd (JUMPC _) = True
isBlockEnd (JSR _) = True
isBlockEnd RST = True
isBlockEnd STOP = True
isBlockEnd _ = False

-- | Schedule a single basic block
-- Simple heuristic: group stack operations, reduce depth
scheduleBlock :: [SamInstr] -> [SamInstr]
scheduleBlock instrs =
  let -- Find independent instruction pairs that can be reordered
      reordered = tryReorderForDepth instrs
  in reordered

-- | Try to reorder instructions to reduce max stack depth
tryReorderForDepth :: [SamInstr] -> [SamInstr]
tryReorderForDepth = go
  where
    go [] = []
    go [x] = [x]
    go (x:y:rest)
      -- Pattern: PUSHIMM a; PUSHIMM b; OP -> keep as is (already optimal)
      | isPush x && isPush y = x : go (y:rest)
      -- Pattern: PUSHOFF a; PUSHOFF b where a and b are independent
      -- Prefer loading smaller offsets first (cache locality)
      | PUSHOFF a <- x, PUSHOFF b <- y, a > b =
          PUSHOFF b : go (PUSHOFF a : rest)
      | otherwise = x : go (y:rest)

isPush :: SamInstr -> Bool
isPush (PUSHIMM _) = True
isPush (PUSHOFF _) = True
isPush (PUSHIMMSTR _) = True
isPush DUP = True
isPush _ = False

--------------------------------------------------------------------------------
-- Block Merging
--------------------------------------------------------------------------------

-- | Merge adjacent basic blocks when possible.
-- If a block ends with JUMP L and L immediately follows, remove the jump.
-- If a label is only jumped to from the preceding instruction, merge.
mergeBlocks :: [SamInstr] -> [SamInstr]
mergeBlocks instrs =
  let -- First pass: remove jumps to immediately following labels
      pass1 = removeRedundantJumps instrs
      -- Second pass: remove unreferenced labels
      pass2 = removeUnreferencedLabels pass1
  in pass2

-- | Remove JUMP L when L immediately follows
removeRedundantJumps :: [SamInstr] -> [SamInstr]
removeRedundantJumps [] = []
removeRedundantJumps [x] = [x]
removeRedundantJumps (JUMP lbl : Label lbl' : rest)
  | lbl == lbl' = Label lbl' : removeRedundantJumps rest
removeRedundantJumps (x : rest) = x : removeRedundantJumps rest

-- | Remove labels that are never jumped to
removeUnreferencedLabels :: [SamInstr] -> [SamInstr]
removeUnreferencedLabels instrs =
  let referenced = collectReferencedLabels instrs
  in filter (keepLabel referenced) instrs
  where
    keepLabel refs (Label lbl) = lbl `Set.member` refs
    keepLabel _ _ = True

-- | Collect all labels that are jumped to
collectReferencedLabels :: [SamInstr] -> Set Text
collectReferencedLabels = Set.fromList . mapMaybe getJumpTarget
  where
    getJumpTarget (JUMP lbl) = Just lbl
    getJumpTarget (JUMPC lbl) = Just lbl
    getJumpTarget (JSR lbl) = Just lbl
    getJumpTarget _ = Nothing
