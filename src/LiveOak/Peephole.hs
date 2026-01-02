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
  ) where

import Data.Text (Text)
import qualified Data.Text as T
import Data.Maybe (mapMaybe)

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
  ["PUSHIMM", n] -> Just $ PUSHIMM (readInt n)
  ("PUSHIMMSTR":rest) -> Just $ PUSHIMMSTR (T.unwords rest)
  ["PUSHOFF", n] -> Just $ PUSHOFF (readInt n)
  ["STOREOFF", n] -> Just $ STOREOFF (readInt n)
  ["PUSHIND"] -> Just PUSHIND
  ["STOREIND"] -> Just STOREIND
  ["DUP"] -> Just DUP
  ["SWAP"] -> Just SWAP
  ["ADD"] -> Just ADD
  ["SUB"] -> Just SUB
  ["TIMES"] -> Just TIMES
  ["DIV"] -> Just DIV
  ["MOD"] -> Just MOD
  ["AND"] -> Just AND
  ["OR"] -> Just OR
  ["EQUAL"] -> Just EQUAL
  ["LESS"] -> Just LESS
  ["GREATER"] -> Just GREATER
  ["CMP"] -> Just CMP
  ["ISNIL"] -> Just ISNIL
  ["ISNEG"] -> Just ISNEG
  ["ADDSP", n] -> Just $ ADDSP (readInt n)
  ["LINK"] -> Just LINK
  ["UNLINK"] -> Just UNLINK
  ["JSR", lbl] -> Just $ JSR lbl
  ["RST"] -> Just RST
  ["JUMP", lbl] -> Just $ JUMP lbl
  ["JUMPC", lbl] -> Just $ JUMPC lbl
  ["STOP"] -> Just STOP
  ["MALLOC"] -> Just MALLOC
  _ -> Nothing  -- Unknown instruction, skip

-- | Read an integer, handling negative numbers
readInt :: Text -> Int
readInt t
  | "-" `T.isPrefixOf` t = negate $ read $ T.unpack $ T.drop 1 t
  | otherwise = read $ T.unpack t

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

-- | Apply peephole optimizations until no more changes
optimize :: [SamInstr] -> [SamInstr]
optimize instrs =
  let optimized = peepholePass instrs
  in if optimized == instrs
     then instrs
     else optimize optimized

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

  -- Jump to next instruction (need to track labels)
  (JUMP lbl : Label lbl' : rest) | lbl == lbl' -> Label lbl' : peepholePass rest

  -- DUP; SWAP = DUP (stack has [a, a], swap gives [a, a])
  (DUP : SWAP : rest) -> DUP : peepholePass rest

  -- Default: keep instruction and continue
  (x : rest) -> x : peepholePass rest
