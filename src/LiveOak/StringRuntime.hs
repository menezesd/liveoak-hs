{-# LANGUAGE OverloadedStrings #-}

-- | String runtime routines for SAM (aligned with reference Scala runtime).
module LiveOak.StringRuntime
  ( -- * Runtime Generation
    emitStringRuntime

    -- * Individual String Operations
  , strLength
  , strReverse
  , strConcat
  , strAppend
  , strRepeat
  , strCompare

    -- * Runtime Labels
  , strLengthLabel
  , strReverseLabel
  , strConcatLabel
  , strAppendLabel
  , strRepeatLabel
  , strCompareLabel
  ) where

import Data.Text (Text)
import qualified Data.Text as T

-- Runtime labels
strLengthLabel, strReverseLabel, strConcatLabel, strAppendLabel, strRepeatLabel, strCompareLabel :: Text
strLengthLabel = "STR_LENGTH"
strReverseLabel = "STR_REVERSE"
strConcatLabel  = "STR_CONCAT"
strAppendLabel  = "STR_APPEND"
strRepeatLabel  = "STR_REPEAT"
strCompareLabel = "STR_COMPARE"

-- Emit all string helper routines
emitStringRuntime :: Text
emitStringRuntime = T.unlines
  [ ""
  , "// String Runtime Library"
  , strLength
  , strReverse
  , strConcat
  , strAppend
  , strRepeat
  , strCompare
  ]

-- STR_LENGTH
strLength :: Text
strLength = T.unlines
  [ strLengthLabel <> ":"
  , "  SWAP"
  , "  DUP"
  , strLengthLabel <> "_loop:"
  , "  DUP"
  , "  PUSHIND"
  , "  ISNIL"
  , "  JUMPC " <> strLengthLabel <> "_done"
  , "  PUSHIMM 1"
  , "  ADD"
  , "  JUMP " <> strLengthLabel <> "_loop"
  , strLengthLabel <> "_done:"
  , "  SWAP"
  , "  SUB"
  , "  SWAP"
  , "  RST"
  ]

-- STR_REVERSE
strReverse :: Text
strReverse = T.unlines
  [ strReverseLabel <> ":"
  , "  PUSHIMM 0"
  , "  PUSHIMM 0"
  , "  PUSHIMM 0"
  , "  PUSHOFF -1"
  , "  JSR " <> strLengthLabel
  , "  STOREOFF 2"
  , "  PUSHOFF 2"
  , "  PUSHIMM 1"
  , "  ADD"
  , "  MALLOC"
  , "  STOREOFF 3"
  , "  PUSHOFF 3"
  , "  STOREOFF 4"
  , "  PUSHOFF 3"
  , "  PUSHOFF 2"
  , "  ADD"
  , "  PUSHIMM 0"
  , "  STOREIND"
  , strReverseLabel <> "_loop:"
  , "  PUSHOFF 2"
  , "  ISNIL"
  , "  JUMPC " <> strReverseLabel <> "_done"
  , "  PUSHOFF 3"
  , "  PUSHOFF -1"
  , "  PUSHOFF 2"
  , "  ADD"
  , "  PUSHIMM 1"
  , "  SUB"
  , "  PUSHIND"
  , "  STOREIND"
  , "  PUSHOFF 3"
  , "  PUSHIMM 1"
  , "  ADD"
  , "  STOREOFF 3"
  , "  PUSHOFF 2"
  , "  PUSHIMM 1"
  , "  SUB"
  , "  STOREOFF 2"
  , "  JUMP " <> strReverseLabel <> "_loop"
  , strReverseLabel <> "_done:"
  , "  PUSHOFF 4"
  , "  STOREOFF -1"
  , "  ADDSP -3"
  , "  RST"
  ]

-- STR_CONCAT
strConcat :: Text
strConcat = T.unlines
  [ strConcatLabel <> ":"
  , "  PUSHIMM 0"
  , "  PUSHIMM 0"
  , "  PUSHOFF -1"
  , "  JSR " <> strLengthLabel
  , "  PUSHOFF -2"
  , "  JSR " <> strLengthLabel
  , "  ADD"
  , "  PUSHIMM 1"
  , "  ADD"
  , "  MALLOC"
  , "  STOREOFF 2"
  , "  PUSHOFF 2"
  , "  STOREOFF 3"
  , "  PUSHIMM 0"
  , "  PUSHOFF 2"
  , "  PUSHOFF -2"
  , "  LINK"
  , "  JSR " <> strAppendLabel
  , "  UNLINK"
  , "  ADDSP -2"
  , "  STOREOFF 2"
  , "  PUSHIMM 0"
  , "  PUSHOFF 2"
  , "  PUSHOFF -1"
  , "  LINK"
  , "  JSR " <> strAppendLabel
  , "  UNLINK"
  , "  ADDSP -2"
  , "  STOREOFF 2"
  , "  PUSHOFF 3"
  , "  STOREOFF -2"
  , "  ADDSP -2"
  , "  RST"
  ]

-- STR_APPEND
strAppend :: Text
strAppend = T.unlines
  [ strAppendLabel <> ":"
  , "  PUSHOFF -2"
  , "  PUSHOFF -1"
  , strAppendLabel <> "_loop:"
  , "  PUSHOFF 3"
  , "  PUSHIND"
  , "  ISNIL"
  , "  JUMPC " <> strAppendLabel <> "_done"
  , "  PUSHOFF 2"
  , "  PUSHOFF 3"
  , "  PUSHIND"
  , "  STOREIND"
  , "  PUSHOFF 2"
  , "  PUSHIMM 1"
  , "  ADD"
  , "  STOREOFF 2"
  , "  PUSHOFF 3"
  , "  PUSHIMM 1"
  , "  ADD"
  , "  STOREOFF 3"
  , "  JUMP " <> strAppendLabel <> "_loop"
  , strAppendLabel <> "_done:"
  , "  PUSHOFF 2"
  , "  PUSHIMM 0"
  , "  STOREIND"
  , "  PUSHOFF 2"
  , "  STOREOFF -3"
  , "  ADDSP -2"
  , "  RST"
  ]

-- STR_REPEAT
strRepeat :: Text
strRepeat = T.unlines
  [ strRepeatLabel <> ":"
  , "  PUSHIMM 0"
  , "  PUSHIMM 0"
  , "  PUSHIMM 0"
  , "  PUSHOFF -2"
  , "  ISNEG"
  , "  JUMPC " <> strRepeatLabel <> "_valid"
  , "  PUSHIMMSTR \"\""
  , "  STOREOFF -2"
  , "  ADDSP -3"
  , "  RST"
  , strRepeatLabel <> "_valid:"
  , "  PUSHOFF -1"
  , "  JSR " <> strLengthLabel
  , "  PUSHOFF -2"
  , "  TIMES"
  , "  PUSHIMM 1"
  , "  ADD"
  , "  MALLOC"
  , "  STOREOFF 3"
  , "  PUSHOFF 3"
  , "  STOREOFF 4"
  , strRepeatLabel <> "_loop:"
  , "  PUSHOFF 2"
  , "  PUSHOFF -2"
  , "  EQUAL"
  , "  JUMPC " <> strRepeatLabel <> "_done"
  , "  PUSHIMM 0"
  , "  PUSHOFF 3"
  , "  PUSHOFF -1"
  , "  LINK"
  , "  JSR " <> strAppendLabel
  , "  UNLINK"
  , "  ADDSP -2"
  , "  STOREOFF 3"
  , "  PUSHOFF 2"
  , "  PUSHIMM 1"
  , "  ADD"
  , "  STOREOFF 2"
  , "  JUMP " <> strRepeatLabel <> "_loop"
  , strRepeatLabel <> "_done:"
  , "  PUSHOFF 4"
  , "  STOREOFF -2"
  , "  ADDSP -3"
  , "  RST"
  ]

-- STR_COMPARE
strCompare :: Text
strCompare = T.unlines
  [ strCompareLabel <> ":"
  , "  PUSHIMM 0"
  , "  PUSHIMM 0"
  , strCompareLabel <> "_loop:"
  , "  PUSHOFF -2"
  , "  PUSHOFF 2"
  , "  ADD"
  , "  PUSHIND"
  , "  ISNIL"
  , "  PUSHOFF -1"
  , "  PUSHOFF 2"
  , "  ADD"
  , "  PUSHIND"
  , "  ISNIL"
  , "  AND"
  , "  JUMPC " <> strCompareLabel <> "_cmp"
  , "  PUSHOFF -2"
  , "  PUSHOFF 2"
  , "  ADD"
  , "  PUSHIND"
  , "  PUSHOFF -1"
  , "  PUSHOFF 2"
  , "  ADD"
  , "  PUSHIND"
  , "  CMP"
  , "  STOREOFF 3"
  , "  PUSHOFF 3"
  , "  JUMPC " <> strCompareLabel <> "_cmp"
  , "  PUSHOFF 2"
  , "  PUSHIMM 1"
  , "  ADD"
  , "  STOREOFF 2"
  , "  JUMP " <> strCompareLabel <> "_loop"
  , strCompareLabel <> "_cmp:"
  , "  PUSHOFF 3"
  , "  STOREOFF -2"
  , "  ADDSP -2"
  , "  RST"
  ]

