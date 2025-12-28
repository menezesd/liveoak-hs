{-# LANGUAGE OverloadedStrings #-}

-- | String runtime routines for SAM.
-- Provides SAM assembly implementations of string operations.
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

-- | Label for string length function.
strLengthLabel :: Text
strLengthLabel = "STR_LENGTH"

-- | Label for string reverse function.
strReverseLabel :: Text
strReverseLabel = "STR_REVERSE"

-- | Label for string concatenation function.
strConcatLabel :: Text
strConcatLabel = "STR_CONCAT"

-- | Label for string append function.
strAppendLabel :: Text
strAppendLabel = "STR_APPEND"

-- | Label for string repeat function.
strRepeatLabel :: Text
strRepeatLabel = "STR_REPEAT"

-- | Label for string compare function.
strCompareLabel :: Text
strCompareLabel = "STR_COMPARE"

-- | Emit all string runtime functions.
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

-- | String length: count characters until null terminator.
-- Input: string address on TOS
-- Output: length on TOS
strLength :: Text
strLength = T.unlines
  [ strLengthLabel <> ":"
  , "  PUSHIMM 0"           -- counter = 0
  , "  SWAP"                -- [counter, addr]
  , strLengthLabel <> "_loop:"
  , "  DUP"                 -- [counter, addr, addr]
  , "  PUSHIND"             -- [counter, addr, char]
  , "  ISNIL"               -- [counter, addr, isNull]
  , "  JUMPC " <> strLengthLabel <> "_done"
  , "  PUSHIMM 1"           -- [counter, addr, 1]
  , "  ADD"                 -- [counter, addr+1]
  , "  SWAP"                -- [addr+1, counter]
  , "  PUSHIMM 1"           -- [addr+1, counter, 1]
  , "  ADD"                 -- [addr+1, counter+1]
  , "  SWAP"                -- [counter+1, addr+1]
  , "  JUMP " <> strLengthLabel <> "_loop"
  , strLengthLabel <> "_done:"
  , "  SWAP"                -- [addr, counter]
  , "  ADDSP -1"            -- drop addr
  , "  RST"
  ]

-- | String reverse: create reversed copy.
-- Input: string address on TOS
-- Output: new string address on TOS
strReverse :: Text
strReverse = T.unlines
  [ strReverseLabel <> ":"
  , "  DUP"                 -- [src, src]
  , "  LINK"
  , "  JSR " <> strLengthLabel
  , "  UNLINK"              -- [src, len]
  , "  ADDSP -1"            -- pop return slot
  , "  DUP"                 -- [src, len, len]
  , "  PUSHIMM 1"
  , "  ADD"                 -- [src, len, len+1]
  , "  MALLOC"              -- [src, len, dest]
  , "  // Copy in reverse"
  , "  SWAP"                -- [src, dest, len]
  , strReverseLabel <> "_loop:"
  , "  DUP"
  , "  ISNIL"
  , "  JUMPC " <> strReverseLabel <> "_done"
  , "  // Decrement len"
  , "  PUSHIMM 1"
  , "  SUB"                 -- [src, dest, len-1]
  , "  // Get char from src+len-1"
  , "  PUSHOFF -3"          -- get src
  , "  PUSHOFF -1"          -- get len
  , "  ADD"                 -- [src, dest, len-1, src+len-1]
  , "  PUSHIND"             -- [src, dest, len-1, char]
  , "  // Store at dest + (origLen - len - 1)"
  , "  PUSHOFF -2"          -- dest
  , "  STOREIND"
  , "  PUSHOFF -2"
  , "  PUSHIMM 1"
  , "  ADD"
  , "  STOREOFF -2"         -- dest++
  , "  JUMP " <> strReverseLabel <> "_loop"
  , strReverseLabel <> "_done:"
  , "  ADDSP -1"            -- drop len
  , "  // Null terminate"
  , "  DUP"
  , "  PUSHIMM 0"
  , "  STOREIND"
  , "  // Return dest start (need to recalculate)"
  , "  SWAP"
  , "  ADDSP -1"
  , "  RST"
  ]

-- | String concatenation: create new string from two strings.
-- Input: str2 on TOS, str1 below
-- Output: new string address on TOS
strConcat :: Text
strConcat = T.unlines
  [ strConcatLabel <> ":"
  , "  // Get lengths"
  , "  PUSHOFF -1"          -- str1
  , "  LINK"
  , "  JSR " <> strLengthLabel
  , "  UNLINK"
  , "  ADDSP -1"            -- [str1, str2, len1]
  , "  PUSHOFF -2"          -- str2
  , "  LINK"
  , "  JSR " <> strLengthLabel
  , "  UNLINK"
  , "  ADDSP -1"            -- [str1, str2, len1, len2]
  , "  // Allocate len1+len2+1"
  , "  DUP"
  , "  PUSHOFF -2"
  , "  ADD"
  , "  PUSHIMM 1"
  , "  ADD"
  , "  MALLOC"              -- [str1, str2, len1, len2, dest]
  , "  // Copy str1"
  , "  DUP"                 -- save dest
  , "  PUSHOFF -5"          -- str1
  , strConcatLabel <> "_copy1:"
  , "  DUP"
  , "  PUSHIND"
  , "  DUP"
  , "  ISNIL"
  , "  JUMPC " <> strConcatLabel <> "_copy2_start"
  , "  PUSHOFF -2"          -- dest
  , "  STOREIND"
  , "  PUSHOFF -2"
  , "  PUSHIMM 1"
  , "  ADD"
  , "  STOREOFF -2"         -- dest++
  , "  PUSHIMM 1"
  , "  ADD"                 -- src++
  , "  JUMP " <> strConcatLabel <> "_copy1"
  , strConcatLabel <> "_copy2_start:"
  , "  ADDSP -2"            -- drop char and src
  , "  // Copy str2"
  , "  PUSHOFF -4"          -- str2
  , strConcatLabel <> "_copy2:"
  , "  DUP"
  , "  PUSHIND"
  , "  DUP"
  , "  ISNIL"
  , "  JUMPC " <> strConcatLabel <> "_done"
  , "  PUSHOFF -2"          -- dest
  , "  STOREIND"
  , "  PUSHOFF -2"
  , "  PUSHIMM 1"
  , "  ADD"
  , "  STOREOFF -2"         -- dest++
  , "  PUSHIMM 1"
  , "  ADD"                 -- src++
  , "  JUMP " <> strConcatLabel <> "_copy2"
  , strConcatLabel <> "_done:"
  , "  ADDSP -2"            -- drop char and src
  , "  // Null terminate"
  , "  DUP"
  , "  PUSHIMM 0"
  , "  STOREIND"
  , "  // Clean up and return"
  , "  ADDSP -4"            -- drop len1, len2, str1, str2
  , "  RST"
  ]

-- | String append (helper for concat).
strAppend :: Text
strAppend = T.unlines
  [ strAppendLabel <> ":"
  , "  // Simple wrapper around concat"
  , "  JUMP " <> strConcatLabel
  ]

-- | String repeat: repeat string N times.
-- Input: count on TOS, string below
-- Output: new string address on TOS
strRepeat :: Text
strRepeat = T.unlines
  [ strRepeatLabel <> ":"
  , "  DUP"                 -- [str, n, n]
  , "  ISNEG"               -- [str, n, isNeg]
  , "  JUMPC " <> strRepeatLabel <> "_empty"
  , "  DUP"
  , "  ISNIL"
  , "  JUMPC " <> strRepeatLabel <> "_empty"
  , "  // Get string length"
  , "  PUSHOFF -2"          -- str
  , "  LINK"
  , "  JSR " <> strLengthLabel
  , "  UNLINK"
  , "  ADDSP -1"            -- [str, n, len]
  , "  // Allocate len*n+1"
  , "  DUP"
  , "  PUSHOFF -2"
  , "  TIMES"
  , "  PUSHIMM 1"
  , "  ADD"
  , "  MALLOC"              -- [str, n, len, dest]
  , "  DUP"                 -- save dest start
  , strRepeatLabel <> "_outer:"
  , "  PUSHOFF -3"          -- n
  , "  ISNIL"
  , "  JUMPC " <> strRepeatLabel <> "_done"
  , "  // Copy one instance"
  , "  PUSHOFF -4"          -- str
  , strRepeatLabel <> "_inner:"
  , "  DUP"
  , "  PUSHIND"
  , "  DUP"
  , "  ISNIL"
  , "  JUMPC " <> strRepeatLabel <> "_inner_done"
  , "  PUSHOFF -2"          -- dest
  , "  STOREIND"
  , "  PUSHOFF -2"
  , "  PUSHIMM 1"
  , "  ADD"
  , "  STOREOFF -2"         -- dest++
  , "  PUSHIMM 1"
  , "  ADD"                 -- src++
  , "  JUMP " <> strRepeatLabel <> "_inner"
  , strRepeatLabel <> "_inner_done:"
  , "  ADDSP -2"            -- drop src and char
  , "  // Decrement n"
  , "  PUSHOFF -3"
  , "  PUSHIMM 1"
  , "  SUB"
  , "  STOREOFF -3"
  , "  JUMP " <> strRepeatLabel <> "_outer"
  , strRepeatLabel <> "_done:"
  , "  // Null terminate"
  , "  DUP"
  , "  PUSHIMM 0"
  , "  STOREIND"
  , "  ADDSP -4"            -- clean up
  , "  RST"
  , strRepeatLabel <> "_empty:"
  , "  ADDSP -2"            -- drop str, n
  , "  PUSHIMM 1"
  , "  MALLOC"
  , "  DUP"
  , "  PUSHIMM 0"
  , "  STOREIND"
  , "  RST"
  ]

-- | String compare: lexicographic comparison.
-- Input: str2 on TOS, str1 below
-- Output: -1 (less), 0 (equal), 1 (greater) on TOS
strCompare :: Text
strCompare = T.unlines
  [ strCompareLabel <> ":"
  , "  // [str1, str2]"
  , strCompareLabel <> "_loop:"
  , "  PUSHOFF -1"          -- str1
  , "  PUSHIND"             -- char1
  , "  PUSHOFF -2"          -- str2
  , "  PUSHIND"             -- [str1, str2, char1, char2]
  , "  // Check if char1 < char2"
  , "  DUP"
  , "  PUSHOFF -2"
  , "  LESS"
  , "  JUMPC " <> strCompareLabel <> "_less"
  , "  // Check if char1 > char2"
  , "  PUSHOFF -2"
  , "  PUSHOFF -1"
  , "  LESS"
  , "  JUMPC " <> strCompareLabel <> "_greater"
  , "  // Equal so far, check if both null"
  , "  PUSHOFF -1"
  , "  ISNIL"
  , "  JUMPC " <> strCompareLabel <> "_equal"
  , "  // Advance pointers"
  , "  ADDSP -2"            -- drop chars
  , "  PUSHOFF -1"
  , "  PUSHIMM 1"
  , "  ADD"
  , "  STOREOFF -1"         -- str1++
  , "  PUSHOFF -2"
  , "  PUSHIMM 1"
  , "  ADD"
  , "  STOREOFF -2"         -- str2++
  , "  JUMP " <> strCompareLabel <> "_loop"
  , strCompareLabel <> "_less:"
  , "  ADDSP -4"
  , "  PUSHIMM -1"
  , "  RST"
  , strCompareLabel <> "_greater:"
  , "  ADDSP -4"
  , "  PUSHIMM 1"
  , "  RST"
  , strCompareLabel <> "_equal:"
  , "  ADDSP -4"
  , "  PUSHIMM 0"
  , "  RST"
  ]
