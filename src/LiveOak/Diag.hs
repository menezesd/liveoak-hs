{-# LANGUAGE LambdaCase #-}

-- | Diagnostic types and Result monad for error handling.
-- Provides structured error reporting with source positions.
module LiveOak.Diag
  ( -- * Diagnostic Types
    Diag (..)
  , diagMessage
  , diagLine
  , diagColumn
  , diagKind
  , formatDiag
  , formatDiagWithSource

    -- * Result Type
  , Result
  , ok
  , err
  , syntaxErr
  , typeErr
  , resolveErr

    -- * Result Combinators
  , mapError
  , sequenceResults
  , traverseResults
  , foldResults
  , fromMaybe
  , require
  ) where

import Data.Text (Text)
import qualified Data.Text as T

-- | Structured diagnostic for parser/semantic/codegen errors.
data Diag
  = SyntaxError  { _diagMsg :: String, _diagLine :: Int, _diagCol :: Int }
  | TypeError    { _diagMsg :: String, _diagLine :: Int, _diagCol :: Int }
  | ResolveError { _diagMsg :: String, _diagLine :: Int, _diagCol :: Int }
  deriving (Eq, Show)

-- | Extract the message from a diagnostic.
diagMessage :: Diag -> String
diagMessage = _diagMsg

-- | Extract the line number from a diagnostic.
diagLine :: Diag -> Int
diagLine = _diagLine

-- | Extract the column number from a diagnostic.
diagColumn :: Diag -> Int
diagColumn = _diagCol

-- | Get the kind of diagnostic as a string.
diagKind :: Diag -> String
diagKind = \case
  SyntaxError{}  -> "Syntax error"
  TypeError{}    -> "Type error"
  ResolveError{} -> "Resolution error"

-- | Format a diagnostic for display (simple format).
formatDiag :: Diag -> String
formatDiag d = diagKind d ++ ": " ++ diagMessage d ++ locationStr
  where
    locationStr
      | diagLine d > 0 = " (line " ++ show (diagLine d) ++ ")"
      | otherwise      = ""

-- | Format a diagnostic with source context.
-- Shows the error message, the relevant source line, and a caret pointing to the error.
formatDiagWithSource :: Text -> Diag -> String
formatDiagWithSource source d = unlines $ filter (not . null)
  [ diagKind d ++ ": " ++ diagMessage d
  , locationLine
  , sourceLine
  , caretLine
  ]
  where
    line = diagLine d
    col  = diagColumn d

    locationLine
      | line > 0  = "  --> line " ++ show line ++ (if col > 0 then ":" ++ show col else "")
      | otherwise = ""

    sourceLines = T.lines source

    sourceLine
      | line > 0 && line <= length sourceLines =
          "   | " ++ T.unpack (sourceLines !! (line - 1))
      | otherwise = ""

    caretLine
      | line > 0 && line <= length sourceLines && col > 0 =
          "   | " ++ replicate (col - 1) ' ' ++ "^"
      | line > 0 && line <= length sourceLines =
          "   | " ++ "^"  -- Point to start if no column info
      | otherwise = ""

-- | Result type: Either a diagnostic or a successful value.
type Result a = Either Diag a

-- | Construct a successful result.
ok :: a -> Result a
ok = Right

-- | Construct a failed result.
err :: Diag -> Result a
err = Left

-- | Construct a syntax error result.
syntaxErr :: String -> Int -> Int -> Result a
syntaxErr msg line col = Left (SyntaxError msg line col)

-- | Construct a type error result.
typeErr :: String -> Int -> Int -> Result a
typeErr msg line col = Left (TypeError msg line col)

-- | Construct a resolve error result.
resolveErr :: String -> Int -> Int -> Result a
resolveErr msg line col = Left (ResolveError msg line col)

-- | Map over the error in a Result.
mapError :: (Diag -> Diag) -> Result a -> Result a
mapError f = \case
  Left d  -> Left (f d)
  Right a -> Right a

-- | Sequence a list of results, short-circuiting on first error.
sequenceResults :: [Result a] -> Result [a]
sequenceResults = foldr go (Right [])
  where
    go (Left d)  _           = Left d
    go (Right a) (Left d)    = Left d
    go (Right a) (Right acc) = Right (a : acc)

-- | Traverse with a fallible function, short-circuiting on first error.
traverseResults :: (a -> Result b) -> [a] -> Result [b]
traverseResults f = sequenceResults . map f

-- | Fold with a fallible function, short-circuiting on first error.
foldResults :: (b -> a -> Result b) -> b -> [a] -> Result b
foldResults _ acc []     = Right acc
foldResults f acc (x:xs) = f acc x >>= \acc' -> foldResults f acc' xs

-- | Convert Maybe to Result with a fallback diagnostic.
fromMaybe :: Diag -> Maybe a -> Result a
fromMaybe d Nothing  = Left d
fromMaybe _ (Just a) = Right a

-- | Require a condition, returning () or an error.
require :: Bool -> Diag -> Result ()
require True  _ = Right ()
require False d = Left d
