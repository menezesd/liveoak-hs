{-# LANGUAGE OverloadedStrings #-}

-- | Lexer for LiveOak using Megaparsec.
-- Provides token parsers and whitespace handling.
module LiveOak.Lexer
  ( -- * Parser Type
    Parser
  , ParserError

    -- * Running Parsers
  , runLexer
  , testParser

    -- * Whitespace and Lexemes
  , sc
  , lexeme
  , symbol

    -- * Literals
  , intLiteral
  , stringLiteral
  , boolLiteral

    -- * Identifiers and Keywords
  , identifier
  , reserved
  , reservedWords

    -- * Operators
  , operator
  , parens
  , braces
  , semi
  , comma
  , dot
  , colon
  , question

    -- * Position Helpers
  , getPosition
  , getLineNo
  ) where

import Control.Monad (void)
import Data.Void (Void)
import Data.Text (Text)
import qualified Data.Text as T
import Data.Set (Set)
import qualified Data.Set as Set

import Text.Megaparsec
import Text.Megaparsec.Char
import qualified Text.Megaparsec.Char.Lexer as L

-- | Parser type: parses Text with no custom error component.
type Parser = Parsec Void Text

-- | Parser error type.
type ParserError = ParseErrorBundle Text Void

-- | Run a parser on input text.
runLexer :: Parser a -> FilePath -> Text -> Either ParserError a
runLexer = parse

-- | Run a parser and print the result (for testing).
testParser :: Show a => Parser a -> Text -> IO ()
testParser = Text.Megaparsec.parseTest

-- | Space consumer: skips whitespace and comments.
-- LiveOak uses // for line comments.
sc :: Parser ()
sc = L.space
  space1                         -- whitespace
  (L.skipLineComment "//")       -- line comments
  empty                          -- no block comments

-- | Wrap a parser to consume trailing whitespace.
lexeme :: Parser a -> Parser a
lexeme = L.lexeme sc

-- | Parse a fixed symbol (keyword or operator) and consume trailing whitespace.
symbol :: Text -> Parser Text
symbol = L.symbol sc

-- | Parse an integer literal.
intLiteral :: Parser Int
intLiteral = lexeme L.decimal

-- | Parse a string literal (double-quoted).
stringLiteral :: Parser String
stringLiteral = lexeme $ char '"' *> manyTill L.charLiteral (char '"')

-- | Parse a boolean literal.
boolLiteral :: Parser Bool
boolLiteral = lexeme $ choice
  [ True  <$ string "true"
  , False <$ string "false"
  ]

-- | Reserved words in LiveOak.
reservedWords :: Set Text
reservedWords = Set.fromList
  [ "class", "if", "else", "while", "return", "break"
  , "new", "null", "this", "true", "false"
  , "int", "bool", "String", "void"
  ]

-- | Check if a word is reserved.
isReserved :: Text -> Bool
isReserved = (`Set.member` reservedWords)

-- | Parse an identifier (not a reserved word).
identifier :: Parser String
identifier = lexeme $ try $ do
  name <- (:) <$> letterChar <*> many (alphaNumChar <|> char '_')
  let nameT = T.pack name
  if isReserved nameT
    then fail $ "keyword " ++ show name ++ " cannot be used as identifier"
    else return name

-- | Parse a specific reserved word.
reserved :: Text -> Parser ()
reserved w = lexeme $ try $ do
  void $ string w
  notFollowedBy alphaNumChar

-- | Parse a single-character operator.
operator :: Char -> Parser ()
operator c = void $ lexeme $ char c

-- | Parse content between parentheses.
parens :: Parser a -> Parser a
parens = between (symbol "(") (symbol ")")

-- | Parse content between braces.
braces :: Parser a -> Parser a
braces = between (symbol "{") (symbol "}")

-- | Parse a semicolon.
semi :: Parser ()
semi = void $ symbol ";"

-- | Parse a comma.
comma :: Parser ()
comma = void $ symbol ","

-- | Parse a dot.
dot :: Parser ()
dot = void $ symbol "."

-- | Parse a colon.
colon :: Parser ()
colon = void $ symbol ":"

-- | Parse a question mark.
question :: Parser ()
question = void $ symbol "?"

-- | Get current source position as line number.
getPosition :: Parser Int
getPosition = unPos . sourceLine <$> getSourcePos

-- | Alias for getPosition.
getLineNo :: Parser Int
getLineNo = getPosition
