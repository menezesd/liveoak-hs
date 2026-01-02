{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RecordWildCards #-}

-- | Parser for LiveOak using Megaparsec.
-- Implements the full grammar for programs, classes, methods, statements, and expressions.
module LiveOak.Parser
  ( -- * Parsing Programs
    parseProgram
  , parseProgramFromFile

    -- * Individual Parsers (for testing)
  , pProgram
  , pClass
  , pMethod
  , pStmt
  , pExpr
  ) where

import Control.Monad (when)
import Data.Text (Text)
import qualified Data.Text as T
import qualified Data.Text.IO as TIO
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map

import Text.Megaparsec

import LiveOak.Lexer
import LiveOak.Types
import LiveOak.Ast
import LiveOak.Symbol
import qualified LiveOak.Diag as D

-- | Parse a program from text.
parseProgram :: FilePath -> Text -> D.Result (Program, ProgramSymbols)
parseProgram path input = case runParser pProgramWithSymbols path input of
  Left err  -> D.syntaxErr (errorBundlePretty err) 0 0
  Right res -> D.ok res

-- | Parse a program from a file.
parseProgramFromFile :: FilePath -> IO (D.Result (Program, ProgramSymbols))
parseProgramFromFile path = do
  input <- TIO.readFile path
  return $ parseProgram path input

-- | Parse program and build symbol table simultaneously.
pProgramWithSymbols :: Parser (Program, ProgramSymbols)
pProgramWithSymbols = do
  sc  -- consume leading whitespace
  classes <- many pClass
  eof
  let prog = Program classes
  syms <- buildSymbols classes
  return (prog, syms)

-- | Build symbol table from parsed classes.
buildSymbols :: [ClassDecl] -> Parser ProgramSymbols
buildSymbols classes = do
  -- Check for duplicate class names
  let classNames = map className classes
      duplicates = findDuplicates classNames
  when (not (null duplicates)) $
    fail $ "Duplicate class definition: " ++ head duplicates
  -- Check for duplicate fields/methods within each class
  mapM_ checkClassDuplicates classes
  let classSyms = map buildClassSymbol classes
  return $ ProgramSymbols $ Map.fromList [(csName cs, cs) | cs <- classSyms]
  where
    findDuplicates :: [String] -> [String]
    findDuplicates names = [n | (n, cnt) <- Map.toList (countNames names), cnt > 1]
    countNames :: [String] -> Map String Int
    countNames = foldr (\n m -> Map.insertWith (+) n 1 m) Map.empty
    checkClassDuplicates :: ClassDecl -> Parser ()
    checkClassDuplicates ClassDecl{..} = do
      let fieldNames = map fst classFields
          fieldDups = findDuplicates fieldNames
      when (not (null fieldDups)) $
        fail $ "Duplicate field in class " ++ className ++ ": " ++ head fieldDups
      let methodNames = map methodName classMethods
          methodDups = findDuplicates methodNames
      when (not (null methodDups)) $
        fail $ "Duplicate method in class " ++ className ++ ": " ++ head methodDups

-- | Build a class symbol from a class declaration.
buildClassSymbol :: ClassDecl -> ClassSymbol
buildClassSymbol ClassDecl{..} = ClassSymbol
  { csName = className
  , csFields = [VarSymbol name vt False i (-1) (-1) | (i, (name, vt)) <- zip [0..] classFields]
  , csMethods = Map.fromList [(methodName m, buildMethodSymbol m) | m <- classMethods]
  , csFieldOrder = map fst classFields
  }

-- | Build a method symbol from a method declaration.
buildMethodSymbol :: MethodDecl -> MethodSymbol
buildMethodSymbol MethodDecl{..} = MethodSymbol
  { msName = methodName
  , msParams = thisParam : userParams
  , msLocals = extractLocals methodBody
  , msReturnType = returnSigToValueType methodReturnSig
  , msBodyStartLine = -1
  , msReturnTypeLine = -1
  , msReturnTypeCol = -1
  }
  where
    thisParam = VarSymbol "this" (ofObject methodClassName) True 0 (-1) (-1)
    userParams = [VarSymbol (paramName p) (paramType p) True (i + 1) (-1) (-1)
                 | (i, p) <- zip [0..] methodParams]

-- | Convert ReturnSig to Maybe ValueType.
returnSigToValueType :: ReturnSig -> Maybe ValueType
returnSigToValueType = \case
  Void       -> Nothing
  RetPrim t  -> Just (PrimitiveType t)
  RetObj cn  -> Just (ObjectRefType (ObjectType cn))

-- | Extract local variable declarations from a statement.
extractLocals :: Stmt -> [VarSymbol]
extractLocals = go 0
  where
    go idx stmt = case stmt of
      Block stmts _ -> goList idx stmts
      VarDecl name (Just vt) _ _ ->
        [VarSymbol name vt False idx (-1) (-1)]
      VarDecl name Nothing _ _ ->
        [VarSymbol name (PrimitiveType TInt) False idx (-1) (-1)]  -- default to int
      If _ th el _ -> go idx th ++ go (idx + length (go idx th)) el
      While _ body _ -> go idx body
      _ -> []

    goList _ [] = []
    goList idx (s:ss) =
      let locals = go idx s
          nextIdx = idx + length locals
      in locals ++ goList nextIdx ss

-- | Parse a program.
pProgram :: Parser Program
pProgram = do
  sc
  classes <- many pClass
  eof
  return $ Program classes

-- | Parse a class declaration.
pClass :: Parser ClassDecl
pClass = do
  reserved "class"
  name <- identifier
  fields <- pFieldsOpt
  methods <- braces (many (pMethod name))
  return ClassDecl
    { className = name
    , classFields = fields
    , classMethods = methods
    }

-- | Parse optional field declarations.
pFieldsOpt :: Parser [(String, ValueType)]
pFieldsOpt = option [] $ parens pFieldDecls

-- | Parse field declarations.
pFieldDecls :: Parser [(String, ValueType)]
pFieldDecls = option [] $ do
  groups <- pFieldGroup `sepBy` pure ()
  return $ concat groups

-- | Parse a group of fields with the same type.
pFieldGroup :: Parser [(String, ValueType)]
pFieldGroup = do
  vt <- pValueType
  names <- identifier `sepBy1` comma
  semi
  return [(name, vt) | name <- names]

-- | Parse a value type.
pValueType :: Parser ValueType
pValueType = do
  name <- pTypeName
  when (name == "void") $
    fail "void is not allowed for fields, parameters, or local variables"
  return $ case parseType name of
    Just t  -> PrimitiveType t
    Nothing -> ObjectRefType (ObjectType name)

-- | Parse a type name (including void).
pTypeName :: Parser String
pTypeName = lexeme $ choice
  [ "int"    <$ reserved "int"
  , "bool"   <$ reserved "bool"
  , "String" <$ reserved "String"
  , "void"   <$ reserved "void"
  , identifier
  ]

-- | Parse a return signature.
pReturnSig :: Parser ReturnSig
pReturnSig = do
  name <- pTypeName
  return $ case name of
    "void"   -> Void
    "int"    -> RetPrim TInt
    "bool"   -> RetPrim TBool
    "String" -> RetPrim TString
    cn       -> RetObj cn

-- | Parse a method declaration.
pMethod :: String -> Parser MethodDecl
pMethod className = do
  retSig <- pReturnSig
  name <- identifier
  params <- parens (pParam `sepBy` comma)
  body <- braces pMethodBody
  return MethodDecl
    { methodClassName = className
    , methodName = name
    , methodParams = params
    , methodReturnSig = retSig
    , methodBody = body
    }

-- | Parse a parameter.
pParam :: Parser ParamDecl
pParam = do
  vt <- pValueType
  name <- identifier
  return ParamDecl { paramName = name, paramType = vt }

-- | Parse method body (local declarations + statements).
pMethodBody :: Parser Stmt
pMethodBody = do
  pos <- getLineNo
  -- Parse local variable declarations
  locals <- many (try pLocalDecl)
  -- Parse statements
  stmts <- many pStmt
  return $ Block (concat locals ++ stmts) pos

-- | Parse local variable declarations.
pLocalDecl :: Parser [Stmt]
pLocalDecl = do
  pos <- getLineNo
  vt <- pValueType
  names <- identifier `sepBy1` comma
  semi
  return [VarDecl name (Just vt) Nothing pos | name <- names]

-- | Parse a statement.
pStmt :: Parser Stmt
pStmt = choice
  [ pBlock
  , pIf
  , pWhile
  , pReturn
  , pBreak
  , pEmptyStmt
  , try pAssignment
  , pExprStmt
  ]

-- | Parse an empty statement (just a semicolon).
pEmptyStmt :: Parser Stmt
pEmptyStmt = do
  pos <- getLineNo
  semi
  return $ Block [] pos

-- | Parse a block.
pBlock :: Parser Stmt
pBlock = do
  pos <- getLineNo
  stmts <- braces (many pStmt)
  return $ Block stmts pos

-- | Parse an if statement.
pIf :: Parser Stmt
pIf = do
  pos <- getLineNo
  reserved "if"
  cond <- parens pExpr
  thenBranch <- pBlock
  reserved "else"
  elseBranch <- pBlock
  return $ If cond thenBranch elseBranch pos

-- | Parse a while statement.
pWhile :: Parser Stmt
pWhile = do
  pos <- getLineNo
  reserved "while"
  cond <- parens pExpr
  body <- pBlock
  return $ While cond body pos

-- | Parse a return statement.
pReturn :: Parser Stmt
pReturn = do
  pos <- getLineNo
  reserved "return"
  value <- optional pExpr
  semi
  return $ Return value pos

-- | Parse a break statement.
pBreak :: Parser Stmt
pBreak = do
  pos <- getLineNo
  reserved "break"
  semi
  return $ Break pos

-- | Parse an assignment statement.
-- Uses pPostfix (not pExpr) for the target to avoid consuming '=' as comparison.
pAssignment :: Parser Stmt
pAssignment = do
  pos <- getLineNo
  target <- pPostfix  -- Only parse variable or field access, not full expressions
  operator '='
  value <- pExpr
  semi
  case target of
    Var name _ -> return $ Assign name value pos
    FieldAccess tgt field _ -> return $ FieldAssign tgt field (-1) value pos
    _ -> fail "Invalid assignment target"

-- | Parse an expression statement.
pExprStmt :: Parser Stmt
pExprStmt = do
  pos <- getLineNo
  expr <- pExpr
  semi
  return $ ExprStmt expr pos

-- | Parse an expression.
pExpr :: Parser Expr
pExpr = pTernary

-- | Parse a ternary expression.
pTernary :: Parser Expr
pTernary = do
  pos <- getLineNo
  cond <- pOr
  option cond $ do
    question
    thenExpr <- pExpr
    colon
    elseExpr <- pExpr
    return $ Ternary cond thenExpr elseExpr pos

-- | Parse an OR expression.
pOr :: Parser Expr
pOr = pBinopLeft pAnd [("|", Or)]

-- | Parse an AND expression.
pAnd :: Parser Expr
pAnd = pBinopLeft pComparison [("&", And)]

-- | Parse a comparison expression.
pComparison :: Parser Expr
pComparison = pBinopLeft pAddSub [("<", Lt), (">", Gt), ("=", Eq)]

-- | Parse addition/subtraction.
pAddSub :: Parser Expr
pAddSub = pBinopLeft pMulDiv [("+", Add), ("-", Sub)]

-- | Parse multiplication/division/modulo.
pMulDiv :: Parser Expr
pMulDiv = pBinopLeft pUnary [("*", Mul), ("/", Div), ("%", Mod)]

-- | Helper for left-associative binary operators.
pBinopLeft :: Parser Expr -> [(String, BinaryOp)] -> Parser Expr
pBinopLeft pSub ops = do
  left <- pSub
  rest left
  where
    rest left = option left $ do
      pos <- getLineNo
      op <- choice [op <$ symbol (T.pack s) | (s, op) <- ops]
      right <- pSub
      rest (Binary op left right pos)

-- | Parse a unary expression.
pUnary :: Parser Expr
pUnary = choice
  [ do pos <- getLineNo
       operator '~'
       expr <- pUnary
       return $ Unary Neg expr pos
  , do pos <- getLineNo
       operator '!'
       expr <- pUnary
       return $ Unary Not expr pos
  , pPostfix
  ]

-- | Parse a postfix expression (method calls, field access).
pPostfix :: Parser Expr
pPostfix = do
  base <- pPrimary
  pPostfixOps base

-- | Parse postfix operations.
pPostfixOps :: Expr -> Parser Expr
pPostfixOps expr = option expr $ do
  pos <- getLineNo
  dot
  name <- identifier
  result <- option (FieldAccess expr name pos) $ do
    args <- parens (pExpr `sepBy` comma)
    return $ InstanceCall expr name args pos
  pPostfixOps result

-- | Parse a primary expression.
pPrimary :: Parser Expr
pPrimary = choice
  [ pParenExpr
  , pNewObject
  , pThisExpr
  , pNullExpr
  , pBoolExpr
  , pIntExpr
  , pStrExpr
  , pVarOrCall
  ]

-- | Parse a parenthesized expression.
pParenExpr :: Parser Expr
pParenExpr = parens pExpr

-- | Parse 'new' object creation.
pNewObject :: Parser Expr
pNewObject = do
  pos <- getLineNo
  reserved "new"
  className <- identifier
  args <- parens (pExpr `sepBy` comma)
  return $ NewObject className args pos

-- | Parse 'this'.
pThisExpr :: Parser Expr
pThisExpr = do
  pos <- getLineNo
  reserved "this"
  return $ This pos

-- | Parse 'null'.
pNullExpr :: Parser Expr
pNullExpr = do
  pos <- getLineNo
  reserved "null"
  return $ NullLit pos

-- | Parse a boolean literal.
pBoolExpr :: Parser Expr
pBoolExpr = do
  pos <- getLineNo
  b <- boolLiteral
  return $ BoolLit b pos

-- | Parse an integer literal.
pIntExpr :: Parser Expr
pIntExpr = do
  pos <- getLineNo
  n <- intLiteral
  return $ IntLit n pos

-- | Parse a string literal.
pStrExpr :: Parser Expr
pStrExpr = do
  pos <- getLineNo
  s <- stringLiteral
  return $ StrLit s pos

-- | Parse a variable reference or method call.
pVarOrCall :: Parser Expr
pVarOrCall = do
  pos <- getLineNo
  name <- identifier
  option (Var name pos) $ do
    args <- parens (pExpr `sepBy` comma)
    return $ Call name args pos
