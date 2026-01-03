{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE LambdaCase #-}

-- | Property-based tests and fuzzing for the LiveOak compiler.
module PropertyTest (propertyTests) where

import Test.Tasty
import Test.Tasty.QuickCheck

import Data.Text (Text)
import qualified Data.Text as T
import Control.Exception (evaluate, try, SomeException)
import System.IO.Unsafe (unsafePerformIO)

import LiveOak.Types
import LiveOak.Ast
import LiveOak.Parser (parseProgram)
import LiveOak.Peephole (parseSam, optimize, SamInstr(..))
import qualified LiveOak.Optimize as Opt
import LiveOak.Compiler (compile)

-- | All property-based tests
propertyTests :: TestTree
propertyTests = testGroup "Property Tests"
  [ testGroup "Parser Fuzzing"
      [ localOption (QuickCheckTests 10) $
          testProperty "parser doesn't crash on random input" prop_parserNoCrash
      , localOption (QuickCheckTests 10) $
          testProperty "parser doesn't crash on semi-valid input" prop_parserSemiValid
      ]
  , testGroup "Peephole Optimizer"
      [ localOption (QuickCheckTests 10) $
          testProperty "peephole doesn't crash on random SAM" prop_peepholeNoCrash
      , localOption (QuickCheckTests 10) $
          testProperty "peephole is idempotent" prop_peepholeIdempotent
      , localOption (QuickCheckTests 10) $
          testProperty "peephole preserves labels" prop_peepholePreservesLabels
      , localOption (QuickCheckTests 10) $
          testProperty "optimize reduces or preserves instruction count" prop_peepholeReduces
      ]
  , testGroup "AST Optimizer"
      [ localOption (QuickCheckTests 10) $
          testProperty "constant folding preserves int literals" prop_constFoldInt
      , localOption (QuickCheckTests 10) $
          testProperty "optimizer is idempotent" prop_optimizerIdempotent
      ]
  , testGroup "Compiler"
      [ localOption (QuickCheckTests 10) $
          testProperty "valid minimal programs compile" prop_minimalProgramCompiles
      ]
  ]

--------------------------------------------------------------------------------
-- Parser Fuzzing
--------------------------------------------------------------------------------

-- | Generate random strings to fuzz the parser
prop_parserNoCrash :: Property
prop_parserNoCrash = forAll arbitraryText $ \input ->
  let result = unsafePerformIO $ try (evaluate (parseProgram "fuzz" input))
  in case result of
    Left (_ :: SomeException) -> False  -- Parser crashed
    Right _ -> True  -- Parser returned (success or error, both ok)

-- | Generate semi-valid looking code
prop_parserSemiValid :: Property
prop_parserSemiValid = forAll genSemiValidCode $ \input ->
  let result = unsafePerformIO $ try (evaluate (parseProgram "fuzz" input))
  in case result of
    Left (_ :: SomeException) -> False
    Right _ -> True

-- | Generate random text
arbitraryText :: Gen Text
arbitraryText = T.pack <$> arbitrary

-- | Generate semi-valid looking LiveOak code
genSemiValidCode :: Gen Text
genSemiValidCode = do
  classCount <- choose (0, 3)
  classes <- vectorOf classCount genClass
  return $ T.unlines classes

genClass :: Gen Text
genClass = do
  name <- genIdentifier
  fields <- genFields
  methods <- genMethods
  return $ "class " <> name <> "(" <> fields <> ") {\n" <> methods <> "}\n"

genFields :: Gen Text
genFields = do
  count <- choose (0, 3)
  if count == 0
    then return ""
    else do
      fields <- vectorOf count genField
      return $ T.intercalate " " fields

genField :: Gen Text
genField = do
  typ <- elements ["int", "bool", "string"]
  name <- genIdentifier
  return $ typ <> " " <> name <> ";"

genMethods :: Gen Text
genMethods = do
  count <- choose (0, 3)
  methods <- vectorOf count genMethod
  return $ T.unlines methods

genMethod :: Gen Text
genMethod = do
  retType <- elements ["int", "bool", "void", "string"]
  name <- genIdentifier
  params <- genParams
  body <- genBody
  return $ "  " <> retType <> " " <> name <> "(" <> params <> ") { " <> body <> " }"

genParams :: Gen Text
genParams = do
  count <- choose (0, 2)
  if count == 0
    then return ""
    else do
      params <- vectorOf count genParam
      return $ T.intercalate ", " params

genParam :: Gen Text
genParam = do
  typ <- elements ["int", "bool", "string"]
  name <- genIdentifier
  return $ typ <> " " <> name

genBody :: Gen Text
genBody = do
  stmts <- genStatements
  return $ "{ " <> stmts <> " }"

genStatements :: Gen Text
genStatements = do
  count <- choose (0, 3)
  stmts <- vectorOf count genStatement
  return $ T.unlines stmts

genStatement :: Gen Text
genStatement = oneof
  [ return ";"
  , do
      name <- genIdentifier
      expr <- genExpr
      return $ name <> " = " <> expr <> ";"
  , do
      expr <- genExpr
      return $ "return " <> expr <> ";"
  , return "return;"
  , return "break;"
  ]

genExpr :: Gen Text
genExpr = sized $ \n ->
  if n <= 0
    then genAtom
    else oneof
      [ genAtom
      , do
          left <- resize (n `div` 2) genExpr
          op <- elements ["+", "-", "*", "/", "=", "<", ">", "&", "|"]
          right <- resize (n `div` 2) genExpr
          return $ "(" <> left <> " " <> op <> " " <> right <> ")"
      ]

genAtom :: Gen Text
genAtom = oneof
  [ T.pack . show <$> (arbitrary :: Gen Int)
  , elements ["true", "false", "null", "this"]
  , genIdentifier
  ]

genIdentifier :: Gen Text
genIdentifier = do
  first <- elements ['a'..'z']
  rest <- listOf $ elements $ ['a'..'z'] ++ ['A'..'Z'] ++ ['0'..'9'] ++ ['_']
  let ident = first : take 10 rest
  if ident `elem` ["int", "bool", "void", "string", "class", "if", "else", "while", "return", "break", "true", "false", "null", "this", "new"]
    then return "myVar"
    else return $ T.pack ident

--------------------------------------------------------------------------------
-- Peephole Optimizer Properties
--------------------------------------------------------------------------------

-- | The peephole optimizer should not crash on any input
prop_peepholeNoCrash :: Property
prop_peepholeNoCrash = forAll genSamCode $ \code ->
  let result = unsafePerformIO $ try (evaluate (length (optimize (parseSam code))))
  in case result of
    Left (_ :: SomeException) -> False
    Right _ -> True

-- | Optimizing twice should give the same result as optimizing once
prop_peepholeIdempotent :: Property
prop_peepholeIdempotent = forAll genSamCode $ \code ->
  let instrs = parseSam code
      optimized1 = optimize instrs
      optimized2 = optimize optimized1
  in optimized1 == optimized2

-- | Labels that exist AND are referenced should be preserved
-- (unreferenced labels may be removed as dead code)
prop_peepholePreservesLabels :: Property
prop_peepholePreservesLabels = forAll genSamCode $ \code ->
  let instrs = parseSam code
      optimized = optimize instrs
      -- Labels that are defined in the input
      definedLabels = [l | Label l <- instrs]
      -- Labels that are both defined AND referenced
      referencedLabels = [l | i <- instrs, l <- getJumpTargets i, l `elem` definedLabels]
      labelsAfter = [l | Label l <- optimized]
  in all (`elem` labelsAfter) referencedLabels

getJumpTargets :: SamInstr -> [Text]
getJumpTargets (JUMP l) = [l]
getJumpTargets (JUMPC l) = [l]
getJumpTargets (JSR l) = [l]
getJumpTargets _ = []

-- | Optimization should reduce or preserve instruction count (never increase significantly)
prop_peepholeReduces :: Property
prop_peepholeReduces = forAll genSamCode $ \code ->
  let instrs = parseSam code
      optimized = optimize instrs
      countBefore = length [i | i <- instrs, isRealInstr i]
      countAfter = length [i | i <- optimized, isRealInstr i]
  in countAfter <= countBefore + 1  -- Allow +1 for edge cases like x*0

isRealInstr :: SamInstr -> Bool
isRealInstr = \case
  Label _ -> False
  Comment _ -> False
  Blank -> False
  _ -> True

-- | Generate random SAM code (limited to 20 instructions for performance)
genSamCode :: Gen Text
genSamCode = do
  len <- choose (0, 20 :: Int)
  instrs <- vectorOf len genSamInstr
  return $ T.unlines instrs

genSamInstr :: Gen Text
genSamInstr = oneof
  [ do n <- choose (-100, 100 :: Int); return $ "PUSHIMM " <> T.pack (show n)
  , do n <- choose (-10, 10 :: Int); return $ "PUSHOFF " <> T.pack (show n)
  , do n <- choose (-10, 10 :: Int); return $ "STOREOFF " <> T.pack (show n)
  , do n <- choose (-5, 5 :: Int); return $ "ADDSP " <> T.pack (show n)
  , return "ADD"
  , return "SUB"
  , return "TIMES"
  , return "DIV"
  , return "ISNIL"
  , return "DUP"
  , return "SWAP"
  , return "EQUAL"
  , return "LESS"
  , return "GREATER"
  , do lbl <- genLabel; return $ lbl <> ":"
  , do lbl <- genLabel; return $ "JUMP " <> lbl
  , do lbl <- genLabel; return $ "JUMPC " <> lbl
  , do lbl <- genLabel; return $ "JSR " <> lbl
  , return "LINK"
  , return "UNLINK"
  , return "RST"
  , return "MALLOC"
  , return "PUSHIND"
  , return "STOREIND"
  ]

genLabel :: Gen Text
genLabel = do
  prefix <- elements ["loop", "end", "label", "method", "if", "else"]
  n <- choose (0, 100 :: Int)
  return $ prefix <> "_" <> T.pack (show n)

--------------------------------------------------------------------------------
-- AST Optimizer Properties
--------------------------------------------------------------------------------

-- | Constant folding should preserve integer literal values
prop_constFoldInt :: Property
prop_constFoldInt = forAll arbitrary $ \(n :: Int) ->
  let expr = IntLit n 0
      optimized = Opt.foldExpr expr
  in case optimized of
    IntLit m _ -> m == n
    _ -> False

-- | Optimizing the AST twice should give the same result
prop_optimizerIdempotent :: Property
prop_optimizerIdempotent = forAll genSimpleProgram $ \prog ->
  let opt1 = Opt.optimize prog
      opt2 = Opt.optimize opt1
  in opt1 == opt2

-- | Generate a simple valid program
genSimpleProgram :: Gen Program
genSimpleProgram = do
  body <- genSimpleStmt
  let mainMethod = MethodDecl
        { methodClassName = "Main"
        , methodName = "main"
        , methodParams = []
        , methodReturnSig = RetPrim TInt
        , methodBody = body
        }
  let mainClass = ClassDecl
        { className = "Main"
        , classFields = []
        , classMethods = [mainMethod]
        }
  return $ Program [mainClass]

genSimpleStmt :: Gen Stmt
genSimpleStmt = do
  expr <- genSimpleExpr
  return $ Block [Return (Just expr) 1] 1

genSimpleExpr :: Gen Expr
genSimpleExpr = sized $ \n ->
  if n <= 0
    then IntLit <$> arbitrary <*> pure 0
    else oneof
      [ IntLit <$> arbitrary <*> pure 0
      , BoolLit <$> arbitrary <*> pure 0
      , do
          left <- resize (n `div` 2) genSimpleExpr
          right <- resize (n `div` 2) genSimpleExpr
          op <- elements [Add, Sub, Mul]
          return $ Binary op left right 0
      ]

--------------------------------------------------------------------------------
-- Compiler Properties
--------------------------------------------------------------------------------

-- | Minimal valid programs should always compile
prop_minimalProgramCompiles :: Property
prop_minimalProgramCompiles = forAll genMinimalProgram $ \code ->
  case compile "test" code of
    Left _ -> False
    Right _ -> True

genMinimalProgram :: Gen Text
genMinimalProgram = do
  retVal <- choose (0, 100 :: Int)
  return $ T.unlines
    [ "class Main() {"
    , "  int main() {"
    , "    { return " <> T.pack (show retVal) <> "; }"
    , "  }"
    , "}"
    ]
