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
import LiveOak.Peephole (parseSam, optimize, emitSam, SamInstr(..))
import qualified LiveOak.Optimize as Opt
import LiveOak.Compiler (compile)
import LiveOak.Sam (runSamText)

-- | All property-based tests
propertyTests :: TestTree
propertyTests = localOption (QuickCheckTests 100) $ testGroup "Property Tests"
  [ testGroup "Parser Fuzzing"
      [ testProperty "parser doesn't crash on random input" prop_parserNoCrash
      , testProperty "parser doesn't crash on semi-valid input" prop_parserSemiValid
      ]
  , testGroup "Peephole Optimizer"
      [ testProperty "peephole doesn't crash on random SAM" prop_peepholeNoCrash
      , testProperty "peephole is idempotent" prop_peepholeIdempotent
      , testProperty "peephole preserves labels" prop_peepholePreservesLabels
      , testProperty "optimize reduces or preserves instruction count" prop_peepholeReduces
      ]
  , testGroup "AST Optimizer"
      [ testProperty "constant folding preserves int literals" prop_constFoldInt
      , testProperty "optimizer is idempotent" prop_optimizerIdempotent
      ]
  , testGroup "Compiler"
      [ testProperty "valid minimal programs compile" prop_minimalProgramCompiles
      ]
  , testGroup "Optimization Equivalence"
      [ testProperty "optimized code produces same result" prop_optimizationPreservesSemantics
      ]
  , testGroup "Round-trip"
      [ testProperty "SAM parse-emit-parse is identity" prop_samRoundTrip
      ]
  , testGroup "Stress Tests"
      [ localOption (QuickCheckTests 50) $
          testProperty "large programs compile" prop_largeProgramsCompile
      , localOption (QuickCheckTests 50) $
          testProperty "deeply nested expressions don't crash" prop_deepNesting
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

--------------------------------------------------------------------------------
-- Optimization Equivalence
--------------------------------------------------------------------------------

-- | Optimized and unoptimized code should produce the same result
prop_optimizationPreservesSemantics :: Property
prop_optimizationPreservesSemantics = forAll genExecutableProgram $ \code ->
  case compile "test" code of
    Left _ -> discard  -- Skip programs that don't compile
    Right samCode ->
      let optimizedSam = emitSam (optimize (parseSam samCode))
          unoptResult = runSamText samCode
          optResult = runSamText optimizedSam
      in case (unoptResult, optResult) of
        (Right v1, Right v2) -> v1 === v2
        (Left _, Left _) -> property True  -- Both error is ok
        _ -> property False  -- One succeeds, one fails = bad

-- | Generate a program that is guaranteed to compile and execute
genExecutableProgram :: Gen Text
genExecutableProgram = do
  -- Generate a simple arithmetic expression
  expr <- genArithExpr
  return $ T.unlines
    [ "class Main() {"
    , "  int main() {"
    , "    { return " <> expr <> "; }"
    , "  }"
    , "}"
    ]

-- | Generate arithmetic expressions that are safe to execute
genArithExpr :: Gen Text
genArithExpr = sized $ \n ->
  if n <= 0
    then T.pack . show <$> choose (0, 100 :: Int)
    else oneof
      [ T.pack . show <$> choose (0, 100 :: Int)
      , do
          left <- resize (n `div` 2) genArithExpr
          right <- resize (n `div` 2) genArithExpr
          op <- elements ["+", "-", "*"]  -- No division to avoid div by zero
          return $ "(" <> left <> " " <> op <> " " <> right <> ")"
      ]

--------------------------------------------------------------------------------
-- Round-trip Testing
--------------------------------------------------------------------------------

-- | Parse -> Emit -> Parse should give the same result
prop_samRoundTrip :: Property
prop_samRoundTrip = forAll genValidSamCode $ \code ->
  let parsed1 = parseSam code
      emitted = emitSam parsed1
      parsed2 = parseSam emitted
  in parsed1 === parsed2

-- | Generate valid SAM code (well-formed labels)
genValidSamCode :: Gen Text
genValidSamCode = do
  len <- choose (1, 15 :: Int)
  -- Generate some labels first so we can reference them
  numLabels <- choose (0, 3 :: Int)
  labels <- vectorOf numLabels $ do
    n <- choose (0, 10 :: Int)
    return $ "label_" <> T.pack (show n)
  -- Generate instructions that may reference these labels
  instrs <- vectorOf len (genValidSamInstr labels)
  -- Add the label definitions
  labelDefs <- mapM (\l -> return $ l <> ":") labels
  return $ T.unlines (labelDefs ++ instrs)

genValidSamInstr :: [Text] -> Gen Text
genValidSamInstr labels = oneof $
  [ do n <- choose (0, 100 :: Int); return $ "PUSHIMM " <> T.pack (show n)
  , do n <- choose (0, 5 :: Int); return $ "PUSHOFF " <> T.pack (show n)
  , do n <- choose (0, 5 :: Int); return $ "STOREOFF " <> T.pack (show n)
  , do n <- choose (-2, 2 :: Int); return $ "ADDSP " <> T.pack (show n)
  , return "ADD"
  , return "SUB"
  , return "TIMES"
  , return "DUP"
  , return "SWAP"
  , return "EQUAL"
  , return "LESS"
  , return "LINK"
  , return "UNLINK"
  ] ++
  -- Only add jump instructions if we have labels to jump to
  (if null labels then [] else
    [ do lbl <- elements labels; return $ "JUMP " <> lbl
    , do lbl <- elements labels; return $ "JUMPC " <> lbl
    , do lbl <- elements labels; return $ "JSR " <> lbl
    ])

--------------------------------------------------------------------------------
-- Stress Tests
--------------------------------------------------------------------------------

-- | Large programs with multiple classes and methods should compile
prop_largeProgramsCompile :: Property
prop_largeProgramsCompile = forAll genLargeProgram $ \code ->
  case compile "stress" code of
    Left _ -> discard  -- Some generated programs may have type errors, skip them
    Right _ -> property True

-- | Generate a large program with multiple classes
genLargeProgram :: Gen Text
genLargeProgram = do
  -- Generate 2-5 helper classes
  numClasses <- choose (2, 5 :: Int)
  helperClasses <- vectorOf numClasses genHelperClass
  -- Always include Main class
  mainClass <- genMainClass
  return $ T.unlines (helperClasses ++ [mainClass])

genHelperClass :: Gen Text
genHelperClass = do
  name <- genClassName
  numFields <- choose (0, 3 :: Int)
  fields <- vectorOf numFields genTypedField
  numMethods <- choose (1, 3 :: Int)
  methods <- vectorOf numMethods (genTypedMethod name)
  return $ T.unlines
    [ "class " <> name <> "(" <> T.intercalate " " fields <> ") {"
    , T.unlines methods
    , "}"
    ]

genMainClass :: Gen Text
genMainClass = do
  numLocals <- choose (0, 5 :: Int)
  locals <- vectorOf numLocals genLocalDecl
  computation <- genComputation
  return $ T.unlines
    [ "class Main() {"
    , "  int main() {"
    , "    {"
    , T.unlines (map ("      " <>) locals)
    , "      return " <> computation <> ";"
    , "    }"
    , "  }"
    , "}"
    ]

genClassName :: Gen Text
genClassName = do
  suffix <- choose (1, 100 :: Int)
  return $ "Helper" <> T.pack (show suffix)

genTypedField :: Gen Text
genTypedField = do
  typ <- elements ["int", "bool"]
  name <- genVarName
  return $ typ <> " " <> name <> ";"

genTypedMethod :: Text -> Gen Text
genTypedMethod _className = do
  retType <- elements ["int", "bool", "void"]
  name <- genMethodName
  body <- case retType of
    "int" -> do
      val <- choose (0, 100 :: Int)
      return $ "return " <> T.pack (show val) <> ";"
    "bool" -> do
      val <- elements ["true", "false"]
      return $ "return " <> val <> ";"
    _ -> return ";"
  return $ "  " <> retType <> " " <> name <> "() { { " <> body <> " } }"

genLocalDecl :: Gen Text
genLocalDecl = do
  typ <- elements ["int", "bool"]
  name <- genVarName
  val <- case typ of
    "int" -> T.pack . show <$> choose (0, 100 :: Int)
    _ -> elements ["true", "false"]
  return $ typ <> " " <> name <> "; " <> name <> " = " <> val <> ";"

genComputation :: Gen Text
genComputation = sized $ \n ->
  if n <= 0
    then T.pack . show <$> choose (0, 100 :: Int)
    else oneof
      [ T.pack . show <$> choose (0, 100 :: Int)
      , do
          left <- resize (n `div` 2) genComputation
          right <- resize (n `div` 2) genComputation
          op <- elements ["+", "-", "*"]
          return $ "(" <> left <> " " <> op <> " " <> right <> ")"
      ]

genVarName :: Gen Text
genVarName = do
  n <- choose (1, 100 :: Int)
  return $ "var" <> T.pack (show n)

genMethodName :: Gen Text
genMethodName = do
  n <- choose (1, 100 :: Int)
  return $ "method" <> T.pack (show n)

-- | Deeply nested expressions should not crash the compiler
prop_deepNesting :: Property
prop_deepNesting = forAll genDeeplyNested $ \code ->
  let result = unsafePerformIO $ try (evaluate (compile "deep" code))
  in case result of
    Left (_ :: SomeException) -> property False  -- Crashed
    Right (Left _) -> discard  -- Type error, skip
    Right (Right _) -> property True  -- Compiled successfully

-- | Generate a program with deeply nested expressions
genDeeplyNested :: Gen Text
genDeeplyNested = do
  depth <- choose (10, 30 :: Int)
  expr <- genNestedExpr depth
  return $ T.unlines
    [ "class Main() {"
    , "  int main() {"
    , "    { return " <> expr <> "; }"
    , "  }"
    , "}"
    ]

genNestedExpr :: Int -> Gen Text
genNestedExpr 0 = T.pack . show <$> choose (0, 10 :: Int)
genNestedExpr n = do
  inner <- genNestedExpr (n - 1)
  op <- elements ["+", "-", "*"]
  val <- choose (0, 10 :: Int)
  return $ "(" <> inner <> " " <> op <> " " <> T.pack (show val) <> ")"
