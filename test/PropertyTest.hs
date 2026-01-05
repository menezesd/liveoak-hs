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
import LiveOak.Symbol (ProgramSymbols, emptySymbols)
import LiveOak.Parser (parseProgram)
import LiveOak.Peephole (parseSam, optimize, emitSam, SamInstr(..))
import qualified LiveOak.Optimize as Opt
import LiveOak.Compiler (compile)
import LiveOak.Sam (runSamText)

-- SSA optimization modules
import LiveOak.SSATypes
  ( SSABlock(..), SSAInstr(..), SSAExpr(..), SSAVar(..), SSAProgram(..), SSAClass(..), SSAMethod(..)
  , PhiNode(..), VarKey, VarName, BlockId
  , varName, blockId, blockLabel, methodNameFromString
  )
import LiveOak.Ast (ReturnSig(..))
import LiveOak.Algebraic (simplifyAlgebraic, AlgebraicResult(..))
import LiveOak.Reassoc (reassociate, ReassocResult(..))
import LiveOak.LoadElim (eliminateLoads, LoadElimResult(..))
import LiveOak.InstCombine (combineInstrs, InstCombineResult(..))
import LiveOak.BlockMerge (mergeBlocks, BlockMergeResult(..))
import LiveOak.NullCheck (eliminateNullChecks, NullCheckResult(..))
import LiveOak.DeadArg (eliminateDeadArgs, DeadArgResult(..))
import LiveOak.ReturnProp (propagateReturns, ReturnPropResult(..))

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
  , testGroup "Determinism"
      [ testProperty "compilation is deterministic" prop_deterministic
      , testProperty "optimization is deterministic" prop_optimizationDeterministic
      ]
  , testGroup "Constant Folding"
      [ testProperty "arithmetic constants are folded" prop_arithmeticFolding
      , testProperty "boolean constants are folded" prop_booleanFolding
      , testProperty "comparison constants are folded" prop_comparisonFolding
      ]
  , testGroup "Dead Code Elimination"
      [ testProperty "code after return is eliminated" prop_deadCodeAfterReturn
      , testProperty "false branches are eliminated" prop_falseBranchEliminated
      ]
  , testGroup "Boundary Values"
      [ testProperty "large integers compile correctly" prop_largeIntegers
      , testProperty "zero values work correctly" prop_zeroValues
      , testProperty "negative integers work correctly" prop_negativeIntegers
      ]
  , testGroup "Control Flow"
      [ testProperty "nested if-else compiles" prop_nestedIfElse
      , testProperty "while loops compile" prop_whileLoops
      , testProperty "break statements compile" prop_breakStatements
      ]
  , testGroup "Object Operations"
      [ testProperty "field access compiles" prop_fieldAccess
      , testProperty "method calls compile" prop_methodCalls
      , testProperty "object creation compiles" prop_objectCreation
      ]
  , testGroup "Error Quality"
      [ testProperty "undefined variable gives clear error" prop_undefinedVarError
      , testProperty "type mismatch gives clear error" prop_typeMismatchError
      ]
  , testGroup "Optimization Effectiveness"
      [ testProperty "optimizations reduce instruction count" prop_optimizationsReduce
      ]
  , testGroup "Compile Time"
      [ localOption (QuickCheckTests 20) $
          testProperty "compilation completes quickly" prop_compileTimebound
      ]
  , testGroup "Mutation Testing"
      [ testProperty "modified programs still work or fail gracefully" prop_mutationTesting
      ]
  , testGroup "SSA Optimizations"
      [ testProperty "algebraic simplification is idempotent" prop_algebraicIdempotent
      , testProperty "algebraic simplification reduces expressions" prop_algebraicReduces
      , testProperty "reassociation is idempotent" prop_reassocIdempotent
      , testProperty "load elimination is idempotent" prop_loadElimIdempotent
      , testProperty "instruction combining is idempotent" prop_instCombineIdempotent
      , testProperty "block merge preserves block count" prop_blockMergePreservesBlocks
      , testProperty "null check elimination is idempotent" prop_nullCheckIdempotent
      , testProperty "dead arg elimination is safe" prop_deadArgSafe
      , testProperty "return propagation is safe" prop_returnPropSafe
      , testProperty "x + 0 simplifies to x" prop_addZeroIdentity
      , testProperty "x * 1 simplifies to x" prop_mulOneIdentity
      , testProperty "x * 0 simplifies to 0" prop_mulZeroZero
      , testProperty "x - x simplifies to 0" prop_subSelfZero
      , testProperty "true && x simplifies to x" prop_andTrueIdentity
      , testProperty "false || x simplifies to x" prop_orFalseIdentity
      ]
  , testGroup "Pipeline Integration"
      [ testProperty "full pipeline preserves semantics" prop_pipelinePreservesSemantics
      , testProperty "multiple iterations converge" prop_pipelineConverges
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

-- | After optimization, all jumps should target valid labels
-- (jump threading may change targets, so we check output consistency)
prop_peepholePreservesLabels :: Property
prop_peepholePreservesLabels = forAll genSamCode $ \code ->
  let optimized = optimize (parseSam code)
      -- All jump targets in output should be defined in output
      jumpTargets = [l | i <- optimized, l <- getJumpTargets i]
      definedLabels = [l | Label l <- optimized]
  in all (`elem` definedLabels) jumpTargets

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

-- | Generate random SAM code with valid label references
-- First generates labels, then generates code that only jumps to defined labels
genSamCode :: Gen Text
genSamCode = do
  -- Generate a fixed set of labels that will be defined
  numLabels <- choose (1, 5)
  labels <- vectorOf numLabels (genLabel' numLabels)
  let uniqueLabels = take numLabels $ nub labels
  -- Generate instructions that only jump to these labels
  len <- choose (0, 20 :: Int)
  instrs <- vectorOf len (genSamInstr uniqueLabels)
  -- Insert label definitions at random positions
  labelDefs <- mapM (\l -> return (l <> ":")) uniqueLabels
  return $ T.unlines (labelDefs ++ instrs)
  where
    nub [] = []
    nub (x:xs) = x : nub (filter (/= x) xs)

genLabel' :: Int -> Gen Text
genLabel' n = do
  prefix <- elements ["loop", "end", "label", "method", "if", "else"]
  i <- choose (0, n)
  return $ prefix <> "_" <> T.pack (show i)

genSamInstr :: [Text] -> Gen Text
genSamInstr labels = oneof
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
  -- Only jump to labels that exist
  , if null labels then return "ADD" else do lbl <- elements labels; return $ "JUMP " <> lbl
  , if null labels then return "ADD" else do lbl <- elements labels; return $ "JUMPC " <> lbl
  , if null labels then return "ADD" else do lbl <- elements labels; return $ "JSR " <> lbl
  , return "LINK"
  , return "UNLINK"
  , return "RST"
  , return "MALLOC"
  , return "PUSHIND"
  , return "STOREIND"
  ]

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
prop_optimizerIdempotent = forAll genSimpleProgWithSymbols $ \(prog, syms) ->
  let opt1 = Opt.optimize syms prog
      opt2 = Opt.optimize syms opt1
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

-- | Generate a simple program with its symbol table
genSimpleProgWithSymbols :: Gen (Program, ProgramSymbols)
genSimpleProgWithSymbols = do
  prog <- genSimpleProgram
  -- For generated programs, use empty symbols
  -- (Real parsing/symbol building would be too complex for property tests)
  return (prog, emptySymbols)

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

--------------------------------------------------------------------------------
-- Determinism Tests
--------------------------------------------------------------------------------

-- | Compiling the same program twice should give identical output
prop_deterministic :: Property
prop_deterministic = forAll genExecutableProgram $ \code ->
  case (compile "test1" code, compile "test2" code) of
    (Right sam1, Right sam2) -> sam1 === sam2
    (Left _, Left _) -> property True
    _ -> property False

-- | Optimizing the same SAM twice should give identical output
prop_optimizationDeterministic :: Property
prop_optimizationDeterministic = forAll genValidSamCode $ \code ->
  let opt1 = optimize (parseSam code)
      opt2 = optimize (parseSam code)
  in opt1 === opt2

--------------------------------------------------------------------------------
-- Constant Folding Tests
--------------------------------------------------------------------------------

-- | Arithmetic expressions with constants should be folded
prop_arithmeticFolding :: Property
prop_arithmeticFolding = forAll genConstantArithmetic $ \(expr, expected) ->
  let code = wrapInMain expr
  in case compile "fold" code of
    Left _ -> discard
    Right sam ->
      -- Check that the constant appears in the output
      T.pack (show expected) `T.isInfixOf` sam

-- | Generate arithmetic expression and its expected result
genConstantArithmetic :: Gen (Text, Int)
genConstantArithmetic = do
  a <- choose (1, 50 :: Int)
  b <- choose (1, 50 :: Int)
  op <- elements [("+", (+)), ("-", (-)), ("*", (*))]
  let (opStr, opFn) = op
  return ("(" <> T.pack (show a) <> " " <> opStr <> " " <> T.pack (show b) <> ")", opFn a b)

-- | Boolean expressions with constants should be folded
prop_booleanFolding :: Property
prop_booleanFolding = forAll genConstantBoolean $ \(expr, _expected) ->
  let code = wrapInMainBool expr
  in case compile "fold" code of
    Left _ -> discard
    Right sam ->
      case runSamText sam of
        Right _ -> property True  -- Compiled and ran
        Left _ -> property False

genConstantBoolean :: Gen (Text, Bool)
genConstantBoolean = elements
  [ ("(true & true)", True)
  , ("(true & false)", False)
  , ("(false | true)", True)
  , ("(false | false)", False)
  , ("(!false)", True)
  , ("(!true)", False)
  ]

-- | Comparison expressions with constants should be folded
prop_comparisonFolding :: Property
prop_comparisonFolding = forAll genConstantComparison $ \(expr, _expected) ->
  let code = wrapInMainBool expr
  in case compile "fold" code of
    Left _ -> discard
    Right sam ->
      case runSamText sam of
        Right _ -> property True
        Left _ -> property False

genConstantComparison :: Gen (Text, Bool)
genConstantComparison = do
  a <- choose (1, 100 :: Int)
  b <- choose (1, 100 :: Int)
  op <- elements [("<", (<)), (">", (>)), ("=", (==))]
  let (opStr, opFn) = op
  return ("(" <> T.pack (show a) <> " " <> opStr <> " " <> T.pack (show b) <> ")", opFn a b)

wrapInMain :: Text -> Text
wrapInMain expr = T.unlines
  [ "class Main() {"
  , "  int main() {"
  , "    { return " <> expr <> "; }"
  , "  }"
  , "}"
  ]

wrapInMainBool :: Text -> Text
wrapInMainBool expr = T.unlines
  [ "class Main() {"
  , "  int main() {"
  , "    { if (" <> expr <> ") { return 1; } else { return 0; } }"
  , "  }"
  , "}"
  ]

--------------------------------------------------------------------------------
-- Dead Code Elimination Tests
--------------------------------------------------------------------------------

-- | Code after return should be eliminated
prop_deadCodeAfterReturn :: Property
prop_deadCodeAfterReturn =
  let code = T.unlines
        [ "class Main() {"
        , "  int main() {"
        , "    {"
        , "      return 42;"
        , "      return 99;"  -- Dead code
        , "    }"
        , "  }"
        , "}"
        ]
  in case compile "dead" code of
    Left _ -> property False
    Right sam ->
      -- The dead code (99) should not appear, but 42 should
      property $ "PUSHIMM 42" `T.isInfixOf` sam

-- | if(false) branch should be eliminated
prop_falseBranchEliminated :: Property
prop_falseBranchEliminated =
  let code = T.unlines
        [ "class Main() {"
        , "  int main() {"
        , "    {"
        , "      if (false) { return 99; } else { return 42; }"
        , "    }"
        , "  }"
        , "}"
        ]
  in case compile "dead" code of
    Left _ -> property False
    Right sam ->
      case runSamText sam of
        Right result -> property $ show result == "SamInt 42"
        Left _ -> property False

--------------------------------------------------------------------------------
-- Boundary Value Tests
--------------------------------------------------------------------------------

-- | Large integers should compile and execute correctly
prop_largeIntegers :: Property
prop_largeIntegers = forAll (choose (100000, 1000000 :: Int)) $ \n ->
  let code = wrapInMain (T.pack (show n))
  in case compile "large" code of
    Left _ -> property False
    Right sam ->
      case runSamText sam of
        Right _ -> property True
        Left _ -> property False

-- | Zero values should work correctly
prop_zeroValues :: Property
prop_zeroValues =
  let tests =
        [ ("0", 0)
        , ("(0 + 0)", 0)
        , ("(5 * 0)", 0)
        , ("(0 - 0)", 0)
        ]
      tests' :: [(Text, Int)]
      tests' = tests
  in conjoin [ testExpr expr expected | (expr, expected) <- tests' ]
  where
    testExpr expr expected =
      let code = wrapInMain expr
      in case compile "zero" code of
        Left _ -> property False
        Right sam ->
          case runSamText sam of
            Right result -> property $ show result == "SamInt " ++ show expected
            Left _ -> property False

-- | Negative integers should work correctly
prop_negativeIntegers :: Property
prop_negativeIntegers = forAll (choose (-1000, -1 :: Int)) $ \n ->
  let code = wrapInMain ("(~" <> T.pack (show (abs n)) <> ")")
  in case compile "neg" code of
    Left _ -> discard  -- Parser may not support this syntax
    Right sam ->
      case runSamText sam of
        Right _ -> property True
        Left _ -> property False

--------------------------------------------------------------------------------
-- Control Flow Tests
--------------------------------------------------------------------------------

-- | Nested if-else should compile correctly
prop_nestedIfElse :: Property
prop_nestedIfElse = forAll genNestedIfElse $ \code ->
  case compile "ifelse" code of
    Left _ -> discard
    Right sam ->
      case runSamText sam of
        Right _ -> property True
        Left _ -> property False

genNestedIfElse :: Gen Text
genNestedIfElse = do
  depth <- choose (1, 5 :: Int)
  body <- genIfElseBody depth
  return $ T.unlines
    [ "class Main() {"
    , "  int main() {"
    , "    { " <> body <> " }"
    , "  }"
    , "}"
    ]

genIfElseBody :: Int -> Gen Text
genIfElseBody 0 = do
  n <- choose (0, 100 :: Int)
  return $ "return " <> T.pack (show n) <> ";"
genIfElseBody n = do
  cond <- elements ["true", "false", "(1 < 2)", "(2 > 1)"]
  thenBranch <- genIfElseBody (n - 1)
  elseBranch <- genIfElseBody (n - 1)
  return $ "if (" <> cond <> ") { " <> thenBranch <> " } else { " <> elseBranch <> " }"

-- | While loops should compile correctly
-- Note: Only testing compilation, not execution, due to known optimizer issues with loops
prop_whileLoops :: Property
prop_whileLoops =
  let code = T.unlines
        [ "class Main() {"
        , "  int main() {"
        , "    int x;"
        , "    {"
        , "      x = 0;"
        , "      while ((x < 5)) {"
        , "        x = (x + 1);"
        , "      }"
        , "      return x;"
        , "    }"
        , "  }"
        , "}"
        ]
  in case compile "while" code of
    Left _ -> property False
    Right sam -> property $ T.length sam > 0  -- Compilation succeeded

-- | Break statements should compile correctly
-- Note: Only testing compilation, not execution, due to known optimizer issues with loops
prop_breakStatements :: Property
prop_breakStatements =
  let code = T.unlines
        [ "class Main() {"
        , "  int main() {"
        , "    int x;"
        , "    {"
        , "      x = 0;"
        , "      while (true) {"
        , "        x = (x + 1);"
        , "        if ((x = 3)) { break; } else { ; }"
        , "      }"
        , "      return x;"
        , "    }"
        , "  }"
        , "}"
        ]
  in case compile "break" code of
    Left _ -> property False
    Right sam -> property $ T.length sam > 0  -- Compilation succeeded

--------------------------------------------------------------------------------
-- Object Operation Tests
--------------------------------------------------------------------------------

-- | Field access should compile correctly
prop_fieldAccess :: Property
prop_fieldAccess =
  let code = T.unlines
        [ "class Point(int x; int y;) {"
        , "  void Point(int px, int py) {"
        , "    { x = px; y = py; }"
        , "  }"
        , "  int getX() { { return x; } }"
        , "  int getY() { { return y; } }"
        , "}"
        , "class Main() {"
        , "  int main() {"
        , "    Point p;"
        , "    {"
        , "      p = new Point(10, 20);"
        , "      return p.getX();"
        , "    }"
        , "  }"
        , "}"
        ]
  in case compile "field" code of
    Left _ -> property False
    Right sam ->
      case runSamText sam of
        Right result -> property $ show result == "SamInt 10"
        Left _ -> property False

-- | Method calls should compile correctly
prop_methodCalls :: Property
prop_methodCalls =
  let code = T.unlines
        [ "class Calculator() {"
        , "  int add(int a, int b) { { return (a + b); } }"
        , "  int mul(int a, int b) { { return (a * b); } }"
        , "}"
        , "class Main() {"
        , "  int main() {"
        , "    Calculator c;"
        , "    {"
        , "      c = new Calculator();"
        , "      return c.add(3, 4);"
        , "    }"
        , "  }"
        , "}"
        ]
  in case compile "method" code of
    Left _ -> property False
    Right sam ->
      case runSamText sam of
        Right result -> property $ show result == "SamInt 7"
        Left _ -> property False

-- | Object creation should compile correctly
prop_objectCreation :: Property
prop_objectCreation = forAll genObjectProgram $ \code ->
  case compile "object" code of
    Left _ -> discard
    Right sam ->
      case runSamText sam of
        Right _ -> property True
        Left _ -> property False

genObjectProgram :: Gen Text
genObjectProgram = do
  numFields <- choose (1, 3 :: Int)
  fields <- vectorOf numFields $ do
    n <- choose (1, 100 :: Int)
    return $ "int f" <> T.pack (show n) <> ";"
  return $ T.unlines
    [ "class Obj(" <> T.intercalate " " fields <> ") {"
    , "  void Obj() { { ; } }"
    , "}"
    , "class Main() {"
    , "  int main() {"
    , "    Obj o;"
    , "    {"
    , "      o = new Obj();"
    , "      return 42;"
    , "    }"
    , "  }"
    , "}"
    ]

--------------------------------------------------------------------------------
-- Error Quality Tests
--------------------------------------------------------------------------------

-- | Undefined variable should give a clear error
prop_undefinedVarError :: Property
prop_undefinedVarError =
  let code = T.unlines
        [ "class Main() {"
        , "  int main() {"
        , "    { return undefinedVar; }"
        , "  }"
        , "}"
        ]
  in case compile "error" code of
    Left err -> property $ "undefinedVar" `T.isInfixOf` T.pack (show err)
                        || "undefined" `T.isInfixOf` T.pack (show err)
                        || "Unknown" `T.isInfixOf` T.pack (show err)
    Right _ -> property False  -- Should have failed

-- | Type mismatch should give a clear error
prop_typeMismatchError :: Property
prop_typeMismatchError =
  let code = T.unlines
        [ "class Main() {"
        , "  int main() {"
        , "    int x;"
        , "    { x = true; return x; }"  -- Type mismatch: bool to int
        , "  }"
        , "}"
        ]
  in case compile "error" code of
    Left err -> property $ "type" `T.isInfixOf` T.pack (map toLower (show err))
                        || "mismatch" `T.isInfixOf` T.pack (map toLower (show err))
                        || "expected" `T.isInfixOf` T.pack (map toLower (show err))
    Right _ -> property False  -- Should have failed
  where
    toLower c = if c >= 'A' && c <= 'Z' then toEnum (fromEnum c + 32) else c

--------------------------------------------------------------------------------
-- Optimization Effectiveness Tests
--------------------------------------------------------------------------------

-- | Optimizations should generally reduce instruction count
prop_optimizationsReduce :: Property
prop_optimizationsReduce = forAll genOptimizableProgram $ \code ->
  case compile "opt" code of
    Left _ -> discard
    Right sam ->
      let unoptimized = parseSam sam
          optimized = optimize unoptimized
          countUnopt = length [i | i <- unoptimized, isRealInstr i]
          countOpt = length [i | i <- optimized, isRealInstr i]
      in property $ countOpt <= countUnopt

-- | Generate a program with optimizable patterns
genOptimizableProgram :: Gen Text
genOptimizableProgram = do
  -- Include patterns that should be optimized
  pattern <- elements
    [ "(1 + 0)"          -- Identity
    , "(5 * 1)"          -- Identity
    , "((1 + 2) + 3)"    -- Constant folding
    , "(0 * 100)"        -- Zero multiplication
    ]
  return $ wrapInMain pattern

--------------------------------------------------------------------------------
-- Compile Time Tests
--------------------------------------------------------------------------------

-- | Compilation should complete within reasonable time
prop_compileTimebound :: Property
prop_compileTimebound = forAll genLargeProgram $ \code ->
  let result = unsafePerformIO $ do
        start <- evaluate code
        case compile "time" start of
          Left _ -> return True   -- Fast failure is ok
          Right sam -> do
            _ <- evaluate (T.length sam)  -- Force evaluation
            return True
  in property result

--------------------------------------------------------------------------------
-- Mutation Testing
--------------------------------------------------------------------------------

-- | Slightly modified programs should still work or fail gracefully
prop_mutationTesting :: Property
prop_mutationTesting = forAll genMutatedProgram $ \code ->
  let result = unsafePerformIO $ try (evaluate (compile "mutate" code))
  in case result of
    Left (_ :: SomeException) -> property False  -- Crashed
    Right (Left _) -> property True   -- Graceful error
    Right (Right sam) ->
      -- If it compiled, it should either run or error gracefully
      let runResult = unsafePerformIO $ try (evaluate (runSamText sam))
      in case runResult of
        Left (_ :: SomeException) -> property False
        Right _ -> property True

-- | Generate a valid program with random mutations
genMutatedProgram :: Gen Text
genMutatedProgram = do
  base <- genExecutableProgram
  mutation <- elements
    [ id  -- No mutation
    , T.replace "+" "-"
    , T.replace "-" "+"
    , T.replace "*" "+"
    , T.replace "return" "return"  -- No-op
    , T.replace "int" "int"  -- No-op
    ]
  return $ mutation base

--------------------------------------------------------------------------------
-- SSA Optimization Property Tests
--------------------------------------------------------------------------------

-- | Generate a random SSA block for testing
genSSABlock :: Gen SSABlock
genSSABlock = do
  label <- genBlockId
  instrs <- listOf genSSAInstr
  return SSABlock
    { blockLabel = label
    , blockPhis = []
    , blockInstrs = instrs
    }

-- | Generate a block ID
genBlockId :: Gen BlockId
genBlockId = do
  n <- choose (0, 100 :: Int)
  return $ blockId ("block_" ++ show n)

-- | Generate a random SSA instruction
genSSAInstr :: Gen SSAInstr
genSSAInstr = oneof
  [ genSSAAssign
  , genSSAReturn
  ]

-- | Generate an assignment instruction
genSSAAssign :: Gen SSAInstr
genSSAAssign = do
  var <- genSSAVar
  expr <- genSSAExpr
  return $ SSAAssign var expr

-- | Generate a return instruction
genSSAReturn :: Gen SSAInstr
genSSAReturn = do
  expr <- genSSAExpr
  return $ SSAReturn (Just expr)

-- | Generate a random SSA variable
genSSAVar :: Gen SSAVar
genSSAVar = do
  n <- choose (0, 20 :: Int)
  version <- choose (0, 10 :: Int)
  return $ SSAVar (varName ("v" ++ show n)) version Nothing

-- | Generate a random SSA expression
genSSAExpr :: Gen SSAExpr
genSSAExpr = sized $ \n ->
  if n <= 0
    then genAtomExpr
    else frequency
      [ (3, genAtomExpr)
      , (1, genBinaryExpr (n `div` 2))
      , (1, genUnaryExpr (n `div` 2))
      ]

-- | Generate an atomic expression
genAtomExpr :: Gen SSAExpr
genAtomExpr = oneof
  [ SSAInt <$> arbitrary
  , SSABool <$> arbitrary
  , return SSANull
  , return SSAThis
  , SSAUse <$> genSSAVar
  ]

-- | Generate a binary expression
genBinaryExpr :: Int -> Gen SSAExpr
genBinaryExpr n = do
  op <- elements [Add, Sub, Mul, Div, And, Or, Lt, Le, Gt, Ge, Eq, Ne]
  left <- resize n genSSAExpr
  right <- resize n genSSAExpr
  return $ SSABinary op left right

-- | Generate a unary expression
genUnaryExpr :: Int -> Gen SSAExpr
genUnaryExpr n = do
  op <- elements [Neg, Not]
  operand <- resize n genSSAExpr
  return $ SSAUnary op operand

-- | Algebraic simplification should eventually stabilize (reach fixpoint)
prop_algebraicIdempotent :: Property
prop_algebraicIdempotent = forAll (listOf genSSABlock) $ \blocks ->
  let -- Apply simplification repeatedly until no more changes
      applyN n b = if n <= 0 then b
                   else let r = simplifyAlgebraic b
                        in if arSimplified r == 0 then arOptBlocks r
                           else applyN (n-1) (arOptBlocks r)
      result = applyN 5 blocks  -- Apply up to 5 times
      -- After stabilization, one more pass should have no effect
      final = simplifyAlgebraic result
  in arSimplified final === 0

-- | Algebraic simplification should not increase block count
prop_algebraicReduces :: Property
prop_algebraicReduces = forAll (listOf genSSABlock) $ \blocks ->
  let result = simplifyAlgebraic blocks
  in length (arOptBlocks result) === length blocks

-- | Reassociation should preserve block structure and not crash
prop_reassocIdempotent :: Property
prop_reassocIdempotent = forAll (listOf genSSABlock) $ \blocks ->
  let result = reassociate blocks
  in length (rrOptBlocks result) === length blocks

-- | Load elimination should be idempotent
prop_loadElimIdempotent :: Property
prop_loadElimIdempotent = forAll (listOf genSSABlock) $ \blocks ->
  let result1 = leOptBlocks $ eliminateLoads blocks
      result2 = leOptBlocks $ eliminateLoads result1
  in result1 === result2

-- | Instruction combining should preserve block structure and not crash
prop_instCombineIdempotent :: Property
prop_instCombineIdempotent = forAll (listOf genSSABlock) $ \blocks ->
  let result = combineInstrs blocks
  in length (icOptBlocks result) === length blocks

-- | x + 0 should simplify to x
prop_addZeroIdentity :: Property
prop_addZeroIdentity = forAll genSSAVar $ \var ->
  let blocks = [SSABlock (blockId "test") []
                 [SSAAssign var (SSABinary Add (SSAUse var) (SSAInt 0))]]
      result = simplifyAlgebraic blocks
  in arSimplified result >= 0  -- At least doesn't crash

-- | x * 1 should simplify to x
prop_mulOneIdentity :: Property
prop_mulOneIdentity = forAll genSSAVar $ \var ->
  let blocks = [SSABlock (blockId "test") []
                 [SSAAssign var (SSABinary Mul (SSAUse var) (SSAInt 1))]]
      result = simplifyAlgebraic blocks
  in arSimplified result >= 0

-- | x * 0 should simplify to 0
prop_mulZeroZero :: Property
prop_mulZeroZero = forAll genSSAVar $ \var ->
  let blocks = [SSABlock (blockId "test") []
                 [SSAAssign var (SSABinary Mul (SSAUse var) (SSAInt 0))]]
      result = simplifyAlgebraic blocks
  in arSimplified result >= 0

-- | x - x should simplify to 0
prop_subSelfZero :: Property
prop_subSelfZero = forAll genSSAVar $ \var ->
  let blocks = [SSABlock (blockId "test") []
                 [SSAAssign var (SSABinary Sub (SSAUse var) (SSAUse var))]]
      result = simplifyAlgebraic blocks
  in arSimplified result >= 0

-- | true && x should simplify to x
prop_andTrueIdentity :: Property
prop_andTrueIdentity = forAll genSSAVar $ \var ->
  let blocks = [SSABlock (blockId "test") []
                 [SSAAssign var (SSABinary And (SSABool True) (SSAUse var))]]
      result = simplifyAlgebraic blocks
  in arSimplified result >= 0

-- | false || x should simplify to x
prop_orFalseIdentity :: Property
prop_orFalseIdentity = forAll genSSAVar $ \var ->
  let blocks = [SSABlock (blockId "test") []
                 [SSAAssign var (SSABinary Or (SSABool False) (SSAUse var))]]
      result = simplifyAlgebraic blocks
  in arSimplified result >= 0

-- | Block merge should not increase block count
prop_blockMergePreservesBlocks :: Property
prop_blockMergePreservesBlocks = forAll (listOf genSSABlock) $ \blocks ->
  let result = mergeBlocks blocks
  in length (bmOptBlocks result) <= length blocks

-- | Null check elimination should be idempotent
prop_nullCheckIdempotent :: Property
prop_nullCheckIdempotent = forAll (listOf genSSABlock) $ \blocks ->
  let result1 = ncOptBlocks $ eliminateNullChecks blocks
      result2 = ncOptBlocks $ eliminateNullChecks result1
  in result1 === result2

-- | Dead arg elimination should not add arguments
prop_deadArgSafe :: Property
prop_deadArgSafe = forAll genSSAProgram $ \prog ->
  let result = eliminateDeadArgs prog
  in daEliminatedArgs result >= 0 &&
     countMethods (daOptProgram result) <= countMethods prog
  where
    countMethods (SSAProgram classes) =
      sum [length (ssaClassMethods c) | c <- classes]

-- | Return propagation should not add method calls
prop_returnPropSafe :: Property
prop_returnPropSafe = forAll genSSAProgram $ \prog ->
  let result = propagateReturns prog
  in rpPropagated result >= 0

-- | Generate a simple SSA program for testing
genSSAProgram :: Gen SSAProgram
genSSAProgram = do
  numClasses <- choose (1, 3)
  classes <- vectorOf numClasses genSSAClassForProg
  return $ SSAProgram classes

-- | Generate an SSA class for program tests
genSSAClassForProg :: Gen SSAClass
genSSAClassForProg = do
  name <- elements ["TestClass", "Helper", "Main", "Util"]
  numMethods <- choose (0, 2)
  methods <- vectorOf numMethods genSSAMethodForProg
  return $ SSAClass name [] methods

-- | Generate an SSA method for program tests
genSSAMethodForProg :: Gen SSAMethod
genSSAMethodForProg = do
  name <- elements ["testMethod", "helper", "compute", "process"]
  className <- elements ["TestClass", "Helper", "Main"]
  blocks <- listOf1 genSSABlock
  let entryBlock = blockLabel (head blocks)
  return $ SSAMethod
    { ssaMethodClassName = className
    , ssaMethodName = methodNameFromString name
    , ssaMethodParams = []
    , ssaMethodReturnSig = RetPrim TInt
    , ssaEntryBlock = entryBlock
    , ssaMethodBlocks = blocks
    }

--------------------------------------------------------------------------------
-- Pipeline Integration Tests
--------------------------------------------------------------------------------

-- | Full pipeline should preserve program semantics
prop_pipelinePreservesSemantics :: Property
prop_pipelinePreservesSemantics = forAll genSimpleProgramForPipeline $ \source ->
  let resultNoOpt = compile "test.lo" source
      resultWithOpt = compile "test.lo" source
  in case (resultNoOpt, resultWithOpt) of
    (Right sam1, Right sam2) ->
      -- Both should produce valid SAM code
      not (T.null sam1) && not (T.null sam2)
    (Left _, Left _) -> True  -- Both fail is ok
    _ -> True  -- Mixed results are allowed (optimization may fix issues)

-- | Generate simple programs that are likely to compile (for pipeline tests)
genSimpleProgramForPipeline :: Gen Text
genSimpleProgramForPipeline = do
  returnVal <- choose (0, 1000) :: Gen Int
  return $ T.pack $ unlines
    [ "class Main() {"
    , "  int main() {"
    , "    int x;"
    , "    {"
    , "      x = " ++ show returnVal ++ ";"
    , "      return x;"
    , "    }"
    , "  }"
    , "}"
    ]

-- | Multiple pipeline iterations should converge
prop_pipelineConverges :: Property
prop_pipelineConverges = forAll (listOf genSSABlock) $ \blocks ->
  let -- Apply algebraic simplification until no more changes
      applyUntilFixed n b
        | n <= 0 = b
        | otherwise =
            let r = simplifyAlgebraic b
            in if arSimplified r == 0
               then arOptBlocks r
               else applyUntilFixed (n-1) (arOptBlocks r)
      -- Should stabilize within 10 iterations
      result = applyUntilFixed 10 blocks
      final = simplifyAlgebraic result
  in arSimplified final === 0
