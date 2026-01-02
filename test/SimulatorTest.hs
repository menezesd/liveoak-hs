{-# LANGUAGE OverloadedStrings #-}

-- | Simulator tests: verify programs execute correctly and produce expected results.
module SimulatorTest (simulatorTests) where

import Test.Tasty
import Test.Tasty.HUnit
import System.Directory (listDirectory, doesFileExist)
import System.FilePath ((</>), takeExtension, takeBaseName, replaceExtension)
import Data.List (sort)
import Control.Monad (forM)
import qualified Data.Text as T
import qualified Data.Text.IO as TIO

import LiveOak.Compiler (compileFile)
import LiveOak.Sam (runSamText, SamValue(..), SamError(..))

-- | All simulator tests.
simulatorTests :: TestTree
simulatorTests = testGroup "Simulator"
  [ executionTests
  ]

-- | Test directory path.
validProgramsDir :: FilePath
validProgramsDir = "test/resources/ValidPrograms"

-- | Tests for program execution.
executionTests :: TestTree
executionTests = testGroup "Execution" $
  [ testCase "All programs with .expected files execute correctly" $ do
      files <- getLoFilesWithExpected validProgramsDir
      results <- forM files $ \file -> do
        result <- runSimulatorTest file
        return (file, result)
      let failures = [(f, err) | (f, Left err) <- results]
      if null failures
        then return ()
        else assertFailure $ unlines $
          "The following programs failed execution:" :
          [takeBaseName f ++ ": " ++ err | (f, err) <- failures]
  ]

-- | Get all .lo files that have corresponding .expected files.
getLoFilesWithExpected :: FilePath -> IO [FilePath]
getLoFilesWithExpected dir = do
  entries <- listDirectory dir
  let loFiles = filter ((== ".lo") . takeExtension) entries
  -- Filter to only those with .expected files
  withExpected <- forM loFiles $ \loFile -> do
    let expectedFile = dir </> replaceExtension loFile ".expected"
    exists <- doesFileExist expectedFile
    return (if exists then Just (dir </> loFile) else Nothing)
  return $ sort [f | Just f <- withExpected]

-- | Run a simulator test: compile, execute, check result.
runSimulatorTest :: FilePath -> IO (Either String ())
runSimulatorTest loFile = do
  -- Compile the program
  compileResult <- compileFile loFile
  case compileResult of
    Left diag -> return $ Left $ "Compilation failed: " ++ show diag
    Right samCode -> do
      -- Load expected result
      let expectedFile = replaceExtension loFile ".expected"
      expectedText <- TIO.readFile expectedFile
      let expectedInt = read (T.unpack $ T.strip expectedText) :: Int
      -- Run the simulator
      case runSamText samCode of
        Left err -> return $ Left $ "Execution failed: " ++ showSamError err
        Right (SamInt result) ->
          if result == expectedInt
            then return $ Right ()
            else return $ Left $ "Expected " ++ show expectedInt ++ " but got " ++ show result

-- | Show a SAM error as a string.
showSamError :: SamError -> String
showSamError (ParseError msg) = "Parse error: " ++ msg
showSamError (StackUnderflow msg) = "Stack underflow: " ++ msg
showSamError DivisionByZero = "Division by zero"
showSamError (InvalidMemoryAccess addr) = "Invalid memory access at " ++ show addr
showSamError (UnknownLabel lbl) = "Unknown label: " ++ lbl
showSamError (PCOutOfBounds pc) = "PC out of bounds: " ++ show pc
showSamError (RuntimeError msg) = "Runtime error: " ++ msg
