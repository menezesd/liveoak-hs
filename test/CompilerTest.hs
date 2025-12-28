{-# LANGUAGE OverloadedStrings #-}

-- | Compiler tests: verify valid programs compile and invalid programs fail.
module CompilerTest (compilerTests) where

import Test.Tasty
import Test.Tasty.HUnit
import System.Directory (listDirectory, doesFileExist)
import System.FilePath ((</>), takeExtension, takeBaseName)
import Data.List (sort)
import Control.Monad (forM)
import LiveOak.Compiler

-- | All compiler tests.
compilerTests :: TestTree
compilerTests = testGroup "Compiler"
  [ validProgramTests
  , invalidProgramTests
  ]

-- | Test directory paths.
validProgramsDir :: FilePath
validProgramsDir = "test/resources/ValidPrograms"

invalidProgramsDir :: FilePath
invalidProgramsDir = "test/resources/InvalidPrograms"

-- | Tests for valid programs (should compile successfully).
validProgramTests :: TestTree
validProgramTests = testGroup "Valid Programs" $
  [ testCase "All valid programs compile" $ do
      files <- getLoFiles validProgramsDir
      results <- forM files $ \file -> do
        result <- compileFile file
        return (file, result)
      let failures = [(f, d) | (f, Left d) <- results]
      if null failures
        then return ()
        else assertFailure $ unlines $
          "The following valid programs failed to compile:" :
          [takeBaseName f ++ ": " ++ formatDiag d | (f, d) <- failures]
  ]

-- | Tests for invalid programs (should fail to compile).
invalidProgramTests :: TestTree
invalidProgramTests = testGroup "Invalid Programs" $
  [ testCase "All invalid programs produce errors" $ do
      files <- getLoFiles invalidProgramsDir
      results <- forM files $ \file -> do
        result <- compileFile file
        return (file, result)
      let successes = [f | (f, Right _) <- results]
      if null successes
        then return ()
        else assertFailure $ unlines $
          "The following invalid programs compiled successfully (should have failed):" :
          map takeBaseName successes
  ]

-- | Get all .lo files in a directory.
getLoFiles :: FilePath -> IO [FilePath]
getLoFiles dir = do
  exists <- doesFileExist dir  -- check if it's not a directory
  if exists
    then return []  -- it's a file, not a directory
    else do
      entries <- listDirectory dir
      let loFiles = filter ((== ".lo") . takeExtension) entries
      return $ sort $ map (dir </>) loFiles
