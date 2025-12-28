-- | Main test entry point.
module Main (main) where

import Test.Tasty
import CompilerTest (compilerTests)

main :: IO ()
main = defaultMain tests

tests :: TestTree
tests = testGroup "LiveOak Compiler Tests"
  [ compilerTests
  ]
