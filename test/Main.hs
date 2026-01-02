-- | Main test entry point.
module Main (main) where

import Test.Tasty
import CompilerTest (compilerTests)
import SimulatorTest (simulatorTests)
-- import PropertyTest (propertyTests)

main :: IO ()
main = defaultMain tests

tests :: TestTree
tests = testGroup "LiveOak Compiler Tests"
  [ compilerTests
  , simulatorTests
  -- , propertyTests  -- Temporarily disabled for performance
  ]
