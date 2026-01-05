{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RecordWildCards #-}

-- | Optimization Pass Interface.
-- Provides a unified interface for all optimization passes.
--
-- == Design
--
-- Each optimization pass can operate at different levels:
-- - Method level: Transforms a single method
-- - Program level: Transforms the entire program (for interprocedural opts)
-- - Block level: Transforms individual blocks
--
-- Passes report statistics about their transformations.
--
module LiveOak.OptPass
  ( -- * Pass Interface
    OptPass(..)
  , PassResult(..)
  , PassStats(..)
  , emptyStats
  , addStat

    -- * Running Passes
  , runMethodPass
  , runProgramPass
  , runPassSequence
  , runPassUntilFixpoint

    -- * Pass Combinators
  , composePass
  , conditionalPass
  , iteratePass
  ) where

import LiveOak.SSATypes

import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map

--------------------------------------------------------------------------------
-- Types
--------------------------------------------------------------------------------

-- | Statistics collected during optimization
newtype PassStats = PassStats (Map String Int)
  deriving (Show)

-- | Empty statistics
emptyStats :: PassStats
emptyStats = PassStats Map.empty

-- | Add a statistic
addStat :: String -> Int -> PassStats -> PassStats
addStat key val (PassStats m) = PassStats $ Map.insertWith (+) key val m

-- | Merge two statistics
mergeStats :: PassStats -> PassStats -> PassStats
mergeStats (PassStats m1) (PassStats m2) = PassStats $ Map.unionWith (+) m1 m2

-- | Result of running a pass
data PassResult a = PassResult
  { prResult :: !a           -- ^ The transformed result
  , prChanged :: !Bool       -- ^ Whether any changes were made
  , prStats :: !PassStats    -- ^ Statistics about the transformation
  } deriving (Show)

-- | An optimization pass
data OptPass
  = MethodPass
    { passName :: !String
    , passMethod :: SSAMethod -> PassResult SSAMethod
    }
  | ProgramPass
    { passName :: !String
    , passProgram :: SSAProgram -> PassResult SSAProgram
    }

--------------------------------------------------------------------------------
-- Running Passes
--------------------------------------------------------------------------------

-- | Run a method-level pass on a method
runMethodPass :: OptPass -> SSAMethod -> PassResult SSAMethod
runMethodPass MethodPass{..} method = passMethod method
runMethodPass ProgramPass{..} method =
  -- Wrap single method in a dummy program, run, extract
  let prog = SSAProgram [SSAClass "Dummy" [] [method]]
      result = passProgram prog
      SSAProgram [SSAClass _ _ [method']] = prResult result
  in result { prResult = method' }

-- | Run a program-level pass
runProgramPass :: OptPass -> SSAProgram -> PassResult SSAProgram
runProgramPass ProgramPass{..} prog = passProgram prog
runProgramPass MethodPass{..} (SSAProgram classes) =
  -- Apply method pass to each method in the program
  let (classes', changed, stats) = unzip3 $ map runClass classes
  in PassResult
    { prResult = SSAProgram classes'
    , prChanged = or changed
    , prStats = foldr mergeStats emptyStats stats
    }
  where
    runClass cls@SSAClass{..} =
      let (methods', changed, stats) = unzip3 $ map runMethod ssaClassMethods
      in (cls { ssaClassMethods = methods' }, or changed, foldr mergeStats emptyStats stats)

    runMethod method =
      let result = passMethod method
      in (prResult result, prChanged result, prStats result)

-- | Run a sequence of passes
runPassSequence :: [OptPass] -> SSAProgram -> PassResult SSAProgram
runPassSequence passes prog = foldr applyPass initResult passes
  where
    initResult = PassResult prog False emptyStats
    applyPass pass prevResult =
      let result = runProgramPass pass (prResult prevResult)
      in PassResult
        { prResult = prResult result
        , prChanged = prChanged prevResult || prChanged result
        , prStats = mergeStats (prStats prevResult) (prStats result)
        }

-- | Run a pass until no more changes occur (fixed point)
runPassUntilFixpoint :: Int -> OptPass -> SSAProgram -> PassResult SSAProgram
runPassUntilFixpoint maxIter pass = go maxIter emptyStats
  where
    go 0 stats prog = PassResult prog False stats
    go n stats prog =
      let result = runProgramPass pass prog
      in if prChanged result
         then go (n - 1) (mergeStats stats (prStats result)) (prResult result)
         else PassResult prog False (mergeStats stats (prStats result))

--------------------------------------------------------------------------------
-- Pass Combinators
--------------------------------------------------------------------------------

-- | Compose two passes into one
composePass :: String -> OptPass -> OptPass -> OptPass
composePass name p1 p2 = ProgramPass name $ \prog ->
  let r1 = runProgramPass p1 prog
      r2 = runProgramPass p2 (prResult r1)
  in PassResult
    { prResult = prResult r2
    , prChanged = prChanged r1 || prChanged r2
    , prStats = mergeStats (prStats r1) (prStats r2)
    }

-- | Run a pass only if a condition is met
conditionalPass :: (SSAProgram -> Bool) -> OptPass -> OptPass
conditionalPass cond pass = ProgramPass (passName pass) $ \prog ->
  if cond prog
  then runProgramPass pass prog
  else PassResult prog False emptyStats

-- | Iterate a pass a fixed number of times
iteratePass :: Int -> OptPass -> OptPass
iteratePass n pass = ProgramPass (passName pass ++ " x" ++ show n) $ \prog ->
  go n emptyStats prog
  where
    go 0 stats p = PassResult p False stats
    go i stats p =
      let result = runProgramPass pass p
      in go (i - 1) (mergeStats stats (prStats result)) (prResult result)
