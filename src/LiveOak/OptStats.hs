{-# LANGUAGE RecordWildCards #-}

-- | Optimization Statistics.
-- Tracks the number of transformations applied by each optimization pass.
--
-- == Usage
--
-- @
-- let (optimized, stats) = runWithStats myPass input
-- putStrLn $ showStats stats
-- @
--
module LiveOak.OptStats
  ( -- * Statistics Types
    OptStats(..)
  , PassStats(..)
  , emptyStats
  , emptyPassStats

    -- * Statistics Operations
  , addPassStats
  , combineStats
  , totalTransformations

    -- * Display
  , showStats
  , showPassStats
  ) where

import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map

--------------------------------------------------------------------------------
-- Types
--------------------------------------------------------------------------------

-- | Statistics for a single optimization pass
data PassStats = PassStats
  { psTransformations :: !Int    -- ^ Number of transformations applied
  , psIterations :: !Int         -- ^ Number of iterations (for fixed-point passes)
  } deriving (Eq, Show)

-- | Aggregate statistics for all optimization passes
data OptStats = OptStats
  { osPassStats :: !(Map String PassStats)  -- ^ Per-pass statistics
  , osTotalPasses :: !Int                   -- ^ Total number of passes run
  } deriving (Eq, Show)

--------------------------------------------------------------------------------
-- Construction
--------------------------------------------------------------------------------

-- | Empty statistics
emptyStats :: OptStats
emptyStats = OptStats
  { osPassStats = Map.empty
  , osTotalPasses = 0
  }

-- | Empty pass statistics
emptyPassStats :: PassStats
emptyPassStats = PassStats
  { psTransformations = 0
  , psIterations = 0
  }

--------------------------------------------------------------------------------
-- Operations
--------------------------------------------------------------------------------

-- | Add statistics for a pass
addPassStats :: String -> PassStats -> OptStats -> OptStats
addPassStats passName stats os@OptStats{..} =
  os { osPassStats = Map.insertWith combinePassStats passName stats osPassStats
     , osTotalPasses = osTotalPasses + 1
     }

-- | Combine two pass statistics
combinePassStats :: PassStats -> PassStats -> PassStats
combinePassStats a b = PassStats
  { psTransformations = psTransformations a + psTransformations b
  , psIterations = psIterations a + psIterations b
  }

-- | Combine two statistics records
combineStats :: OptStats -> OptStats -> OptStats
combineStats a b = OptStats
  { osPassStats = Map.unionWith combinePassStats (osPassStats a) (osPassStats b)
  , osTotalPasses = osTotalPasses a + osTotalPasses b
  }

-- | Total number of transformations across all passes
totalTransformations :: OptStats -> Int
totalTransformations OptStats{..} =
  sum [psTransformations ps | ps <- Map.elems osPassStats]

--------------------------------------------------------------------------------
-- Display
--------------------------------------------------------------------------------

-- | Show statistics in human-readable format
showStats :: OptStats -> String
showStats OptStats{..} =
  unlines $
    [ "Optimization Statistics:"
    , "========================"
    , ""
    ] ++
    [ showPassStats name stats | (name, stats) <- Map.toList osPassStats ] ++
    [ ""
    , "Total passes: " ++ show osTotalPasses
    , "Total transformations: " ++ show (sum [psTransformations ps | ps <- Map.elems osPassStats])
    ]

-- | Show statistics for a single pass
showPassStats :: String -> PassStats -> String
showPassStats name PassStats{..} =
  name ++ ": " ++ show psTransformations ++ " transformations" ++
  (if psIterations > 1 then " (" ++ show psIterations ++ " iterations)" else "")
