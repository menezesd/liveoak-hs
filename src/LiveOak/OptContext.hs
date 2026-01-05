{-# LANGUAGE RecordWildCards #-}

-- | Optimization Context.
-- Provides cached analysis results to avoid redundant computation across passes.
--
-- == Usage
--
-- @
-- let ctx = buildOptContext method
--     cfg = octCFG ctx
--     domTree = octDomTree ctx
-- @
--
-- The context can be invalidated when blocks are modified, requiring
-- recomputation.
--
module LiveOak.OptContext
  ( -- * Optimization Context
    OptContext(..)
  , buildOptContext
  , invalidateContext
  , updateBlocks

    -- * Queries
  , getCFG
  , getDomTree
  , getLoopNest
  ) where

import LiveOak.SSATypes
import LiveOak.CFG
import LiveOak.Dominance
import LiveOak.Loop

import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map

--------------------------------------------------------------------------------
-- Types
--------------------------------------------------------------------------------

-- | Optimization context with cached analysis results
data OptContext = OptContext
  { octMethod :: !SSAMethod       -- ^ The method being optimized
  , octCFG :: !CFG                -- ^ Cached CFG
  , octDomTree :: !DomTree        -- ^ Cached dominator tree
  , octLoopNest :: !LoopNest      -- ^ Cached loop nest
  , octBlockMap :: !(Map BlockId SSABlock)  -- ^ Block lookup map
  } deriving (Show)

--------------------------------------------------------------------------------
-- Construction
--------------------------------------------------------------------------------

-- | Build optimization context for a method
buildOptContext :: SSAMethod -> OptContext
buildOptContext method@SSAMethod{..} =
  let cfg = buildCFG method
      domTree = computeDominators cfg
      loops = findLoops cfg domTree
      blockMap = Map.fromList [(blockLabel b, b) | b <- ssaMethodBlocks]
  in OptContext
    { octMethod = method
    , octCFG = cfg
    , octDomTree = domTree
    , octLoopNest = loops
    , octBlockMap = blockMap
    }

-- | Invalidate context (force recomputation)
-- Use this when blocks have been modified
invalidateContext :: OptContext -> OptContext
invalidateContext ctx = buildOptContext (octMethod ctx)

-- | Update blocks and recompute context
updateBlocks :: [SSABlock] -> OptContext -> OptContext
updateBlocks newBlocks ctx =
  let method = (octMethod ctx) { ssaMethodBlocks = newBlocks }
  in buildOptContext method

--------------------------------------------------------------------------------
-- Queries
--------------------------------------------------------------------------------

-- | Get cached CFG
getCFG :: OptContext -> CFG
getCFG = octCFG

-- | Get cached dominator tree
getDomTree :: OptContext -> DomTree
getDomTree = octDomTree

-- | Get cached loop nest
getLoopNest :: OptContext -> LoopNest
getLoopNest = octLoopNest
