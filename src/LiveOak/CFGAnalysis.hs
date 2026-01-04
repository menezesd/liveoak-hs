-- | CFG Analysis module for LiveOak.
-- Bundles CFG construction, dominance analysis, and loop detection
-- with a unified interface for SSA optimizations.
module LiveOak.CFGAnalysis
  ( -- * Analysis Result
    CFGAnalysis(..)
  , analyzeCFG

    -- * Re-exports from CFG
  , CFG(..)
  , CFGBlock(..)
  , Terminator(..)
  , BlockId
  , buildCFG
  , cfgFromBlocks
  , predecessors
  , successors
  , allBlockIds
  , getBlock
  , entryBlock
  , exitBlocks
  , reversePostorder
  , postorder
  , dfs
  , isCriticalEdge
  , findCriticalEdges
  , splitCriticalEdges

    -- * Re-exports from Dominance
  , DomTree
  , DomFrontier
  , computeDominators
  , computeDomFrontier
  , dominates
  , strictlyDominates
  , immediateDom
  , domChildren

    -- * Re-exports from Loop
  , Loop(..)
  , LoopNest
  , findLoops
  , findBackEdges
  , computeLoopBody
  , isLoopHeader
  , loopDepth
  , innerMostLoop
  , loopBlocks
  , loopExits
  , isLoopInvariant
  ) where

import LiveOak.CFG
import LiveOak.Dominance
import LiveOak.Loop
import LiveOak.SSATypes (SSAMethod(..))

--------------------------------------------------------------------------------
-- CFG Analysis
--------------------------------------------------------------------------------

-- | Complete CFG analysis results
data CFGAnalysis = CFGAnalysis
  { cfgaCFG :: !CFG               -- ^ Control flow graph
  , cfgaDomTree :: !DomTree       -- ^ Dominator tree
  , cfgaDomFrontier :: !DomFrontier -- ^ Dominance frontier
  , cfgaLoops :: !LoopNest        -- ^ Loop nest structure
  } deriving (Show)

-- | Perform complete CFG analysis on a method
analyzeCFG :: SSAMethod -> CFGAnalysis
analyzeCFG method =
  let cfg = buildCFG method
      domTree = computeDominators cfg
      domFrontier = computeDomFrontier cfg domTree
      loops = findLoops cfg domTree
  in CFGAnalysis
    { cfgaCFG = cfg
    , cfgaDomTree = domTree
    , cfgaDomFrontier = domFrontier
    , cfgaLoops = loops
    }
