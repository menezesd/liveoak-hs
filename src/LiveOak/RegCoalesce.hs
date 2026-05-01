{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RecordWildCards #-}

-- | Register Coalescing.
-- Eliminates redundant register-to-register moves by assigning
-- the source and destination of a move to the same physical register.
--
-- == Algorithm
-- Uses Chaitin-Briggs style aggressive coalescing:
-- 1. Build interference graph
-- 2. Find copy instructions (mov %r1, %r2)
-- 3. If source and destination don't interfere, merge them
-- 4. Repeat until no more coalescing possible
--
module LiveOak.RegCoalesce
  ( -- * Coalescing
    coalesceRegisters
  , CoalesceResult(..)

    -- * Interference Graph
  , InterferenceGraph(..)
  , buildInterferenceGraph

    -- * Analysis
  , CopyInstr(..)
  , findCopies
  ) where

import LiveOak.X86
import LiveOak.Liveness (LivenessInfo, LiveInterval(..), liVar)

import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Set (Set)
import qualified Data.Set as Set
import Data.List (foldl')
import Data.Maybe (mapMaybe)

--------------------------------------------------------------------------------
-- Types
--------------------------------------------------------------------------------

-- | Coalescing result
data CoalesceResult = CoalesceResult
  { crCoalesced :: !Int              -- ^ Number of copies eliminated
  , crMergedVars :: ![(String, String)]  -- ^ Pairs of merged variables
  } deriving (Show)

-- | Copy instruction
data CopyInstr = CopyInstr
  { ciDest :: !String               -- ^ Destination variable
  , ciSrc :: !String                -- ^ Source variable
  , ciIndex :: !Int                 -- ^ Instruction index
  } deriving (Show)

-- | Interference graph node
data IGNode = IGNode
  { ignVar :: !String               -- ^ Variable name
  , ignInterferences :: !(Set String)  -- ^ Variables this interferes with
  , ignCopies :: !(Set String)      -- ^ Variables this is copy-related to
  , ignDegree :: !Int               -- ^ Number of interferences
  } deriving (Show)

-- | Interference graph
data InterferenceGraph = InterferenceGraph
  { igNodes :: !(Map String IGNode)
  , igEdges :: !(Set (String, String))  -- ^ Interference edges
  , igCopyEdges :: !(Set (String, String))  -- ^ Copy edges
  } deriving (Show)

--------------------------------------------------------------------------------
-- Interference Graph Construction
--------------------------------------------------------------------------------

-- | Build interference graph from live intervals
buildInterferenceGraph :: [LiveInterval] -> InterferenceGraph
buildInterferenceGraph intervals =
  let -- Find all variables
      vars = map liVar intervals

      -- Initialize nodes
      initialNodes = Map.fromList [(v, IGNode v Set.empty Set.empty 0) | v <- vars]

      -- Add interference edges
      edges = findInterferences intervals
      nodesWithInt = foldl' addInterference initialNodes edges

      -- Compute degrees
      finalNodes = Map.map updateDegree nodesWithInt

  in InterferenceGraph
    { igNodes = finalNodes
    , igEdges = Set.fromList edges
    , igCopyEdges = Set.empty
    }
  where
    updateDegree node = node { ignDegree = Set.size (ignInterferences node) }

-- | Find interference edges between intervals
findInterferences :: [LiveInterval] -> [(String, String)]
findInterferences intervals =
  [(liVar i1, liVar i2)
  | i1 <- intervals
  , i2 <- intervals
  , liVar i1 < liVar i2  -- Avoid duplicates
  , intervalsInterfere i1 i2]

-- | Check if two intervals interfere
intervalsInterfere :: LiveInterval -> LiveInterval -> Bool
intervalsInterfere i1 i2 =
  not (liEnd i1 < liStart i2 || liEnd i2 < liStart i1)

-- | Add an interference edge to the graph
addInterference :: Map String IGNode -> (String, String) -> Map String IGNode
addInterference nodes (v1, v2) =
  let nodes' = Map.adjust (addIntTo v2) v1 nodes
  in Map.adjust (addIntTo v1) v2 nodes'
  where
    addIntTo other node = node { ignInterferences = Set.insert other (ignInterferences node) }

--------------------------------------------------------------------------------
-- Copy Detection
--------------------------------------------------------------------------------

-- | Find copy instructions from SSA phi copies and explicit moves
-- This operates on the phi copy information that was computed during codegen
findCopies :: [(String, String)] -> [CopyInstr]
findCopies phiCopies = zipWith mkCopy [0..] phiCopies
  where
    mkCopy idx (dst, src) = CopyInstr dst src idx

--------------------------------------------------------------------------------
-- Register Coalescing
--------------------------------------------------------------------------------

-- | Coalesce registers by merging copy-related variables
coalesceRegisters :: InterferenceGraph -> [CopyInstr] -> CoalesceResult
coalesceRegisters graph copies =
  let (_, coalesced, merged) = foldl' tryCoalesce (graph, 0, []) copies
  in CoalesceResult
    { crCoalesced = coalesced
    , crMergedVars = merged
    }

-- | Try to coalesce a copy
tryCoalesce :: (InterferenceGraph, Int, [(String, String)]) -> CopyInstr
            -> (InterferenceGraph, Int, [(String, String)])
tryCoalesce (graph, count, merged) CopyInstr{..}
  | canCoalesce graph ciDest ciSrc =
      let graph' = mergeNodes graph ciDest ciSrc
      in (graph', count + 1, (ciDest, ciSrc) : merged)
  | otherwise = (graph, count, merged)

-- | Check if two variables can be coalesced
canCoalesce :: InterferenceGraph -> String -> String -> Bool
canCoalesce graph v1 v2 =
  case (Map.lookup v1 (igNodes graph), Map.lookup v2 (igNodes graph)) of
    (Just n1, Just n2) ->
      -- Can coalesce if they don't interfere
      not (Set.member v2 (ignInterferences n1))
      -- And the merged node won't have too high degree
      && briggsSafe n1 n2 (numRegs - 1)
    _ -> False
  where
    numRegs = 5  -- Number of available registers

-- | Briggs test: safe to coalesce if < K neighbors of high degree
briggsSafe :: IGNode -> IGNode -> Int -> Bool
briggsSafe n1 n2 k =
  let combined = Set.union (ignInterferences n1) (ignInterferences n2)
      -- This is simplified - full Briggs would check neighbor degrees
  in Set.size combined < k * 2

-- | Merge two nodes in the interference graph
mergeNodes :: InterferenceGraph -> String -> String -> InterferenceGraph
mergeNodes graph keep remove =
  case (Map.lookup keep (igNodes graph), Map.lookup remove (igNodes graph)) of
    (Just keepNode, Just removeNode) ->
      let -- Merge interferences
          newInt = Set.union (ignInterferences keepNode)
                             (Set.delete keep (ignInterferences removeNode))
          -- Update the kept node
          keepNode' = keepNode
            { ignInterferences = newInt
            , ignDegree = Set.size newInt
            }
          -- Update graph
          nodes' = Map.insert keep keepNode' $ Map.delete remove (igNodes graph)
          -- Update edges: redirect edges from 'remove' to 'keep'
          edges' = Set.map (redirectEdge keep remove) (igEdges graph)
          -- Update other nodes' interference sets
          nodes'' = Map.map (updateInterferences keep remove) nodes'
      in graph { igNodes = nodes'', igEdges = edges' }
    _ -> graph
  where
    redirectEdge k r (a, b)
      | a == r = (k, b)
      | b == r = (a, k)
      | otherwise = (a, b)

    updateInterferences k r node =
      if Set.member r (ignInterferences node)
      then node { ignInterferences = Set.insert k (Set.delete r (ignInterferences node)) }
      else node

--------------------------------------------------------------------------------
-- Applying Coalescing to Register Allocation
--------------------------------------------------------------------------------

-- | Build a substitution map from coalescing results
buildSubstitution :: [(String, String)] -> Map String String
buildSubstitution merged = Map.fromList [(remove, keep) | (keep, remove) <- merged]

-- | Apply substitution to live intervals (rename variables)
applySubstitution :: Map String String -> [LiveInterval] -> [LiveInterval]
applySubstitution subst = map substInterval
  where
    substInterval li = li { liVar = Map.findWithDefault (liVar li) (liVar li) subst }
