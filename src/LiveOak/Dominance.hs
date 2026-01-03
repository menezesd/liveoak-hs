{-# LANGUAGE RecordWildCards #-}

-- | Dominance analysis for Control Flow Graphs.
-- Implements the Cooper-Harvey-Kennedy algorithm for computing dominators
-- and dominance frontiers, which are needed for proper phi node placement.
module LiveOak.Dominance
  ( -- * Types
    DomTree(..)
  , DomFrontier

    -- * Dominance Computation
  , computeDominators
  , computeDomFrontier

    -- * Queries
  , immediateDom
  , dominates
  , strictlyDominates
  , domChildren
  , domDepth

    -- * Utilities
  , postDomTree
  ) where

import LiveOak.CFG
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Maybe (fromMaybe)
import Data.List (foldl')

--------------------------------------------------------------------------------
-- Types
--------------------------------------------------------------------------------

-- | Dominator tree
-- A node D dominates node N if every path from entry to N must go through D.
-- The immediate dominator of N is the closest dominator (other than N itself).
data DomTree = DomTree
  { domIdom :: !(Map BlockId BlockId)      -- ^ Immediate dominator of each block
  , domChildren_ :: !(Map BlockId [BlockId]) -- ^ Children in dominator tree
  , domRPO :: ![BlockId]                   -- ^ Reverse postorder (for iteration)
  , domRPOIndex :: !(Map BlockId Int)      -- ^ RPO index for each block
  } deriving (Eq, Show)

-- | Dominance frontier
-- The dominance frontier of a block B is the set of blocks where B's
-- dominance ends - i.e., blocks that have a predecessor dominated by B
-- but are not themselves strictly dominated by B.
type DomFrontier = Map BlockId (Set BlockId)

--------------------------------------------------------------------------------
-- Dominance Computation (Cooper-Harvey-Kennedy Algorithm)
--------------------------------------------------------------------------------

-- | Compute the dominator tree for a CFG
-- Uses the Cooper-Harvey-Kennedy algorithm which is simple and efficient
-- for reducible control flow graphs.
computeDominators :: CFG -> DomTree
computeDominators cfg =
  let rpo = reversePostorder cfg
      rpoIdx = Map.fromList $ zip rpo [0..]
      entry = cfgEntry cfg
      -- Initial: entry dominates itself, everything else undefined
      initIdom = Map.singleton entry entry
      -- Iterate until fixed point
      finalIdom = iterateDom cfg rpo rpoIdx initIdom
      -- Build children map
      children = buildChildren finalIdom
  in DomTree
    { domIdom = finalIdom
    , domChildren_ = children
    , domRPO = rpo
    , domRPOIndex = rpoIdx
    }

-- | Iterate dominator computation until fixed point
iterateDom :: CFG -> [BlockId] -> Map BlockId Int -> Map BlockId BlockId -> Map BlockId BlockId
iterateDom cfg rpo rpoIdx idom =
  let idom' = foldl' (processBlock cfg rpoIdx) idom rpo
  in if idom' == idom
     then idom
     else iterateDom cfg rpo rpoIdx idom'

-- | Process a block to update its immediate dominator
processBlock :: CFG -> Map BlockId Int -> Map BlockId BlockId -> BlockId -> Map BlockId BlockId
processBlock cfg rpoIdx idom bid =
  let preds = predecessors cfg bid
      -- Get predecessors that have already been processed (have idom)
      processedPreds = filter (`Map.member` idom) preds
  in case processedPreds of
    [] -> idom  -- No processed predecessors, skip
    (p:ps) ->
      -- Start with first processed predecessor
      -- Find common dominator with all other processed predecessors
      let newIdom = foldl' (findCommonDom rpoIdx idom) p ps
      in Map.insert bid newIdom idom

-- | Find common dominator of two blocks (intersection in dominator tree)
findCommonDom :: Map BlockId Int -> Map BlockId BlockId -> BlockId -> BlockId -> BlockId
findCommonDom rpoIdx idom b1 b2 = go b1 b2
  where
    idx bid = fromMaybe maxBound $ Map.lookup bid rpoIdx

    go finger1 finger2
      | finger1 == finger2 = finger1
      | idx finger1 > idx finger2 =
          case Map.lookup finger1 idom of
            Just parent -> go parent finger2
            Nothing -> finger2  -- finger1 unreachable
      | otherwise =
          case Map.lookup finger2 idom of
            Just parent -> go finger1 parent
            Nothing -> finger1  -- finger2 unreachable

-- | Build children map from idom map
buildChildren :: Map BlockId BlockId -> Map BlockId [BlockId]
buildChildren idom =
  let -- Group by parent
      addChild children (child, parent)
        | child == parent = children  -- Entry is its own parent, skip
        | otherwise = Map.insertWith (++) parent [child] children
  in foldl' addChild Map.empty (Map.toList idom)

--------------------------------------------------------------------------------
-- Dominance Frontier
--------------------------------------------------------------------------------

-- | Compute dominance frontiers for all blocks
-- Uses the algorithm from Cytron et al. (1991)
computeDomFrontier :: CFG -> DomTree -> DomFrontier
computeDomFrontier cfg domTree =
  let blocks = allBlockIds cfg
      -- Initialize empty frontiers
      emptyDF = Map.fromList [(b, Set.empty) | b <- blocks]
  in foldl' (computeDF cfg domTree) emptyDF blocks

-- | Compute dominance frontier contribution from a block
computeDF :: CFG -> DomTree -> DomFrontier -> BlockId -> DomFrontier
computeDF cfg domTree df bid =
  let succs = successors cfg bid
      idomBid = immediateDom domTree bid
  in foldl' (addToFrontier domTree idomBid bid) df succs

-- | Add block to frontier if appropriate
addToFrontier :: DomTree -> Maybe BlockId -> BlockId -> DomFrontier -> BlockId -> DomFrontier
addToFrontier domTree _idomRunner runner df target =
  -- Walk up dominator tree from runner, adding target to frontiers
  -- Stop when we reach a strict dominator of target
  go runner df
  where
    go current df'
      -- Stop if current strictly dominates target
      | strictlyDominates domTree current target = df'
      -- Add target to current's frontier
      | otherwise =
          let df'' = Map.adjust (Set.insert target) current df'
          in case immediateDom domTree current of
               Just parent | parent /= current -> go parent df''
               _ -> df''

--------------------------------------------------------------------------------
-- Queries
--------------------------------------------------------------------------------

-- | Get immediate dominator of a block
immediateDom :: DomTree -> BlockId -> Maybe BlockId
immediateDom DomTree{..} bid =
  case Map.lookup bid domIdom of
    Just parent | parent /= bid -> Just parent
    _ -> Nothing  -- Entry block or not found

-- | Check if block A dominates block B
dominates :: DomTree -> BlockId -> BlockId -> Bool
dominates domTree a b
  | a == b = True
  | otherwise = case immediateDom domTree b of
      Just parent -> dominates domTree a parent
      Nothing -> False

-- | Check if block A strictly dominates block B (A dom B and A /= B)
strictlyDominates :: DomTree -> BlockId -> BlockId -> Bool
strictlyDominates domTree a b = a /= b && dominates domTree a b

-- | Get children of a block in the dominator tree
domChildren :: DomTree -> BlockId -> [BlockId]
domChildren DomTree{..} bid = Map.findWithDefault [] bid domChildren_

-- | Get depth of block in dominator tree (entry = 0)
domDepth :: DomTree -> BlockId -> Int
domDepth domTree bid = go 0 bid
  where
    go depth b = case immediateDom domTree b of
      Just parent -> go (depth + 1) parent
      Nothing -> depth

--------------------------------------------------------------------------------
-- Post-Dominator Tree
--------------------------------------------------------------------------------

-- | Compute post-dominator tree by reversing the CFG
-- A block A post-dominates B if every path from B to exit goes through A.
postDomTree :: CFG -> DomTree
postDomTree cfg =
  -- Create reversed CFG with exit as entry
  let exits = exitBlocks cfg
      -- Add a virtual exit node if multiple exits
      (reversedCFG, _) = reverseCFG cfg exits
  in computeDominators reversedCFG

-- | Reverse a CFG (swap predecessors and successors)
reverseCFG :: CFG -> [BlockId] -> (CFG, BlockId)
reverseCFG cfg exits =
  case exits of
    [] ->
      -- No exits (infinite loop or unreachable code), use entry as virtual exit
      (cfg { cfgPreds = cfgSuccs cfg, cfgSuccs = cfgPreds cfg }, cfgEntry cfg)
    [single] ->
      -- Single exit, just reverse edges
      let reversed = CFG
            { cfgBlocks = cfgBlocks cfg  -- Keep blocks (terminators will be ignored)
            , cfgEntry = single
            , cfgPreds = cfgSuccs cfg
            , cfgSuccs = cfgPreds cfg
            }
      in (reversed, single)
    _ ->
      -- Multiple exits: add virtual exit node
      let virtualExit = "__exit__"
          -- Add edges from virtual exit to all real exits
          newSuccs = Map.insert virtualExit exits $
                     foldl' (\m e -> Map.insertWith (++) e [virtualExit] m)
                           (cfgPreds cfg) exits
          newPreds = Map.insert virtualExit [] $
                     foldl' (\m e -> Map.insertWith (++) virtualExit [e] m)
                           (cfgSuccs cfg) exits
          reversed = CFG
            { cfgBlocks = cfgBlocks cfg
            , cfgEntry = virtualExit
            , cfgPreds = newSuccs
            , cfgSuccs = newPreds
            }
      in (reversed, virtualExit)
