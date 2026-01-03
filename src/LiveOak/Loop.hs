{-# LANGUAGE RecordWildCards #-}

-- | Natural loop detection and analysis.
-- Uses dominance information to find back edges and compute loop bodies.
module LiveOak.Loop
  ( -- * Types
    Loop(..)
  , LoopNest

    -- * Loop Detection
  , findLoops
  , findBackEdges
  , computeLoopBody

    -- * Loop Queries
  , isLoopHeader
  , loopDepth
  , innerMostLoop
  , loopBlocks
  , loopExits
  , isLoopInvariant
  ) where

import LiveOak.CFG
import LiveOak.Dominance
import LiveOak.SSATypes

import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Set (Set)
import qualified Data.Set as Set
import Data.List (foldl')

--------------------------------------------------------------------------------
-- Types
--------------------------------------------------------------------------------

-- | A natural loop
data Loop = Loop
  { loopHeader :: !BlockId           -- ^ Loop header (target of back edge)
  , loopBackEdges :: ![(BlockId, BlockId)]  -- ^ Back edges (from, to=header)
  , loopBody :: !(Set BlockId)       -- ^ All blocks in the loop
  , loopPreheader :: !(Maybe BlockId) -- ^ Preheader if it exists
  , loopLatches :: ![BlockId]        -- ^ Latch blocks (sources of back edges)
  , loopNestDepth :: !Int            -- ^ Nesting depth (1 = outermost)
  , loopParent :: !(Maybe BlockId)   -- ^ Parent loop's header (if nested)
  , loopChildren :: ![BlockId]       -- ^ Nested loop headers
  } deriving (Eq, Show)

-- | Loop nest - all loops indexed by header
type LoopNest = Map BlockId Loop

--------------------------------------------------------------------------------
-- Loop Detection
--------------------------------------------------------------------------------

-- | Find all natural loops in a CFG
findLoops :: CFG -> DomTree -> LoopNest
findLoops cfg domTree =
  let backEdges = findBackEdges cfg domTree
      -- Group back edges by header
      edgesByHeader = groupByHeader backEdges
      -- Create loops for each header
      loops = Map.mapWithKey (makeLoop cfg domTree) edgesByHeader
      -- Compute nesting relationships
      nested = computeNesting loops
  in nested

-- | Find all back edges in the CFG
-- A back edge is an edge from N to H where H dominates N
findBackEdges :: CFG -> DomTree -> [(BlockId, BlockId)]
findBackEdges cfg domTree =
  [ (from, to)
  | from <- allBlockIds cfg
  , to <- successors cfg from
  , dominates domTree to from  -- to dominates from => back edge
  ]

-- | Group back edges by their target (header)
groupByHeader :: [(BlockId, BlockId)] -> Map BlockId [(BlockId, BlockId)]
groupByHeader = foldl' addEdge Map.empty
  where
    addEdge m edge@(_, header) = Map.insertWith (++) header [edge] m

-- | Create a loop from its header and back edges
makeLoop :: CFG -> DomTree -> BlockId -> [(BlockId, BlockId)] -> Loop
makeLoop cfg _domTree header backEdges =
  let latches = map fst backEdges
      body = computeLoopBody cfg header latches
      preheader = findPreheader cfg header body
  in Loop
    { loopHeader = header
    , loopBackEdges = backEdges
    , loopBody = body
    , loopPreheader = preheader
    , loopLatches = latches
    , loopNestDepth = 1  -- Updated by computeNesting
    , loopParent = Nothing
    , loopChildren = []
    }

-- | Compute the body of a natural loop
-- Uses reverse DFS from latches, stopping at header
computeLoopBody :: CFG -> BlockId -> [BlockId] -> Set BlockId
computeLoopBody cfg header latches =
  let initial = Set.singleton header
      -- Add all blocks reachable backwards from latches to header
  in foldl' (addReachable cfg header) initial latches

-- | Add blocks reachable backwards from a block to the loop body
addReachable :: CFG -> BlockId -> Set BlockId -> BlockId -> Set BlockId
addReachable cfg header body block
  | Set.member block body = body  -- Already in body
  | otherwise =
      let body' = Set.insert block body
      in foldl' (addReachable cfg header) body' (predecessors cfg block)

-- | Find preheader if it exists
-- A preheader is the unique predecessor of the header that is not in the loop
findPreheader :: CFG -> BlockId -> Set BlockId -> Maybe BlockId
findPreheader cfg header body =
  case filter (not . (`Set.member` body)) (predecessors cfg header) of
    [single] -> Just single
    _ -> Nothing  -- No unique preheader

-- | Compute loop nesting relationships
computeNesting :: LoopNest -> LoopNest
computeNesting loops =
  let headers = Map.keys loops
      -- For each loop, find its parent (smallest enclosing loop)
      withParents = Map.mapWithKey (findParent loops headers) loops
      -- Update children based on parent relationships
      withChildren = updateChildren withParents
      -- Compute depths
  in computeDepths withChildren

-- | Find the parent loop of a loop
findParent :: LoopNest -> [BlockId] -> BlockId -> Loop -> Loop
findParent loops headers myHeader loop =
  let -- Find loops that contain this loop's header (but aren't this loop)
      candidates =
        [ (h, l)
        | h <- headers
        , h /= myHeader
        , Just l <- [Map.lookup h loops]
        , Set.member myHeader (loopBody l)
        ]
      -- Find the smallest (innermost) containing loop
      parent = case candidates of
        [] -> Nothing
        cs -> Just $ fst $ minimumBy (\(_, l1) (_, l2) ->
                compare (Set.size (loopBody l1)) (Set.size (loopBody l2))) cs
  in loop { loopParent = parent }
  where
    minimumBy f (x:xs) = foldl' (\a b -> if f a b == LT then a else b) x xs
    minimumBy _ [] = error "minimumBy: empty list"

-- | Update children based on parent relationships
updateChildren :: LoopNest -> LoopNest
updateChildren loops =
  let -- Build child map
      childMap = foldl' addChild Map.empty (Map.toList loops)
      -- Update each loop with its children
  in Map.mapWithKey (\h l -> l { loopChildren = Map.findWithDefault [] h childMap }) loops
  where
    addChild m (childHeader, loop) =
      case loopParent loop of
        Just parentHeader -> Map.insertWith (++) parentHeader [childHeader] m
        Nothing -> m

-- | Compute nesting depths
computeDepths :: LoopNest -> LoopNest
computeDepths loops = Map.map (setDepth loops) loops
  where
    setDepth ls loop = loop { loopNestDepth = computeDepth ls loop }

    computeDepth ls loop =
      case loopParent loop of
        Nothing -> 1
        Just parentHeader ->
          case Map.lookup parentHeader ls of
            Just parent -> 1 + computeDepth ls parent
            Nothing -> 1

--------------------------------------------------------------------------------
-- Loop Queries
--------------------------------------------------------------------------------

-- | Check if a block is a loop header
isLoopHeader :: LoopNest -> BlockId -> Bool
isLoopHeader loops bid = Map.member bid loops

-- | Get the nesting depth of a block (0 if not in any loop)
loopDepth :: LoopNest -> BlockId -> Int
loopDepth loops bid =
  case innerMostLoop loops bid of
    Just loop -> loopNestDepth loop
    Nothing -> 0

-- | Get the innermost loop containing a block
innerMostLoop :: LoopNest -> BlockId -> Maybe Loop
innerMostLoop loops bid =
  let containing = [l | l <- Map.elems loops, Set.member bid (loopBody l)]
  in case containing of
    [] -> Nothing
    ls -> Just $ maximumBy (\l1 l2 -> compare (loopNestDepth l1) (loopNestDepth l2)) ls
  where
    maximumBy f (x:xs) = foldl' (\a b -> if f a b == GT then a else b) x xs
    maximumBy _ [] = error "maximumBy: empty list"

-- | Get all blocks in a loop (including nested loops)
loopBlocks :: Loop -> [BlockId]
loopBlocks = Set.toList . loopBody

-- | Get exit blocks of a loop (blocks outside the loop that have predecessors in the loop)
loopExits :: CFG -> Loop -> [BlockId]
loopExits cfg loop =
  Set.toList $ Set.fromList
    [ succ'
    | block <- Set.toList (loopBody loop)
    , succ' <- successors cfg block
    , not (Set.member succ' (loopBody loop))
    ]

-- | Check if an SSA expression is loop-invariant
-- An expression is loop-invariant if all its operands are:
-- 1. Constants
-- 2. Defined outside the loop
-- 3. Themselves loop-invariant
isLoopInvariant :: Loop -> Set String -> SSAExpr -> Bool
isLoopInvariant _loop defsInLoop expr = go expr
  where
    go (SSAInt _) = True
    go (SSABool _) = True
    go (SSAStr _) = True
    go SSANull = True
    go SSAThis = True  -- 'this' doesn't change
    go (SSAUse var) = not (Set.member (ssaName var) defsInLoop)
    go (SSAUnary _ e) = go e
    go (SSABinary _ l r) = go l && go r
    go (SSATernary c t e) = go c && go t && go e
    go (SSACall _ _) = False  -- Calls may have side effects
    go (SSAInstanceCall _ _ _) = False
    go (SSANewObject _ _) = False  -- Allocations not invariant
    go (SSAFieldAccess target _) = go target  -- Field access of invariant is invariant
