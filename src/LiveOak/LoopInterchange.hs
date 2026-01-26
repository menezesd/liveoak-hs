{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RecordWildCards #-}

-- | Loop Interchange.
-- Swaps the order of nested loops for better cache locality.
--
-- == When to Interchange
-- Consider:
-- @
-- for i in 0..N:
--   for j in 0..M:
--     A[j][i] = ...  // Column-major access
-- @
-- Interchanging to:
-- @
-- for j in 0..M:
--   for i in 0..N:
--     A[j][i] = ...  // Row-major access (better locality)
-- @
--
-- == Legality
-- Interchange is legal if it doesn't violate data dependencies.
--
module LiveOak.LoopInterchange
  ( -- * Loop Interchange
    interchangeLoops
  , InterchangeResult(..)

    -- * Analysis
  , canInterchange
  , shouldInterchange
  ) where

import LiveOak.SSATypes
import LiveOak.CFG
import LiveOak.Loop
import LiveOak.Dominance (DomTree, computeDominators)

import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Set (Set)
import qualified Data.Set as Set
import Data.List (foldl')
import Data.Maybe (mapMaybe)

--------------------------------------------------------------------------------
-- Types
--------------------------------------------------------------------------------

-- | Loop interchange result
data InterchangeResult = InterchangeResult
  { liOptBlocks :: ![SSABlock]
  , liInterchanged :: !Int           -- ^ Number of loop pairs interchanged
  } deriving (Show)

-- | Nested loop pair
data NestedPair = NestedPair
  { npOuter :: !Loop
  , npInner :: !Loop
  , npAccessPattern :: !AccessPattern
  } deriving (Show)

-- | Memory access pattern in nested loops
data AccessPattern
  = RowMajor                        -- ^ A[i][j] with outer=i, inner=j
  | ColumnMajor                     -- ^ A[j][i] with outer=i, inner=j
  | Unknown
  deriving (Eq, Show)

--------------------------------------------------------------------------------
-- Loop Interchange
--------------------------------------------------------------------------------

-- | Apply loop interchange optimization
interchangeLoops :: SSAMethod -> InterchangeResult
interchangeLoops method =
  let cfg = buildCFG method
      domTree = computeDominators cfg
      loopNest = findLoops cfg domTree
      blocks = ssaMethodBlocks method
      blockMap = Map.fromList [(blockLabel b, b) | b <- blocks]

      -- Find nested loop pairs
      nestedPairs = findNestedPairs loopNest blockMap

      -- Filter for interchangeable pairs
      candidates = filter (\np -> canInterchange np && shouldInterchange np) nestedPairs

      -- Apply interchange
      (optimized, count) = applyInterchange candidates blockMap
  in InterchangeResult
    { liOptBlocks = Map.elems optimized
    , liInterchanged = count
    }

-- | Find nested loop pairs
findNestedPairs :: LoopNest -> Map BlockId SSABlock -> [NestedPair]
findNestedPairs loops blockMap = mapMaybe (makeNestedPair loops blockMap) (Map.elems loops)

-- | Create a nested pair if loop has exactly one child
makeNestedPair :: LoopNest -> Map BlockId SSABlock -> Loop -> Maybe NestedPair
makeNestedPair loops blockMap outer =
  case loopChildren outer of
    [innerHeader] ->
      case Map.lookup innerHeader loops of
        Just inner ->
          let pattern = analyzeAccessPattern blockMap outer inner
          in Just $ NestedPair outer inner pattern
        Nothing -> Nothing
    _ -> Nothing  -- Not exactly one nested loop

-- | Analyze access pattern in nested loops
analyzeAccessPattern :: Map BlockId SSABlock -> Loop -> Loop -> AccessPattern
analyzeAccessPattern blockMap outer inner =
  let outerIV = extractLoopIV blockMap outer
      innerIV = extractLoopIV blockMap inner
      bodyBlocks = [b | bid <- Set.toList (loopBody inner), Just b <- [Map.lookup bid blockMap]]
      accesses = concatMap (collectArrayAccesses outerIV innerIV) bodyBlocks
  in classifyPattern accesses

-- | Extract loop induction variable
extractLoopIV :: Map BlockId SSABlock -> Loop -> Maybe String
extractLoopIV blockMap loop =
  case Map.lookup (loopHeader loop) blockMap of
    Just SSABlock{..} ->
      case blockPhis of
        (phi:_) -> Just $ varNameString (ssaName (phiVar phi))
        [] -> Nothing
    Nothing -> Nothing

-- | Array access with indices
data ArrayAccess = ArrayAccess
  { aaBase :: !String               -- ^ Base variable
  , aaOuterIdx :: !Bool             -- ^ True if outer IV is first index
  , aaInnerIdx :: !Bool             -- ^ True if inner IV is first index
  } deriving (Show)

-- | Collect array accesses from a block
collectArrayAccesses :: Maybe String -> Maybe String -> SSABlock -> [ArrayAccess]
collectArrayAccesses outerIV innerIV SSABlock{..} =
  concatMap (instrAccesses outerIV innerIV) blockInstrs

instrAccesses :: Maybe String -> Maybe String -> SSAInstr -> [ArrayAccess]
instrAccesses _outerIV _innerIV = \case
  -- Would need more sophisticated array analysis
  -- For now, return empty - this is a placeholder
  _ -> []

-- | Classify access pattern from collected accesses
classifyPattern :: [ArrayAccess] -> AccessPattern
classifyPattern [] = Unknown
classifyPattern accesses =
  let outerFirst = length [a | a <- accesses, aaOuterIdx a]
      innerFirst = length [a | a <- accesses, aaInnerIdx a]
  in if outerFirst > innerFirst then RowMajor
     else if innerFirst > outerFirst then ColumnMajor
     else Unknown

--------------------------------------------------------------------------------
-- Legality Analysis
--------------------------------------------------------------------------------

-- | Check if interchange is legal (doesn't violate dependencies)
canInterchange :: NestedPair -> Bool
canInterchange NestedPair{..} =
  -- Interchange is legal if:
  -- 1. Both loops are perfectly nested (inner is only thing in outer)
  -- 2. No loop-carried dependencies that would be violated
  isPerfectlyNested npOuter npInner
  && noViolatedDependencies npOuter npInner

-- | Check if loops are perfectly nested
isPerfectlyNested :: Loop -> Loop -> Bool
isPerfectlyNested outer inner =
  -- Outer body should be just: header, inner loop body, latch
  let outerBody = loopBody outer
      innerBody = loopBody inner
      outerOnly = outerBody Set.\\ innerBody
  in Set.size outerOnly <= 2  -- Header and latch only

-- | Check for violated dependencies
noViolatedDependencies :: Loop -> Loop -> Bool
noViolatedDependencies _outer _inner =
  -- Simplified: would need full dependency analysis
  True

--------------------------------------------------------------------------------
-- Profitability Analysis
--------------------------------------------------------------------------------

-- | Check if interchange would be profitable
shouldInterchange :: NestedPair -> Bool
shouldInterchange NestedPair{..} =
  -- Interchange if current pattern is column-major (non-sequential)
  npAccessPattern == ColumnMajor

--------------------------------------------------------------------------------
-- Apply Interchange
--------------------------------------------------------------------------------

-- | Apply interchange to candidate pairs
applyInterchange :: [NestedPair] -> Map BlockId SSABlock -> (Map BlockId SSABlock, Int)
applyInterchange pairs blockMap = foldl' applyOne (blockMap, 0) pairs

-- | Apply interchange to one pair
applyOne :: (Map BlockId SSABlock, Int) -> NestedPair -> (Map BlockId SSABlock, Int)
applyOne (blockMap, count) NestedPair{..} =
  -- Loop interchange is complex:
  -- 1. Swap the loop headers
  -- 2. Update bounds expressions
  -- 3. Update induction variable uses
  -- For now, just return unchanged - full implementation would transform the CFG
  (blockMap, count)
