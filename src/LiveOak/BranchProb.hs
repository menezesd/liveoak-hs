{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RecordWildCards #-}

-- | Branch Probability Analysis and Hints.
-- Estimates branch probabilities for better code layout and optimization decisions.
--
-- == Heuristics
-- 1. Loop back edges are likely taken (~90%)
-- 2. Error handling branches are unlikely (~10%)
-- 3. Pointer null checks: non-null is likely (~90%)
-- 4. Comparison with 0: non-zero is often likely
-- 5. Return blocks are less likely in loops
--
module LiveOak.BranchProb
  ( -- * Branch Probability
    BranchProb(..)
  , Probability
  , likely, unlikely, evenProb

    -- * Analysis
  , analyzeBranchProbs
  , BranchProbInfo(..)
  , getEdgeProb
  , isLikelyEdge

    -- * Hints
  , BranchHint(..)
  , generateHints
  ) where

import LiveOak.SSATypes
import LiveOak.CFG
import LiveOak.Loop
import LiveOak.Dominance (DomTree, computeDominators)
import LiveOak.Ast (BinaryOp(..), UnaryOp(..))

import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Set (Set)
import qualified Data.Set as Set
import Data.List (foldl')

--------------------------------------------------------------------------------
-- Types
--------------------------------------------------------------------------------

-- | Probability as a percentage (0-100)
type Probability = Int

-- | Common probability values
likely, unlikely, evenProb :: Probability
likely = 90
unlikely = 10
evenProb = 50

-- | Branch probability for an edge
data BranchProb = BranchProb
  { bpFrom :: !BlockId
  , bpTo :: !BlockId
  , bpProb :: !Probability           -- ^ 0-100
  } deriving (Show)

-- | Branch probability information for a method
data BranchProbInfo = BranchProbInfo
  { bpiEdgeProbs :: !(Map (BlockId, BlockId) Probability)
  , bpiHotBlocks :: !(Set BlockId)   -- ^ Blocks likely to execute
  , bpiColdBlocks :: !(Set BlockId)  -- ^ Blocks unlikely to execute
  } deriving (Show)

-- | Branch hint for code generation
data BranchHint
  = HintLikely !BlockId              -- ^ This target is likely
  | HintUnlikely !BlockId            -- ^ This target is unlikely
  | HintNone
  deriving (Show)

--------------------------------------------------------------------------------
-- Branch Probability Analysis
--------------------------------------------------------------------------------

-- | Analyze branch probabilities for a method
analyzeBranchProbs :: SSAMethod -> BranchProbInfo
analyzeBranchProbs method =
  let cfg = buildCFG method
      domTree = computeDominators cfg
      loopNest = findLoops cfg domTree
      blocks = ssaMethodBlocks method
      blockMap = Map.fromList [(blockLabel b, b) | b <- blocks]

      -- Compute edge probabilities
      edgeProbs = computeEdgeProbs cfg loopNest blockMap

      -- Identify hot/cold blocks
      (hot, cold) = classifyBlocks' cfg edgeProbs
  in BranchProbInfo
    { bpiEdgeProbs = edgeProbs
    , bpiHotBlocks = hot
    , bpiColdBlocks = cold
    }

-- | Compute edge probabilities
computeEdgeProbs :: CFG -> LoopNest -> Map BlockId SSABlock -> Map (BlockId, BlockId) Probability
computeEdgeProbs cfg loops blockMap =
  let allEdges = [(from, to) | from <- allBlockIds cfg, to <- successors cfg from]
      probs = map (computeEdgeProb cfg loops blockMap) allEdges
  in Map.fromList (zip allEdges probs)

-- | Compute probability for a single edge
computeEdgeProb :: CFG -> LoopNest -> Map BlockId SSABlock -> (BlockId, BlockId) -> Probability
computeEdgeProb cfg loops blockMap (from, to) =
  case Map.lookup from blockMap of
    Nothing -> evenProb
    Just block ->
      let hints = collectHints cfg loops block from to
      in combineHints hints

-- | Collect probability hints for an edge
collectHints :: CFG -> LoopNest -> SSABlock -> BlockId -> BlockId -> [Probability]
collectHints cfg loops SSABlock{..} from to = concat
  [ loopHint
  , conditionHint
  , errorHint
  ]
  where
    -- Loop back edge heuristic
    loopHint =
      let backEdges = [(latch, loopHeader l) | l <- Map.elems loops, latch <- loopLatches l]
      in if (from, to) `elem` backEdges then [likely] else []

    -- Condition-based heuristics
    conditionHint = case lastBranch blockInstrs of
      Just (SSABranch cond thenB elseB) ->
        applyConditionHeuristics cond thenB elseB to
      _ -> []

    -- Error handling heuristic
    errorHint =
      case getBlock cfg to of
        Nothing -> []
        Just targetBlock ->
          if hasErrorPattern targetBlock then [unlikely] else []

    lastBranch [] = Nothing
    lastBranch [x] = Just x
    lastBranch (_:xs) = lastBranch xs

-- | Apply condition-based heuristics
applyConditionHeuristics :: SSAExpr -> BlockId -> BlockId -> BlockId -> [Probability]
applyConditionHeuristics cond thenB elseB target = case cond of
  -- Null check: non-null is likely
  SSABinary Eq expr SSANull ->
    if target == elseB then [likely] else [unlikely]  -- else = non-null
  SSABinary Ne expr SSANull ->
    if target == thenB then [likely] else [unlikely]  -- then = non-null

  -- Comparison with 0: non-zero often likely
  SSABinary Eq _ (SSAInt 0) ->
    if target == elseB then [70] else [30]
  SSABinary Ne _ (SSAInt 0) ->
    if target == thenB then [70] else [30]

  -- Boolean: true is often the "normal" path
  SSABool True -> if target == thenB then [likely] else [unlikely]
  SSABool False -> if target == elseB then [likely] else [unlikely]

  -- Negation: flip probabilities
  SSAUnary Not e ->
    applyConditionHeuristics e elseB thenB target

  _ -> []

-- | Check if block has error-handling pattern
hasErrorPattern :: CFGBlock -> Bool
hasErrorPattern CFGBlock{..} = any isErrorInstr cfgInstrs
  where
    isErrorInstr = \case
      SSAExprStmt (SSACall name _) -> isErrorName name
      SSAAssign _ (SSACall name _) -> isErrorName name
      _ -> False

    isErrorName name =
      any (`isSubstringOf` name) ["error", "throw", "assert", "fail", "panic", "abort"]

    isSubstringOf needle haystack = needle `elem` words haystack
    words s = filter (not . null) $ splitOn '_' s
    splitOn c str = case break (== c) str of
      (a, "") -> [a]
      (a, _:b) -> a : splitOn c b

-- | Combine multiple probability hints
combineHints :: [Probability] -> Probability
combineHints [] = evenProb
combineHints hints =
  -- Use geometric mean for combining probabilities
  let product' = foldl' (\acc p -> acc * p) 100 hints
      n = length hints
  in truncate (fromIntegral product' ** (1.0 / fromIntegral (n + 1)) :: Double)

-- | Classify blocks as hot or cold based on probabilities
classifyBlocks' :: CFG -> Map (BlockId, BlockId) Probability -> (Set BlockId, Set BlockId)
classifyBlocks' cfg edgeProbs =
  let entry = cfgEntry cfg
      allBlocks = allBlockIds cfg
      -- BFS with probability thresholds
      hot = propagateHot cfg edgeProbs entry
      cold = Set.fromList [b | b <- allBlocks, not (Set.member b hot)]
  in (hot, cold)

-- | Propagate hot marking from entry
propagateHot :: CFG -> Map (BlockId, BlockId) Probability -> BlockId -> Set BlockId
propagateHot cfg edgeProbs entry = go (Set.singleton entry) [entry]
  where
    go visited [] = visited
    go visited (b:queue) =
      let succs = successors cfg b
          hotSuccs = [s | s <- succs
                       , not (Set.member s visited)
                       , Map.findWithDefault evenProb (b, s) edgeProbs >= 50]
          visited' = Set.union visited (Set.fromList hotSuccs)
          queue' = queue ++ hotSuccs
      in go visited' queue'

--------------------------------------------------------------------------------
-- Queries
--------------------------------------------------------------------------------

-- | Get probability of an edge
getEdgeProb :: BranchProbInfo -> BlockId -> BlockId -> Probability
getEdgeProb info from to = Map.findWithDefault evenProb (from, to) (bpiEdgeProbs info)

-- | Check if an edge is likely (>= 70%)
isLikelyEdge :: BranchProbInfo -> BlockId -> BlockId -> Bool
isLikelyEdge info from to = getEdgeProb info from to >= 70

--------------------------------------------------------------------------------
-- Hint Generation
--------------------------------------------------------------------------------

-- | Generate branch hints for code generation
generateHints :: BranchProbInfo -> SSABlock -> BranchHint
generateHints info SSABlock{..} = case lastInstr of
  Just (SSABranch _ thenB elseB) ->
    let thenProb = getEdgeProb info blockLabel thenB
        elseProb = getEdgeProb info blockLabel elseB
    in if thenProb >= 70 then HintLikely thenB
       else if elseProb >= 70 then HintUnlikely thenB
       else HintNone
  _ -> HintNone
  where
    lastInstr = if null blockInstrs then Nothing else Just (last blockInstrs)
