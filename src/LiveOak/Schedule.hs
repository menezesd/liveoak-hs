{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RecordWildCards #-}

-- | Instruction Scheduling.
-- Reorders instructions to minimize pipeline stalls and improve
-- instruction-level parallelism.
module LiveOak.Schedule
  ( -- * Instruction Scheduling
    scheduleMethod
  , ScheduleResult(..)

    -- * Dependency Analysis
  , DepGraph(..)
  , buildDepGraph
  , criticalPath

    -- * Scheduling Algorithms
  , listSchedule
  , traceSchedule
  ) where

import LiveOak.SSATypes
import LiveOak.CFG
import LiveOak.Ast (BinaryOp(..))
import LiveOak.SSAUtils (instrUses, instrDefs)

import qualified Data.IntMap.Strict as IntMap
import qualified Data.Set as Set
import Data.List (foldl', sortBy, partition)
import Data.Ord (comparing, Down(..))
import Data.Maybe (mapMaybe)

--------------------------------------------------------------------------------
-- Types
--------------------------------------------------------------------------------

-- | Dependency type
data DepType
  = TrueDep       -- ^ Read-after-write (RAW)
  | AntiDep       -- ^ Write-after-read (WAR)
  | OutputDep     -- ^ Write-after-write (WAW)
  | ControlDep    -- ^ Control dependency
  deriving (Eq, Ord, Show)

-- | Dependency edge
data DepEdge = DepEdge
  { depFrom :: !Int         -- ^ Source instruction index
  , depTo :: !Int           -- ^ Target instruction index
  , depType :: !DepType     -- ^ Dependency type
  , depLatency :: !Int      -- ^ Latency (cycles)
  } deriving (Show)

-- | Dependency graph
data DepGraph = DepGraph
  { dgNodes :: ![Int]                          -- ^ Instruction indices
  , dgSuccs :: !(IntMap.IntMap [DepEdge])      -- ^ Successors of each node
  , dgPreds :: !(IntMap.IntMap [DepEdge])      -- ^ Predecessors of each node
  , dgLatency :: !(IntMap.IntMap Int)          -- ^ Latency of each instruction
  } deriving (Show)

-- | Scheduling result
data ScheduleResult = ScheduleResult
  { schedOptBlocks :: ![SSABlock]     -- ^ Scheduled blocks
  , schedCyclesSaved :: !Int          -- ^ Estimated cycles saved
  } deriving (Show)

--------------------------------------------------------------------------------
-- Instruction Latencies
--------------------------------------------------------------------------------

-- | Estimate instruction latency
instrLatency :: SSAInstr -> Int
instrLatency = \case
  SSAAssign _ expr -> exprLatency expr
  SSAReturn _ -> 1
  SSAJump _ -> 1
  SSABranch _ _ _ -> 1
  SSAFieldStore _ _ _ _ -> 3  -- Memory store
  SSAExprStmt expr -> exprLatency expr

-- | Estimate expression latency
exprLatency :: SSAExpr -> Int
exprLatency = \case
  SSAInt _ -> 1
  SSABool _ -> 1
  SSAStr _ -> 1
  SSANull -> 1
  SSAThis -> 1
  SSAUse _ -> 1
  SSAUnary _ _ -> 1
  SSABinary op _ _ -> binaryOpLatency op
  SSATernary _ _ _ -> 2
  SSACall _ _ -> 10     -- Function call
  SSAInstanceCall _ _ _ -> 10
  SSANewObject _ _ -> 20  -- Allocation
  SSAFieldAccess _ _ -> 3  -- Memory load

-- | Binary operation latency
binaryOpLatency :: BinaryOp -> Int
binaryOpLatency = \case
  Add -> 1
  Sub -> 1
  Mul -> 3
  Div -> 10
  Mod -> 10
  _ -> 1

--------------------------------------------------------------------------------
-- Dependency Graph Construction
--------------------------------------------------------------------------------

-- | Build dependency graph for a basic block
buildDepGraph :: [SSAInstr] -> DepGraph
buildDepGraph instrs =
  let nodes = [0..length instrs - 1]
      indexed = zip nodes instrs
      -- Build edges for each pair
      edges = concatMap (findDeps indexed) indexed
      -- Group by source and target
      succs = foldl' addSucc IntMap.empty edges
      preds = foldl' addPred IntMap.empty edges
      lats = IntMap.fromList [(i, instrLatency instr) | (i, instr) <- indexed]
  in DepGraph
    { dgNodes = nodes
    , dgSuccs = succs
    , dgPreds = preds
    , dgLatency = lats
    }
  where
    addSucc m e = IntMap.insertWith (++) (depFrom e) [e] m
    addPred m e = IntMap.insertWith (++) (depTo e) [e] m

-- | Find dependencies from one instruction to all later ones
findDeps :: [(Int, SSAInstr)] -> (Int, SSAInstr) -> [DepEdge]
findDeps allInstrs (fromIdx, fromInstr) =
  concatMap (findDep fromIdx fromInstr) [(i, instr) | (i, instr) <- allInstrs, i > fromIdx]

-- | Find dependency between two instructions
findDep :: Int -> SSAInstr -> (Int, SSAInstr) -> [DepEdge]
findDep fromIdx fromInstr (toIdx, toInstr) =
  let fromDefs = instrDefs fromInstr
      fromUses = instrUses fromInstr
      toDefs = instrDefs toInstr
      toUses = instrUses toInstr

      -- RAW: from writes, to reads
      raw = if not (Set.null (Set.intersection fromDefs toUses))
            then [DepEdge fromIdx toIdx TrueDep (instrLatency fromInstr)]
            else []

      -- WAR: from reads, to writes
      war = if not (Set.null (Set.intersection fromUses toDefs))
            then [DepEdge fromIdx toIdx AntiDep 0]
            else []

      -- WAW: both write same variable
      waw = if not (Set.null (Set.intersection fromDefs toDefs))
            then [DepEdge fromIdx toIdx OutputDep 0]
            else []

  in raw ++ war ++ waw

--------------------------------------------------------------------------------
-- Critical Path Analysis
--------------------------------------------------------------------------------

-- | Compute critical path length for each instruction
criticalPath :: DepGraph -> IntMap.IntMap Int
criticalPath graph =
  -- Work backwards from nodes with no successors
  let exits = [n | n <- dgNodes graph, null (IntMap.findWithDefault [] n (dgSuccs graph))]
      initial = IntMap.fromList [(n, IntMap.findWithDefault 1 n (dgLatency graph)) | n <- exits]
  in foldl' (propagateCP graph) initial (reverse $ topSort graph)

-- | Propagate critical path length
propagateCP :: DepGraph -> IntMap.IntMap Int -> Int -> IntMap.IntMap Int
propagateCP graph cpMap node =
  case IntMap.lookup node cpMap of
    Just _ -> cpMap  -- Already computed
    Nothing ->
      let succs = IntMap.findWithDefault [] node (dgSuccs graph)
          lat = IntMap.findWithDefault 1 node (dgLatency graph)
          maxSucc = foldl' (\acc e -> max acc (IntMap.findWithDefault 0 (depTo e) cpMap + depLatency e)) 0 succs
      in IntMap.insert node (lat + maxSucc) cpMap

-- | Topological sort of the dependency graph
topSort :: DepGraph -> [Int]
topSort graph = go (dgNodes graph) Set.empty []
  where
    go [] _ acc = acc
    go remaining visited acc =
      let ready = [n | n <- remaining,
                      all (`Set.member` visited) (predNodes n)]
      in case ready of
        [] -> remaining ++ acc  -- Cycle detected, just append remaining
        (n:_) -> go (filter (/= n) remaining) (Set.insert n visited) (n : acc)

    predNodes n = [depFrom e | e <- IntMap.findWithDefault [] n (dgPreds graph)]

--------------------------------------------------------------------------------
-- List Scheduling
--------------------------------------------------------------------------------

-- | List scheduling algorithm
listSchedule :: DepGraph -> [Int]
listSchedule graph =
  let cp = criticalPath graph
      -- Priority: critical path length (higher = schedule first)
      priority n = IntMap.findWithDefault 0 n cp
      allPredsScheduled n scheduled =
        all (\e -> Set.member (depFrom e) scheduled) (IntMap.findWithDefault [] n (dgPreds graph))
      go remaining scheduled acc
        | Set.null remaining = reverse acc
        | otherwise =
            let ready = [n | n <- Set.toList remaining, allPredsScheduled n scheduled]
                -- Sort by priority (descending)
                sorted = sortBy (comparing (Down . priority)) ready
            in case sorted of
              [] -> reverse acc ++ Set.toList remaining  -- Cycle or deadlock
              (n:_) -> go (Set.delete n remaining) (Set.insert n scheduled) (n : acc)
  in go (Set.fromList $ dgNodes graph) Set.empty []

--------------------------------------------------------------------------------
-- Trace Scheduling
--------------------------------------------------------------------------------

-- | Trace scheduling for superblock optimization
traceSchedule :: CFG -> [SSABlock] -> [SSABlock]
traceSchedule cfg blocks =
  let -- Find traces (sequences of blocks that are likely to execute together)
      traces = findTraces cfg blocks
      -- Schedule each trace
      scheduled = map (scheduleTrace blocks) traces
  in scheduled

-- | Find execution traces
findTraces :: CFG -> [SSABlock] -> [[BlockId]]
findTraces cfg _blocks =
  let entry = cfgEntry cfg
      visited = Set.empty
  in buildTrace cfg entry visited []
  where
    buildTrace cfg' bid visited trace
      | Set.member bid visited = [reverse (bid : trace)]
      | otherwise =
          let visited' = Set.insert bid visited
              succs = successors cfg' bid
          in case succs of
            [] -> [reverse (bid : trace)]
            [s] -> buildTrace cfg' s visited' (bid : trace)
            (s:_) -> reverse (bid : trace) : buildTrace cfg' s visited' []

-- | Schedule a trace
scheduleTrace :: [SSABlock] -> [BlockId] -> SSABlock
scheduleTrace blocks trace =
  case [b | b <- blocks, blockLabel b `elem` trace] of
    [] -> SSABlock (BlockId "__empty__") [] []
    (b:_) -> b  -- Simplified: return first block

--------------------------------------------------------------------------------
-- Instruction Scheduling for Method
--------------------------------------------------------------------------------

-- | Schedule all blocks in a method
scheduleMethod :: CFG -> [SSABlock] -> ScheduleResult
scheduleMethod _cfg blocks =
  let (scheduled, saved) = foldl' scheduleBlock ([], 0) blocks
  in ScheduleResult
    { schedOptBlocks = reverse scheduled
    , schedCyclesSaved = saved
    }

-- | Schedule a single block
scheduleBlock :: ([SSABlock], Int) -> SSABlock -> ([SSABlock], Int)
scheduleBlock (acc, saved) block@SSABlock{..} =
  let -- Split into schedulable and non-schedulable parts
      (nonTerm, term) = splitTerm blockInstrs
      -- Build an IntMap for safe O(1) lookup by index
      instrMap = IntMap.fromList $ zip [0..] nonTerm
      -- Build dependency graph
      depGraph = buildDepGraph nonTerm
      -- Schedule
      schedule = listSchedule depGraph
      -- Reorder instructions using safe lookup
      scheduled = mapMaybe (`IntMap.lookup` instrMap) schedule
      -- Estimate cycles saved
      origLen = estimateCycles depGraph [0..length nonTerm - 1]
      newLen = estimateCycles depGraph schedule
      block' = block { blockInstrs = scheduled ++ term }
  in (block' : acc, saved + max 0 (origLen - newLen))
  where
    splitTerm instrs =
      let (term, nonTerm) = partition isTerm (reverse instrs)
      in (reverse nonTerm, reverse term)

    isTerm (SSAJump _) = True
    isTerm (SSABranch _ _ _) = True
    isTerm (SSAReturn _) = True
    isTerm _ = False

-- | Estimate execution cycles for a schedule
estimateCycles :: DepGraph -> [Int] -> Int
estimateCycles graph schedule =
  sum [IntMap.findWithDefault 1 i (dgLatency graph) | i <- schedule]
