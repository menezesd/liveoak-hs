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
      raw = [DepEdge fromIdx toIdx TrueDep (instrLatency fromInstr) |
              not (Set.null (Set.intersection fromDefs toUses))]

      -- WAR: from reads, to writes
      war = [DepEdge fromIdx toIdx AntiDep 0 |
              not (Set.null (Set.intersection fromUses toDefs))]

      -- WAW: both write same variable
      waw = [DepEdge fromIdx toIdx OutputDep 0 |
              not (Set.null (Set.intersection fromDefs toDefs))]

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

-- | Topological sort of the dependency graph using Kahn's algorithm
-- Time complexity: O(V + E) instead of O(V²)
topSort :: DepGraph -> [Int]
topSort graph =
  let -- Compute in-degree for each node
      inDegree0 = IntMap.fromList [(n, 0) | n <- dgNodes graph]
      inDegree = foldl' countPreds inDegree0 (dgNodes graph)
      -- Find initially ready nodes (in-degree = 0)
      ready0 = [n | n <- dgNodes graph, IntMap.findWithDefault 0 n inDegree == 0]
  in go ready0 inDegree []
  where
    countPreds deg n =
      let preds = IntMap.findWithDefault [] n (dgPreds graph)
      in IntMap.insert n (length preds) deg

    go [] _ acc = reverse acc
    go (n:ready) inDeg acc =
      let -- Decrement in-degree of successors
          succs = [depTo e | e <- IntMap.findWithDefault [] n (dgSuccs graph)]
          (newReady, newInDeg) = foldl' (decrementDeg n) (ready, inDeg) succs
      in go newReady newInDeg (n : acc)

    decrementDeg _ (ready, inDeg) succ =
      let oldDeg = IntMap.findWithDefault 0 succ inDeg
          newDeg = oldDeg - 1
          newInDeg = IntMap.insert succ newDeg inDeg
      in if newDeg == 0
         then (succ : ready, newInDeg)
         else (ready, newInDeg)

--------------------------------------------------------------------------------
-- List Scheduling
--------------------------------------------------------------------------------

-- | List scheduling algorithm with register pressure awareness
-- Uses critical path as primary heuristic and register pressure as tiebreaker
listSchedule :: DepGraph -> [Int]
listSchedule graph =
  let cp = criticalPath graph
      -- Compute live-in and live-out for pressure calculation
      liveInfo = computeLiveInfo graph
      -- Priority: critical path length (higher = schedule first)
      allPredsScheduled n scheduled =
        all (\e -> Set.member (depFrom e) scheduled) (IntMap.findWithDefault [] n (dgPreds graph))
      go remaining scheduled liveNow acc
        | Set.null remaining = reverse acc
        | otherwise =
            let ready = [n | n <- Set.toList remaining, allPredsScheduled n scheduled]
                -- Score each ready instruction: (critical path, -pressure increase)
                -- Higher is better for both components
                readyWithPriority = [(n, scorePriority cp liveInfo liveNow n) | n <- ready]
                -- Sort by priority (descending by critical path, then by pressure)
                sorted = sortBy (comparing (Down . snd)) readyWithPriority
            in case sorted of
              [] -> reverse acc ++ Set.toList remaining  -- Cycle or deadlock
              ((n, _):_) ->
                let liveNow' = updateLiveSet liveInfo liveNow n
                in go (Set.delete n remaining) (Set.insert n scheduled) liveNow' (n : acc)
  in go (Set.fromList $ dgNodes graph) Set.empty Set.empty []

-- | Score for scheduling priority: (critical path length, -pressure increase)
-- We want high critical path and low pressure increase
scorePriority :: IntMap.IntMap Int -> LiveInfo -> Set.Set Int -> Int -> (Int, Int)
scorePriority cp liveInfo liveNow n =
  let cpScore = IntMap.findWithDefault 0 n cp
      -- Estimate pressure change: how many new values minus consumed values
      pressureChange = estimatePressureChange liveInfo liveNow n
  in (cpScore, -pressureChange)  -- Negate so lower pressure is better

-- | Live variable information for each instruction
data LiveInfo = LiveInfo
  { liDefs :: !(IntMap.IntMap (Set.Set Int))  -- Instruction -> defined values
  , liUses :: !(IntMap.IntMap (Set.Set Int))  -- Instruction -> used values
  } deriving (Show)

-- | Compute live information for each instruction
computeLiveInfo :: DepGraph -> LiveInfo
computeLiveInfo graph =
  let nodes = dgNodes graph
      -- For simplicity, assume instruction i defines value i and uses its predecessors
      defs = IntMap.fromList [(n, Set.singleton n) | n <- nodes]
      uses = IntMap.fromList [(n, Set.fromList [depFrom e | e <- IntMap.findWithDefault [] n (dgPreds graph)])
                             | n <- nodes]
  in LiveInfo defs uses

-- | Estimate pressure change from scheduling instruction n
-- The change is: (+1 for each defined) - (+0 for consumed, conservative estimate)
-- A more accurate estimate would track last uses, but this is safe
estimatePressureChange :: LiveInfo -> Set.Set Int -> Int -> Int
estimatePressureChange LiveInfo{..} _liveNow n =
  let defined = IntMap.findWithDefault Set.empty n liDefs
      -- New values introduced (each definition increases pressure)
      newLive = Set.size defined
      -- Note: We conservatively assume values aren't consumed (last used) here
      -- This makes scheduling slightly less optimal but is always safe
  in newLive

-- | Update live set after scheduling instruction n
updateLiveSet :: LiveInfo -> Set.Set Int -> Int -> Set.Set Int
updateLiveSet LiveInfo{..} liveNow n =
  let defined = IntMap.findWithDefault Set.empty n liDefs
  in Set.union liveNow defined

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
    [] -> SSABlock (blockId "__empty__") [] []
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
