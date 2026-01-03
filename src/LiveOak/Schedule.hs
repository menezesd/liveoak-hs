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

import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Set (Set)
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
  { dgNodes :: ![Int]                       -- ^ Instruction indices
  , dgSuccs :: !(Map Int [DepEdge])         -- ^ Successors of each node
  , dgPreds :: !(Map Int [DepEdge])         -- ^ Predecessors of each node
  , dgLatency :: !(Map Int Int)             -- ^ Latency of each instruction
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
      succs = foldl' addSucc Map.empty edges
      preds = foldl' addPred Map.empty edges
      lats = Map.fromList [(i, instrLatency instr) | (i, instr) <- indexed]
  in DepGraph
    { dgNodes = nodes
    , dgSuccs = succs
    , dgPreds = preds
    , dgLatency = lats
    }
  where
    addSucc m e = Map.insertWith (++) (depFrom e) [e] m
    addPred m e = Map.insertWith (++) (depTo e) [e] m

-- | Find dependencies from one instruction to all later ones
findDeps :: [(Int, SSAInstr)] -> (Int, SSAInstr) -> [DepEdge]
findDeps allInstrs (fromIdx, fromInstr) =
  concatMap (findDep fromIdx fromInstr) [(i, instr) | (i, instr) <- allInstrs, i > fromIdx]

-- | Find dependency between two instructions
findDep :: Int -> SSAInstr -> (Int, SSAInstr) -> [DepEdge]
findDep fromIdx fromInstr (toIdx, toInstr) =
  let fromDefs = instrDefs fromInstr
      fromUses = instrUseSet fromInstr
      toDefs = instrDefs toInstr
      toUses = instrUseSet toInstr

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

-- | Get definitions from an instruction
instrDefs :: SSAInstr -> Set String
instrDefs = \case
  SSAAssign var _ -> Set.singleton (ssaName var)
  _ -> Set.empty

-- | Get uses from an instruction as a Set
instrUseSet :: SSAInstr -> Set String
instrUseSet = \case
  SSAAssign _ expr -> exprUseSet expr
  SSAReturn (Just expr) -> exprUseSet expr
  SSAReturn Nothing -> Set.empty
  SSAJump _ -> Set.empty
  SSABranch cond _ _ -> exprUseSet cond
  SSAFieldStore target _ _ value -> exprUseSet target `Set.union` exprUseSet value
  SSAExprStmt expr -> exprUseSet expr

-- | Get uses from an expression as a Set
exprUseSet :: SSAExpr -> Set String
exprUseSet = \case
  SSAUse var -> Set.singleton (ssaName var)
  SSAUnary _ e -> exprUseSet e
  SSABinary _ l r -> exprUseSet l `Set.union` exprUseSet r
  SSATernary c t e -> exprUseSet c `Set.union` exprUseSet t `Set.union` exprUseSet e
  SSACall _ args -> Set.unions (map exprUseSet args)
  SSAInstanceCall target _ args ->
    exprUseSet target `Set.union` Set.unions (map exprUseSet args)
  SSANewObject _ args -> Set.unions (map exprUseSet args)
  SSAFieldAccess target _ -> exprUseSet target
  _ -> Set.empty

--------------------------------------------------------------------------------
-- Critical Path Analysis
--------------------------------------------------------------------------------

-- | Compute critical path length for each instruction
criticalPath :: DepGraph -> Map Int Int
criticalPath graph =
  -- Work backwards from nodes with no successors
  let exits = [n | n <- dgNodes graph, null (Map.findWithDefault [] n (dgSuccs graph))]
      initial = Map.fromList [(n, Map.findWithDefault 1 n (dgLatency graph)) | n <- exits]
  in foldl' (propagateCP graph) initial (reverse $ topSort graph)

-- | Propagate critical path length
propagateCP :: DepGraph -> Map Int Int -> Int -> Map Int Int
propagateCP graph cpMap node =
  case Map.lookup node cpMap of
    Just _ -> cpMap  -- Already computed
    Nothing ->
      let succs = Map.findWithDefault [] node (dgSuccs graph)
          lat = Map.findWithDefault 1 node (dgLatency graph)
          maxSucc = if null succs
                    then 0
                    else maximum [Map.findWithDefault 0 (depTo e) cpMap + depLatency e | e <- succs]
      in Map.insert node (lat + maxSucc) cpMap

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

    predNodes n = [depFrom e | e <- Map.findWithDefault [] n (dgPreds graph)]

--------------------------------------------------------------------------------
-- List Scheduling
--------------------------------------------------------------------------------

-- | List scheduling algorithm
listSchedule :: DepGraph -> [Int]
listSchedule graph =
  let cp = criticalPath graph
      -- Priority: critical path length (higher = schedule first)
      priority n = Map.findWithDefault 0 n cp
  in go (Set.fromList $ dgNodes graph) Set.empty []
  where
    go remaining scheduled acc
      | Set.null remaining = reverse acc
      | otherwise =
          let ready = [n | n <- Set.toList remaining, allPredsScheduled n scheduled]
              -- Sort by priority (descending)
              sorted = sortBy (comparing (Down . priority)) ready
          in case sorted of
            [] -> reverse acc ++ Set.toList remaining  -- Cycle or deadlock
            (n:_) -> go (Set.delete n remaining) (Set.insert n scheduled) (n : acc)

    allPredsScheduled n scheduled =
      all (\e -> Set.member (depFrom e) scheduled) (Map.findWithDefault [] n (dgPreds graph))

    priority n = Map.findWithDefault 0 n (criticalPath graph)

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
findTraces cfg blocks =
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
    [] -> SSABlock "__empty__" [] []
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
      -- Build dependency graph
      depGraph = buildDepGraph nonTerm
      -- Schedule
      schedule = listSchedule depGraph
      -- Reorder instructions
      scheduled = [nonTerm !! i | i <- schedule]
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
  sum [Map.findWithDefault 1 i (dgLatency graph) | i <- schedule]
