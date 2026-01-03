{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RecordWildCards #-}

-- | Register Allocation using Graph Coloring.
-- While SAM is a stack machine, this module provides register allocation
-- that can be used for optimization hints or future register-based targets.
module LiveOak.RegAlloc
  ( -- * Register Allocation
    allocateRegisters
  , RegAllocResult(..)

    -- * Interference Graph
  , InterferenceGraph(..)
  , buildInterference
  , colorGraph

    -- * Liveness Analysis
  , LivenessInfo(..)
  , computeLiveness
  ) where

import LiveOak.SSATypes
import LiveOak.CFG

import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Set (Set)
import qualified Data.Set as Set
import Data.List (foldl', sortBy)
import Data.Ord (comparing, Down(..))

--------------------------------------------------------------------------------
-- Types
--------------------------------------------------------------------------------

-- | Number of available registers
type NumRegisters = Int

-- | Register assignment
type RegAssignment = Map String Int

-- | Liveness information for a block
data LivenessInfo = LivenessInfo
  { liveIn :: !(Map BlockId (Set String))   -- ^ Variables live at block entry
  , liveOut :: !(Map BlockId (Set String))  -- ^ Variables live at block exit
  , liveAtPoint :: !(Map (BlockId, Int) (Set String))  -- ^ Live at each instruction
  } deriving (Show)

-- | Interference graph (adjacency set representation)
data InterferenceGraph = InterferenceGraph
  { igNodes :: !(Set String)                    -- ^ All variables
  , igEdges :: !(Map String (Set String))       -- ^ Interference edges
  , igMoveEdges :: !(Set (String, String))      -- ^ Move-related edges (for coalescing)
  } deriving (Show)

-- | Register allocation result
data RegAllocResult = RegAllocResult
  { raAssignment :: !RegAssignment      -- ^ Variable -> register mapping
  , raSpilled :: ![String]              -- ^ Spilled variables (didn't fit in registers)
  , raColorsUsed :: !Int                -- ^ Number of registers used
  } deriving (Show)

--------------------------------------------------------------------------------
-- Liveness Analysis
--------------------------------------------------------------------------------

-- | Compute liveness information
computeLiveness :: CFG -> [SSABlock] -> LivenessInfo
computeLiveness cfg blocks =
  let blockMap = Map.fromList [(blockLabel b, b) | b <- blocks]
      -- Initialize with empty sets
      initIn = Map.fromList [(blockLabel b, Set.empty) | b <- blocks]
      initOut = Map.fromList [(blockLabel b, Set.empty) | b <- blocks]
      -- Iterate until fixed point
      (finalIn, finalOut) = iterateLiveness cfg blockMap initIn initOut
      -- Compute per-instruction liveness
      perInstr = computePerInstrLiveness blockMap finalOut
  in LivenessInfo
    { liveIn = finalIn
    , liveOut = finalOut
    , liveAtPoint = perInstr
    }

-- | Iterate liveness until fixed point
iterateLiveness :: CFG -> Map BlockId SSABlock ->
                   Map BlockId (Set String) -> Map BlockId (Set String) ->
                   (Map BlockId (Set String), Map BlockId (Set String))
iterateLiveness cfg blockMap liveIn liveOut =
  let -- Compute new liveOut: union of liveIn of all successors
      newOut = Map.mapWithKey (computeOut cfg liveIn) liveOut
      -- Compute new liveIn: (liveOut - defs) ∪ uses
      newIn = Map.mapWithKey (computeIn blockMap newOut) liveIn
  in if newIn == liveIn && newOut == liveOut
     then (newIn, newOut)
     else iterateLiveness cfg blockMap newIn newOut

-- | Compute live-out for a block
computeOut :: CFG -> Map BlockId (Set String) -> BlockId -> Set String -> Set String
computeOut cfg liveIn bid _ =
  let succs = successors cfg bid
  in Set.unions [Map.findWithDefault Set.empty s liveIn | s <- succs]

-- | Compute live-in for a block
computeIn :: Map BlockId SSABlock -> Map BlockId (Set String) ->
             BlockId -> Set String -> Set String
computeIn blockMap liveOut bid _ =
  case Map.lookup bid blockMap of
    Nothing -> Set.empty
    Just block ->
      let out = Map.findWithDefault Set.empty bid liveOut
          defs = blockDefs block
          uses = blockUses block
      in Set.union uses (Set.difference out defs)

-- | Get definitions in a block
blockDefs :: SSABlock -> Set String
blockDefs SSABlock{..} = Set.fromList $
  [ssaName (phiVar phi) | phi <- blockPhis] ++
  [ssaName var | SSAAssign var _ <- blockInstrs]

-- | Get uses in a block
blockUses :: SSABlock -> Set String
blockUses SSABlock{..} = Set.unions $
  [Set.fromList [ssaName v | (_, v) <- phiArgs phi] | phi <- blockPhis] ++
  map instrUses blockInstrs

-- | Get uses in an instruction
instrUses :: SSAInstr -> Set String
instrUses = \case
  SSAAssign _ expr -> exprUses expr
  SSAReturn (Just expr) -> exprUses expr
  SSAReturn Nothing -> Set.empty
  SSAJump _ -> Set.empty
  SSABranch cond _ _ -> exprUses cond
  SSAFieldStore target _ _ value -> exprUses target `Set.union` exprUses value
  SSAExprStmt expr -> exprUses expr

-- | Get uses in an expression
exprUses :: SSAExpr -> Set String
exprUses = \case
  SSAUse var -> Set.singleton (ssaName var)
  SSAUnary _ e -> exprUses e
  SSABinary _ l r -> exprUses l `Set.union` exprUses r
  SSATernary c t e -> exprUses c `Set.union` exprUses t `Set.union` exprUses e
  SSACall _ args -> Set.unions (map exprUses args)
  SSAInstanceCall target _ args ->
    exprUses target `Set.union` Set.unions (map exprUses args)
  SSANewObject _ args -> Set.unions (map exprUses args)
  SSAFieldAccess target _ -> exprUses target
  _ -> Set.empty

-- | Compute liveness at each instruction point
computePerInstrLiveness :: Map BlockId SSABlock -> Map BlockId (Set String) ->
                           Map (BlockId, Int) (Set String)
computePerInstrLiveness blockMap liveOut =
  Map.unions [blockInstrLiveness bid block (Map.findWithDefault Set.empty bid liveOut)
             | (bid, block) <- Map.toList blockMap]

-- | Compute per-instruction liveness for a block
blockInstrLiveness :: BlockId -> SSABlock -> Set String -> Map (BlockId, Int) (Set String)
blockInstrLiveness bid SSABlock{..} out =
  let indexed = zip [length blockInstrs - 1, length blockInstrs - 2..] (reverse blockInstrs)
      (_, result) = foldl' go (out, Map.empty) indexed
  in result
  where
    go (live, acc) (idx, instr) =
      let acc' = Map.insert (bid, idx) live acc
          def = case instr of
            SSAAssign var _ -> Set.singleton (ssaName var)
            _ -> Set.empty
          use = instrUses instr
          live' = Set.union use (Set.difference live def)
      in (live', acc')

--------------------------------------------------------------------------------
-- Interference Graph Construction
--------------------------------------------------------------------------------

-- | Build interference graph from liveness information
buildInterference :: [SSABlock] -> LivenessInfo -> InterferenceGraph
buildInterference blocks liveness =
  let allVars = collectAllVars blocks
      -- Variables interfere if they're live at the same point
      edges = buildEdges blocks liveness
      -- Find move-related pairs (for coalescing)
      moves = findMoves blocks
  in InterferenceGraph
    { igNodes = allVars
    , igEdges = edges
    , igMoveEdges = moves
    }

-- | Collect all variables
collectAllVars :: [SSABlock] -> Set String
collectAllVars blocks = Set.unions $ map blockVars blocks
  where
    blockVars SSABlock{..} = Set.fromList $
      [ssaName (phiVar phi) | phi <- blockPhis] ++
      [ssaName v | (_, v) <- concatMap phiArgs blockPhis] ++
      [ssaName var | SSAAssign var _ <- blockInstrs] ++
      Set.toList (Set.unions $ map instrUses blockInstrs)

-- | Build interference edges
buildEdges :: [SSABlock] -> LivenessInfo -> Map String (Set String)
buildEdges blocks liveness =
  foldl' addBlockEdges Map.empty blocks
  where
    addBlockEdges acc block@SSABlock{..} =
      foldl' (addInstrEdges blockLabel liveness) acc (zip [0..] blockInstrs)

    addInstrEdges bid linfo acc (idx, instr) =
      let live = Map.findWithDefault Set.empty (bid, idx) (liveAtPoint linfo)
          def = case instr of
            SSAAssign var _ -> Just (ssaName var)
            _ -> Nothing
      in case def of
        Just d ->
          -- d interferes with everything live at this point (except itself)
          let others = Set.delete d live
          in foldl' (\m v -> addEdge m d v) acc (Set.toList others)
        Nothing -> acc

    addEdge m v1 v2 =
      let m' = Map.insertWith Set.union v1 (Set.singleton v2) m
      in Map.insertWith Set.union v2 (Set.singleton v1) m'

-- | Find move-related pairs (for coalescing)
findMoves :: [SSABlock] -> Set (String, String)
findMoves blocks = Set.fromList $ concatMap blockMoves blocks
  where
    blockMoves SSABlock{..} = concat
      [ [(ssaName (phiVar phi), ssaName v) | (_, v) <- phiArgs phi]
      | phi <- blockPhis
      ] ++
      [ (ssaName var, ssaName src)
      | SSAAssign var (SSAUse src) <- blockInstrs
      ]

--------------------------------------------------------------------------------
-- Graph Coloring
--------------------------------------------------------------------------------

-- | Color the interference graph using a greedy algorithm
colorGraph :: NumRegisters -> InterferenceGraph -> RegAllocResult
colorGraph numRegs graph =
  let -- Sort nodes by degree (high degree first - Chaitin's heuristic)
      nodes = sortBy (comparing (Down . nodeDegree graph)) (Set.toList $ igNodes graph)
      -- Try to color each node
      (assignment, spilled) = foldl' (tryColor numRegs graph) (Map.empty, []) nodes
  in RegAllocResult
    { raAssignment = assignment
    , raSpilled = spilled
    , raColorsUsed = if Map.null assignment then 0 else maximum (Map.elems assignment) + 1
    }

-- | Get degree of a node
nodeDegree :: InterferenceGraph -> String -> Int
nodeDegree graph node = Set.size $ Map.findWithDefault Set.empty node (igEdges graph)

-- | Try to color a node
tryColor :: NumRegisters -> InterferenceGraph ->
            (RegAssignment, [String]) -> String -> (RegAssignment, [String])
tryColor numRegs graph (assignment, spilled) node =
  let neighbors = Map.findWithDefault Set.empty node (igEdges graph)
      usedColors = Set.fromList [c | n <- Set.toList neighbors,
                                    Just c <- [Map.lookup n assignment]]
      availableColors = [c | c <- [0..numRegs-1], not (Set.member c usedColors)]
  in case availableColors of
    (c:_) -> (Map.insert node c assignment, spilled)
    [] -> (assignment, node : spilled)  -- Spill this variable

--------------------------------------------------------------------------------
-- Register Allocation
--------------------------------------------------------------------------------

-- | Allocate registers for a method
allocateRegisters :: NumRegisters -> CFG -> [SSABlock] -> RegAllocResult
allocateRegisters numRegs cfg blocks =
  let -- Compute liveness
      liveness = computeLiveness cfg blocks
      -- Build interference graph
      interference = buildInterference blocks liveness
      -- Color the graph
      result = colorGraph numRegs interference
  in result

--------------------------------------------------------------------------------
-- Spill Code Generation
--------------------------------------------------------------------------------

-- | Generate spill code for spilled variables
generateSpillCode :: [String] -> [SSABlock] -> [SSABlock]
generateSpillCode spilled = map (spillBlock spilled)
  where
    spilledSet = Set.fromList spilled

    spillBlock vars block@SSABlock{..} =
      block { blockInstrs = concatMap (spillInstr vars spilledSet) blockInstrs }

    spillInstr vars spilledVars instr =
      let -- Reload uses of spilled variables before the instruction
          uses = Set.intersection spilledVars (instrUses instr)
          reloads = [mkReload v | v <- Set.toList uses]
          -- Store definitions of spilled variables after the instruction
          def = case instr of
            SSAAssign var _ | Set.member (ssaName var) spilledVars ->
              [mkStore (ssaName var)]
            _ -> []
      in reloads ++ [instr] ++ def

    mkReload var = SSAExprStmt (SSACall ("__reload_" ++ var) [])
    mkStore var = SSAExprStmt (SSACall ("__store_" ++ var) [])

--------------------------------------------------------------------------------
-- Coalescing
--------------------------------------------------------------------------------

-- | Try to coalesce move-related variables
coalesce :: InterferenceGraph -> RegAssignment -> RegAssignment
coalesce graph assignment =
  foldl' tryCoalesce assignment (Set.toList $ igMoveEdges graph)
  where
    tryCoalesce assign (v1, v2) =
      -- Can coalesce if:
      -- 1. Both have the same color, OR
      -- 2. They don't interfere and one doesn't have a color yet
      case (Map.lookup v1 assign, Map.lookup v2 assign) of
        (Just c1, Just c2) | c1 == c2 -> assign  -- Already coalesced
        (Just c1, Nothing) | not (interferes graph v1 v2) ->
          Map.insert v2 c1 assign
        (Nothing, Just c2) | not (interferes graph v1 v2) ->
          Map.insert v1 c2 assign
        _ -> assign  -- Can't coalesce

    interferes g a b = Set.member b (Map.findWithDefault Set.empty a (igEdges g))
