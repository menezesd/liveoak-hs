{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RecordWildCards #-}

-- | Copy Coalescing for SSA.
-- Eliminates unnecessary copies introduced during phi node lowering
-- by merging variables that can share the same storage location.
module LiveOak.Coalesce
  ( -- * Copy Coalescing
    coalescePhiCopies
  , CoalesceResult(..)

    -- * Interference Graph
  , InterferenceGraph
  , buildInterferenceGraph
  , interferes
  ) where

import LiveOak.CFG
import LiveOak.SSATypes
import LiveOak.Dominance

import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Set (Set)
import qualified Data.Set as Set
import Data.List (foldl')
import Control.Monad.State.Strict

--------------------------------------------------------------------------------
-- Interference Graph
--------------------------------------------------------------------------------

-- | Interference graph - edges between variables that cannot share storage
type InterferenceGraph = Map String (Set String)

-- | Build interference graph from liveness information
-- Two variables interfere if they are both live at the same point
buildInterferenceGraph :: CFG -> DomTree -> [SSABlock] -> InterferenceGraph
buildInterferenceGraph cfg domTree blocks =
  let -- Compute live-out sets for each block
      liveOut = computeLiveness cfg blocks
      -- Build interference edges
  in foldl' (addBlockInterference liveOut) Map.empty blocks

-- | Compute liveness (simplified - full liveness would need dataflow)
computeLiveness :: CFG -> [SSABlock] -> Map BlockId (Set String)
computeLiveness cfg blocks =
  let blockMap = Map.fromList [(blockLabel b, b) | b <- blocks]
      -- Initialize with uses in successors
      initial = Map.fromList [(blockLabel b, Set.empty) | b <- blocks]
      -- Iterate until fixed point
  in iterateLiveness cfg blockMap initial

-- | Iterate liveness computation
iterateLiveness :: CFG -> Map BlockId SSABlock -> Map BlockId (Set String) -> Map BlockId (Set String)
iterateLiveness cfg blockMap liveOut =
  let liveOut' = Map.mapWithKey (updateLiveOut cfg blockMap liveOut) liveOut
  in if liveOut' == liveOut
     then liveOut
     else iterateLiveness cfg blockMap liveOut'

-- | Update live-out for a block
updateLiveOut :: CFG -> Map BlockId SSABlock -> Map BlockId (Set String) -> BlockId -> Set String -> Set String
updateLiveOut cfg blockMap liveOut bid _ =
  -- Live-out = union of live-in of all successors
  let succs = successors cfg bid
      liveIns = map (computeLiveIn blockMap liveOut) succs
  in Set.unions liveIns

-- | Compute live-in for a block
computeLiveIn :: Map BlockId SSABlock -> Map BlockId (Set String) -> BlockId -> Set String
computeLiveIn blockMap liveOut bid =
  case Map.lookup bid blockMap of
    Nothing -> Set.empty
    Just block ->
      let out = Map.findWithDefault Set.empty bid liveOut
          -- Live-in = (live-out - defs) + uses
          defs = blockDefs block
          uses = blockUses block
      in Set.union uses (Set.difference out defs)

-- | Get all definitions in a block
blockDefs :: SSABlock -> Set String
blockDefs SSABlock{..} = Set.fromList $
  [ssaName (phiVar phi) | phi <- blockPhis] ++
  [ssaName var | SSAAssign var _ <- blockInstrs]

-- | Get all uses in a block
blockUses :: SSABlock -> Set String
blockUses SSABlock{..} = Set.unions $
  [phiUses phi | phi <- blockPhis] ++
  map instrUses blockInstrs
  where
    phiUses PhiNode{..} = Set.fromList [ssaName v | (_, v) <- phiArgs]

    instrUses = \case
      SSAAssign _ expr -> exprUses expr
      SSAReturn (Just expr) -> exprUses expr
      SSAReturn Nothing -> Set.empty
      SSAJump _ -> Set.empty
      SSABranch cond _ _ -> exprUses cond
      SSAFieldStore target _ _ value -> exprUses target `Set.union` exprUses value
      SSAExprStmt expr -> exprUses expr

    exprUses = \case
      SSAUse var -> Set.singleton (ssaName var)
      SSAUnary _ e -> exprUses e
      SSABinary _ l r -> exprUses l `Set.union` exprUses r
      SSATernary c t e -> exprUses c `Set.union` exprUses t `Set.union` exprUses e
      SSACall _ args -> Set.unions (map exprUses args)
      SSAInstanceCall target _ args -> exprUses target `Set.union` Set.unions (map exprUses args)
      SSANewObject _ args -> Set.unions (map exprUses args)
      SSAFieldAccess target _ -> exprUses target
      _ -> Set.empty

-- | Add interference edges for a block
addBlockInterference :: Map BlockId (Set String) -> InterferenceGraph -> SSABlock -> InterferenceGraph
addBlockInterference liveOut graph block =
  let live = Map.findWithDefault Set.empty (blockLabel block) liveOut
      -- All live variables interfere with each other
      liveList = Set.toList live
  in foldl' (addEdges liveList) graph liveList
  where
    addEdges vars g v =
      let others = Set.fromList $ filter (/= v) vars
      in Map.insertWith Set.union v others g

-- | Check if two variables interfere
interferes :: InterferenceGraph -> String -> String -> Bool
interferes graph v1 v2 =
  case Map.lookup v1 graph of
    Just neighbors -> Set.member v2 neighbors
    Nothing -> False

--------------------------------------------------------------------------------
-- Copy Coalescing
--------------------------------------------------------------------------------

-- | Result of copy coalescing
data CoalesceResult = CoalesceResult
  { coalescedVars :: !(Map String String)  -- ^ Variable -> representative
  , eliminatedCopies :: !Int               -- ^ Number of eliminated copies
  } deriving (Show)

-- | Coalesce phi-related copies
coalescePhiCopies :: CFG -> DomTree -> [SSABlock] -> CoalesceResult
coalescePhiCopies cfg domTree blocks =
  let -- Build interference graph
      interference = buildInterferenceGraph cfg domTree blocks
      -- Find copy-related pairs from phi nodes
      copyPairs = findPhiCopies blocks
      -- Try to coalesce each pair
      (coalesced, count) = foldl' (tryCoalesce interference) (Map.empty, 0) copyPairs
  in CoalesceResult
    { coalescedVars = coalesced
    , eliminatedCopies = count
    }

-- | Find copy-related pairs from phi nodes
findPhiCopies :: [SSABlock] -> [(String, String)]
findPhiCopies blocks = concatMap blockPhiCopies blocks
  where
    blockPhiCopies SSABlock{..} =
      [ (ssaName (phiVar phi), ssaName argVar)
      | phi <- blockPhis
      , (_, argVar) <- phiArgs phi
      ]

-- | Try to coalesce a pair of variables
tryCoalesce :: InterferenceGraph -> (Map String String, Int) -> (String, String) -> (Map String String, Int)
tryCoalesce interference (coalesced, count) (v1, v2)
  -- Already coalesced to same representative
  | findRep coalesced v1 == findRep coalesced v2 = (coalesced, count)
  -- Interfere - cannot coalesce
  | interferes interference (findRep coalesced v1) (findRep coalesced v2) = (coalesced, count)
  -- Can coalesce
  | otherwise =
      let rep1 = findRep coalesced v1
          rep2 = findRep coalesced v2
          -- Use lexicographically smaller as representative
          (keepRep, mergeVar) = if rep1 <= rep2 then (rep1, rep2) else (rep2, rep1)
      in (Map.insert mergeVar keepRep coalesced, count + 1)

-- | Find representative of a variable (with path compression)
findRep :: Map String String -> String -> String
findRep coalesced v =
  case Map.lookup v coalesced of
    Nothing -> v
    Just rep -> findRep coalesced rep

--------------------------------------------------------------------------------
-- Apply Coalescing
--------------------------------------------------------------------------------

-- | Apply coalescing to a program (rename variables)
applyCoalescing :: CoalesceResult -> [SSABlock] -> [SSABlock]
applyCoalescing result = map (applyToBlock (coalescedVars result))

-- | Apply coalescing to a block
applyToBlock :: Map String String -> SSABlock -> SSABlock
applyToBlock coalesced block@SSABlock{..} = block
  { blockPhis = map (applyToPhi coalesced) blockPhis
  , blockInstrs = map (applyToInstr coalesced) blockInstrs
  }

-- | Apply coalescing to a phi node
applyToPhi :: Map String String -> PhiNode -> PhiNode
applyToPhi coalesced phi@PhiNode{..} = phi
  { phiVar = renameVar coalesced phiVar
  , phiArgs = [(pred', renameVar coalesced var) | (pred', var) <- phiArgs]
  }

-- | Apply coalescing to an instruction
applyToInstr :: Map String String -> SSAInstr -> SSAInstr
applyToInstr coalesced = \case
  SSAAssign var expr -> SSAAssign (renameVar coalesced var) (applyToExpr coalesced expr)
  SSAReturn mexpr -> SSAReturn (fmap (applyToExpr coalesced) mexpr)
  SSAJump target -> SSAJump target
  SSABranch cond t e -> SSABranch (applyToExpr coalesced cond) t e
  SSAFieldStore target field off value ->
    SSAFieldStore (applyToExpr coalesced target) field off (applyToExpr coalesced value)
  SSAExprStmt expr -> SSAExprStmt (applyToExpr coalesced expr)

-- | Apply coalescing to an expression
applyToExpr :: Map String String -> SSAExpr -> SSAExpr
applyToExpr coalesced = \case
  SSAUse var -> SSAUse (renameVar coalesced var)
  SSAUnary op e -> SSAUnary op (applyToExpr coalesced e)
  SSABinary op l r -> SSABinary op (applyToExpr coalesced l) (applyToExpr coalesced r)
  SSATernary c t e -> SSATernary (applyToExpr coalesced c) (applyToExpr coalesced t) (applyToExpr coalesced e)
  SSACall name args -> SSACall name (map (applyToExpr coalesced) args)
  SSAInstanceCall target method args ->
    SSAInstanceCall (applyToExpr coalesced target) method (map (applyToExpr coalesced) args)
  SSANewObject cn args -> SSANewObject cn (map (applyToExpr coalesced) args)
  SSAFieldAccess target field -> SSAFieldAccess (applyToExpr coalesced target) field
  other -> other

-- | Rename a variable according to coalescing
renameVar :: Map String String -> SSAVar -> SSAVar
renameVar coalesced var =
  let rep = findRep coalesced (ssaName var)
  in var { ssaName = rep }
