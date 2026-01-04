{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RecordWildCards #-}

-- | Copy Coalescing for SSA.
-- Eliminates unnecessary copies introduced during phi node lowering
-- by merging variables that can share the same storage location.
module LiveOak.Coalesce
  ( -- * Copy Coalescing
    coalescePhiCopies
  , applyCoalescing
  , CoalesceResult(..)

    -- * Interference Graph
  , InterferenceGraph
  , buildInterferenceGraph
  , interferes
  ) where

import LiveOak.CFG
import LiveOak.SSATypes
import LiveOak.Dominance
import LiveOak.RegAlloc (LivenessInfo(..), computeLiveness)
import LiveOak.MapUtils (lookupSet)

import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Set (Set)
import qualified Data.Set as Set
import Data.List (foldl')

--------------------------------------------------------------------------------
-- Interference Graph
--------------------------------------------------------------------------------

-- | Interference graph - edges between variables that cannot share storage
type InterferenceGraph = Map String (Set String)

-- | Build interference graph from liveness information
-- Two variables interfere if they are both live at the same point
buildInterferenceGraph :: CFG -> DomTree -> [SSABlock] -> InterferenceGraph
buildInterferenceGraph cfg _domTree blocks =
  let -- Compute live-out sets for each block using RegAlloc's liveness
      liveness = computeLiveness cfg blocks
      -- Build interference edges
  in foldl' (addBlockInterference (liveOut liveness)) Map.empty blocks

-- | Add interference edges for a block
addBlockInterference :: Map BlockId (Set String) -> InterferenceGraph -> SSABlock -> InterferenceGraph
addBlockInterference liveOutMap graph block =
  let live = lookupSet (blockLabel block) liveOutMap
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
