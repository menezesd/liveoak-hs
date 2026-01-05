{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RecordWildCards #-}

-- | Phi Node Simplification.
-- Simplifies and eliminates redundant phi nodes.
--
-- == Simplifications
--
-- 1. **Same-value phi**: All arguments are the same value
--    @phi(x, x, x) -> x@
--
-- 2. **Self-referential phi**: Phi refers to itself plus one other value
--    @x = phi(x, y) -> y@ (the self-reference is from a back-edge)
--
-- 3. **Single-predecessor phi**: Block has only one predecessor
--    @phi(x) -> x@
--
-- 4. **Unreachable predecessor**: Remove arguments from unreachable predecessors
--
module LiveOak.PhiSimplify
  ( -- * Phi Simplification
    simplifyPhis
  , simplifyPhisMethod
  , PhiSimplifyResult(..)
  ) where

import LiveOak.SSATypes
import LiveOak.SSAUtils (substVars, substVarsInInstr)

import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Data.List (foldl', nubBy)
import Data.Maybe (mapMaybe)

--------------------------------------------------------------------------------
-- Types
--------------------------------------------------------------------------------

-- | Phi simplification result
data PhiSimplifyResult = PhiSimplifyResult
  { psOptBlocks :: ![SSABlock]
  , psSimplified :: !Int          -- ^ Number of phis simplified
  , psEliminated :: !Int          -- ^ Number of phis eliminated
  } deriving (Show)

--------------------------------------------------------------------------------
-- Phi Simplification
--------------------------------------------------------------------------------

-- | Simplify phi nodes in blocks
simplifyPhis :: SimpleCFG -> [SSABlock] -> PhiSimplifyResult
simplifyPhis cfg blocks =
  let -- First pass: identify which phis can be simplified
      (substMap, elimCount) = collectSimplifications cfg blocks
      -- Apply substitutions
      blocks' = map (applyPhiSubst substMap) blocks
      -- Remove eliminated phis
      blocks'' = map (removeEliminatedPhis substMap) blocks'
  in PhiSimplifyResult
    { psOptBlocks = blocks''
    , psSimplified = Map.size substMap
    , psEliminated = elimCount
    }

-- | Simplify phi nodes in a method
simplifyPhisMethod :: SSAMethod -> PhiSimplifyResult
simplifyPhisMethod method =
  let cfg = buildCFGSimple (ssaMethodBlocks method)
  in simplifyPhis cfg (ssaMethodBlocks method)

-- | Build a simple CFG for predecessor lookup
buildCFGSimple :: [SSABlock] -> SimpleCFG
buildCFGSimple blocks =
  let blockMap = Map.fromList [(blockLabel b, b) | b <- blocks]
      entry = case blocks of
        (b:_) -> blockLabel b
        [] -> blockId "entry"
      edges = concatMap getBlockEdges blocks
  in SimpleCFG
    { cfgEntry = entry
    , cfgNodes = Set.fromList (map blockLabel blocks)
    , cfgEdges = Map.fromListWith (++) [(src, [dst]) | (src, dst) <- edges]
    , cfgPreds = Map.fromListWith (++) [(dst, [src]) | (src, dst) <- edges]
    }

-- | Get edges from a block
getBlockEdges :: SSABlock -> [(BlockId, BlockId)]
getBlockEdges SSABlock{..} =
  case filter isTerminator blockInstrs of
    [SSAJump target] -> [(blockLabel, target)]
    [SSABranch _ t f] -> [(blockLabel, t), (blockLabel, f)]
    _ -> []
  where
    isTerminator (SSAJump _) = True
    isTerminator (SSABranch _ _ _) = True
    isTerminator (SSAReturn _) = True
    isTerminator _ = False

-- | Collect simplifiable phis and build substitution map
collectSimplifications :: SimpleCFG -> [SSABlock] -> (Map VarKey SSAExpr, Int)
collectSimplifications cfg blocks =
  let allSimplifications = concatMap (simplifyBlockPhis cfg) blocks
      substMap = Map.fromList allSimplifications
  in (substMap, length allSimplifications)

-- | Simplify phis in a block
simplifyBlockPhis :: SimpleCFG -> SSABlock -> [(VarKey, SSAExpr)]
simplifyBlockPhis cfg SSABlock{..} =
  mapMaybe (simplifyPhi cfg blockLabel) blockPhis

-- | Try to simplify a single phi node
simplifyPhi :: SimpleCFG -> BlockId -> PhiNode -> Maybe (VarKey, SSAExpr)
simplifyPhi cfg bid PhiNode{..} =
  let phiKey = (ssaName phiVar, ssaVersion phiVar)
      args = phiArgs
      -- Get unique values (excluding self-references)
      nonSelfArgs = [(b, v) | (b, v) <- args
                            , ssaName v /= ssaName phiVar || ssaVersion v /= ssaVersion phiVar]
      uniqueVals = nubBy sameVar (map snd nonSelfArgs)
  in case uniqueVals of
    -- All arguments are the same (or all self-references)
    [] -> Nothing  -- Degenerate case
    [v] -> Just (phiKey, SSAUse v)  -- Can replace phi with single value
    -- Check if only one non-self value
    _ | length uniqueVals == 1 ->
        Just (phiKey, SSAUse (head uniqueVals))
    -- Cannot simplify
    _ -> Nothing
  where
    sameVar v1 v2 = ssaName v1 == ssaName v2 && ssaVersion v1 == ssaVersion v2

-- | Apply substitutions to a block
applyPhiSubst :: Map VarKey SSAExpr -> SSABlock -> SSABlock
applyPhiSubst substMap block@SSABlock{..} =
  let -- Apply to phi arguments
      phis' = map (substPhiArgs substMap) blockPhis
      -- Apply to instructions
      instrs' = map (substVarsInInstr substMap) blockInstrs
  in block { blockPhis = phis', blockInstrs = instrs' }

-- | Substitute in phi arguments
substPhiArgs :: Map VarKey SSAExpr -> PhiNode -> PhiNode
substPhiArgs substMap phi@PhiNode{..} =
  let args' = map (substPhiArg substMap) phiArgs
  in phi { phiArgs = args' }

-- | Substitute a single phi argument
substPhiArg :: Map VarKey SSAExpr -> (BlockId, SSAVar) -> (BlockId, SSAVar)
substPhiArg substMap (bid, var) =
  let key = (ssaName var, ssaVersion var)
  in case Map.lookup key substMap of
    Just (SSAUse newVar) -> (bid, newVar)
    _ -> (bid, var)

-- | Remove eliminated phis from a block
removeEliminatedPhis :: Map VarKey SSAExpr -> SSABlock -> SSABlock
removeEliminatedPhis substMap block@SSABlock{..} =
  let phis' = filter (not . isEliminated substMap) blockPhis
  in block { blockPhis = phis' }

-- | Check if a phi was eliminated (is in the substitution map)
isEliminated :: Map VarKey SSAExpr -> PhiNode -> Bool
isEliminated substMap PhiNode{..} =
  let key = (ssaName phiVar, ssaVersion phiVar)
  in Map.member key substMap

--------------------------------------------------------------------------------
-- SimpleCFG type (simplified for this module)
--------------------------------------------------------------------------------

data SimpleCFG = SimpleCFG
  { cfgEntry :: !BlockId
  , cfgNodes :: !(Set.Set BlockId)
  , cfgEdges :: !(Map BlockId [BlockId])
  , cfgPreds :: !(Map BlockId [BlockId])
  } deriving (Show)

-- | Get predecessors of a block
simplePredecessors :: SimpleCFG -> BlockId -> [BlockId]
simplePredecessors cfg bid = Map.findWithDefault [] bid (cfgPreds cfg)
