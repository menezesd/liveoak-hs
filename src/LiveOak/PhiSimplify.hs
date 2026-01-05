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
import LiveOak.SSAUtils (substVarsInInstr)
import LiveOak.CFG (CFG, buildCFG)

import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
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

-- | Simplify phi nodes in blocks (takes pre-built CFG)
simplifyPhis :: CFG -> [SSABlock] -> PhiSimplifyResult
simplifyPhis _cfg blocks =
  let -- First pass: identify which phis can be simplified
      (substMap, elimCount) = collectSimplifications blocks
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
  let cfg = buildCFG method
  in simplifyPhis cfg (ssaMethodBlocks method)

-- | Collect simplifiable phis and build substitution map
collectSimplifications :: [SSABlock] -> (Map VarKey SSAExpr, Int)
collectSimplifications blocks =
  let allSimplifications = concatMap simplifyBlockPhis blocks
      substMap = Map.fromList allSimplifications
  in (substMap, length allSimplifications)

-- | Simplify phis in a block
simplifyBlockPhis :: SSABlock -> [(VarKey, SSAExpr)]
simplifyBlockPhis SSABlock{..} =
  mapMaybe simplifyPhi blockPhis

-- | Try to simplify a single phi node
simplifyPhi :: PhiNode -> Maybe (VarKey, SSAExpr)
simplifyPhi PhiNode{..} =
  let phiKey = (ssaName phiVar, ssaVersion phiVar)
      -- Get unique values (excluding self-references) using Map for O(n log n) instead of O(n²)
      nonSelfArgs = [(b, v) | (b, v) <- phiArgs
                            , ssaName v /= ssaName phiVar || ssaVersion v /= ssaVersion phiVar]
      uniqueVals = Map.elems $ Map.fromList
        [((ssaName v, ssaVersion v), v) | v <- map snd nonSelfArgs]
  in case uniqueVals of
    -- All arguments are the same (or all self-references)
    [] -> Nothing  -- Degenerate case
    [v] -> Just (phiKey, SSAUse v)  -- Can replace phi with single value
    -- Cannot simplify
    _ -> Nothing

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
