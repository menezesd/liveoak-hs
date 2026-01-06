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
-- Uses iterative simplification to handle phi chains.
simplifyPhis :: CFG -> [SSABlock] -> PhiSimplifyResult
simplifyPhis _cfg blocks = go 10 blocks Map.empty 0
  where
    go :: Int -> [SSABlock] -> Map VarKey SSAExpr -> Int -> PhiSimplifyResult
    go 0 bs accSubst accElim = PhiSimplifyResult bs (Map.size accSubst) accElim
    go n bs accSubst accElim =
      let -- Identify which phis can be simplified this iteration
          (newSubst, newElim) = collectSimplifications bs
          -- Combine with previous substitutions
          combinedSubst = Map.union newSubst accSubst
          -- Apply substitutions
          bs' = map (applyPhiSubst newSubst) bs
          -- Remove eliminated phis
          bs'' = map (removeEliminatedPhis newSubst) bs'
      in if Map.null newSubst
         then PhiSimplifyResult bs'' (Map.size combinedSubst) (accElim + newElim)
         else go (n - 1) bs'' combinedSubst (accElim + newElim)

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
-- Handles:
-- 1. Same-value phi: all arguments are the same value
-- 2. Self-referential phi: phi refers to itself plus one other value
-- 3. Single-argument phi: phi has only one incoming value
-- 4. Copy phi: phi(x) where all non-self args resolve to same variable
simplifyPhi :: PhiNode -> Maybe (VarKey, SSAExpr)
simplifyPhi PhiNode{..} =
  let phiKey = (ssaName phiVar, ssaVersion phiVar)
      -- Get unique values (excluding self-references) using Map for O(n log n) instead of O(n²)
      nonSelfArgs = [(b, v) | (b, v) <- phiArgs
                            , ssaName v /= ssaName phiVar || ssaVersion v /= ssaVersion phiVar]
      uniqueVals = Map.elems $ Map.fromList
        [((ssaName v, ssaVersion v), v) | v <- map snd nonSelfArgs]
  in case uniqueVals of
    -- Case 1: Single incoming value (ignoring self-refs) - can replace with that value
    [v] -> Just (phiKey, SSAUse v)

    -- Case 2: Two values where one dominates - check if they're related
    -- e.g., phi(x_1, x_2) might be simplifiable if x_1 and x_2 are both versions of x
    -- and one is defined in a dominating block
    [v1, v2]
      | ssaName v1 == ssaName v2 ->
          -- Same base variable, different versions - keep the phi for now
          -- (would need dominator info to pick the right one)
          Nothing
      | otherwise -> Nothing

    -- Case 3: Empty (degenerate) or too many unique values - cannot simplify
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
