{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RecordWildCards #-}

-- | Copy Propagation.
-- Replaces uses of copied variables with their source.
--
-- == Example
--
-- @
-- Before:                After:
--   x = y                  x = y        -- may become dead
--   z = x + 1              z = y + 1    -- x replaced with y
--   return z               return z
-- @
--
-- == Algorithm
--
-- 1. Find all copy instructions (x = y where y is a variable)
-- 2. Build a substitution map
-- 3. Apply substitutions transitively (if x = y and y = z, then x = z)
-- 4. Replace all uses with their ultimate source
--
module LiveOak.CopyProp
  ( -- * Copy Propagation
    propagateCopies
  , propagateCopiesMethod
  , CopyPropResult(..)
  ) where

import LiveOak.SSATypes
import LiveOak.SSAUtils (substVars, substVarsInInstr)

import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.List (foldl')

--------------------------------------------------------------------------------
-- Types
--------------------------------------------------------------------------------

-- | Copy propagation result
data CopyPropResult = CopyPropResult
  { cpOptBlocks :: ![SSABlock]
  , cpPropagated :: !Int          -- ^ Number of copies propagated
  } deriving (Show)

--------------------------------------------------------------------------------
-- Copy Propagation
--------------------------------------------------------------------------------

-- | Propagate copies in a list of blocks
propagateCopies :: [SSABlock] -> CopyPropResult
propagateCopies blocks =
  let -- Collect all copies from all blocks
      copies = concatMap collectBlockCopies blocks
      -- Build transitive substitution map
      substMap = buildSubstMap copies
      -- Apply substitutions to all blocks
      (optimized, counts) = unzip $ map (applySubstBlock substMap) blocks
  in CopyPropResult
    { cpOptBlocks = optimized
    , cpPropagated = sum counts
    }

-- | Propagate copies in a method
propagateCopiesMethod :: SSAMethod -> CopyPropResult
propagateCopiesMethod method =
  let result = propagateCopies (ssaMethodBlocks method)
  in result

-- | Collect copy instructions from a block
-- A copy is: x = y (where y is just a variable use)
collectBlockCopies :: SSABlock -> [(VarKey, VarKey)]
collectBlockCopies SSABlock{..} =
  [ (destKey, srcKey)
  | SSAAssign dest (SSAUse src) <- blockInstrs
  , let destKey = (ssaName dest, ssaVersion dest)
  , let srcKey = (ssaName src, ssaVersion src)
  ]
  ++
  -- Also collect from phi nodes where all args are the same
  [ (phiKey, srcKey)
  | PhiNode{..} <- blockPhis
  , let phiKey = (ssaName phiVar, ssaVersion phiVar)
  , allSame (map snd phiArgs)
  , (_, src) <- take 1 phiArgs
  , let srcKey = (ssaName src, ssaVersion src)
  ]
  where
    allSame [] = False
    allSame (x:xs) = all (sameVar x) xs
    sameVar v1 v2 = ssaName v1 == ssaName v2 && ssaVersion v1 == ssaVersion v2

-- | Build a transitive substitution map
-- If x = y and y = z, then x maps to z
buildSubstMap :: [(VarKey, VarKey)] -> Map VarKey SSAExpr
buildSubstMap copies =
  let -- Initial map: dest -> src
      initial = Map.fromList [(dest, src) | (dest, src) <- copies]
      -- Resolve transitively
      resolved = Map.map (resolveChain initial) initial
  in Map.map (\vk -> SSAUse (SSAVar (fst vk) (snd vk) Nothing)) resolved

-- | Resolve a copy chain to find the ultimate source
resolveChain :: Map VarKey VarKey -> VarKey -> VarKey
resolveChain copies = go 100  -- Limit to prevent infinite loops
  where
    go 0 key = key
    go n key = case Map.lookup key copies of
      Just next | next /= key -> go (n - 1) next
      _ -> key

-- | Apply substitutions to a block
applySubstBlock :: Map VarKey SSAExpr -> SSABlock -> (SSABlock, Int)
applySubstBlock substMap block@SSABlock{..} =
  let -- Apply to phi nodes
      (phis', phiCount) = unzip $ map (applySubstPhi substMap) blockPhis
      -- Apply to instructions
      (instrs', instrCount) = unzip $ map (applySubstInstr substMap) blockInstrs
  in (block { blockPhis = phis', blockInstrs = instrs' }, sum phiCount + sum instrCount)

-- | Apply substitutions to a phi node
applySubstPhi :: Map VarKey SSAExpr -> PhiNode -> (PhiNode, Int)
applySubstPhi substMap phi@PhiNode{..} =
  let (args', counts) = unzip $ map (applySubstPhiArg substMap) phiArgs
  in (phi { phiArgs = args' }, sum counts)

-- | Apply substitutions to a phi argument
applySubstPhiArg :: Map VarKey SSAExpr -> (BlockId, SSAVar) -> ((BlockId, SSAVar), Int)
applySubstPhiArg substMap (bid, var) =
  let key = (ssaName var, ssaVersion var)
  in case Map.lookup key substMap of
    Just (SSAUse newVar) -> ((bid, newVar), 1)
    _ -> ((bid, var), 0)

-- | Apply substitutions to an instruction
applySubstInstr :: Map VarKey SSAExpr -> SSAInstr -> (SSAInstr, Int)
applySubstInstr substMap instr =
  let instr' = substVarsInInstr substMap instr
      -- Count substitutions (rough estimate based on whether instr changed)
      count = if instr' == instr then 0 else 1
  in (instr', count)
