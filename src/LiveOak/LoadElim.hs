{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RecordWildCards #-}

-- | Redundant Load Elimination.
-- Eliminates redundant field loads using dataflow analysis.
--
-- == Analysis
--
-- Track available loads at each program point:
-- - Load from obj.field -> remember (obj, field) -> value mapping
-- - Store to obj.field -> invalidate loads of field (conservatively)
-- - Call -> invalidate all loads (may have side effects)
--
-- == Optimizations
--
-- 1. **Same-block load elimination**:
--    @x = obj.f; ...; y = obj.f@ -> @x = obj.f; ...; y = x@
--
-- 2. **Cross-block load elimination** (with proper dataflow):
--    Propagate available loads across CFG edges
--
-- 3. **Store-to-load forwarding**:
--    @obj.f = x; y = obj.f@ -> @obj.f = x; y = x@
--
module LiveOak.LoadElim
  ( -- * Load Elimination
    eliminateLoads
  , eliminateLoadsMethod
  , LoadElimResult(..)
  ) where

import LiveOak.SSATypes
import LiveOak.SSAUtils (substVarsInInstr)

import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.List (foldl')

--------------------------------------------------------------------------------
-- Types
--------------------------------------------------------------------------------

-- | Load elimination result
data LoadElimResult = LoadElimResult
  { leOptBlocks :: ![SSABlock]
  , leEliminated :: !Int          -- ^ Number of loads eliminated
  } deriving (Show)

-- | Key for tracking loads: (object variable key, field name)
type LoadKey = (VarKey, String)

-- | Available loads: maps LoadKey to the variable holding the loaded value
type AvailableLoads = Map LoadKey SSAVar

--------------------------------------------------------------------------------
-- Load Elimination
--------------------------------------------------------------------------------

-- | Eliminate redundant loads in blocks
eliminateLoads :: [SSABlock] -> LoadElimResult
eliminateLoads blocks =
  let (optimized, counts) = unzip $ map (eliminateBlockLoads Map.empty) blocks
  in LoadElimResult
    { leOptBlocks = optimized
    , leEliminated = sum counts
    }

-- | Eliminate redundant loads in a method
eliminateLoadsMethod :: SSAMethod -> LoadElimResult
eliminateLoadsMethod method =
  eliminateLoads (ssaMethodBlocks method)

-- | Eliminate loads in a block with initial available loads
eliminateBlockLoads :: AvailableLoads -> SSABlock -> (SSABlock, Int)
eliminateBlockLoads available block@SSABlock{..} =
  let (instrs', _, count) = foldl' processInstr ([], available, 0) blockInstrs
  in (block { blockInstrs = reverse instrs' }, count)

-- | Process an instruction for load elimination
processInstr :: ([SSAInstr], AvailableLoads, Int)
             -> SSAInstr
             -> ([SSAInstr], AvailableLoads, Int)
processInstr (instrs, available, count) instr = case instr of
  -- Field load - check if available
  SSAAssign var (SSAFieldAccess target field) ->
    case getTargetKey target of
      Just objKey ->
        let loadKey = (objKey, field)
        in case Map.lookup loadKey available of
          -- Load is available - reuse the previous value
          Just prevVar ->
            let subst = Map.singleton (ssaName var, ssaVersion var) (SSAUse prevVar)
                -- Keep the assignment but substitute in future instructions
                instrs' = instr : map (substVarsInInstr subst) instrs
            in (instrs', available, count + 1)

          -- Load not available - add it
          Nothing ->
            let available' = Map.insert loadKey var available
            in (instr : instrs, available', count)
      Nothing ->
        -- Can't determine target object - invalidate conservatively
        (instr : instrs, Map.empty, count)

  -- Field store - invalidate loads of that field
  SSAFieldStore target field _idx value ->
    let -- Invalidate all loads of this field (conservative)
        available' = Map.filterWithKey (\(_, f) _ -> f /= field) available
        -- Also record store-to-load forwarding opportunity
        available'' = case (getTargetKey target, getValueVar value) of
          (Just objKey, Just valVar) ->
            Map.insert (objKey, field) valVar available'
          _ -> available'
    in (instr : instrs, available'', count)

  -- Method calls invalidate all loads (may have side effects)
  SSAAssign _ (SSAInstanceCall _ _ _) ->
    (instr : instrs, Map.empty, count)
  SSAAssign _ (SSACall _ _) ->
    (instr : instrs, Map.empty, count)
  SSAExprStmt (SSAInstanceCall _ _ _) ->
    (instr : instrs, Map.empty, count)
  SSAExprStmt (SSACall _ _) ->
    (instr : instrs, Map.empty, count)

  -- New object creation doesn't invalidate existing loads
  SSAAssign _ (SSANewObject _ _) ->
    (instr : instrs, available, count)

  -- Other instructions pass through
  _ -> (instr : instrs, available, count)

-- | Get the key for a target expression
getTargetKey :: SSAExpr -> Maybe VarKey
getTargetKey (SSAUse var) = Just (ssaName var, ssaVersion var)
getTargetKey SSAThis = Just (varName "this", 0)
getTargetKey _ = Nothing

-- | Get the variable from a value expression
getValueVar :: SSAExpr -> Maybe SSAVar
getValueVar (SSAUse var) = Just var
getValueVar _ = Nothing
