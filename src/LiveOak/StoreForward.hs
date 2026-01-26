{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RecordWildCards #-}

-- | Store-to-Load Forwarding across basic blocks.
-- Extends LoadElim with cross-block forwarding using dataflow analysis.
--
-- == Algorithm
-- Uses a forward dataflow analysis to track available stores:
-- - GEN[B]: stores generated in block B
-- - KILL[B]: stores killed in block B (by stores to same location or calls)
-- - IN[B] = ∩ OUT[P] for all predecessors P
-- - OUT[B] = (IN[B] - KILL[B]) ∪ GEN[B]
--
-- Then replaces loads with forwarded values when available.
--
module LiveOak.StoreForward
  ( -- * Store Forwarding
    forwardStores
  , StoreForwardResult(..)
  ) where

import LiveOak.SSATypes
import LiveOak.SSAUtils (substVarsInInstr)
import LiveOak.CFG
import LiveOak.Alias (PointsToInfo, computePointsTo, queryAlias, mayAlias)

import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Set (Set)
import qualified Data.Set as Set
import Data.List (foldl')

--------------------------------------------------------------------------------
-- Types
--------------------------------------------------------------------------------

-- | Store forwarding result
data StoreForwardResult = StoreForwardResult
  { sfOptBlocks :: ![SSABlock]
  , sfForwarded :: !Int          -- ^ Number of loads forwarded
  } deriving (Show)

-- | Key for tracking stores: (object variable key, field name)
type StoreKey = (VarKey, String)

-- | Available store: maps StoreKey to the value expression
type AvailableStores = Map StoreKey SSAExpr

-- | Dataflow state for a block
data BlockState = BlockState
  { bsIn :: !AvailableStores      -- ^ Stores available at block entry
  , bsOut :: !AvailableStores     -- ^ Stores available at block exit
  , bsGen :: !AvailableStores     -- ^ Stores generated in this block
  , bsKill :: !(Set StoreKey)     -- ^ Stores killed in this block
  } deriving (Eq, Show)

--------------------------------------------------------------------------------
-- Store Forwarding
--------------------------------------------------------------------------------

-- | Forward stores to loads across blocks
forwardStores :: SSAMethod -> StoreForwardResult
forwardStores method =
  let cfg = buildCFG method
      blocks = ssaMethodBlocks method
      blockMap = Map.fromList [(blockLabel b, b) | b <- blocks]
      ptInfo = computePointsTo method

      -- Compute local gen/kill sets for each block
      localInfo = Map.map (computeLocalInfo ptInfo) blockMap

      -- Run dataflow analysis
      finalState = runDataflow cfg blockMap localInfo

      -- Apply forwarding
      (optimized, count) = applyForwarding ptInfo finalState blocks
  in StoreForwardResult
    { sfOptBlocks = optimized
    , sfForwarded = count
    }

-- | Compute local gen/kill sets for a block
computeLocalInfo :: PointsToInfo -> SSABlock -> BlockState
computeLocalInfo ptInfo SSABlock{..} =
  let (gen, kill) = foldl' (processInstrLocal ptInfo) (Map.empty, Set.empty) blockInstrs
  in BlockState
    { bsIn = Map.empty
    , bsOut = gen
    , bsGen = gen
    , bsKill = kill
    }

-- | Process instruction for gen/kill computation
processInstrLocal :: PointsToInfo -> (AvailableStores, Set StoreKey) -> SSAInstr
                  -> (AvailableStores, Set StoreKey)
processInstrLocal ptInfo (gen, kill) = \case
  -- Field store: add to gen, kill any aliasing stores
  SSAFieldStore target field _idx value ->
    case getTargetKey target of
      Just objKey ->
        let storeKey = (objKey, field)
            -- Kill all stores that may alias with this one
            aliasKeys = findAliasingKeys ptInfo target field (Map.keys gen)
            kill' = Set.union kill (Set.fromList aliasKeys)
            gen' = Map.insert storeKey value (foldr Map.delete gen aliasKeys)
        in (gen', kill')
      Nothing ->
        -- Can't determine target, kill all stores to this field
        let kill' = Set.union kill (Set.fromList [(k, f) | (k, f) <- Map.keys gen, f == field])
            gen' = Map.filterWithKey (\(_, f) _ -> f /= field) gen
        in (gen', kill')

  -- Calls kill all stores (may have side effects)
  SSAAssign _ (SSAInstanceCall _ _ _) -> (Map.empty, Set.fromList (Map.keys gen))
  SSAAssign _ (SSACall _ _) -> (Map.empty, Set.fromList (Map.keys gen))
  SSAExprStmt (SSAInstanceCall _ _ _) -> (Map.empty, Set.fromList (Map.keys gen))
  SSAExprStmt (SSACall _ _) -> (Map.empty, Set.fromList (Map.keys gen))

  -- Other instructions don't affect stores
  _ -> (gen, kill)

-- | Find store keys that may alias with a given store
findAliasingKeys :: PointsToInfo -> SSAExpr -> String -> [StoreKey] -> [StoreKey]
findAliasingKeys ptInfo target field keys =
  [(k, f) | (k, f) <- keys, f == field, mayAliasKey ptInfo target k]

-- | Check if target may alias with a variable key
mayAliasKey :: PointsToInfo -> SSAExpr -> VarKey -> Bool
mayAliasKey ptInfo target (name, ver) =
  mayAlias $ queryAlias ptInfo target (SSAUse (SSAVar name ver Nothing))

--------------------------------------------------------------------------------
-- Dataflow Analysis
--------------------------------------------------------------------------------

-- | Run forward dataflow analysis
runDataflow :: CFG -> Map BlockId SSABlock -> Map BlockId BlockState -> Map BlockId BlockState
runDataflow cfg _blockMap initState = iterate' maxIterations initState
  where
    maxIterations = 50

    iterate' 0 state = state
    iterate' n state =
      let state' = oneIteration cfg state
      in if state' == state then state' else iterate' (n-1) state'

-- | One iteration of dataflow
oneIteration :: CFG -> Map BlockId BlockState -> Map BlockId BlockState
oneIteration cfg state = Map.mapWithKey (updateBlock cfg state) state

-- | Update a single block's state
updateBlock :: CFG -> Map BlockId BlockState -> BlockId -> BlockState -> BlockState
updateBlock cfg allState bid bs =
  let preds = predecessors cfg bid
      -- IN = intersection of all predecessor OUTs
      newIn = case preds of
        [] -> Map.empty  -- Entry block
        _ -> foldl1 intersectStores [bsOut (Map.findWithDefault emptyState p allState) | p <- preds]
      -- OUT = (IN - KILL) ∪ GEN
      newOut = Map.union (bsGen bs) (Map.withoutKeys newIn (bsKill bs))
  in bs { bsIn = newIn, bsOut = newOut }
  where
    emptyState = BlockState Map.empty Map.empty Map.empty Set.empty

-- | Intersect two store maps (conservative: only keep stores present in both)
intersectStores :: AvailableStores -> AvailableStores -> AvailableStores
intersectStores a b = Map.intersectionWith pickValue a b
  where
    -- If both have the same value, keep it; otherwise drop
    pickValue v1 v2 = if v1 == v2 then v1 else SSANull  -- SSANull as placeholder

--------------------------------------------------------------------------------
-- Apply Forwarding
--------------------------------------------------------------------------------

-- | Apply store forwarding to blocks
applyForwarding :: PointsToInfo -> Map BlockId BlockState -> [SSABlock] -> ([SSABlock], Int)
applyForwarding ptInfo state blocks =
  let results = map (forwardBlock ptInfo state) blocks
  in (map fst results, sum (map snd results))

-- | Forward stores in a single block
forwardBlock :: PointsToInfo -> Map BlockId BlockState -> SSABlock -> (SSABlock, Int)
forwardBlock ptInfo state block@SSABlock{..} =
  let initAvail = case Map.lookup blockLabel state of
        Just bs -> bsIn bs
        Nothing -> Map.empty
      (instrs', _, count) = foldl' (forwardInstr ptInfo) ([], initAvail, 0) blockInstrs
  in (block { blockInstrs = reverse instrs' }, count)

-- | Forward stores in an instruction
forwardInstr :: PointsToInfo -> ([SSAInstr], AvailableStores, Int) -> SSAInstr
             -> ([SSAInstr], AvailableStores, Int)
forwardInstr ptInfo (instrs, avail, count) instr = case instr of
  -- Field load: check if we can forward from a store
  SSAAssign var (SSAFieldAccess target field) ->
    case getTargetKey target of
      Just objKey ->
        let storeKey = (objKey, field)
        in case Map.lookup storeKey avail of
          Just value | value /= SSANull ->
            -- Forward the stored value
            let subst = Map.singleton (ssaName var, ssaVersion var) value
                instrs' = map (substVarsInInstr subst) instrs
            in (SSAAssign var value : instrs', avail, count + 1)
          _ ->
            (instr : instrs, avail, count)
      Nothing ->
        (instr : instrs, avail, count)

  -- Field store: update available stores
  SSAFieldStore target field _idx value ->
    case getTargetKey target of
      Just objKey ->
        let storeKey = (objKey, field)
            -- Kill aliasing stores
            aliasKeys = findAliasingKeys ptInfo target field (Map.keys avail)
            avail' = Map.insert storeKey value (foldr Map.delete avail aliasKeys)
        in (instr : instrs, avail', count)
      Nothing ->
        let avail' = Map.filterWithKey (\(_, f) _ -> f /= field) avail
        in (instr : instrs, avail', count)

  -- Calls kill all available stores
  SSAAssign _ (SSAInstanceCall _ _ _) -> (instr : instrs, Map.empty, count)
  SSAAssign _ (SSACall _ _) -> (instr : instrs, Map.empty, count)
  SSAExprStmt (SSAInstanceCall _ _ _) -> (instr : instrs, Map.empty, count)
  SSAExprStmt (SSACall _ _) -> (instr : instrs, Map.empty, count)

  -- Other instructions pass through
  _ -> (instr : instrs, avail, count)

--------------------------------------------------------------------------------
-- Utilities
--------------------------------------------------------------------------------

-- | Get the key for a target expression
getTargetKey :: SSAExpr -> Maybe VarKey
getTargetKey (SSAUse var) = Just (ssaName var, ssaVersion var)
getTargetKey SSAThis = Just (varName "this", 0)
getTargetKey _ = Nothing
