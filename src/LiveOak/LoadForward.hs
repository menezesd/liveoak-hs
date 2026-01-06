{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RecordWildCards #-}

-- | Load-After-Store Forwarding.
-- Replaces redundant loads with the value that was just stored.
--
-- == Algorithm
--
-- Track stores to field locations. When a load is encountered that may alias
-- a tracked store, replace the load with the stored value.
--
-- == Example
--
-- @
-- Before:                    After:
--   this.x = 5                 this.x = 5
--   y = this.x                 y = 5        -- load forwarded
--   return y                   return 5
-- @
--
-- == Safety
--
-- Load forwarding is safe when:
-- - The store and load must-alias (same object, same field)
-- - No intervening store may-alias the location
-- - No intervening call (could modify memory)
--
module LiveOak.LoadForward
  ( -- * Load Forwarding
    forwardLoads
  , forwardLoadsMethod
  , LoadForwardResult(..)
  ) where

import LiveOak.SSATypes
import LiveOak.Alias

import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map

--------------------------------------------------------------------------------
-- Types
--------------------------------------------------------------------------------

-- | Key for identifying a target expression efficiently
-- Avoids string concatenation for Map lookups
data TargetKey
  = TKThis                          -- ^ 'this' object
  | TKVar !VarName !Int             -- ^ SSA variable (name + version)
  | TKUnknown                       -- ^ Unknown/complex expression
  deriving (Eq, Ord, Show)

-- | Tracked store information
data TrackedStore = TrackedStore
  { tsTarget :: !SSAExpr     -- ^ Store target object
  , tsField :: !String       -- ^ Field name
  , tsOffset :: !Int         -- ^ Field offset
  , tsValue :: !SSAExpr      -- ^ Stored value
  } deriving (Show)

-- | Load forwarding result
data LoadForwardResult = LoadForwardResult
  { lfOptBlocks :: ![SSABlock]    -- ^ Optimized blocks
  , lfForwarded :: !Int           -- ^ Number of loads forwarded
  } deriving (Show)

--------------------------------------------------------------------------------
-- Load Forwarding
--------------------------------------------------------------------------------

-- | Forward loads without alias analysis (conservative, exact matching only)
forwardLoads :: [SSABlock] -> LoadForwardResult
forwardLoads blocks =
  let (optimized, counts) = unzip $ map forwardBlockLoadsSimple blocks
  in LoadForwardResult
    { lfOptBlocks = optimized
    , lfForwarded = sum counts
    }

-- | Value substitution map for chaining
type ValueSubst = Map VarKey SSAExpr

-- | Forward loads in a single block (simple version without alias analysis)
forwardBlockLoadsSimple :: SSABlock -> (SSABlock, Int)
forwardBlockLoadsSimple block@SSABlock{..} =
  let (instrs', count) = processInstrsSimple Map.empty Map.empty 0 blockInstrs
  in (block { blockInstrs = instrs' }, count)

-- | Process instructions for load forwarding (simple version)
-- Now also tracks value substitutions for chaining
processInstrsSimple :: Map (TargetKey, String) SSAExpr -> ValueSubst -> Int -> [SSAInstr] -> ([SSAInstr], Int)
processInstrsSimple _ _ count [] = ([], count)
processInstrsSimple stores valSubst count (instr:rest) =
  case instr of
    -- Track stores (using target string representation for simple matching)
    SSAFieldStore target field _ value ->
      let -- Substitute values in the store target and value for chaining
          target' = substValues valSubst target
          value' = substValues valSubst value
          key = (targetKey target', field)
          stores' = Map.insert key value' stores
          (rest', count') = processInstrsSimple stores' valSubst count rest
      in (SSAFieldStore target' field 0 value' : rest', count')

    -- Forward loads in assignments
    SSAAssign var expr ->
      let -- First apply value substitutions for chaining
          exprSubst = substValues valSubst expr
          -- Then try to forward field loads
          (expr', didForward) = forwardExprSimple stores exprSubst
          count' = if didForward then count + 1 else count
          -- Track this assignment for value chaining if it's a simple value
          varK = (ssaName var, ssaVersion var)
          valSubst' = case expr' of
            -- Track constants and variable copies
            SSAInt _ -> Map.insert varK expr' valSubst
            SSABool _ -> Map.insert varK expr' valSubst
            SSANull -> Map.insert varK expr' valSubst
            SSAUse v ->
              -- Follow the chain: if v maps to something, use that
              let vKey = (ssaName v, ssaVersion v)
              in case Map.lookup vKey valSubst of
                Just ultimate -> Map.insert varK ultimate valSubst
                Nothing -> Map.insert varK expr' valSubst
            _ -> valSubst
          -- If the expression is a call, invalidate stores
          stores' = if hasCall expr' then Map.empty else stores
          (rest', count'') = processInstrsSimple stores' valSubst' count' rest
      in (SSAAssign var expr' : rest', count'')

    -- Calls invalidate all stores
    SSAExprStmt expr | hasCall expr ->
      let (rest', count') = processInstrsSimple Map.empty valSubst count rest
      in (instr : rest', count')

    -- Returns may escape objects
    SSAReturn (Just expr) ->
      let expr' = substValues valSubst expr
          (rest', count') = processInstrsSimple Map.empty valSubst count rest
      in (SSAReturn (Just expr') : rest', count')

    -- Substitute in branch conditions
    SSABranch cond thenB elseB ->
      let cond' = substValues valSubst cond
      in ([SSABranch cond' thenB elseB], count)

    -- Control flow ends the block
    SSAJump _ -> ([instr], count)

    -- Other instructions pass through
    _ ->
      let (rest', count') = processInstrsSimple stores valSubst count rest
      in (instr : rest', count')

-- | Substitute known values in an expression
substValues :: ValueSubst -> SSAExpr -> SSAExpr
substValues valSubst = go
  where
    go = \case
      SSAUse var ->
        let key = (ssaName var, ssaVersion var)
        in case Map.lookup key valSubst of
          Just val -> val
          Nothing -> SSAUse var
      SSAUnary op e -> SSAUnary op (go e)
      SSABinary op l r -> SSABinary op (go l) (go r)
      SSATernary c t e -> SSATernary (go c) (go t) (go e)
      SSACall n args -> SSACall n (map go args)
      SSAInstanceCall t m args -> SSAInstanceCall (go t) m (map go args)
      SSANewObject cn args -> SSANewObject cn (map go args)
      SSAFieldAccess t f -> SSAFieldAccess (go t) f
      e -> e

-- | Try to forward a field access in an expression
forwardExprSimple :: Map (TargetKey, String) SSAExpr -> SSAExpr -> (SSAExpr, Bool)
forwardExprSimple stores = go
  where
    go expr = case expr of
      SSAFieldAccess target field ->
        let key = (targetKey target, field)
        in case Map.lookup key stores of
          Just value -> (value, True)
          Nothing ->
            let (target', fwd) = go target
            in (SSAFieldAccess target' field, fwd)
      SSAUnary op e ->
        let (e', fwd) = go e
        in (SSAUnary op e', fwd)
      SSABinary op l r ->
        let (l', fwdL) = go l
            (r', fwdR) = go r
        in (SSABinary op l' r', fwdL || fwdR)
      SSATernary c t e ->
        let (c', fwdC) = go c
            (t', fwdT) = go t
            (e', fwdE) = go e
        in (SSATernary c' t' e', fwdC || fwdT || fwdE)
      SSACall n args ->
        let (args', fwds) = unzip $ map go args
        in (SSACall n args', or fwds)
      SSAInstanceCall t m args ->
        let (t', fwdT) = go t
            (args', fwds) = unzip $ map go args
        in (SSAInstanceCall t' m args', fwdT || or fwds)
      SSANewObject cn args ->
        let (args', fwds) = unzip $ map go args
        in (SSANewObject cn args', or fwds)
      e -> (e, False)

-- | Get a key for a target expression (for efficient Map lookups)
-- Uses a dedicated data type instead of string concatenation
targetKey :: SSAExpr -> TargetKey
targetKey = \case
  SSAThis -> TKThis
  SSAUse var -> TKVar (ssaName var) (ssaVersion var)
  _ -> TKUnknown

-- | Check if expression has a call
hasCall :: SSAExpr -> Bool
hasCall = \case
  SSACall _ _ -> True
  SSAInstanceCall _ _ _ -> True
  SSANewObject _ _ -> True
  SSAUnary _ e -> hasCall e
  SSABinary _ l r -> hasCall l || hasCall r
  SSATernary c t e -> hasCall c || hasCall t || hasCall e
  SSAFieldAccess t _ -> hasCall t
  _ -> False

--------------------------------------------------------------------------------
-- Alias-Aware Load Forwarding
--------------------------------------------------------------------------------

-- | Forward loads using alias analysis for better precision
forwardLoadsMethod :: SSAMethod -> LoadForwardResult
forwardLoadsMethod method =
  let ptInfo = computePointsTo method
      (optimized, counts) = unzip $ map (forwardBlockLoadsAlias ptInfo) (ssaMethodBlocks method)
  in LoadForwardResult
    { lfOptBlocks = optimized
    , lfForwarded = sum counts
    }

-- | Forward loads in a block with alias analysis
forwardBlockLoadsAlias :: PointsToInfo -> SSABlock -> (SSABlock, Int)
forwardBlockLoadsAlias ptInfo block@SSABlock{..} =
  let (instrs', count) = processInstrsAlias ptInfo [] 0 blockInstrs
  in (block { blockInstrs = instrs' }, count)

-- | Process instructions with alias analysis
processInstrsAlias :: PointsToInfo -> [TrackedStore] -> Int -> [SSAInstr] -> ([SSAInstr], Int)
processInstrsAlias _ _ count [] = ([], count)
processInstrsAlias ptInfo stores count (instr:rest) =
  case instr of
    -- Track stores
    SSAFieldStore target field off value ->
      let newStore = TrackedStore target field off value
          -- Remove stores that this might overwrite (may-alias)
          stores' = filter (not . mayAliasStore ptInfo target field off) stores
          stores'' = newStore : stores'
          (rest', count') = processInstrsAlias ptInfo stores'' count rest
      in (instr : rest', count')

    -- Forward loads in assignments
    SSAAssign var expr ->
      let (expr', forwarded) = forwardExprAlias ptInfo stores expr
          count' = count + forwarded
          -- If the expression is a call, invalidate all stores
          stores' = if hasCall expr' then [] else stores
          (rest', count'') = processInstrsAlias ptInfo stores' count' rest
      in (SSAAssign var expr' : rest', count'')

    -- Calls invalidate all stores
    SSAExprStmt expr | hasCall expr ->
      let (rest', count') = processInstrsAlias ptInfo [] count rest
      in (instr : rest', count')

    -- Returns may escape objects
    SSAReturn (Just _) ->
      let (rest', count') = processInstrsAlias ptInfo [] count rest
      in (instr : rest', count')

    -- Control flow ends the block
    SSAJump _ -> ([instr], count)
    SSABranch _ _ _ -> ([instr], count)

    -- Other instructions pass through
    _ ->
      let (rest', count') = processInstrsAlias ptInfo stores count rest
      in (instr : rest', count')

-- | Check if a new store may alias an existing tracked store
mayAliasStore :: PointsToInfo -> SSAExpr -> String -> Int -> TrackedStore -> Bool
mayAliasStore ptInfo target field off TrackedStore{..} =
  case storesAlias ptInfo tsTarget tsField tsOffset target field off of
    NoAlias -> False
    _ -> True

-- | Forward field accesses in an expression using alias analysis
forwardExprAlias :: PointsToInfo -> [TrackedStore] -> SSAExpr -> (SSAExpr, Int)
forwardExprAlias ptInfo stores = go
  where
    go expr = case expr of
      SSAFieldAccess target field ->
        -- Look for a store that must-alias this load
        case findMustAliasStore ptInfo stores target field of
          Just value -> (value, 1)
          Nothing ->
            let (target', fwd) = go target
            in (SSAFieldAccess target' field, fwd)
      SSAUnary op e ->
        let (e', fwd) = go e
        in (SSAUnary op e', fwd)
      SSABinary op l r ->
        let (l', fwdL) = go l
            (r', fwdR) = go r
        in (SSABinary op l' r', fwdL + fwdR)
      SSATernary c t e ->
        let (c', fwdC) = go c
            (t', fwdT) = go t
            (e', fwdE) = go e
        in (SSATernary c' t' e', fwdC + fwdT + fwdE)
      SSACall n args ->
        let (args', fwds) = unzip $ map go args
        in (SSACall n args', sum fwds)
      SSAInstanceCall t m args ->
        let (t', fwdT) = go t
            (args', fwds) = unzip $ map go args
        in (SSAInstanceCall t' m args', fwdT + sum fwds)
      SSANewObject cn args ->
        let (args', fwds) = unzip $ map go args
        in (SSANewObject cn args', sum fwds)
      e -> (e, 0)

-- | Find a store that must-alias the given load
findMustAliasStore :: PointsToInfo -> [TrackedStore] -> SSAExpr -> String -> Maybe SSAExpr
findMustAliasStore ptInfo stores loadBase loadField =
  case filter (isMustAlias ptInfo loadBase loadField) stores of
    (TrackedStore _ _ _ value : _) -> Just value
    [] -> Nothing

-- | Check if a store must-alias a load
isMustAlias :: PointsToInfo -> SSAExpr -> String -> TrackedStore -> Bool
isMustAlias ptInfo loadBase loadField TrackedStore{..} =
  case loadStoreAlias ptInfo loadBase loadField tsTarget tsField tsOffset of
    MustAlias -> True
    _ -> False
