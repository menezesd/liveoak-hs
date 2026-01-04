{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RecordWildCards #-}

-- | Dead Store Elimination (DSE).
-- Removes stores to memory locations that are overwritten before being read.
-- In SSA form, this primarily applies to field stores.
--
-- == Algorithm
--
-- 1. Build a map of stores to each field of each object
-- 2. For each store, check if there's a subsequent store to the same location
--    with no intervening read
-- 3. Remove stores that are definitely dead
--
-- == Safety
--
-- A store is only removed if:
-- - Another store to the same field of the same object follows it
-- - No read of that field occurs between the two stores
-- - No function call occurs between them (could read the field)
--
module LiveOak.DSE
  ( -- * Dead Store Elimination
    eliminateDeadStores
  , DSEResult(..)
  ) where

import LiveOak.SSATypes
import LiveOak.CFG

import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Set (Set)
import qualified Data.Set as Set
import Data.List (foldl')

--------------------------------------------------------------------------------
-- Types
--------------------------------------------------------------------------------

-- | Store location: (object variable, field name)
type StoreLoc = (String, String)

-- | DSE result
data DSEResult = DSEResult
  { dseOptBlocks :: ![SSABlock]   -- ^ Optimized blocks
  , dseEliminated :: !Int         -- ^ Number of eliminated stores
  } deriving (Show)

-- | Store info
data StoreInfo = StoreInfo
  { siBlock :: !BlockId
  , siIndex :: !Int
  , siLoc :: !StoreLoc
  , siValue :: !SSAExpr
  } deriving (Show)

--------------------------------------------------------------------------------
-- Dead Store Elimination
--------------------------------------------------------------------------------

-- | Eliminate dead stores from SSA blocks
-- Currently handles intra-block DSE (stores within the same basic block)
eliminateDeadStores :: [SSABlock] -> DSEResult
eliminateDeadStores blocks =
  let (optimized, count) = unzip $ map eliminateBlockDeadStores blocks
  in DSEResult
    { dseOptBlocks = optimized
    , dseEliminated = sum count
    }

-- | Eliminate dead stores within a single block
eliminateBlockDeadStores :: SSABlock -> (SSABlock, Int)
eliminateBlockDeadStores block@SSABlock{..} =
  let -- Find all stores and their locations
      indexed = zip [0..] blockInstrs
      -- Analyze which stores are dead (overwritten before read)
      deadStores = findDeadStores indexed
      -- Remove dead stores
      filtered = [instr | (i, instr) <- indexed, not (Set.member i deadStores)]
  in (block { blockInstrs = filtered }, Set.size deadStores)

-- | Find indices of dead stores
-- A store is dead if a later store to the same location exists
-- with no intervening read, call, or variable reassignment
findDeadStores :: [(Int, SSAInstr)] -> Set Int
findDeadStores indexed = go Map.empty Set.empty indexed
  where
    -- Track last store to each location, mark previous as dead when overwritten
    go :: Map StoreLoc Int -> Set Int -> [(Int, SSAInstr)] -> Set Int
    go _ dead [] = dead
    go lastStore dead ((i, instr):rest) = case instr of
      -- Field store: check if previous store to same location is dead
      SSAFieldStore target field _ _ ->
        case getTargetVar target of
          Just objVar ->
            let loc = (objVar, field)
            in case Map.lookup loc lastStore of
                 Just prevIdx ->
                   -- Previous store is dead (overwritten without read)
                   go (Map.insert loc i lastStore)
                      (Set.insert prevIdx dead)
                      rest
                 Nothing ->
                   go (Map.insert loc i lastStore) dead rest
          Nothing ->
            -- Can't determine object, conservatively kill all pending stores
            go Map.empty dead rest

      -- Assignments: check for calls, field reads, and variable reassignment
      SSAAssign var expr ->
        if exprHasCall expr
        then go Map.empty dead rest  -- Calls can read/write any field
        else
          let -- If variable is reassigned, remove all stores through that variable
              -- (they're to a different object now)
              varName = varNameString (ssaName var)
              lastStore' = Map.filterWithKey (\(v, _) _ -> v /= varName) lastStore
              -- Also remove stores for fields that are read
              reads = getFieldReads expr
              lastStore'' = foldl' (flip Map.delete) lastStore' reads
          in go lastStore'' dead rest

      SSAReturn (Just expr) ->
        -- Return could escape the object, invalidate all stores
        go Map.empty dead rest

      SSABranch cond _ _ ->
        let reads = getFieldReads cond
            lastStore' = foldl' (flip Map.delete) lastStore reads
        in go lastStore' dead rest

      SSAExprStmt expr ->
        -- Expression statement might have side effects
        if exprHasCall expr
        then go Map.empty dead rest  -- Calls can read/write any field
        else let reads = getFieldReads expr
                 lastStore' = foldl' (flip Map.delete) lastStore reads
             in go lastStore' dead rest

      -- Jump/branch terminators: stores might be read in successor blocks
      SSAJump _ -> go Map.empty dead rest

      SSAReturn Nothing -> go lastStore dead rest

-- | Check if an expression contains a call (which could have side effects)
exprHasCall :: SSAExpr -> Bool
exprHasCall = \case
  SSACall _ _ -> True
  SSAInstanceCall _ _ _ -> True
  SSANewObject _ _ -> True  -- Constructor can have side effects
  SSAUnary _ e -> exprHasCall e
  SSABinary _ l r -> exprHasCall l || exprHasCall r
  SSATernary c t e -> exprHasCall c || exprHasCall t || exprHasCall e
  SSAFieldAccess t _ -> exprHasCall t
  _ -> False

-- | Get the variable name of a target expression (if it's a simple variable)
getTargetVar :: SSAExpr -> Maybe String
getTargetVar = \case
  SSAUse var -> Just $ varNameString (ssaName var)
  SSAThis -> Just "this"
  _ -> Nothing

-- | Get all field read locations from an expression
getFieldReads :: SSAExpr -> [StoreLoc]
getFieldReads = \case
  SSAFieldAccess target field ->
    case getTargetVar target of
      Just objVar -> [(objVar, field)]
      Nothing -> []
    ++ getFieldReads target
  SSAUse _ -> []
  SSAInt _ -> []
  SSABool _ -> []
  SSAStr _ -> []
  SSANull -> []
  SSAThis -> []
  SSAUnary _ e -> getFieldReads e
  SSABinary _ l r -> getFieldReads l ++ getFieldReads r
  SSATernary c t e -> getFieldReads c ++ getFieldReads t ++ getFieldReads e
  SSACall _ args -> concatMap getFieldReads args
  SSAInstanceCall target _ args -> getFieldReads target ++ concatMap getFieldReads args
  SSANewObject _ args -> concatMap getFieldReads args
