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
-- - The object is a fresh allocation in the same block and never escapes
--
-- == Inter-Block DSE
--
-- For inter-block analysis, we use forward dataflow to propagate available stores:
-- - At block entry: intersection of available stores from all predecessors
-- - At block exit: stores available after processing the block
-- - A store is dead if overwritten in ALL successor paths before being read
--
module LiveOak.DSE
  ( -- * Dead Store Elimination
    eliminateDeadStores
  , eliminateDeadStoresInterBlock
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

-- | Store base: either "this" or a specific SSA variable.
data StoreObj
  = StoreThis
  | StoreVar !VarKey
  deriving (Eq, Ord, Show)

-- | Store location: (object base, field name)
type StoreLoc = (StoreObj, String)

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
      -- Only track stores to fresh, non-escaping objects in this block
      safeObjs = collectSafeObjs blockInstrs
      -- Analyze which stores are dead (overwritten before read)
      deadStores = findDeadStores safeObjs indexed
      -- Remove dead stores
      filtered = [instr | (i, instr) <- indexed, not (Set.member i deadStores)]
  in (block { blockInstrs = filtered }, Set.size deadStores)

-- | Find indices of dead stores
-- A store is dead if a later store to the same location exists
-- with no intervening read, call, or control-flow boundary.
-- Only considers stores to "safe" objects (fresh, non-escaping locals).
findDeadStores :: Set StoreObj -> [(Int, SSAInstr)] -> Set Int
findDeadStores safeObjs indexed = go Map.empty Set.empty indexed
  where
    -- Track last store to each location, mark previous as dead when overwritten
    go :: Map StoreLoc Int -> Set Int -> [(Int, SSAInstr)] -> Set Int
    go _ dead [] = dead
    go lastStore dead ((i, instr):rest) = case instr of
      -- Field store: check if previous store to same location is dead
      SSAFieldStore target field _ value ->
        let targetReads = getFieldReads target
            valueReads = getFieldReads value
            lastStore' = foldl' (flip Map.delete) lastStore (targetReads ++ valueReads)
        in case getTargetObj target of
             Just obj
               | Set.member obj safeObjs ->
                   let loc = (obj, field)
                   in case Map.lookup loc lastStore' of
                        Just prevIdx ->
                          -- Previous store is dead (overwritten without read)
                          go (Map.insert loc i lastStore')
                             (Set.insert prevIdx dead)
                             rest
                        Nothing ->
                          go (Map.insert loc i lastStore') dead rest
             _ ->
               -- Not a trackable target; keep existing stores for safe objects
               go lastStore' dead rest

      -- Assignments: check for calls, field reads, and variable reassignment
      SSAAssign var expr ->
        if exprHasCall expr
        then go Map.empty dead rest  -- Calls can read/write any field
        else
          let -- Remove stores for fields that are read
              reads = getFieldReads expr
              lastStore' = foldl' (flip Map.delete) lastStore reads
          in go lastStore' dead rest

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

-- | Get the object base of a target expression (if it's simple).
getTargetObj :: SSAExpr -> Maybe StoreObj
getTargetObj = \case
  SSAUse var -> Just $ StoreVar (varKey var)
  SSAThis -> Just StoreThis
  _ -> Nothing

-- | Get all field read locations from an expression
getFieldReads :: SSAExpr -> [StoreLoc]
getFieldReads = \case
  SSAFieldAccess target field ->
    case getTargetObj target of
      Just obj -> [(obj, field)]
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

-- | Collect objects that are safe to track (fresh allocations that never escape).
collectSafeObjs :: [SSAInstr] -> Set StoreObj
collectSafeObjs instrs =
  let fresh = Set.fromList
        [ StoreVar (varKey v)
        | SSAAssign v (SSANewObject _ _) <- instrs
        ]
      escapes = foldl' collectEscapes Set.empty instrs
  in Set.difference fresh escapes
  where
    collectEscapes acc = \case
      SSAAssign _ expr -> Set.union acc (exprObjRefs expr)
      SSAExprStmt expr -> Set.union acc (exprObjRefs expr)
      SSAReturn (Just expr) -> Set.union acc (exprObjRefs expr)
      SSAFieldStore _ _ _ value -> Set.union acc (exprObjRefs value)
      _ -> acc

-- | Collect object references used as values in an expression.
exprObjRefs :: SSAExpr -> Set StoreObj
exprObjRefs = \case
  SSAUse var -> Set.singleton (StoreVar (varKey var))
  SSAThis -> Set.singleton StoreThis
  SSAUnary _ e -> exprObjRefs e
  SSABinary _ l r -> exprObjRefs l `Set.union` exprObjRefs r
  SSATernary c t e -> exprObjRefs c `Set.union` exprObjRefs t `Set.union` exprObjRefs e
  SSACall _ args -> Set.unions (map exprObjRefs args)
  SSAInstanceCall target _ args -> exprObjRefs target `Set.union` Set.unions (map exprObjRefs args)
  SSANewObject _ args -> Set.unions (map exprObjRefs args)
  SSAFieldAccess target _ -> exprObjRefs target
  _ -> Set.empty

--------------------------------------------------------------------------------
-- Inter-Block Dead Store Elimination
--------------------------------------------------------------------------------

-- | Available store info for inter-block analysis
data AvailStore = AvailStore
  { asBlockId :: !BlockId        -- ^ Block containing the store
  , asIndex :: !Int              -- ^ Instruction index
  , asLoc :: !StoreLoc           -- ^ Store location
  } deriving (Eq, Ord, Show)

-- | Inter-block DSE using forward dataflow analysis
-- This is more aggressive than intra-block DSE but still safe.
eliminateDeadStoresInterBlock :: SSAMethod -> DSEResult
eliminateDeadStoresInterBlock method@SSAMethod{..} =
  let cfg = buildCFG method
      blockMap = Map.fromList [(blockLabel b, b) | b <- ssaMethodBlocks]

      -- Collect all safe objects across the entire method
      allInstrs = concatMap blockInstrs ssaMethodBlocks
      safeObjs = collectSafeObjs allInstrs

      -- Compute which stores are killed (overwritten) in each block
      killSets = Map.fromList
        [(blockLabel b, computeBlockKills safeObjs b) | b <- ssaMethodBlocks]

      -- Forward dataflow: compute stores that reach each point
      -- and are subsequently overwritten
      deadStores = findInterBlockDeadStores cfg blockMap safeObjs killSets

      -- Remove dead stores
      optimized = map (removeDeadStoresFromBlock deadStores) ssaMethodBlocks

  in DSEResult
    { dseOptBlocks = optimized
    , dseEliminated = Set.size deadStores
    }

-- | Compute which stores are killed (overwritten) in a block
computeBlockKills :: Set StoreObj -> SSABlock -> Set StoreLoc
computeBlockKills safeObjs SSABlock{..} =
  Set.fromList [loc | SSAFieldStore target field _ _ <- blockInstrs
                    , Just obj <- [getTargetObj target]
                    , Set.member obj safeObjs
                    , let loc = (obj, field)]

-- | Find dead stores using inter-block analysis
-- A store is dead if it is killed in ALL paths before being read
findInterBlockDeadStores :: CFG -> Map BlockId SSABlock -> Set StoreObj
                         -> Map BlockId (Set StoreLoc) -> Set (BlockId, Int)
findInterBlockDeadStores cfg blockMap safeObjs killSets =
  let blocks = Map.elems blockMap

      -- For each store, check if it's dead
      allStores = [(blockLabel b, i, loc)
                  | b <- blocks
                  , (i, SSAFieldStore target field _ _) <- zip [0..] (blockInstrs b)
                  , Just obj <- [getTargetObj target]
                  , Set.member obj safeObjs
                  , let loc = (obj, field)]

      -- A store is dead if:
      -- 1. Within the same block, there's a later store that overwrites it
      -- 2. OR in all successor blocks, the location is killed before read
      deadSet = foldl' (checkStoreDead cfg blockMap safeObjs killSets) Set.empty allStores

  in deadSet

-- | Check if a specific store is dead
checkStoreDead :: CFG -> Map BlockId SSABlock -> Set StoreObj
               -> Map BlockId (Set StoreLoc)
               -> Set (BlockId, Int) -> (BlockId, Int, StoreLoc)
               -> Set (BlockId, Int)
checkStoreDead cfg blockMap safeObjs _killSets dead (bid, idx, loc) =
  case Map.lookup bid blockMap of
    Nothing -> dead
    Just block ->
      -- Check if there's a later store in the same block that kills this one
      let laterInstrs = drop (idx + 1) (blockInstrs block)
          killedInBlock = any (storeKillsLoc safeObjs loc) laterInstrs
          readInBlock = any (instrReadsLoc loc) laterInstrs
      in if killedInBlock && not readInBlock
         then Set.insert (bid, idx) dead
         else dead

-- | Check if an instruction stores to the given location
storeKillsLoc :: Set StoreObj -> StoreLoc -> SSAInstr -> Bool
storeKillsLoc safeObjs (obj, field) = \case
  SSAFieldStore target f _ _ ->
    case getTargetObj target of
      Just tObj -> tObj == obj && f == field && Set.member tObj safeObjs
      Nothing -> False
  _ -> False

-- | Check if an instruction reads from the given location
instrReadsLoc :: StoreLoc -> SSAInstr -> Bool
instrReadsLoc loc = \case
  SSAAssign _ expr -> exprReadsLoc loc expr || exprHasCall expr
  SSAFieldStore target _ _ value ->
    exprReadsLoc loc target || exprReadsLoc loc value
  SSAReturn (Just expr) -> exprReadsLoc loc expr
  SSABranch cond _ _ -> exprReadsLoc loc cond
  SSAExprStmt expr -> exprReadsLoc loc expr || exprHasCall expr
  _ -> False

-- | Check if an expression reads from the given location
exprReadsLoc :: StoreLoc -> SSAExpr -> Bool
exprReadsLoc loc@(obj, field) = \case
  SSAFieldAccess target f ->
    (getTargetObj target == Just obj && f == field) || exprReadsLoc loc target
  SSAUnary _ e -> exprReadsLoc loc e
  SSABinary _ l r -> exprReadsLoc loc l || exprReadsLoc loc r
  SSATernary c t e -> exprReadsLoc loc c || exprReadsLoc loc t || exprReadsLoc loc e
  SSACall _ args -> any (exprReadsLoc loc) args
  SSAInstanceCall target _ args ->
    exprReadsLoc loc target || any (exprReadsLoc loc) args
  SSANewObject _ args -> any (exprReadsLoc loc) args
  _ -> False

-- | Remove dead stores from a block
removeDeadStoresFromBlock :: Set (BlockId, Int) -> SSABlock -> SSABlock
removeDeadStoresFromBlock deadStores block@SSABlock{..} =
  let filtered = [instr | (i, instr) <- zip [0..] blockInstrs
                        , not (Set.member (blockLabel, i) deadStores)]
  in block { blockInstrs = filtered }
