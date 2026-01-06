{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RecordWildCards #-}

-- | Alias Analysis for LiveOak SSA.
-- Determines whether two memory references can alias (point to same memory).
--
-- == Overview
-- This module provides points-to analysis for SSA programs to enable
-- more aggressive memory optimizations like DSE and LICM.
--
-- == Alias Categories
-- * Must-alias: References definitely point to same memory
-- * May-alias: References might point to same memory
-- * No-alias: References definitely point to different memory
--
-- == Supported Patterns
-- * Distinct allocations (new Object() never aliases another new Object())
-- * This-pointer analysis (this is unique within a method)
-- * Field offset analysis (different field offsets never alias)
-- * SSA def-use chains (track allocation sites through assignments)
--
module LiveOak.Alias
  ( -- * Alias Query
    AliasResult(..)
  , queryAlias
  , mayAlias
  , mustAlias
  , noAlias

    -- * Points-To Analysis
  , PointsToInfo(..)
  , AbstractLoc(..)
  , computePointsTo
  , lookupPointsTo

    -- * Convenience Queries
  , storesAlias
  , loadStoreAlias
  ) where

import LiveOak.SSATypes hiding (varKey)

import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Set (Set)
import qualified Data.Set as Set
import Data.List (foldl')

--------------------------------------------------------------------------------
-- Alias Result
--------------------------------------------------------------------------------

-- | Result of an alias query
data AliasResult
  = MustAlias      -- ^ Definitely the same memory location
  | MayAlias       -- ^ Could be the same memory location
  | NoAlias        -- ^ Definitely different memory locations
  deriving (Eq, Ord, Show)

-- | Check if result indicates may-alias (or must-alias)
mayAlias :: AliasResult -> Bool
mayAlias NoAlias = False
mayAlias _ = True

-- | Check if result indicates must-alias
mustAlias :: AliasResult -> Bool
mustAlias MustAlias = True
mustAlias _ = False

-- | Check if result indicates no-alias
noAlias :: AliasResult -> Bool
noAlias NoAlias = True
noAlias _ = False

--------------------------------------------------------------------------------
-- Abstract Locations
--------------------------------------------------------------------------------

-- | Abstract memory locations for points-to analysis
data AbstractLoc
  = LocAlloc !Int            -- ^ Allocation site (unique ID)
  | LocThis                  -- ^ The 'this' pointer
  | LocParam !VarName        -- ^ Method parameter
  | LocField !AbstractLoc !String !Int  -- ^ Field of an object (base, field name, offset)
  | LocUnknown               -- ^ Unknown/escaped location
  deriving (Eq, Ord, Show)

-- | Points-to information for a method
data PointsToInfo = PointsToInfo
  { ptVarToLocs :: !(Map VarKey (Set AbstractLoc))  -- ^ Variable -> possible locations
  , ptAllocCounter :: !Int                          -- ^ Counter for allocation site IDs
  } deriving (Show)

--------------------------------------------------------------------------------
-- Points-To Analysis
--------------------------------------------------------------------------------

-- | Compute points-to information for a method
computePointsTo :: SSAMethod -> PointsToInfo
computePointsTo method =
  let -- Initialize with parameters pointing to unknown/param locations
      initPt = PointsToInfo
        { ptVarToLocs = Map.fromList
            [ ((ssaName p, ssaVersion p), Set.singleton (LocParam (ssaName p)))
            | p <- ssaMethodParams method
            ]
        , ptAllocCounter = 0
        }
      -- Process all blocks
      blocks = ssaMethodBlocks method
  in foldl' processBlock initPt blocks

-- | Process a single block
processBlock :: PointsToInfo -> SSABlock -> PointsToInfo
processBlock pt SSABlock{..} =
  let pt' = foldl' processPhis pt blockPhis
  in foldl' processInstr pt' blockInstrs

-- | Process phi nodes
processPhis :: PointsToInfo -> PhiNode -> PointsToInfo
processPhis pt PhiNode{..} =
  let varKey = (ssaName phiVar, ssaVersion phiVar)
      -- Merge points-to sets from all incoming values
      incomingLocs = Set.unions
        [ lookupPointsTo (ssaName v, ssaVersion v) pt
        | (_, v) <- phiArgs
        ]
  in pt { ptVarToLocs = Map.insert varKey incomingLocs (ptVarToLocs pt) }

-- | Process an instruction
processInstr :: PointsToInfo -> SSAInstr -> PointsToInfo
processInstr pt = \case
  SSAAssign var expr ->
    let varKey = (ssaName var, ssaVersion var)
        (locs, pt') = exprPointsTo pt expr
    in pt' { ptVarToLocs = Map.insert varKey locs (ptVarToLocs pt') }

  -- Other instructions don't define new pointer variables
  _ -> pt

-- | Get points-to set for an expression
exprPointsTo :: PointsToInfo -> SSAExpr -> (Set AbstractLoc, PointsToInfo)
exprPointsTo pt = \case
  SSAThis -> (Set.singleton LocThis, pt)

  SSAUse var ->
    let locs = lookupPointsTo (ssaName var, ssaVersion var) pt
    in (locs, pt)

  SSANewObject _ _ ->
    -- Fresh allocation site
    let allocId = ptAllocCounter pt
        pt' = pt { ptAllocCounter = allocId + 1 }
    in (Set.singleton (LocAlloc allocId), pt')

  SSAFieldAccess base field ->
    -- Field-sensitive: track which field is being accessed on which base
    -- This allows us to determine that obj.x and obj.y don't alias
    let baseLocs = exprToLocs pt base
        -- Create field locations for each possible base
        -- Use field name hash as offset approximation (real offset would need type info)
        fieldOffset = abs (hash field) `mod` 1000
        fieldLocs = Set.map (\bl -> LocField bl field fieldOffset) baseLocs
    in (fieldLocs, pt)

  SSACall _ _ ->
    -- Function calls can return anything
    (Set.singleton LocUnknown, pt)

  SSAInstanceCall _ _ _ ->
    -- Method calls can return anything
    (Set.singleton LocUnknown, pt)

  -- Non-pointer expressions don't have locations
  _ -> (Set.empty, pt)

-- | Simple hash for field names (for offset approximation)
hash :: String -> Int
hash = foldl' (\h c -> 31 * h + fromEnum c) 0

-- | Get points-to set for an expression (without updating state)
exprToLocs :: PointsToInfo -> SSAExpr -> Set AbstractLoc
exprToLocs pt = \case
  SSAThis -> Set.singleton LocThis
  SSAUse var -> lookupPointsTo (ssaName var, ssaVersion var) pt
  SSANewObject _ _ -> Set.singleton LocUnknown  -- Can't determine without context
  SSAFieldAccess base field ->
    -- Field-sensitive: create LocField locations
    let baseLocs = exprToLocs pt base
        fieldOffset = abs (hash field) `mod` 1000
    in Set.map (\bl -> LocField bl field fieldOffset) baseLocs
  _ -> Set.empty

-- | Lookup points-to set for a variable
lookupPointsTo :: VarKey -> PointsToInfo -> Set AbstractLoc
lookupPointsTo key pt = Map.findWithDefault (Set.singleton LocUnknown) key (ptVarToLocs pt)

--------------------------------------------------------------------------------
-- Alias Queries
--------------------------------------------------------------------------------

-- | Query alias relationship between two expressions
queryAlias :: PointsToInfo -> SSAExpr -> SSAExpr -> AliasResult
queryAlias pt expr1 expr2 =
  let locs1 = exprToLocs pt expr1
      locs2 = exprToLocs pt expr2
  in queryAliasLocs locs1 locs2

-- | Query alias relationship between two sets of abstract locations
queryAliasLocs :: Set AbstractLoc -> Set AbstractLoc -> AliasResult
queryAliasLocs locs1 locs2
  -- If either is empty, they can't alias
  | Set.null locs1 || Set.null locs2 = NoAlias
  -- If either contains Unknown, conservatively return MayAlias
  | Set.member LocUnknown locs1 || Set.member LocUnknown locs2 = MayAlias
  -- Check for intersection
  | otherwise =
      let intersection = Set.intersection locs1 locs2
      in if Set.null intersection
         then NoAlias
         else if locs1 == locs2 && Set.size locs1 == 1
              then MustAlias
              else MayAlias

-- | Check if two field stores may alias
storesAlias :: PointsToInfo -> SSAExpr -> String -> Int -> SSAExpr -> String -> Int -> AliasResult
storesAlias pt base1 field1 off1 base2 field2 off2
  -- Different field offsets definitely don't alias
  | off1 /= off2 = NoAlias
  -- Same field on definitely different objects don't alias
  | otherwise =
      let baseLocs1 = exprToLocs pt base1
          baseLocs2 = exprToLocs pt base2
      in case queryAliasLocs baseLocs1 baseLocs2 of
           NoAlias -> NoAlias
           MustAlias | field1 == field2 && off1 == off2 -> MustAlias
           _ -> MayAlias

-- | Check if a load and store may alias
loadStoreAlias :: PointsToInfo -> SSAExpr -> String -> SSAExpr -> String -> Int -> AliasResult
loadStoreAlias pt loadBase loadField storeBase storeField _storeOff =
  -- For field access, check if bases could be same object and fields match
  let loadLocs = exprToLocs pt loadBase
      storeLocs = exprToLocs pt storeBase
  in case queryAliasLocs loadLocs storeLocs of
       NoAlias -> NoAlias
       MustAlias | loadField == storeField -> MustAlias
       _ | loadField == storeField -> MayAlias
       _ -> NoAlias  -- Different fields never alias
