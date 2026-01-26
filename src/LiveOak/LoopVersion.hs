{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RecordWildCards #-}

-- | Loop Versioning.
-- Creates specialized loop versions with runtime guards.
--
-- == Use Cases
-- 1. Alias-free loops: Version for when pointers don't alias
-- 2. Bounds-check-free loops: Version for when index is in bounds
-- 3. Type-specialized loops: Version for specific runtime types
--
-- == Structure
-- @
-- if (guard_condition) {
--   // Optimized loop version (no alias checks, etc.)
-- } else {
--   // Original loop (conservative)
-- }
-- @
--
module LiveOak.LoopVersion
  ( -- * Loop Versioning
    versionLoops
  , LoopVersionResult(..)

    -- * Version Guards
  , VersionGuard(..)
  , generateGuard
  ) where

import LiveOak.SSATypes
import LiveOak.CFG
import LiveOak.Loop
import LiveOak.Dominance (DomTree, computeDominators)
import LiveOak.Alias (PointsToInfo, computePointsTo, queryAlias, mayAlias)
import LiveOak.Ast (BinaryOp(..))

import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Set (Set)
import qualified Data.Set as Set
import Data.List (foldl')
import Data.Maybe (mapMaybe)

--------------------------------------------------------------------------------
-- Types
--------------------------------------------------------------------------------

-- | Loop versioning result
data LoopVersionResult = LoopVersionResult
  { lvOptBlocks :: ![SSABlock]
  , lvVersioned :: !Int              -- ^ Number of loops versioned
  } deriving (Show)

-- | Version guard type
data VersionGuard
  = AliasGuard !SSAExpr !SSAExpr     -- ^ Check that two pointers don't alias
  | BoundsGuard !SSAExpr !SSAExpr !SSAExpr  -- ^ Check index in [lo, hi)
  | TypeGuard !SSAExpr !String       -- ^ Check object is of specific type
  deriving (Show)

-- | Loop versioning candidate
data VersionCandidate = VersionCandidate
  { vcLoop :: !Loop
  , vcGuards :: ![VersionGuard]      -- ^ Guards needed for optimized version
  , vcBenefit :: !Int                -- ^ Estimated benefit
  } deriving (Show)

--------------------------------------------------------------------------------
-- Loop Versioning
--------------------------------------------------------------------------------

-- | Apply loop versioning to a method
versionLoops :: SSAMethod -> LoopVersionResult
versionLoops method =
  let cfg = buildCFG method
      domTree = computeDominators cfg
      loopNest = findLoops cfg domTree
      blocks = ssaMethodBlocks method
      blockMap = Map.fromList [(blockLabel b, b) | b <- blocks]
      ptInfo = computePointsTo method

      -- Find loops worth versioning
      candidates = findVersionCandidates ptInfo loopNest blockMap

      -- Apply versioning
      (optimized, count) = applyVersioning candidates blockMap
  in LoopVersionResult
    { lvOptBlocks = Map.elems optimized
    , lvVersioned = count
    }

-- | Find loops that would benefit from versioning
findVersionCandidates :: PointsToInfo -> LoopNest -> Map BlockId SSABlock -> [VersionCandidate]
findVersionCandidates ptInfo loops blockMap =
  mapMaybe (analyzeForVersioning ptInfo blockMap) (Map.elems loops)

-- | Analyze a loop for versioning opportunities
analyzeForVersioning :: PointsToInfo -> Map BlockId SSABlock -> Loop -> Maybe VersionCandidate
analyzeForVersioning ptInfo blockMap loop =
  let bodyBlocks = [b | bid <- Set.toList (loopBody loop), Just b <- [Map.lookup bid blockMap]]
      -- Find memory accesses that might benefit from alias versioning
      accesses = collectMemAccesses bodyBlocks
      -- Find pairs of accesses that may alias
      mayAliasPairs = findMayAliasPairs ptInfo accesses
      -- Generate guards for alias-free version
      aliasGuards = map makeAliasGuard mayAliasPairs
      -- Calculate benefit
      benefit = length aliasGuards * 5  -- 5 cycles per avoided alias check
  in if not (null aliasGuards) && benefit > 10
     then Just $ VersionCandidate loop aliasGuards benefit
     else Nothing

-- | Memory access in a loop
data MemAccess = MemAccess
  { maBase :: !SSAExpr
  , maField :: !String
  , maIsWrite :: !Bool
  } deriving (Show, Eq)

-- | Collect memory accesses from blocks
collectMemAccesses :: [SSABlock] -> [MemAccess]
collectMemAccesses = concatMap blockAccesses
  where
    blockAccesses SSABlock{..} = concatMap instrAccesses blockInstrs

    instrAccesses = \case
      SSAAssign _ (SSAFieldAccess base field) ->
        [MemAccess base field False]
      SSAFieldStore base field _ _ ->
        [MemAccess base field True]
      _ -> []

-- | Find pairs of accesses that may alias
findMayAliasPairs :: PointsToInfo -> [MemAccess] -> [(MemAccess, MemAccess)]
findMayAliasPairs ptInfo accesses =
  [(a1, a2) | a1 <- accesses
            , a2 <- accesses
            , a1 /= a2
            , maIsWrite a1 || maIsWrite a2  -- At least one write
            , maField a1 == maField a2
            , mayAlias (queryAlias ptInfo (maBase a1) (maBase a2))]

-- | Create an alias guard for two accesses
makeAliasGuard :: (MemAccess, MemAccess) -> VersionGuard
makeAliasGuard (a1, a2) = AliasGuard (maBase a1) (maBase a2)

--------------------------------------------------------------------------------
-- Apply Versioning
--------------------------------------------------------------------------------

-- | Apply versioning transformations
applyVersioning :: [VersionCandidate] -> Map BlockId SSABlock -> (Map BlockId SSABlock, Int)
applyVersioning candidates blockMap =
  foldl' applyOneVersion (blockMap, 0) candidates

-- | Apply versioning to one loop
applyOneVersion :: (Map BlockId SSABlock, Int) -> VersionCandidate -> (Map BlockId SSABlock, Int)
applyOneVersion (blockMap, count) VersionCandidate{..}
  | null vcGuards = (blockMap, count)
  | otherwise =
      case loopPreheader vcLoop of
        Nothing -> (blockMap, count)  -- Need preheader for guard
        Just preheader ->
          case Map.lookup preheader blockMap of
            Nothing -> (blockMap, count)
            Just preBlock ->
              -- Create versioning structure:
              -- preheader:
              --   if (guard) goto optimized_header else goto original_header
              -- optimized_loop: ...
              -- original_loop: ...
              let guardExpr = combineGuards vcGuards
                  -- For now, just add a comment indicating versioning opportunity
                  -- Full implementation would clone the loop
                  newInstrs = blockInstrs preBlock ++
                              [SSAExprStmt (SSACall "__version_guard" [guardExpr])]
                  preBlock' = preBlock { blockInstrs = newInstrs }
                  blockMap' = Map.insert preheader preBlock' blockMap
              in (blockMap', count + 1)

-- | Combine multiple guards into a single expression
combineGuards :: [VersionGuard] -> SSAExpr
combineGuards [] = SSABool True
combineGuards [g] = guardToExpr g
combineGuards (g:gs) = SSABinary And (guardToExpr g) (combineGuards gs)

-- | Convert a guard to an SSA expression
guardToExpr :: VersionGuard -> SSAExpr
guardToExpr = \case
  AliasGuard e1 e2 ->
    -- Generate: e1 != e2 (base pointers are different)
    SSABinary Ne e1 e2
  BoundsGuard idx lo hi ->
    -- Generate: idx >= lo && idx < hi
    SSABinary And (SSABinary Ge idx lo) (SSABinary Lt idx hi)
  TypeGuard _obj _typeName ->
    -- Type guards would need runtime type info
    SSABool True

--------------------------------------------------------------------------------
-- Guard Generation
--------------------------------------------------------------------------------

-- | Generate guard code for a version
generateGuard :: VersionGuard -> [SSAInstr]
generateGuard = \case
  AliasGuard e1 e2 ->
    -- Check that base pointers are different
    let cmp = SSABinary Ne e1 e2
    in [SSAAssign (SSAVar (varName "__guard") 0 Nothing) cmp]

  BoundsGuard idx lo hi ->
    -- Check index is in bounds
    let loCheck = SSABinary Ge idx lo
        hiCheck = SSABinary Lt idx hi
        combined = SSABinary And loCheck hiCheck
    in [SSAAssign (SSAVar (varName "__guard") 0 Nothing) combined]

  TypeGuard _obj _typeName ->
    -- Would need runtime type checking support
    []
