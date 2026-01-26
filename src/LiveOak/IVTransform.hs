{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RecordWildCards #-}

-- | Induction Variable Transformations.
-- Optimizes loop induction variables through widening and narrowing.
--
-- == Widening
-- Convert narrow IVs to wider types to avoid sign extension:
-- @
-- for (byte i = 0; i < 100; i++) { arr[i] = ... }
-- @
-- becomes:
-- @
-- for (int i = 0; i < 100; i++) { arr[i] = ... }  // No sign-extend on each iteration
-- @
--
-- == Narrowing
-- Convert wide IVs to narrower types when range allows:
-- @
-- for (long i = 0; i < 10; i++) { ... }
-- @
-- becomes:
-- @
-- for (int i = 0; i < 10; i++) { ... }  // Smaller registers, faster ops
-- @
--
module LiveOak.IVTransform
  ( -- * IV Transformations
    transformIVs
  , IVTransformResult(..)

    -- * Widening
  , widenIV
  , shouldWiden

    -- * Narrowing
  , narrowIV
  , shouldNarrow
  ) where

import LiveOak.SSATypes
import LiveOak.CFG
import LiveOak.Loop
import LiveOak.Dominance (DomTree, computeDominators)
import LiveOak.ValueRange
import LiveOak.StrengthReduce (InductionVar(..), findInductionVars)

import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Set (Set)
import qualified Data.Set as Set
import Data.List (foldl')
import Data.Maybe (mapMaybe)

--------------------------------------------------------------------------------
-- Types
--------------------------------------------------------------------------------

-- | IV transformation result
data IVTransformResult = IVTransformResult
  { ivtOptBlocks :: ![SSABlock]
  , ivtWidened :: !Int               -- ^ IVs widened
  , ivtNarrowed :: !Int              -- ^ IVs narrowed
  } deriving (Show)

-- | IV type classification
data IVType
  = IVByte                           -- ^ 8-bit
  | IVShort                          -- ^ 16-bit
  | IVInt                            -- ^ 32-bit
  | IVLong                           -- ^ 64-bit
  deriving (Eq, Ord, Show)

--------------------------------------------------------------------------------
-- IV Transformation
--------------------------------------------------------------------------------

-- | Apply IV transformations
transformIVs :: SSAMethod -> IVTransformResult
transformIVs method =
  let cfg = buildCFG method
      domTree = computeDominators cfg
      loopNest = findLoops cfg domTree
      blocks = ssaMethodBlocks method
      blockMap = Map.fromList [(blockLabel b, b) | b <- blocks]
      rangeInfo = computeRanges cfg blocks

      -- Find IVs and their ranges
      ivRanges = findIVRanges loopNest blockMap rangeInfo

      -- Apply widening/narrowing
      (optimized, widened, narrowed) = applyTransforms ivRanges blockMap
  in IVTransformResult
    { ivtOptBlocks = Map.elems optimized
    , ivtWidened = widened
    , ivtNarrowed = narrowed
    }

-- | IV with range information
data IVWithRange = IVWithRange
  { ivrIV :: !InductionVar
  , ivrRange :: !ValueRange
  , ivrCurrentType :: !IVType
  , ivrOptimalType :: !IVType
  } deriving (Show)

-- | Find IVs and their ranges
findIVRanges :: LoopNest -> Map BlockId SSABlock -> RangeInfo -> [IVWithRange]
findIVRanges loops blockMap rangeInfo =
  concatMap (loopIVRanges blockMap rangeInfo) (Map.elems loops)

-- | Find IV ranges for a single loop
loopIVRanges :: Map BlockId SSABlock -> RangeInfo -> Loop -> [IVWithRange]
loopIVRanges blockMap rangeInfo loop =
  let ivs = findInductionVars loop blockMap
  in mapMaybe (analyzeIVRange rangeInfo) ivs

-- | Analyze IV range and optimal type
analyzeIVRange :: RangeInfo -> InductionVar -> Maybe IVWithRange
analyzeIVRange rangeInfo iv = case iv of
  BasicIV{..} ->
    let varKey = (varName ivVar, 0)  -- Simplified key
        range = lookupRange varKey rangeInfo
        currentType = IVLong  -- Assume 64-bit for now
        optimalType = optimalTypeForRange range
    in if optimalType /= currentType
       then Just $ IVWithRange iv range currentType optimalType
       else Nothing
  _ -> Nothing

-- | Determine optimal type for a range
optimalTypeForRange :: ValueRange -> IVType
optimalTypeForRange = \case
  Range lo hi
    | lo >= -128 && hi <= 127 -> IVByte
    | lo >= -32768 && hi <= 32767 -> IVShort
    | lo >= -2147483648 && hi <= 2147483647 -> IVInt
    | otherwise -> IVLong
  _ -> IVLong

--------------------------------------------------------------------------------
-- Widening
--------------------------------------------------------------------------------

-- | Check if IV should be widened
shouldWiden :: IVWithRange -> Bool
shouldWiden IVWithRange{..} =
  -- Widen if current type is narrower than machine word
  -- and widening would avoid repeated sign extension
  ivrCurrentType < IVLong && hasArrayAccess ivrIV
  where
    hasArrayAccess _ = True  -- Simplified: assume all IVs are used in array access

-- | Widen an IV to 64-bit
widenIV :: IVWithRange -> Map BlockId SSABlock -> Map BlockId SSABlock
widenIV IVWithRange{..} blockMap =
  -- Transform IV operations to use 64-bit arithmetic
  -- This would involve updating the IV definition and uses
  blockMap  -- Placeholder

--------------------------------------------------------------------------------
-- Narrowing
--------------------------------------------------------------------------------

-- | Check if IV should be narrowed
shouldNarrow :: IVWithRange -> Bool
shouldNarrow IVWithRange{..} =
  -- Narrow if range fits in smaller type and it would be beneficial
  ivrOptimalType < ivrCurrentType
  && rangeIsKnown ivrRange
  where
    rangeIsKnown (Range _ _) = True
    rangeIsKnown _ = False

-- | Narrow an IV to smaller type
narrowIV :: IVWithRange -> Map BlockId SSABlock -> Map BlockId SSABlock
narrowIV IVWithRange{..} blockMap =
  -- Transform IV operations to use narrower arithmetic
  blockMap  -- Placeholder

--------------------------------------------------------------------------------
-- Apply Transforms
--------------------------------------------------------------------------------

-- | Apply all IV transformations
applyTransforms :: [IVWithRange] -> Map BlockId SSABlock -> (Map BlockId SSABlock, Int, Int)
applyTransforms ivs blockMap =
  let -- Find IVs to widen
      toWiden = filter shouldWiden ivs
      -- Find IVs to narrow
      toNarrow = filter shouldNarrow ivs
      -- Apply widening
      (blockMap1, widened) = foldl' applyWiden (blockMap, 0) toWiden
      -- Apply narrowing
      (blockMap2, narrowed) = foldl' applyNarrow (blockMap1, 0) toNarrow
  in (blockMap2, widened, narrowed)

-- | Apply widening to one IV
applyWiden :: (Map BlockId SSABlock, Int) -> IVWithRange -> (Map BlockId SSABlock, Int)
applyWiden (blockMap, count) ivr =
  let blockMap' = widenIV ivr blockMap
  in (blockMap', count + 1)

-- | Apply narrowing to one IV
applyNarrow :: (Map BlockId SSABlock, Int) -> IVWithRange -> (Map BlockId SSABlock, Int)
applyNarrow (blockMap, count) ivr =
  let blockMap' = narrowIV ivr blockMap
  in (blockMap', count + 1)
