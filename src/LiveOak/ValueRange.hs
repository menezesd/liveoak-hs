{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RecordWildCards #-}

-- | Value Range Analysis for LiveOak SSA.
-- Computes integer value ranges to enable optimizations like:
-- - Bounds check elimination
-- - Dead branch elimination (when condition is always true/false)
-- - Overflow detection
--
-- == Lattice
-- Uses an interval lattice: [lo, hi] represents all integers in [lo, hi]
-- Special values: Top (unknown), Bottom (unreachable)
--
module LiveOak.ValueRange
  ( -- * Range Types
    ValueRange(..)
  , rangeContains
  , rangeIntersect
  , rangeUnion
  , rangeWidth
  , isConstantRange
  , getConstant

    -- * Range Analysis
  , RangeInfo(..)
  , computeRanges
  , lookupRange

    -- * Analysis Queries
  , isAlwaysTrue
  , isAlwaysFalse
  , rangeProvePositive
  , rangeProveNonNegative
  , rangeProveLessThan
  ) where

import LiveOak.SSATypes hiding (varKey)
import LiveOak.CFG
import LiveOak.Ast (BinaryOp(..), UnaryOp(..))

import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Set (Set)
import qualified Data.Set as Set
import Data.List (foldl')

--------------------------------------------------------------------------------
-- Value Range Type
--------------------------------------------------------------------------------

-- | Represents a range of possible integer values
data ValueRange
  = RangeBottom              -- ^ Unreachable/undefined
  | Range !Integer !Integer  -- ^ Closed interval [lo, hi]
  | RangeTop                 -- ^ Unknown (any value possible)
  deriving (Eq, Show)

-- | Check if a value is in the range
rangeContains :: Integer -> ValueRange -> Bool
rangeContains _ RangeBottom = False
rangeContains _ RangeTop = True
rangeContains v (Range lo hi) = v >= lo && v <= hi

-- | Intersect two ranges (meet operation)
rangeIntersect :: ValueRange -> ValueRange -> ValueRange
rangeIntersect RangeBottom _ = RangeBottom
rangeIntersect _ RangeBottom = RangeBottom
rangeIntersect RangeTop r = r
rangeIntersect r RangeTop = r
rangeIntersect (Range lo1 hi1) (Range lo2 hi2) =
  let lo = max lo1 lo2
      hi = min hi1 hi2
  in if lo > hi then RangeBottom else Range lo hi

-- | Union two ranges (join operation)
rangeUnion :: ValueRange -> ValueRange -> ValueRange
rangeUnion RangeBottom r = r
rangeUnion r RangeBottom = r
rangeUnion RangeTop _ = RangeTop
rangeUnion _ RangeTop = RangeTop
rangeUnion (Range lo1 hi1) (Range lo2 hi2) =
  Range (min lo1 lo2) (max hi1 hi2)

-- | Get the width of a range (number of values)
rangeWidth :: ValueRange -> Maybe Integer
rangeWidth RangeBottom = Just 0
rangeWidth RangeTop = Nothing
rangeWidth (Range lo hi) = Just (hi - lo + 1)

-- | Check if range represents a single constant value
isConstantRange :: ValueRange -> Bool
isConstantRange (Range lo hi) = lo == hi
isConstantRange _ = False

-- | Get the constant value if range is a singleton
getConstant :: ValueRange -> Maybe Integer
getConstant (Range lo hi) | lo == hi = Just lo
getConstant _ = Nothing

--------------------------------------------------------------------------------
-- Range Analysis State
--------------------------------------------------------------------------------

-- | Range information for a method
data RangeInfo = RangeInfo
  { riVarRanges :: !(Map VarKey ValueRange)  -- ^ Variable -> range
  , riBlockReachable :: !(Set BlockId)       -- ^ Reachable blocks
  } deriving (Eq, Show)

-- | Empty range info
emptyRangeInfo :: RangeInfo
emptyRangeInfo = RangeInfo Map.empty Set.empty

-- | Lookup range for a variable
lookupRange :: VarKey -> RangeInfo -> ValueRange
lookupRange key ri = Map.findWithDefault RangeTop key (riVarRanges ri)

--------------------------------------------------------------------------------
-- Range Analysis
--------------------------------------------------------------------------------

-- | Compute value ranges for all variables in a method
-- Uses a forward dataflow analysis with interval lattice
computeRanges :: CFG -> [SSABlock] -> RangeInfo
computeRanges cfg blocks =
  let blockMap = Map.fromList [(blockLabel b, b) | b <- blocks]
      entry = cfgEntry cfg
      initInfo = emptyRangeInfo { riBlockReachable = Set.singleton entry }
      -- Iterate until fixed point
      finalInfo = iterateRanges cfg blockMap initInfo
  in finalInfo

-- | Maximum iterations for range analysis
maxRangeIterations :: Int
maxRangeIterations = 50

-- | Iterate until fixed point
iterateRanges :: CFG -> Map BlockId SSABlock -> RangeInfo -> RangeInfo
iterateRanges cfg blockMap = go maxRangeIterations
  where
    go 0 info = info  -- Max iterations reached
    go n info =
      let -- Process all reachable blocks
          reachable = Set.toList (riBlockReachable info)
          info' = foldl' (processRangeBlock cfg blockMap) info reachable
      in if info' == info
         then info'  -- Fixed point
         else go (n - 1) info'

-- | Process a block for range analysis
processRangeBlock :: CFG -> Map BlockId SSABlock -> RangeInfo -> BlockId -> RangeInfo
processRangeBlock cfg blockMap info bid =
  case Map.lookup bid blockMap of
    Nothing -> info
    Just block ->
      let -- Process phi nodes
          info1 = foldl' processRangePhi info (blockPhis block)
          -- Process instructions
          info2 = foldl' processRangeInstr info1 (blockInstrs block)
          -- Mark successors as reachable
          succs = successors cfg bid
          info3 = info2 { riBlockReachable = Set.union (riBlockReachable info2) (Set.fromList succs) }
      in info3

-- | Process a phi node for range analysis
processRangePhi :: RangeInfo -> PhiNode -> RangeInfo
processRangePhi info PhiNode{..} =
  let varKey = (ssaName phiVar, ssaVersion phiVar)
      -- Join ranges from all incoming edges
      incomingRanges = [lookupRange (ssaName v, ssaVersion v) info | (_, v) <- phiArgs]
      joinedRange = foldl' rangeUnion RangeBottom incomingRanges
  in info { riVarRanges = Map.insert varKey joinedRange (riVarRanges info) }

-- | Process an instruction for range analysis
processRangeInstr :: RangeInfo -> SSAInstr -> RangeInfo
processRangeInstr info = \case
  SSAAssign var expr ->
    let varKey = (ssaName var, ssaVersion var)
        range = evalExprRange info expr
    in info { riVarRanges = Map.insert varKey range (riVarRanges info) }

  -- Other instructions don't define ranges
  _ -> info

-- | Evaluate expression range
evalExprRange :: RangeInfo -> SSAExpr -> ValueRange
evalExprRange info = \case
  SSAInt n -> Range (fromIntegral n) (fromIntegral n)

  SSABool True -> Range 1 1
  SSABool False -> Range 0 0

  SSAUse var -> lookupRange (ssaName var, ssaVersion var) info

  SSAUnary Not e ->
    case evalExprRange info e of
      Range 0 0 -> Range 1 1  -- !false = true
      Range 1 1 -> Range 0 0  -- !true = false
      _ -> Range 0 1          -- Boolean result

  SSAUnary Neg e ->
    case evalExprRange info e of
      Range lo hi -> Range (-hi) (-lo)
      r -> r

  SSABinary op l r ->
    let lr = evalExprRange info l
        rr = evalExprRange info r
    in evalBinaryRange op lr rr

  SSATernary c t e ->
    let cr = evalExprRange info c
        tr = evalExprRange info t
        er = evalExprRange info e
    in case cr of
      Range 1 1 -> tr  -- Condition always true
      Range 0 0 -> er  -- Condition always false
      _ -> rangeUnion tr er  -- Could be either

  -- Other expressions have unknown range
  _ -> RangeTop

-- | Evaluate binary operation on ranges
evalBinaryRange :: BinaryOp -> ValueRange -> ValueRange -> ValueRange
evalBinaryRange _ RangeBottom _ = RangeBottom
evalBinaryRange _ _ RangeBottom = RangeBottom
evalBinaryRange op (Range lo1 hi1) (Range lo2 hi2) = case op of
  Add -> Range (lo1 + lo2) (hi1 + hi2)
  Sub -> Range (lo1 - hi2) (hi1 - lo2)
  Mul ->
    let products = [lo1 * lo2, lo1 * hi2, hi1 * lo2, hi1 * hi2]
    in Range (minimum products) (maximum products)
  Div
    | lo2 > 0 -> Range (lo1 `div` hi2) (hi1 `div` lo2)
    | hi2 < 0 -> Range (hi1 `div` hi2) (lo1 `div` lo2)
    | otherwise -> RangeTop  -- Division by zero possible
  Mod
    | lo2 > 0 -> Range 0 (hi2 - 1)
    | otherwise -> RangeTop
  -- Comparison operations return boolean (0 or 1)
  Lt -> boolRange (hi1 < lo2) (lo1 < hi2)
  Le -> boolRange (hi1 <= lo2) (lo1 <= hi2)
  Gt -> boolRange (lo1 > hi2) (hi1 > lo2)
  Ge -> boolRange (lo1 >= hi2) (hi1 >= lo2)
  Eq -> boolRange (lo1 == hi1 && lo2 == hi2 && lo1 == lo2)
                  (not (hi1 < lo2 || hi2 < lo1))
  Ne -> boolRange (hi1 < lo2 || hi2 < lo1)
                  (not (lo1 == hi1 && lo2 == hi2 && lo1 == lo2))
  And -> Range 0 1  -- Boolean and
  Or -> Range 0 1   -- Boolean or
  Concat -> RangeTop  -- String concatenation, not integer
evalBinaryRange _ _ _ = RangeTop

-- | Convert boolean proof to range
boolRange :: Bool -> Bool -> ValueRange
boolRange True _ = Range 1 1    -- Always true
boolRange _ False = Range 0 0   -- Always false
boolRange _ _ = Range 0 1       -- Could be either

--------------------------------------------------------------------------------
-- Analysis Queries
--------------------------------------------------------------------------------

-- | Check if expression is always true
isAlwaysTrue :: RangeInfo -> SSAExpr -> Bool
isAlwaysTrue info expr = evalExprRange info expr == Range 1 1

-- | Check if expression is always false
isAlwaysFalse :: RangeInfo -> SSAExpr -> Bool
isAlwaysFalse info expr = evalExprRange info expr == Range 0 0

-- | Check if variable is always positive
rangeProvePositive :: RangeInfo -> VarKey -> Bool
rangeProvePositive info key = case lookupRange key info of
  Range lo _ -> lo > 0
  _ -> False

-- | Check if variable is always non-negative
rangeProveNonNegative :: RangeInfo -> VarKey -> Bool
rangeProveNonNegative info key = case lookupRange key info of
  Range lo _ -> lo >= 0
  _ -> False

-- | Check if one variable is always less than another
rangeProveLessThan :: RangeInfo -> VarKey -> VarKey -> Bool
rangeProveLessThan info key1 key2 =
  case (lookupRange key1 info, lookupRange key2 info) of
    (Range _ hi1, Range lo2 _) -> hi1 < lo2
    _ -> False
