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
  , lookupRangeInBlock

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
  { riVarRanges :: !(Map VarKey ValueRange)  -- ^ Variable -> range (global)
  , riBlockRanges :: !(Map BlockId (Map VarKey ValueRange))  -- ^ Per-block ranges
  , riBlockReachable :: !(Set BlockId)       -- ^ Reachable blocks
  , riEdgeConstraints :: !(Map (BlockId, BlockId) [(VarKey, ValueRange)])  -- ^ Edge constraints
  } deriving (Eq, Show)

-- | Empty range info
emptyRangeInfo :: RangeInfo
emptyRangeInfo = RangeInfo Map.empty Map.empty Set.empty Map.empty

-- | Lookup range for a variable (global)
lookupRange :: VarKey -> RangeInfo -> ValueRange
lookupRange key ri = Map.findWithDefault RangeTop key (riVarRanges ri)

-- | Lookup range for a variable in a specific block (with narrowing)
lookupRangeInBlock :: BlockId -> VarKey -> RangeInfo -> ValueRange
lookupRangeInBlock bid key ri =
  case Map.lookup bid (riBlockRanges ri) of
    Just blockRanges -> Map.findWithDefault (lookupRange key ri) key blockRanges
    Nothing -> lookupRange key ri

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
      let -- Compute entry ranges by merging predecessors with edge constraints
          preds = predecessors cfg bid
          entryRanges = computeEntryRanges info preds bid
          -- Start with entry ranges for this block
          info0 = info { riBlockRanges = Map.insert bid entryRanges (riBlockRanges info) }
          -- Process phi nodes (using block-local context)
          info1 = foldl' (processRangePhiInBlock bid) info0 (blockPhis block)
          -- Process instructions
          info2 = foldl' (processRangeInstrInBlock bid) info1 (blockInstrs block)
          -- Extract edge constraints from branch and mark successors
          info3 = extractEdgeConstraints bid block info2
          -- Mark successors as reachable
          succs = successors cfg bid
          info4 = info3 { riBlockReachable = Set.union (riBlockReachable info3) (Set.fromList succs) }
      in info4

-- | Compute entry ranges for a block by merging predecessor ranges with edge constraints
computeEntryRanges :: RangeInfo -> [BlockId] -> BlockId -> Map VarKey ValueRange
computeEntryRanges info preds bid =
  case preds of
    [] -> Map.empty  -- Entry block, use global ranges
    _ ->
      let -- Get ranges from each predecessor, applying edge constraints
          predRanges = [applyEdgeConstraints info pred bid | pred <- preds]
          -- Join all predecessor ranges
          allKeys = Set.toList $ Set.unions [Map.keysSet r | r <- predRanges]
          joinedRanges = [(k, foldl' rangeUnion RangeBottom [Map.findWithDefault RangeTop k r | r <- predRanges]) | k <- allKeys]
      in Map.fromList joinedRanges

-- | Apply edge constraints from pred->bid to predecessor's ranges
applyEdgeConstraints :: RangeInfo -> BlockId -> BlockId -> Map VarKey ValueRange
applyEdgeConstraints info pred bid =
  let predRanges = Map.findWithDefault Map.empty pred (riBlockRanges info)
      constraints = Map.findWithDefault [] (pred, bid) (riEdgeConstraints info)
      -- Apply each constraint by intersecting
      applyConstraint ranges (key, constraintRange) =
        let currentRange = Map.findWithDefault RangeTop key ranges
            narrowed = rangeIntersect currentRange constraintRange
        in Map.insert key narrowed ranges
  in foldl' applyConstraint predRanges constraints

-- | Extract edge constraints from a branch instruction
extractEdgeConstraints :: BlockId -> SSABlock -> RangeInfo -> RangeInfo
extractEdgeConstraints bid block info =
  case lastInstr (blockInstrs block) of
    Just (SSABranch cond thenB elseB) ->
      let (thenConstraints, elseConstraints) = extractBranchConstraints info cond
          info1 = addEdgeConstraints (bid, thenB) thenConstraints info
          info2 = addEdgeConstraints (bid, elseB) elseConstraints info1
      in info2
    _ -> info
  where
    lastInstr [] = Nothing
    lastInstr xs = Just (last xs)

-- | Add edge constraints
addEdgeConstraints :: (BlockId, BlockId) -> [(VarKey, ValueRange)] -> RangeInfo -> RangeInfo
addEdgeConstraints _ [] info = info
addEdgeConstraints edge constraints info =
  info { riEdgeConstraints = Map.insertWith (++) edge constraints (riEdgeConstraints info) }

-- | Extract constraints from a branch condition
-- Returns (then-branch constraints, else-branch constraints)
extractBranchConstraints :: RangeInfo -> SSAExpr -> ([(VarKey, ValueRange)], [(VarKey, ValueRange)])
extractBranchConstraints info = \case
  -- x < N: then x in [lo, N-1], else x in [N, hi]
  SSABinary Lt (SSAUse var) (SSAInt n) ->
    let key = (ssaName var, ssaVersion var)
        current = lookupRange key info
    in case current of
      Range lo hi ->
        ( [(key, Range lo (min hi (fromIntegral n - 1)))]
        , [(key, Range (max lo (fromIntegral n)) hi)] )
      _ -> ([], [])

  -- x <= N: then x in [lo, N], else x in [N+1, hi]
  SSABinary Le (SSAUse var) (SSAInt n) ->
    let key = (ssaName var, ssaVersion var)
        current = lookupRange key info
    in case current of
      Range lo hi ->
        ( [(key, Range lo (min hi (fromIntegral n)))]
        , [(key, Range (max lo (fromIntegral n + 1)) hi)] )
      _ -> ([], [])

  -- x > N: then x in [N+1, hi], else x in [lo, N]
  SSABinary Gt (SSAUse var) (SSAInt n) ->
    let key = (ssaName var, ssaVersion var)
        current = lookupRange key info
    in case current of
      Range lo hi ->
        ( [(key, Range (max lo (fromIntegral n + 1)) hi)]
        , [(key, Range lo (min hi (fromIntegral n)))] )
      _ -> ([], [])

  -- x >= N: then x in [N, hi], else x in [lo, N-1]
  SSABinary Ge (SSAUse var) (SSAInt n) ->
    let key = (ssaName var, ssaVersion var)
        current = lookupRange key info
    in case current of
      Range lo hi ->
        ( [(key, Range (max lo (fromIntegral n)) hi)]
        , [(key, Range lo (min hi (fromIntegral n - 1)))] )
      _ -> ([], [])

  -- x == N: then x in [N, N], else unchanged (could refine but complex)
  SSABinary Eq (SSAUse var) (SSAInt n) ->
    let key = (ssaName var, ssaVersion var)
    in ( [(key, Range (fromIntegral n) (fromIntegral n))]
       , [] )

  -- x != N: then unchanged, else x in [N, N]
  SSABinary Ne (SSAUse var) (SSAInt n) ->
    let key = (ssaName var, ssaVersion var)
    in ( []
       , [(key, Range (fromIntegral n) (fromIntegral n))] )

  -- Handle reversed comparisons (N < x means x > N)
  SSABinary Lt (SSAInt n) (SSAUse var) ->
    extractBranchConstraints info (SSABinary Gt (SSAUse var) (SSAInt n))
  SSABinary Le (SSAInt n) (SSAUse var) ->
    extractBranchConstraints info (SSABinary Ge (SSAUse var) (SSAInt n))
  SSABinary Gt (SSAInt n) (SSAUse var) ->
    extractBranchConstraints info (SSABinary Lt (SSAUse var) (SSAInt n))
  SSABinary Ge (SSAInt n) (SSAUse var) ->
    extractBranchConstraints info (SSABinary Le (SSAUse var) (SSAInt n))

  -- Variable vs variable comparisons
  SSABinary Lt (SSAUse v1) (SSAUse v2) ->
    let key1 = (ssaName v1, ssaVersion v1)
        key2 = (ssaName v2, ssaVersion v2)
        r1 = lookupRange key1 info
        r2 = lookupRange key2 info
    in case (r1, r2) of
      (Range lo1 hi1, Range lo2 hi2) ->
        -- In then: v1 < v2, so v1 <= hi2-1 and v2 >= lo1+1
        ( [(key1, Range lo1 (min hi1 (hi2 - 1))), (key2, Range (max lo2 (lo1 + 1)) hi2)]
        -- In else: v1 >= v2
        , [(key1, Range (max lo1 lo2) hi1), (key2, Range lo2 (min hi2 hi1))] )
      _ -> ([], [])

  _ -> ([], [])

-- | Process a phi node for range analysis
processRangePhi :: RangeInfo -> PhiNode -> RangeInfo
processRangePhi info PhiNode{..} =
  let varKey = (ssaName phiVar, ssaVersion phiVar)
      -- Join ranges from all incoming edges
      incomingRanges = [lookupRange (ssaName v, ssaVersion v) info | (_, v) <- phiArgs]
      joinedRange = foldl' rangeUnion RangeBottom incomingRanges
  in info { riVarRanges = Map.insert varKey joinedRange (riVarRanges info) }

-- | Process a phi node with block-local context
processRangePhiInBlock :: BlockId -> RangeInfo -> PhiNode -> RangeInfo
processRangePhiInBlock bid info PhiNode{..} =
  let varKey = (ssaName phiVar, ssaVersion phiVar)
      -- Join ranges from all incoming edges, using edge-constrained ranges
      incomingRanges = [lookupRangeFromEdge info pred bid (ssaName v, ssaVersion v) | (pred, v) <- phiArgs]
      joinedRange = foldl' rangeUnion RangeBottom incomingRanges
      -- Update both global and block-local ranges
      newGlobal = Map.insert varKey joinedRange (riVarRanges info)
      blockRanges = Map.findWithDefault Map.empty bid (riBlockRanges info)
      newBlockRanges = Map.insert varKey joinedRange blockRanges
  in info { riVarRanges = newGlobal
          , riBlockRanges = Map.insert bid newBlockRanges (riBlockRanges info) }

-- | Lookup range considering edge constraints
lookupRangeFromEdge :: RangeInfo -> BlockId -> BlockId -> VarKey -> ValueRange
lookupRangeFromEdge info pred bid key =
  let baseRange = lookupRangeInBlock pred key info
      constraints = Map.findWithDefault [] (pred, bid) (riEdgeConstraints info)
      relevantConstraints = [r | (k, r) <- constraints, k == key]
  in foldl' rangeIntersect baseRange relevantConstraints

-- | Process an instruction for range analysis
processRangeInstr :: RangeInfo -> SSAInstr -> RangeInfo
processRangeInstr info = \case
  SSAAssign var expr ->
    let varKey = (ssaName var, ssaVersion var)
        range = evalExprRange info expr
    in info { riVarRanges = Map.insert varKey range (riVarRanges info) }

  -- Other instructions don't define ranges
  _ -> info

-- | Process an instruction with block-local context
processRangeInstrInBlock :: BlockId -> RangeInfo -> SSAInstr -> RangeInfo
processRangeInstrInBlock bid info = \case
  SSAAssign var expr ->
    let varKey = (ssaName var, ssaVersion var)
        range = evalExprRangeInBlock bid info expr
        -- Update both global and block-local ranges
        newGlobal = Map.insert varKey range (riVarRanges info)
        blockRanges = Map.findWithDefault Map.empty bid (riBlockRanges info)
        newBlockRanges = Map.insert varKey range blockRanges
    in info { riVarRanges = newGlobal
            , riBlockRanges = Map.insert bid newBlockRanges (riBlockRanges info) }

  -- Other instructions don't define ranges
  _ -> info

-- | Evaluate expression range using block-local context
evalExprRangeInBlock :: BlockId -> RangeInfo -> SSAExpr -> ValueRange
evalExprRangeInBlock bid info = \case
  SSAInt n -> Range (fromIntegral n) (fromIntegral n)

  SSABool True -> Range 1 1
  SSABool False -> Range 0 0

  SSAUse var -> lookupRangeInBlock bid (ssaName var, ssaVersion var) info

  SSAUnary Not e ->
    case evalExprRangeInBlock bid info e of
      Range 0 0 -> Range 1 1  -- !false = true
      Range 1 1 -> Range 0 0  -- !true = false
      _ -> Range 0 1          -- Boolean result

  SSAUnary Neg e ->
    case evalExprRangeInBlock bid info e of
      Range lo hi -> Range (-hi) (-lo)
      r -> r

  SSABinary op l r ->
    let lr = evalExprRangeInBlock bid info l
        rr = evalExprRangeInBlock bid info r
    in evalBinaryRange op lr rr

  SSATernary c t e ->
    let cr = evalExprRangeInBlock bid info c
        tr = evalExprRangeInBlock bid info t
        er = evalExprRangeInBlock bid info e
    in case cr of
      Range 1 1 -> tr  -- Condition always true
      Range 0 0 -> er  -- Condition always false
      _ -> rangeUnion tr er  -- Could be either

  -- Other expressions have unknown range
  _ -> RangeTop

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
    | lo2 == 0 && hi2 == 0 -> RangeBottom  -- Definite division by zero (unreachable)
    | otherwise -> RangeTop  -- Division by zero possible but not certain
  Mod
    | lo2 > 0 -> Range 0 (hi2 - 1)
    | lo2 == 0 && hi2 == 0 -> RangeBottom  -- Definite mod by zero (unreachable)
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
