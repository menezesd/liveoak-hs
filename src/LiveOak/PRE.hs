{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RecordWildCards #-}

-- | Partial Redundancy Elimination (PRE).
-- Eliminates computations that are redundant on some (but not all) paths.
-- Uses the lazy code motion algorithm (Knoop, Rüthing, Steffen).
module LiveOak.PRE
  ( -- * PRE Optimization
    eliminatePartialRedundancy
  , PREResult(..)

    -- * Analysis
  , anticipatable
  , available
  , earliest
  , latest
  ) where

import LiveOak.SSATypes
import LiveOak.CFG
import LiveOak.Dominance
import LiveOak.SSAUtils (blockMapFromList)
import LiveOak.Ast (BinaryOp(..), UnaryOp(..))
import LiveOak.MapUtils (lookupSet)

import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Set (Set)
import qualified Data.Set as Set
import Data.List (foldl')

-- | Safely intersect all sets in a list. Returns empty set for empty list.
intersectAll :: Ord a => [Set a] -> Set a
intersectAll [] = Set.empty
intersectAll (x:xs) = foldl' Set.intersection x xs

--------------------------------------------------------------------------------
-- Types
--------------------------------------------------------------------------------

-- | Expression for PRE (normalized form)
data PREExpr
  = PREBinary !BinaryOp !String !String  -- ^ op, left operand, right operand
  | PREUnary !UnaryOp !String            -- ^ op, operand
  deriving (Eq, Ord, Show)

-- | PRE dataflow sets for a block
data PREBlockInfo = PREBlockInfo
  { preAntIn :: !(Set PREExpr)      -- ^ Anticipatable at entry
  , preAntOut :: !(Set PREExpr)     -- ^ Anticipatable at exit
  , preAvailIn :: !(Set PREExpr)    -- ^ Available at entry
  , preAvailOut :: !(Set PREExpr)   -- ^ Available at exit
  , preEarliest :: !(Set PREExpr)   -- ^ Earliest placement
  , preLatest :: !(Set PREExpr)     -- ^ Latest placement (optimal)
  , preInsert :: !(Set PREExpr)     -- ^ Expressions to insert
  , preDelete :: !(Set PREExpr)     -- ^ Expressions to delete
  } deriving (Show)

-- | PRE result
data PREResult = PREResult
  { preOptBlocks :: ![SSABlock]     -- ^ Optimized blocks
  , preInsertions :: !Int           -- ^ Number of inserted computations
  , preDeletions :: !Int            -- ^ Number of deleted computations
  } deriving (Show)

--------------------------------------------------------------------------------
-- Expression Collection
--------------------------------------------------------------------------------

-- | Collect all expressions from a program
collectExpressions :: [SSABlock] -> Set PREExpr
collectExpressions blocks = Set.unions $ map collectBlockExprs blocks
  where
    collectBlockExprs SSABlock{..} =
      Set.unions $ map collectInstrExprs blockInstrs

    collectInstrExprs = \case
      SSAAssign _ expr -> collectExpr expr
      SSAReturn (Just expr) -> collectExpr expr
      SSABranch cond _ _ -> collectExpr cond
      SSAExprStmt expr -> collectExpr expr
      _ -> Set.empty

    collectExpr = \case
      SSABinary op l r ->
        let left = exprToName l
            right = exprToName r
        in case (left, right) of
          (Just ln, Just rn) -> Set.singleton $ PREBinary op ln rn
          _ -> Set.empty
      SSAUnary op e ->
        case exprToName e of
          Just n -> Set.singleton $ PREUnary op n
          Nothing -> Set.empty
      _ -> Set.empty

    exprToName = \case
      SSAUse var -> Just (ssaName var)
      SSAInt n -> Just (show n)
      SSABool b -> Just (show b)
      _ -> Nothing

-- | Get expressions computed in a block
blockComputes :: SSABlock -> Set PREExpr
blockComputes SSABlock{..} = Set.unions $ map instrComputes blockInstrs
  where
    instrComputes = \case
      SSAAssign _ expr -> exprComputes expr
      _ -> Set.empty

    exprComputes = \case
      SSABinary op l r ->
        case (exprToName l, exprToName r) of
          (Just ln, Just rn) -> Set.singleton $ PREBinary op ln rn
          _ -> Set.empty
      SSAUnary op e ->
        case exprToName e of
          Just n -> Set.singleton $ PREUnary op n
          Nothing -> Set.empty
      _ -> Set.empty

    exprToName = \case
      SSAUse var -> Just (ssaName var)
      SSAInt n -> Just (show n)
      SSABool b -> Just (show b)
      _ -> Nothing

-- | Get expressions killed in a block (operand is redefined)
blockKills :: SSABlock -> Set PREExpr -> Set PREExpr
blockKills SSABlock{..} allPREExprs =
  let defs = Set.fromList [ssaName (phiVar phi) | phi <- blockPhis] `Set.union`
             Set.fromList [ssaName var | SSAAssign var _ <- blockInstrs]
  in Set.filter (exprKilledBy defs) allPREExprs
  where
    exprKilledBy defs = \case
      PREBinary _ l r -> Set.member l defs || Set.member r defs
      PREUnary _ o -> Set.member o defs

--------------------------------------------------------------------------------
-- Anticipatability Analysis (Backward)
--------------------------------------------------------------------------------

-- | Compute anticipatable expressions
-- An expression is anticipatable at point p if it will be computed on every path from p
anticipatable :: CFG -> [SSABlock] -> Map BlockId (Set PREExpr, Set PREExpr)
anticipatable cfg blocks =
  let allExprs = collectExpressions blocks
      blockMap = blockMapFromList blocks
      initial = Map.fromList [(blockLabel b, (allExprs, allExprs)) | b <- blocks]
  in iterateBackward cfg blockMap allExprs initial

-- | Iterate backward dataflow until fixed point
iterateBackward :: CFG -> Map BlockId SSABlock -> Set PREExpr ->
                   Map BlockId (Set PREExpr, Set PREExpr) ->
                   Map BlockId (Set PREExpr, Set PREExpr)
iterateBackward cfg blockMap allExprs current =
  let next = Map.mapWithKey (updateAntBlock cfg blockMap allExprs current) current
  in if next == current then current else iterateBackward cfg blockMap allExprs next

-- | Update anticipatable sets for a block
updateAntBlock :: CFG -> Map BlockId SSABlock -> Set PREExpr ->
                  Map BlockId (Set PREExpr, Set PREExpr) ->
                  BlockId -> (Set PREExpr, Set PREExpr) -> (Set PREExpr, Set PREExpr)
updateAntBlock cfg blockMap allExprs antSets bid _ =
  case Map.lookup bid blockMap of
    Nothing -> (Set.empty, Set.empty)
    Just block ->
      let -- AntOut = intersection of AntIn of successors
          succs = successors cfg bid
          antOut = intersectAll [fst $ Map.findWithDefault (Set.empty, Set.empty) s antSets | s <- succs]
          -- AntIn = (AntOut - Kill) ∪ Comp
          comp = blockComputes block
          kill = blockKills block allExprs
          antIn = Set.union comp (Set.difference antOut kill)
      in (antIn, antOut)

--------------------------------------------------------------------------------
-- Availability Analysis (Forward)
--------------------------------------------------------------------------------

-- | Compute available expressions
-- An expression is available at point p if it has been computed on every path to p
available :: CFG -> [SSABlock] -> Map BlockId (Set PREExpr, Set PREExpr)
available cfg blocks =
  let allExprs = collectExpressions blocks
      blockMap = blockMapFromList blocks
      initial = Map.fromList [(blockLabel b, (Set.empty, Set.empty)) | b <- blocks]
  in iterateForward cfg blockMap allExprs initial

-- | Iterate forward dataflow until fixed point
iterateForward :: CFG -> Map BlockId SSABlock -> Set PREExpr ->
                  Map BlockId (Set PREExpr, Set PREExpr) ->
                  Map BlockId (Set PREExpr, Set PREExpr)
iterateForward cfg blockMap allExprs current =
  let next = Map.mapWithKey (updateAvailBlock cfg blockMap allExprs current) current
  in if next == current then current else iterateForward cfg blockMap allExprs next

-- | Update available sets for a block
updateAvailBlock :: CFG -> Map BlockId SSABlock -> Set PREExpr ->
                    Map BlockId (Set PREExpr, Set PREExpr) ->
                    BlockId -> (Set PREExpr, Set PREExpr) -> (Set PREExpr, Set PREExpr)
updateAvailBlock cfg blockMap allExprs availSets bid _ =
  case Map.lookup bid blockMap of
    Nothing -> (Set.empty, Set.empty)
    Just block ->
      let -- AvailIn = intersection of AvailOut of predecessors
          preds = predecessors cfg bid
          availIn = intersectAll [snd $ Map.findWithDefault (Set.empty, Set.empty) p availSets | p <- preds]
          -- AvailOut = (AvailIn - Kill) ∪ Comp
          comp = blockComputes block
          kill = blockKills block allExprs
          availOut = Set.union comp (Set.difference availIn kill)
      in (availIn, availOut)

--------------------------------------------------------------------------------
-- Earliest and Latest Placement
--------------------------------------------------------------------------------

-- | Compute earliest placement points
-- Earliest = places where expression becomes anticipatable but not yet available
earliest :: Map BlockId (Set PREExpr, Set PREExpr) ->  -- ^ Anticipatable
            Map BlockId (Set PREExpr, Set PREExpr) ->  -- ^ Available
            Map BlockId (Set PREExpr)
earliest antSets availSets =
  Map.intersectionWith computeEarliest antSets availSets
  where
    computeEarliest (antIn, _) (availIn, _) =
      Set.difference antIn availIn

-- | Compute latest placement points (optimal positions)
-- Latest delays computation as long as possible while still being beneficial
latest :: CFG -> Map BlockId (Set PREExpr) -> Map BlockId (Set PREExpr, Set PREExpr) ->
          Map BlockId (Set PREExpr)
latest cfg earliestSets antSets =
  Map.mapWithKey (computeLatest cfg earliestSets antSets) earliestSets

computeLatest :: CFG -> Map BlockId (Set PREExpr) -> Map BlockId (Set PREExpr, Set PREExpr) ->
                 BlockId -> Set PREExpr -> Set PREExpr
computeLatest cfg earliestSets antSets bid earliestHere =
  let succs = successors cfg bid
      -- Can delay if all successors either have the expression earliest or anticipate it
      canDelay expr = all (canDelayTo expr) succs
      canDelayTo expr succId =
        let succEarliest = lookupSet succId earliestSets
            (succAntIn, _) = Map.findWithDefault (Set.empty, Set.empty) succId antSets
        in Set.member expr succEarliest || Set.member expr succAntIn
  in Set.filter (not . canDelay) earliestHere

--------------------------------------------------------------------------------
-- PRE Transformation
--------------------------------------------------------------------------------

-- | Eliminate partial redundancies
eliminatePartialRedundancy :: CFG -> DomTree -> [SSABlock] -> PREResult
eliminatePartialRedundancy cfg _domTree blocks =
  let -- Compute dataflow information
      antSets = anticipatable cfg blocks
      availSets = available cfg blocks
      earliestSets = earliest antSets availSets
      latestSets = latest cfg earliestSets antSets

      -- Determine insertions and deletions
      insertions = computeInsertions latestSets availSets
      deletions = computeDeletions latestSets availSets

      -- Apply transformations
      optimized = applyPRE insertions deletions blocks

      -- Count changes
      insertCount = sum [Set.size s | s <- Map.elems insertions]
      deleteCount = sum [Set.size s | s <- Map.elems deletions]
  in PREResult
    { preOptBlocks = optimized
    , preInsertions = insertCount
    , preDeletions = deleteCount
    }

-- | Compute where to insert expressions
computeInsertions :: Map BlockId (Set PREExpr) ->
                     Map BlockId (Set PREExpr, Set PREExpr) ->
                     Map BlockId (Set PREExpr)
computeInsertions latestSets availSets =
  Map.intersectionWith insertHere latestSets availSets
  where
    insertHere latest' (availIn, _) =
      Set.difference latest' availIn

-- | Compute where to delete expressions
computeDeletions :: Map BlockId (Set PREExpr) ->
                    Map BlockId (Set PREExpr, Set PREExpr) ->
                    Map BlockId (Set PREExpr)
computeDeletions latestSets availSets =
  Map.intersectionWith deleteHere latestSets availSets
  where
    deleteHere latest' (availIn, _) =
      Set.intersection latest' availIn

-- | Apply PRE transformations to blocks
applyPRE :: Map BlockId (Set PREExpr) ->
            Map BlockId (Set PREExpr) ->
            [SSABlock] -> [SSABlock]
applyPRE insertions deletions = map applyToBlock
  where
    applyToBlock block@SSABlock{..} =
      let toInsert = lookupSet blockLabel insertions
          toDelete = lookupSet blockLabel deletions
          -- Insert expressions at beginning (after phis)
          insertedInstrs = map exprToInstr (Set.toList toInsert)
          -- Delete redundant computations
          filteredInstrs = filter (not . shouldDelete toDelete) blockInstrs
      in block { blockInstrs = insertedInstrs ++ filteredInstrs }

    exprToInstr = \case
      PREBinary op l r ->
        -- Create a temporary variable for the result
        let tempVar = SSAVar ("__pre_" ++ show op ++ "_" ++ l ++ "_" ++ r) 0 Nothing
            expr = SSABinary op (nameToExpr l) (nameToExpr r)
        in SSAAssign tempVar expr
      PREUnary op o ->
        let tempVar = SSAVar ("__pre_" ++ show op ++ "_" ++ o) 0 Nothing
            expr = SSAUnary op (nameToExpr o)
        in SSAAssign tempVar expr

    shouldDelete toDelete = \case
      SSAAssign _ (SSABinary op l r) ->
        case (exprToName l, exprToName r) of
          (Just ln, Just rn) -> Set.member (PREBinary op ln rn) toDelete
          _ -> False
      SSAAssign _ (SSAUnary op e) ->
        case exprToName e of
          Just n -> Set.member (PREUnary op n) toDelete
          Nothing -> False
      _ -> False

    exprToName = \case
      SSAUse var -> Just (ssaName var)
      SSAInt n -> Just (show n)
      SSABool b -> Just (show b)
      _ -> Nothing

    nameToExpr name
      | all (`elem` ("-0123456789" :: String)) name = SSAInt (read name)
      | name == "True" = SSABool True
      | name == "False" = SSABool False
      | otherwise = SSAUse (SSAVar name 0 Nothing)
