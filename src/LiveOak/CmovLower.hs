{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RecordWildCards #-}

-- | Conditional Move Lowering.
-- Converts simple if-then-else patterns to conditional move instructions.
--
-- == Pattern
-- @
-- if (cond) { x = a; } else { x = b; }
-- @
-- becomes:
-- @
-- x = b;           // Default value (else)
-- if (cond) x = a; // Conditional override (cmov)
-- @
--
-- == Benefits
-- - Avoids branch misprediction penalty
-- - Better for unpredictable branches
-- - Smaller code size
--
-- == When NOT to Use
-- - When then/else have side effects (calls, stores)
-- - When values are expensive to compute
-- - When branch is highly predictable
--
module LiveOak.CmovLower
  ( -- * Conditional Move Lowering
    lowerToCmov
  , CmovResult(..)

    -- * Pattern Detection
  , CmovCandidate(..)
  , findCmovCandidates
  ) where

import LiveOak.SSATypes
import LiveOak.CFG
import LiveOak.Dominance (DomTree, computeDominators)
import LiveOak.BranchProb (BranchProbInfo, getEdgeProb)

import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Set (Set)
import qualified Data.Set as Set
import Data.List (foldl')
import Data.Maybe (mapMaybe)

--------------------------------------------------------------------------------
-- Types
--------------------------------------------------------------------------------

-- | Conditional move lowering result
data CmovResult = CmovResult
  { cmOptBlocks :: ![SSABlock]
  , cmLowered :: !Int                -- ^ Number of if-then-else patterns lowered
  } deriving (Show)

-- | Candidate for CMOV lowering
data CmovCandidate = CmovCandidate
  { ccCondBlock :: !BlockId          -- ^ Block with the branch
  , ccCondition :: !SSAExpr          -- ^ Branch condition
  , ccThenBlock :: !BlockId          -- ^ Then target
  , ccElseBlock :: !BlockId          -- ^ Else target
  , ccMergeBlock :: !BlockId         -- ^ Merge point
  , ccThenValue :: !SSAExpr          -- ^ Value in then path
  , ccElseValue :: !SSAExpr          -- ^ Value in else path
  , ccResultVar :: !SSAVar           -- ^ Result variable (phi at merge)
  } deriving (Show)

--------------------------------------------------------------------------------
-- Conditional Move Lowering
--------------------------------------------------------------------------------

-- | Lower suitable if-then-else patterns to conditional moves
lowerToCmov :: SSAMethod -> CmovResult
lowerToCmov method =
  let cfg = buildCFG method
      domTree = computeDominators cfg
      blocks = ssaMethodBlocks method
      blockMap = Map.fromList [(blockLabel b, b) | b <- blocks]

      -- Find candidates
      candidates = findCmovCandidates cfg domTree blockMap

      -- Apply lowering
      (optimized, count) = applyCmovLowering candidates blockMap
  in CmovResult
    { cmOptBlocks = Map.elems optimized
    , cmLowered = count
    }

--------------------------------------------------------------------------------
-- Pattern Detection
--------------------------------------------------------------------------------

-- | Find CMOV candidates in a method
findCmovCandidates :: CFG -> DomTree -> Map BlockId SSABlock -> [CmovCandidate]
findCmovCandidates cfg _domTree blockMap =
  mapMaybe (analyzeBlock cfg blockMap) (Map.toList blockMap)

-- | Analyze a block for CMOV opportunity
analyzeBlock :: CFG -> Map BlockId SSABlock -> (BlockId, SSABlock) -> Maybe CmovCandidate
analyzeBlock cfg blockMap (bid, SSABlock{..}) =
  case lastInstr of
    Just (SSABranch cond thenB elseB) ->
      -- Check if this is a diamond pattern with simple phi merge
      case findDiamondMerge cfg thenB elseB of
        Just mergeB ->
          case Map.lookup mergeB blockMap of
            Just mergeBlock ->
              case analyzePhiForCmov blockMap thenB elseB mergeBlock of
                Just (thenVal, elseVal, resultVar) ->
                  -- Check if then/else blocks are suitable
                  if isSuitableForCmov blockMap thenB elseB
                  then Just $ CmovCandidate bid cond thenB elseB mergeB thenVal elseVal resultVar
                  else Nothing
                Nothing -> Nothing
            Nothing -> Nothing
        Nothing -> Nothing
    _ -> Nothing
  where
    lastInstr = if null blockInstrs then Nothing else Just (last blockInstrs)

-- | Find merge point of a diamond pattern
findDiamondMerge :: CFG -> BlockId -> BlockId -> Maybe BlockId
findDiamondMerge cfg thenB elseB =
  let thenSuccs = successors cfg thenB
      elseSuccs = successors cfg elseB
      common = filter (`elem` elseSuccs) thenSuccs
  in case common of
    [merge] -> Just merge
    _ -> Nothing

-- | Analyze phi node for CMOV conversion
analyzePhiForCmov :: Map BlockId SSABlock -> BlockId -> BlockId -> SSABlock
                  -> Maybe (SSAExpr, SSAExpr, SSAVar)
analyzePhiForCmov blockMap thenB elseB SSABlock{..} =
  case blockPhis of
    [phi] ->
      -- Single phi node: good candidate
      let PhiNode{..} = phi
          thenVal = lookup thenB [(b, SSAUse v) | (b, v) <- phiArgs]
          elseVal = lookup elseB [(b, SSAUse v) | (b, v) <- phiArgs]
      in case (thenVal, elseVal) of
        (Just tv, Just ev) -> Just (tv, ev, phiVar)
        _ -> Nothing
    _ -> Nothing  -- Multiple phis - too complex

-- | Check if then/else blocks are suitable for CMOV
isSuitableForCmov :: Map BlockId SSABlock -> BlockId -> BlockId -> Bool
isSuitableForCmov blockMap thenB elseB =
  isSingleAssignment blockMap thenB && isSingleAssignment blockMap elseB

-- | Check if block is just a single assignment and jump
isSingleAssignment :: Map BlockId SSABlock -> BlockId -> Bool
isSingleAssignment blockMap bid =
  case Map.lookup bid blockMap of
    Just SSABlock{..} ->
      case blockInstrs of
        [] -> True  -- Empty block (just jump)
        [SSAAssign _ expr] -> not (hasEffect expr)  -- Single assignment
        [SSAJump _] -> True  -- Just a jump
        [SSAAssign _ expr, SSAJump _] -> not (hasEffect expr)
        _ -> False
    Nothing -> False

-- | Check if expression has side effects
hasEffect :: SSAExpr -> Bool
hasEffect = \case
  SSACall _ _ -> True
  SSAInstanceCall _ _ _ -> True
  SSANewObject _ _ -> True
  SSAUnary _ e -> hasEffect e
  SSABinary _ l r -> hasEffect l || hasEffect r
  SSATernary c t e -> hasEffect c || hasEffect t || hasEffect e
  _ -> False

--------------------------------------------------------------------------------
-- Apply Lowering
--------------------------------------------------------------------------------

-- | Apply CMOV lowering to candidates
applyCmovLowering :: [CmovCandidate] -> Map BlockId SSABlock -> (Map BlockId SSABlock, Int)
applyCmovLowering candidates blockMap = foldl' applyOne (blockMap, 0) candidates

-- | Apply lowering to one candidate
applyOne :: (Map BlockId SSABlock, Int) -> CmovCandidate -> (Map BlockId SSABlock, Int)
applyOne (blockMap, count) CmovCandidate{..} =
  case Map.lookup ccCondBlock blockMap of
    Just condBlock ->
      let -- Transform condition block:
          -- Replace: if (cond) goto then else goto else
          -- With: x = elseVal; if (cond) x = thenVal; goto merge
          newInstrs = init (blockInstrs condBlock) ++  -- Remove branch
            [ SSAAssign ccResultVar ccElseValue         -- Default: else value
            , SSAAssign ccResultVar
                (SSATernary ccCondition ccThenValue ccElseValue)  -- CMOV-like
            , SSAJump ccMergeBlock                       -- Direct jump to merge
            ]
          condBlock' = condBlock { blockInstrs = newInstrs }

          -- Remove the phi from merge block (variable already set)
          mergeBlock' = case Map.lookup ccMergeBlock blockMap of
            Just mb -> mb { blockPhis = filter (not . isPhi ccResultVar) (blockPhis mb) }
            Nothing -> error "Merge block not found"

          blockMap' = Map.insert ccCondBlock condBlock' $
                      Map.insert ccMergeBlock mergeBlock' blockMap
      in (blockMap', count + 1)
    Nothing -> (blockMap, count)
  where
    isPhi var phi = ssaName (phiVar phi) == ssaName var &&
                    ssaVersion (phiVar phi) == ssaVersion var
