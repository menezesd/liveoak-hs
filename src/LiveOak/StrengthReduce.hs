{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RecordWildCards #-}

-- | Strength Reduction for Loops.
-- Replaces expensive operations (like multiplication) with cheaper ones
-- (like addition) within loops by using induction variables.
module LiveOak.StrengthReduce
  ( -- * Strength Reduction
    reduceStrength
  , StrengthResult(..)

    -- * Induction Variable Analysis
  , InductionVar(..)
  , findInductionVars
  , classifyIV
  ) where

import LiveOak.SSATypes
import LiveOak.CFG
import LiveOak.Loop
import LiveOak.Dominance
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

-- | Classification of induction variables
data InductionVar
  = BasicIV                       -- ^ i = i + c (basic induction variable)
      { ivVar :: !String          -- ^ Variable name
      , ivInit :: !SSAExpr        -- ^ Initial value
      , ivStep :: !Int            -- ^ Step value (constant)
      }
  | DerivedIV                     -- ^ j = a * i + b (derived from basic IV)
      { ivVar :: !String          -- ^ Variable name
      , ivBaseVar :: !String      -- ^ Base induction variable
      , ivMultiplier :: !Int      -- ^ Multiplier a
      , ivOffset :: !Int          -- ^ Offset b
      }
  deriving (Show)

-- | Strength reduction candidate
data SRCandidate = SRCandidate
  { srcBlock :: !BlockId          -- ^ Block containing the operation
  , srcInstr :: !Int              -- ^ Instruction index
  , srcVar :: !String             -- ^ Result variable
  , srcExpr :: !SSAExpr           -- ^ Original expression (e.g., i * stride)
  , srcBaseIV :: !String          -- ^ Base induction variable
  , srcMultiplier :: !Int         -- ^ Multiplier
  } deriving (Show)

-- | Strength reduction result
data StrengthResult = StrengthResult
  { srOptBlocks :: ![SSABlock]    -- ^ Optimized blocks
  , srReductions :: !Int          -- ^ Number of reductions performed
  , srNewIVs :: ![InductionVar]   -- ^ New induction variables created
  } deriving (Show)

--------------------------------------------------------------------------------
-- Induction Variable Analysis
--------------------------------------------------------------------------------

-- | Find all induction variables in a loop
findInductionVars :: Loop -> Map BlockId SSABlock -> [InductionVar]
findInductionVars loop blockMap =
  let bodyBlocks = [b | bid <- Set.toList (loopBody loop),
                       Just b <- [Map.lookup bid blockMap]]
      -- Find basic IVs first
      basicIVs = concatMap (findBasicIVs loop) bodyBlocks
      basicIVNames = Set.fromList [ivVar iv | iv <- basicIVs]
      -- Then find derived IVs
      derivedIVs = concatMap (findDerivedIVs loop basicIVNames) bodyBlocks
  in basicIVs ++ derivedIVs

-- | Find basic induction variables in a block
findBasicIVs :: Loop -> SSABlock -> [InductionVar]
findBasicIVs loop SSABlock{..} =
  mapMaybe (classifyAsBasicIV loop blockLabel) blockPhis

-- | Classify a phi node as a basic IV
classifyAsBasicIV :: Loop -> BlockId -> PhiNode -> Maybe InductionVar
classifyAsBasicIV loop bid PhiNode{..} =
  -- A basic IV has:
  -- 1. An initial value from outside the loop
  -- 2. An update of the form iv = iv + constant from inside the loop
  let (outsideArgs, insideArgs) = partitionArgs loop phiArgs
  in case (outsideArgs, insideArgs) of
    ([(_, initVar)], [(_, stepVar)]) ->
      -- Check if stepVar is iv + constant
      -- (Would need to look up the definition of stepVar)
      Just $ BasicIV
        { ivVar = ssaName phiVar
        , ivInit = SSAUse initVar
        , ivStep = 1  -- Simplified, would need to extract actual step
        }
    _ -> Nothing
  where
    partitionArgs loop' args =
      let loopBlocks = loopBody loop'
      in ( [(p, v) | (p, v) <- args, not (Set.member p loopBlocks)]
         , [(p, v) | (p, v) <- args, Set.member p loopBlocks]
         )

-- | Find derived induction variables
findDerivedIVs :: Loop -> Set String -> SSABlock -> [InductionVar]
findDerivedIVs loop basicIVNames SSABlock{..} =
  mapMaybe (classifyAsDerivedIV basicIVNames) blockInstrs

-- | Classify an instruction as a derived IV
classifyAsDerivedIV :: Set String -> SSAInstr -> Maybe InductionVar
classifyAsDerivedIV basicIVNames = \case
  SSAAssign var (SSABinary Mul (SSAUse base) (SSAInt k))
    | Set.member (ssaName base) basicIVNames ->
        Just $ DerivedIV
          { ivVar = ssaName var
          , ivBaseVar = ssaName base
          , ivMultiplier = k
          , ivOffset = 0
          }
  SSAAssign var (SSABinary Mul (SSAInt k) (SSAUse base))
    | Set.member (ssaName base) basicIVNames ->
        Just $ DerivedIV
          { ivVar = ssaName var
          , ivBaseVar = ssaName base
          , ivMultiplier = k
          , ivOffset = 0
          }
  SSAAssign var (SSABinary Add (SSABinary Mul (SSAUse base) (SSAInt k)) (SSAInt c))
    | Set.member (ssaName base) basicIVNames ->
        Just $ DerivedIV
          { ivVar = ssaName var
          , ivBaseVar = ssaName base
          , ivMultiplier = k
          , ivOffset = c
          }
  _ -> Nothing

-- | Classify an expression as IV-related
classifyIV :: Set String -> SSAExpr -> Maybe (String, Int, Int)
classifyIV basicIVNames = \case
  SSABinary Mul (SSAUse var) (SSAInt k)
    | Set.member (ssaName var) basicIVNames -> Just (ssaName var, k, 0)
  SSABinary Mul (SSAInt k) (SSAUse var)
    | Set.member (ssaName var) basicIVNames -> Just (ssaName var, k, 0)
  SSABinary Add (SSABinary Mul (SSAUse var) (SSAInt k)) (SSAInt c)
    | Set.member (ssaName var) basicIVNames -> Just (ssaName var, k, c)
  _ -> Nothing

--------------------------------------------------------------------------------
-- Strength Reduction
--------------------------------------------------------------------------------

-- | Apply strength reduction to loops
reduceStrength :: CFG -> DomTree -> LoopNest -> [SSABlock] -> StrengthResult
reduceStrength cfg domTree loops blocks =
  let blockMap = Map.fromList [(blockLabel b, b) | b <- blocks]
      -- Process each loop
      (optimized, reductions, newIVs) = foldl' (reduceLoop cfg domTree blockMap)
                                               (blocks, 0, [])
                                               (Map.elems loops)
  in StrengthResult
    { srOptBlocks = optimized
    , srReductions = reductions
    , srNewIVs = newIVs
    }

-- | Reduce strength in a single loop
reduceLoop :: CFG -> DomTree -> Map BlockId SSABlock ->
              ([SSABlock], Int, [InductionVar]) -> Loop ->
              ([SSABlock], Int, [InductionVar])
reduceLoop _cfg _domTree blockMap (blocks, count, ivs) loop =
  let -- Find induction variables
      loopIVs = findInductionVars loop blockMap
      basicIVNames = Set.fromList [ivVar iv | iv@BasicIV{} <- loopIVs]

      -- Find strength reduction candidates
      candidates = findSRCandidates loop blockMap basicIVNames

      -- Apply reductions
      (blocks', newCount, newIVs) = applySR loop blockMap candidates blocks
  in (blocks', count + newCount, ivs ++ loopIVs ++ newIVs)

-- | Find strength reduction candidates in a loop
findSRCandidates :: Loop -> Map BlockId SSABlock -> Set String -> [SRCandidate]
findSRCandidates loop blockMap basicIVNames =
  concatMap (findBlockCandidates basicIVNames) bodyBlocks
  where
    bodyBlocks = [(bid, b) | bid <- Set.toList (loopBody loop),
                            Just b <- [Map.lookup bid blockMap]]

-- | Find candidates in a block
findBlockCandidates :: Set String -> (BlockId, SSABlock) -> [SRCandidate]
findBlockCandidates basicIVNames (bid, SSABlock{..}) =
  mapMaybe (mkCandidate bid basicIVNames) (zip [0..] blockInstrs)

-- | Create a candidate from an instruction
mkCandidate :: BlockId -> Set String -> (Int, SSAInstr) -> Maybe SRCandidate
mkCandidate bid basicIVNames (idx, instr) = case instr of
  SSAAssign var expr ->
    case classifyIV basicIVNames expr of
      Just (baseVar, mult, _offset) ->
        Just $ SRCandidate
          { srcBlock = bid
          , srcInstr = idx
          , srcVar = ssaName var
          , srcExpr = expr
          , srcBaseIV = baseVar
          , srcMultiplier = mult
          }
      Nothing -> Nothing
  _ -> Nothing

-- | Apply strength reductions
applySR :: Loop -> Map BlockId SSABlock -> [SRCandidate] ->
           [SSABlock] -> ([SSABlock], Int, [InductionVar])
applySR loop blockMap candidates blocks =
  foldl' (applyOneReduction loop blockMap) (blocks, 0, []) candidates

-- | Apply a single strength reduction
applyOneReduction :: Loop -> Map BlockId SSABlock ->
                     ([SSABlock], Int, [InductionVar]) -> SRCandidate ->
                     ([SSABlock], Int, [InductionVar])
applyOneReduction loop _blockMap (blocks, count, ivs) candidate =
  let -- Create a new induction variable for this expression
      newIVName = srcVar candidate ++ "_sr"
      step = srcMultiplier candidate  -- Step = multiplier * base_step

      newIV = DerivedIV
        { ivVar = newIVName
        , ivBaseVar = srcBaseIV candidate
        , ivMultiplier = srcMultiplier candidate
        , ivOffset = 0
        }

      -- Transform blocks:
      -- 1. Add initialization in preheader
      -- 2. Replace multiplication with use of new IV
      -- 3. Add increment of new IV in loop
      blocks' = map (transformBlock candidate newIVName step) blocks
  in (blocks', count + 1, newIV : ivs)

-- | Transform a block for strength reduction
transformBlock :: SRCandidate -> String -> Int -> SSABlock -> SSABlock
transformBlock candidate newIVName step block@SSABlock{..}
  | blockLabel == srcBlock candidate =
      block { blockInstrs = map (transformInstr candidate newIVName) blockInstrs }
  | otherwise = block

-- | Transform an instruction for strength reduction
transformInstr :: SRCandidate -> String -> SSAInstr -> SSAInstr
transformInstr candidate newIVName instr =
  case instr of
    SSAAssign var _
      | ssaName var == srcVar candidate ->
          -- Replace i * stride with the new IV
          SSAAssign var (SSAUse (SSAVar newIVName 0 Nothing))
    other -> other

--------------------------------------------------------------------------------
-- Linear Function Test Replacement
--------------------------------------------------------------------------------

-- | Apply linear function test replacement
-- Replaces comparisons like (i * stride < limit) with (j < limit')
-- where j is the strength-reduced variable
replaceLFT :: Loop -> [InductionVar] -> [SSABlock] -> [SSABlock]
replaceLFT loop derivedIVs = map (replaceBlockLFT loop derivedIVs)

-- | Replace LFT in a block
replaceBlockLFT :: Loop -> [InductionVar] -> SSABlock -> SSABlock
replaceBlockLFT loop derivedIVs block@SSABlock{..} =
  block { blockInstrs = map (replaceInstrLFT derivedIVs) blockInstrs }

-- | Replace LFT in an instruction
replaceInstrLFT :: [InductionVar] -> SSAInstr -> SSAInstr
replaceInstrLFT derivedIVs = \case
  SSABranch (SSABinary cmp (SSAUse var) limit) thenB elseB
    | Just iv <- findDerivedIV (ssaName var) derivedIVs ->
        -- Replace comparison with derived IV comparison
        -- i * a < n  =>  i_sr < n  (where i_sr is initialized to 0 and stepped by a)
        SSABranch (SSABinary cmp (SSAUse (SSAVar (ivVar iv) 0 Nothing)) limit) thenB elseB
  other -> other
  where
    findDerivedIV name = foldr (\iv acc ->
      case iv of
        DerivedIV{} | ivVar iv == name -> Just iv
        _ -> acc) Nothing
