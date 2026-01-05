{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RecordWildCards #-}

-- | Loop-Closed SSA Form (LCSSA).
-- Transforms code to ensure values defined in loops have phi nodes at exits.
--
-- == Purpose
--
-- LCSSA form makes loop transformations easier by ensuring that:
-- - All values used outside a loop are defined by a phi at the loop exit
-- - Modifications to loop code don't require updating uses outside the loop
--
-- == Example
--
-- @
-- Before:               After:
--   loop:                 loop:
--     x = ...               x = ...
--     br cond exit loop     br cond exit loop
--   exit:                 exit:
--     use(x)                x.lcssa = phi(x, loop)
--                           use(x.lcssa)
-- @
--
module LiveOak.LCSSA
  ( -- * LCSSA Transformation
    transformLCSSA
  , transformLCSSAMethod
  , LCSSAResult(..)
  ) where

import LiveOak.SSATypes
import LiveOak.CFG (CFG, buildCFG, successors, allBlockIds)
import LiveOak.Loop (LoopNest, Loop(..), findLoops)
import LiveOak.Dominance (DomTree, computeDominators)

import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Set (Set)
import qualified Data.Set as Set
import Data.List (foldl')

--------------------------------------------------------------------------------
-- Types
--------------------------------------------------------------------------------

-- | LCSSA transformation result
data LCSSAResult = LCSSAResult
  { lcssaOptBlocks :: ![SSABlock]
  , lcssaPhisAdded :: !Int          -- ^ Number of LCSSA phis added
  } deriving (Show)

--------------------------------------------------------------------------------
-- LCSSA Transformation
--------------------------------------------------------------------------------

-- | Transform blocks to LCSSA form
transformLCSSA :: [SSABlock] -> LCSSAResult
transformLCSSA blocks =
  LCSSAResult
    { lcssaOptBlocks = blocks  -- Simplified: just return blocks as-is for now
    , lcssaPhisAdded = 0
    }

-- | Transform a method to LCSSA form
transformLCSSAMethod :: SSAMethod -> LCSSAResult
transformLCSSAMethod method =
  let cfg = buildCFG method
      domTree = computeDominators cfg
      loopNest = findLoops cfg domTree
      blocks = ssaMethodBlocks method
  in transformWithLoops cfg loopNest blocks

-- | Transform with loop information
transformWithLoops :: CFG -> LoopNest -> [SSABlock] -> LCSSAResult
transformWithLoops cfg loopNest blocks =
  case Map.toList loopNest of
    [] -> LCSSAResult blocks 0  -- No loops
    loops ->
      let -- Find exit blocks for each loop
          loopInfo = map (gatherLoopInfo cfg blocks . snd) loops
          -- Transform each loop
          (blocks', count) = foldl' transformLoop (blocks, 0) loopInfo
      in LCSSAResult blocks' count

-- | Information needed for LCSSA transformation
data LoopTransformInfo = LoopTransformInfo
  { ltiHeader :: !BlockId
  , ltiBlocks :: !(Set BlockId)      -- ^ Blocks in the loop
  , ltiExits :: ![(BlockId, BlockId)] -- ^ (exit source in loop, exit target outside)
  , ltiDefs :: !(Set VarKey)         -- ^ Variables defined in the loop
  } deriving (Show)

-- | Gather information about a loop
gatherLoopInfo :: CFG -> [SSABlock] -> Loop -> LoopTransformInfo
gatherLoopInfo cfg blocks Loop{..} =
  let loopBlockSet = loopBody
      -- Find exit edges
      exits = findExitEdges cfg loopBlockSet
      -- Find definitions in the loop
      defs = findLoopDefs blocks loopBlockSet
  in LoopTransformInfo
    { ltiHeader = loopHeader
    , ltiBlocks = loopBlockSet
    , ltiExits = exits
    , ltiDefs = defs
    }

-- | Find exit edges from a loop
findExitEdges :: CFG -> Set BlockId -> [(BlockId, BlockId)]
findExitEdges cfg loopBlocks =
  [ (from, to)
  | from <- Set.toList loopBlocks
  , to <- successors cfg from
  , not (to `Set.member` loopBlocks)
  ]

-- | Find variables defined in the loop
findLoopDefs :: [SSABlock] -> Set BlockId -> Set VarKey
findLoopDefs blocks loopBlocks =
  Set.fromList $ concatMap getBlockDefs $ filter inLoop blocks
  where
    inLoop SSABlock{..} = blockLabel `Set.member` loopBlocks

    getBlockDefs SSABlock{..} =
      -- Phi definitions
      [(ssaName (phiVar phi), ssaVersion (phiVar phi)) | phi <- blockPhis]
      ++
      -- Instruction definitions
      concatMap getInstrDefs blockInstrs

    getInstrDefs (SSAAssign var _) = [(ssaName var, ssaVersion var)]
    getInstrDefs _ = []

-- | Transform a single loop to LCSSA form
transformLoop :: ([SSABlock], Int) -> LoopTransformInfo -> ([SSABlock], Int)
transformLoop (blocks, count) LoopTransformInfo{..} =
  let -- Find uses outside the loop of values defined inside
      usesOutside = findUsesOutside blocks ltiBlocks ltiDefs
      -- For each such use, we need an LCSSA phi
      (blocks', newCount) = addLCSSAPhis blocks ltiExits usesOutside
  in (blocks', count + newCount)

-- | Find uses outside the loop of values defined inside
findUsesOutside :: [SSABlock] -> Set BlockId -> Set VarKey -> Set VarKey
findUsesOutside blocks loopBlocks loopDefs =
  Set.fromList $ concatMap getBlockUses $ filter outsideLoop blocks
  where
    outsideLoop SSABlock{..} = not (blockLabel `Set.member` loopBlocks)

    getBlockUses SSABlock{..} =
      -- Phi uses
      [(ssaName v, ssaVersion v) | phi <- blockPhis
                                 , (_, v) <- phiArgs phi
                                 , (ssaName v, ssaVersion v) `Set.member` loopDefs]
      ++
      -- Instruction uses
      concatMap getInstrUses blockInstrs

    getInstrUses instr = filter (`Set.member` loopDefs) (getUsedVars instr)

-- | Get variables used by an instruction
getUsedVars :: SSAInstr -> [VarKey]
getUsedVars = \case
  SSAAssign _ expr -> getExprVars expr
  SSABranch cond _ _ -> getExprVars cond
  SSAReturn (Just expr) -> getExprVars expr
  SSAReturn Nothing -> []
  SSAFieldStore target _ _ value -> getExprVars target ++ getExprVars value
  SSAExprStmt expr -> getExprVars expr
  _ -> []

-- | Get variables used by an expression
getExprVars :: SSAExpr -> [VarKey]
getExprVars = \case
  SSAUse var -> [(ssaName var, ssaVersion var)]
  SSABinary _ l r -> getExprVars l ++ getExprVars r
  SSAUnary _ e -> getExprVars e
  SSAFieldAccess target _ -> getExprVars target
  SSAInstanceCall target _ args -> getExprVars target ++ concatMap getExprVars args
  SSACall _ args -> concatMap getExprVars args
  SSANewObject _ args -> concatMap getExprVars args
  _ -> []

-- | Add LCSSA phi nodes
addLCSSAPhis :: [SSABlock] -> [(BlockId, BlockId)] -> Set VarKey -> ([SSABlock], Int)
addLCSSAPhis blocks _exits usesOutside
  | Set.null usesOutside = (blocks, 0)
  | otherwise = (blocks, 0)  -- Simplified: would add phi nodes here
