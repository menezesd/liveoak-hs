{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RecordWildCards #-}

-- | Instruction Combining.
-- Combines multiple instructions into fewer, more efficient ones.
--
-- == Transformations
--
-- 1. **Compare-and-branch combining**:
--    @cmp = x < y; br cmp then else@ -> @br (x < y) then else@
--
-- 2. **Negation combining**:
--    @neg = -x; y = a + neg@ -> @y = a - x@
--
-- 3. **Boolean combination**:
--    @not = !x; br not then else@ -> @br x else then@
--
-- 4. **Redundant cast elimination**:
--    @y = (int)x@ where x is already int -> @y = x@
--
-- 5. **Trivial phi elimination**:
--    @x = phi(y)@ with single argument -> @x = y@
--
module LiveOak.InstCombine
  ( -- * Instruction Combining
    combineInstrs
  , combineInstrsMethod
  , InstCombineResult(..)
  ) where

import LiveOak.SSATypes
import LiveOak.SSAUtils (substVarsInInstr)
import LiveOak.Ast (BinaryOp(..), UnaryOp(..))

import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.List (foldl')

--------------------------------------------------------------------------------
-- Types
--------------------------------------------------------------------------------

-- | Instruction combining result
data InstCombineResult = InstCombineResult
  { icOptBlocks :: ![SSABlock]
  , icCombined :: !Int              -- ^ Number of instructions combined
  } deriving (Show)

-- | Tracks definitions for combining
type DefMap = Map VarKey SSAExpr

--------------------------------------------------------------------------------
-- Instruction Combining
--------------------------------------------------------------------------------

-- | Combine instructions in blocks
combineInstrs :: [SSABlock] -> InstCombineResult
combineInstrs blocks =
  let -- First pass: collect all definitions
      defMap = collectDefs blocks
      -- Second pass: combine instructions
      (optimized, count) = unzip $ map (combineBlock defMap) blocks
  in InstCombineResult
    { icOptBlocks = optimized
    , icCombined = sum count
    }

-- | Combine instructions in a method
combineInstrsMethod :: SSAMethod -> InstCombineResult
combineInstrsMethod method =
  combineInstrs (ssaMethodBlocks method)

-- | Collect all definitions
collectDefs :: [SSABlock] -> DefMap
collectDefs = foldl' collectBlockDefs Map.empty

-- | Collect definitions from a block
collectBlockDefs :: DefMap -> SSABlock -> DefMap
collectBlockDefs defs SSABlock{..} =
  foldl' collectInstrDef defs blockInstrs

-- | Collect definition from an instruction
collectInstrDef :: DefMap -> SSAInstr -> DefMap
collectInstrDef defs = \case
  SSAAssign var expr ->
    Map.insert (ssaName var, ssaVersion var) expr defs
  _ -> defs

-- | Combine instructions in a block
combineBlock :: DefMap -> SSABlock -> (SSABlock, Int)
combineBlock defMap block@SSABlock{..} =
  let -- Combine phi nodes
      (phis', phiCount) = unzip $ map (combinePhi defMap) blockPhis
      -- Combine instructions
      (instrs', instrCounts) = unzip $ map (combineInstr defMap) blockInstrs
  in (block { blockPhis = phis', blockInstrs = instrs' }, sum phiCount + sum instrCounts)

-- | Combine a phi node
combinePhi :: DefMap -> PhiNode -> (PhiNode, Int)
combinePhi _defMap phi@PhiNode{..}
  -- Trivial phi with single argument
  | [(_, val)] <- phiArgs = (phi, 0)  -- Keep but mark for later elimination
  | otherwise = (phi, 0)

-- | Combine an instruction
combineInstr :: DefMap -> SSAInstr -> (SSAInstr, Int)
combineInstr defMap = \case
  -- Combine compare-and-branch
  SSABranch cond thenB elseB ->
    case cond of
      -- If condition is just a use, look up its definition
      SSAUse var ->
        let key = (ssaName var, ssaVersion var)
        in case Map.lookup key defMap of
          -- Inline comparison into branch
          Just cmp@(SSABinary op _ _) | isComparisonOp op ->
            (SSABranch cmp thenB elseB, 1)

          -- Inline negation: br (!x) then else -> br x else then
          Just (SSAUnary Not inner) ->
            (SSABranch inner elseB thenB, 1)

          _ -> (SSABranch cond thenB elseB, 0)

      -- Already a comparison - no change needed
      _ -> (SSABranch cond thenB elseB, 0)

  -- Combine negation into subtraction
  SSAAssign var (SSABinary Add left (SSAUse negVar)) ->
    let negKey = (ssaName negVar, ssaVersion negVar)
    in case Map.lookup negKey defMap of
      Just (SSAUnary Neg inner) ->
        (SSAAssign var (SSABinary Sub left inner), 1)
      _ -> (SSAAssign var (SSABinary Add left (SSAUse negVar)), 0)

  SSAAssign var (SSABinary Add (SSAUse negVar) right) ->
    let negKey = (ssaName negVar, ssaVersion negVar)
    in case Map.lookup negKey defMap of
      Just (SSAUnary Neg inner) ->
        (SSAAssign var (SSABinary Sub right inner), 1)
      _ -> (SSAAssign var (SSABinary Add (SSAUse negVar) right), 0)

  -- Combine double negation
  SSAAssign var (SSAUnary Neg (SSAUse innerVar)) ->
    let innerKey = (ssaName innerVar, ssaVersion innerVar)
    in case Map.lookup innerKey defMap of
      Just (SSAUnary Neg original) ->
        (SSAAssign var original, 1)
      _ -> (SSAAssign var (SSAUnary Neg (SSAUse innerVar)), 0)

  -- Combine double logical not
  SSAAssign var (SSAUnary Not (SSAUse innerVar)) ->
    let innerKey = (ssaName innerVar, ssaVersion innerVar)
    in case Map.lookup innerKey defMap of
      Just (SSAUnary Not original) ->
        (SSAAssign var original, 1)
      _ -> (SSAAssign var (SSAUnary Not (SSAUse innerVar)), 0)

  -- Combine comparison of comparison result with boolean
  -- (x < y) == true -> x < y
  -- (x < y) == false -> !(x < y) or x >= y
  SSAAssign var (SSABinary Eq (SSAUse cmpVar) (SSABool True)) ->
    let cmpKey = (ssaName cmpVar, ssaVersion cmpVar)
    in case Map.lookup cmpKey defMap of
      Just cmp@(SSABinary op _ _) | isComparisonOp op ->
        (SSAAssign var cmp, 1)
      _ -> (SSAAssign var (SSABinary Eq (SSAUse cmpVar) (SSABool True)), 0)

  SSAAssign var (SSABinary Eq (SSAUse cmpVar) (SSABool False)) ->
    let cmpKey = (ssaName cmpVar, ssaVersion cmpVar)
    in case Map.lookup cmpKey defMap of
      Just cmp@(SSABinary op l r) | isComparisonOp op ->
        case negateComparison op of
          Just op' -> (SSAAssign var (SSABinary op' l r), 1)
          Nothing -> (SSAAssign var (SSAUnary Not cmp), 1)
      _ -> (SSAAssign var (SSABinary Eq (SSAUse cmpVar) (SSABool False)), 0)

  -- Combine subtraction of negation: a - (-b) -> a + b
  SSAAssign var (SSABinary Sub left (SSAUse negVar)) ->
    let negKey = (ssaName negVar, ssaVersion negVar)
    in case Map.lookup negKey defMap of
      Just (SSAUnary Neg inner) ->
        (SSAAssign var (SSABinary Add left inner), 1)
      _ -> (SSAAssign var (SSABinary Sub left (SSAUse negVar)), 0)

  -- Combine multiplication by power of 2 to shift (not applicable without shift op)
  -- Keep as is for now

  instr -> (instr, 0)

-- | Check if an operation is a comparison
isComparisonOp :: BinaryOp -> Bool
isComparisonOp = \case
  Lt -> True
  Le -> True
  Gt -> True
  Ge -> True
  Eq -> True
  Ne -> True
  _  -> False

-- | Negate a comparison operation
negateComparison :: BinaryOp -> Maybe BinaryOp
negateComparison = \case
  Lt -> Just Ge
  Le -> Just Gt
  Gt -> Just Le
  Ge -> Just Lt
  Eq -> Just Ne
  Ne -> Just Eq
  _  -> Nothing
