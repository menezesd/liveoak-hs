{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RecordWildCards #-}

-- | Tail Call Optimization (TCO).
-- Converts tail-recursive calls into jumps, avoiding stack growth.
-- A call is in tail position if it's the last thing a function does before returning.
module LiveOak.TailCall
  ( -- * Tail Call Optimization
    optimizeTailCalls
  , TCOResult(..)

    -- * Analysis
  , findTailCalls
  , isTailCall
  ) where

import LiveOak.SSATypes
import LiveOak.CFG

import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Set (Set)
import qualified Data.Set as Set
import Data.List (foldl')

--------------------------------------------------------------------------------
-- Types
--------------------------------------------------------------------------------

-- | Information about a tail call
data TailCallInfo = TailCallInfo
  { tcBlock :: !BlockId           -- ^ Block containing the call
  , tcInstrIndex :: !Int          -- ^ Instruction index
  , tcCallee :: !String           -- ^ Called function/method
  , tcArgs :: ![SSAExpr]          -- ^ Arguments
  , tcIsSelfRecursive :: !Bool    -- ^ Is this a self-recursive call?
  } deriving (Show)

-- | TCO result
data TCOResult = TCOResult
  { tcoOptBlocks :: ![SSABlock]       -- ^ Optimized blocks
  , tcoTailCallsOptimized :: !Int     -- ^ Number of tail calls optimized
  , tcoSelfRecursive :: !Int          -- ^ Number of self-recursive calls converted to loops
  } deriving (Show)

--------------------------------------------------------------------------------
-- Tail Call Analysis
--------------------------------------------------------------------------------

-- | Find all tail calls in a method
findTailCalls :: String -> String -> [SSABlock] -> [TailCallInfo]
findTailCalls className methodName blocks =
  concatMap (findBlockTailCalls className methodName) blocks

-- | Find tail calls in a single block
findBlockTailCalls :: String -> String -> SSABlock -> [TailCallInfo]
findBlockTailCalls className methodName SSABlock{..} =
  let indexed = zip [0..] blockInstrs
      -- Find instructions that are followed only by a return of the call result
      tailCalls = findTailPositionCalls indexed
  in map (mkTailCallInfo className methodName blockLabel) tailCalls

-- | Find calls in tail position
-- A call is in tail position if:
-- 1. The call result is assigned to a variable
-- 2. That variable is immediately returned (possibly after the assignment)
findTailPositionCalls :: [(Int, SSAInstr)] -> [(Int, SSAInstr, String, [SSAExpr])]
findTailPositionCalls instrs = go instrs
  where
    go [] = []
    go [(_, SSAReturn (Just (SSACall name args)))] =
      -- Direct return of call result
      [(0, SSAReturn (Just (SSACall name args)), name, args)]
    go [(_, SSAReturn (Just (SSAInstanceCall _ method args)))] =
      [(0, SSAReturn (Just (SSAInstanceCall SSAThis method args)), method, args)]
    go ((i, SSAAssign var (SSACall name args)) : rest)
      | isReturnOfVar var rest =
          (i, SSAAssign var (SSACall name args), name, args) : go rest
    go ((i, SSAAssign var (SSAInstanceCall target method args)) : rest)
      | isReturnOfVar var rest =
          (i, SSAAssign var (SSAInstanceCall target method args), method, args) : go rest
    go (_ : rest) = go rest

-- | Check if remaining instructions just return the given variable
isReturnOfVar :: SSAVar -> [(Int, SSAInstr)] -> Bool
isReturnOfVar var instrs =
  case instrs of
    [(_, SSAReturn (Just (SSAUse v)))] -> ssaName v == ssaName var
    _ -> False

-- | Create TailCallInfo
mkTailCallInfo :: String -> String -> BlockId -> (Int, SSAInstr, String, [SSAExpr]) -> TailCallInfo
mkTailCallInfo className methodName blockId (idx, _, callee, args) =
  let fullMethodName = className ++ "_" ++ methodName
      isSelf = callee == fullMethodName || callee == methodName
  in TailCallInfo
    { tcBlock = blockId
    , tcInstrIndex = idx
    , tcCallee = callee
    , tcArgs = args
    , tcIsSelfRecursive = isSelf
    }

-- | Check if an instruction is a tail call
isTailCall :: String -> String -> SSABlock -> SSAInstr -> Bool
isTailCall className methodName block instr =
  not $ null $ findBlockTailCalls className methodName block

--------------------------------------------------------------------------------
-- Tail Call Optimization
--------------------------------------------------------------------------------

-- | Optimize tail calls in a method
optimizeTailCalls :: String -> String -> [SSABlock] -> TCOResult
optimizeTailCalls className methodName blocks =
  let tailCalls = findTailCalls className methodName blocks
      selfRecursive = filter tcIsSelfRecursive tailCalls
      -- Optimize self-recursive tail calls (convert to loops)
      (optimized, count) = if null selfRecursive
                           then (blocks, 0)
                           else optimizeSelfRecursive className methodName blocks selfRecursive
  in TCOResult
    { tcoOptBlocks = optimized
    , tcoTailCallsOptimized = length tailCalls
    , tcoSelfRecursive = count
    }

-- | Optimize self-recursive tail calls by converting to loops
optimizeSelfRecursive :: String -> String -> [SSABlock] -> [TailCallInfo] -> ([SSABlock], Int)
optimizeSelfRecursive className methodName blocks tailCalls =
  let -- Create a loop header block for the method
      entryBlock = case blocks of
        (b:_) -> blockLabel b
        [] -> "entry"
      -- Replace tail calls with jumps back to entry
      optimized = map (optimizeBlockTailCalls entryBlock tailCalls) blocks
  in (optimized, length tailCalls)

-- | Optimize tail calls in a single block
optimizeBlockTailCalls :: BlockId -> [TailCallInfo] -> SSABlock -> SSABlock
optimizeBlockTailCalls entryBlock tailCalls block@SSABlock{..} =
  let relevantCalls = filter (\tc -> tcBlock tc == blockLabel) tailCalls
  in if null relevantCalls
     then block
     else block { blockInstrs = optimizeInstrs entryBlock relevantCalls blockInstrs }

-- | Optimize instructions, replacing tail calls with parameter updates + jumps
optimizeInstrs :: BlockId -> [TailCallInfo] -> [SSAInstr] -> [SSAInstr]
optimizeInstrs entryBlock tailCalls = go 0
  where
    go _ [] = []
    go idx (instr : rest) =
      case findTailCallAt idx tailCalls of
        Just tc ->
          -- Replace call with: update parameters, jump to entry
          let paramUpdates = zipWith mkParamUpdate [0..] (tcArgs tc)
              jump = SSAJump entryBlock
          in paramUpdates ++ [jump]
        Nothing ->
          instr : go (idx + 1) rest

    findTailCallAt idx = foldr (\tc acc -> if tcInstrIndex tc == idx then Just tc else acc) Nothing

    -- Create parameter update instruction
    mkParamUpdate :: Int -> SSAExpr -> SSAInstr
    mkParamUpdate paramIdx expr =
      -- Store to parameter slot (this is a simplified version)
      -- In practice, we'd need to track parameter variables
      SSAAssign (SSAVar ("__param_" ++ show paramIdx) 0 Nothing) expr

--------------------------------------------------------------------------------
-- Tail Call Detection for General Calls
--------------------------------------------------------------------------------

-- | Analyze a method to find all tail call sites
analyzeTailCalls :: CFG -> [SSABlock] -> Map BlockId [TailCallInfo]
analyzeTailCalls cfg blocks =
  let blockMap = Map.fromList [(blockLabel b, b) | b <- blocks]
      -- Find blocks that end with a return
      returnBlocks = [bid | bid <- allBlockIds cfg,
                           Just b <- [Map.lookup bid blockMap],
                           endsWithReturn b]
  in Map.fromList [(bid, []) | bid <- returnBlocks]  -- Placeholder
  where
    endsWithReturn SSABlock{..} =
      case reverse blockInstrs of
        (SSAReturn _ : _) -> True
        _ -> False

--------------------------------------------------------------------------------
-- Tail Call Marking for Code Generation
--------------------------------------------------------------------------------

-- | Mark tail calls in SSA for code generation
-- Returns instructions with tail calls marked (using a special wrapper)
markTailCalls :: String -> String -> [SSABlock] -> [SSABlock]
markTailCalls className methodName blocks =
  let tailCalls = findTailCalls className methodName blocks
      tailCallSet = Set.fromList [(tcBlock tc, tcInstrIndex tc) | tc <- tailCalls]
  in map (markBlockTailCalls tailCallSet) blocks

-- | Mark tail calls in a block
markBlockTailCalls :: Set (BlockId, Int) -> SSABlock -> SSABlock
markBlockTailCalls tailCallSet block@SSABlock{..} =
  -- For now, we don't modify the instructions, just identify them
  -- A real implementation would wrap calls in a TailCall marker
  block
