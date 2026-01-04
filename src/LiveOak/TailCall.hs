{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RecordWildCards #-}

-- | Tail Call Optimization (TCO).
-- Converts tail-recursive calls into jumps, avoiding stack growth.
-- A call is in tail position if it's the last thing a function does before returning.
--
-- For self-recursive tail calls, this creates a loop structure:
-- 1. Entry block becomes a loop header with phi nodes for parameters
-- 2. A preheader block is inserted for the initial entry
-- 3. Tail calls are replaced with jumps back to the loop header
--
-- Available via 'optimizeMethodTailCalls' for individual methods or
-- 'ssaTailCallOpt' (from LiveOak.SSA) for program-wide optimization.
-- Not enabled by default in the optimization pipeline.
module LiveOak.TailCall
  ( -- * Tail Call Optimization
    optimizeTailCalls
  , optimizeMethodTailCalls
  , TCOResult(..)

    -- * Analysis
  , findTailCalls
  , isTailCall
  , TailCallInfo(..)
  ) where

import LiveOak.SSATypes

import Data.List (foldl')
import qualified Data.Map.Strict as Map

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
findTailCalls className methodName =
  concatMap (findBlockTailCalls className methodName)

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
-- Note: For instance calls, only calls on 'this' can be self-recursive
findTailPositionCalls :: [(Int, SSAInstr)] -> [(Int, SSAInstr, String, [SSAExpr], Bool)]
findTailPositionCalls = go
  where
    go [] = []
    go [(_, SSAReturn (Just (SSACall name args)))] =
      -- Direct return of call result (static call, not instance)
      [(0, SSAReturn (Just (SSACall name args)), name, args, True)]
    go [(_, SSAReturn (Just (SSAInstanceCall target method args)))] =
      -- Instance call - only self-recursive if target is 'this'
      [(0, SSAReturn (Just (SSAInstanceCall target method args)), method, args, isThisCall target)]
    go ((i, SSAAssign var (SSACall name args)) : rest)
      | isReturnOfVar var rest =
          (i, SSAAssign var (SSACall name args), name, args, True) : go rest
    go ((i, SSAAssign var (SSAInstanceCall target method args)) : rest)
      | isReturnOfVar var rest =
          (i, SSAAssign var (SSAInstanceCall target method args), method, args, isThisCall target) : go rest
    go (_ : rest) = go rest

    -- Check if target is 'this'
    isThisCall SSAThis = True
    isThisCall _ = False

-- | Check if remaining instructions just return the given variable
isReturnOfVar :: SSAVar -> [(Int, SSAInstr)] -> Bool
isReturnOfVar var instrs =
  case instrs of
    [(_, SSAReturn (Just (SSAUse v)))] -> ssaName v == ssaName var
    _ -> False

-- | Create TailCallInfo
mkTailCallInfo :: String -> String -> BlockId -> (Int, SSAInstr, String, [SSAExpr], Bool) -> TailCallInfo
mkTailCallInfo className methodName bid (idx, _, callee, args, canBeSelfRecursive) =
  let fullMethodName = className ++ "_" ++ methodName
      -- Only self-recursive if: method name matches AND it's a call on 'this' (for instance calls)
      isSelf = canBeSelfRecursive && (callee == fullMethodName || callee == methodName)
  in TailCallInfo
    { tcBlock = bid
    , tcInstrIndex = idx
    , tcCallee = callee
    , tcArgs = args
    , tcIsSelfRecursive = isSelf
    }

-- | Check if an instruction is a tail call
isTailCall :: String -> String -> SSABlock -> SSAInstr -> Bool
isTailCall className methodName block _instr =
  not $ null $ findBlockTailCalls className methodName block

--------------------------------------------------------------------------------
-- Tail Call Optimization
--------------------------------------------------------------------------------

-- | Optimize tail calls in a method (legacy interface)
optimizeTailCalls :: String -> String -> [SSABlock] -> TCOResult
optimizeTailCalls className methodName blocks =
  let tailCalls = findTailCalls className methodName blocks
      selfRecursive = filter tcIsSelfRecursive tailCalls
      -- Optimize self-recursive tail calls (convert to loops)
      (optimized, count) = if null selfRecursive
                           then (blocks, 0)
                           else optimizeSelfRecursiveLegacy className methodName blocks selfRecursive
  in TCOResult
    { tcoOptBlocks = optimized
    , tcoTailCallsOptimized = length tailCalls
    , tcoSelfRecursive = count
    }

-- | Optimize tail calls in an SSA method (preferred interface)
-- This version properly handles parameter updates using phi nodes.
optimizeMethodTailCalls :: SSAMethod -> SSAMethod
optimizeMethodTailCalls method@SSAMethod{..} =
  let className = ssaMethodClassName
      methodName = methodNameString ssaMethodName
      tailCalls = findTailCalls className methodName ssaMethodBlocks
      selfRecursive = filter tcIsSelfRecursive tailCalls
  in if null selfRecursive
     then method
     else optimizeMethodSelfRecursive method selfRecursive

-- | Optimize self-recursive tail calls by creating a loop structure
-- Creates: preheader -> loop_header (with phis) -> body -> jump back
optimizeMethodSelfRecursive :: SSAMethod -> [TailCallInfo] -> SSAMethod
optimizeMethodSelfRecursive method@SSAMethod{..} tailCalls =
  let params = ssaMethodParams
      entryBid = ssaEntryBlock

      -- Create block IDs
      preheaderBid = blockId (blockIdName entryBid ++ "_preheader")
      loopHeaderBid = entryBid  -- Entry becomes loop header

      -- Build map of tail call blocks for quick lookup
      tailCallBlocks = Map.fromList [(tcBlock tc, tc) | tc <- tailCalls]

      -- Create preheader block (just jumps to loop header)
      preheaderBlock = SSABlock
        { blockLabel = preheaderBid
        , blockPhis = []
        , blockInstrs = [SSAJump loopHeaderBid]
        }

      -- Build parameter renaming: original param -> phi result
      paramRenames = [(param, param { ssaVersion = ssaVersion param + 100 }) | param <- params]

      -- Transform blocks (replace tail calls with jumps)
      transformedBlocks = map (transformBlock params loopHeaderBid preheaderBid tailCallBlocks) ssaMethodBlocks

      -- Apply parameter renaming to all loop blocks (except preheader)
      renamedBlocks = map (renameParamsInBlock paramRenames) transformedBlocks

      -- Find the actual entry block (by ID) and add phi nodes to it
      finalBlocks =
        let updateEntry block =
              if blockLabel block == entryBid
              then addParamPhis params preheaderBid tailCallBlocks block
              else block
        in preheaderBlock : map updateEntry renamedBlocks

  in method
    { ssaMethodBlocks = finalBlocks
    , ssaEntryBlock = preheaderBid  -- Entry is now the preheader
    }

-- | Rename parameter uses in a block
renameParamsInBlock :: [(SSAVar, SSAVar)] -> SSABlock -> SSABlock
renameParamsInBlock renames block@SSABlock{..} =
  block { blockInstrs = map (renameParamsInInstr renames) blockInstrs }

-- | Rename parameter uses in an instruction
renameParamsInInstr :: [(SSAVar, SSAVar)] -> SSAInstr -> SSAInstr
renameParamsInInstr renames = \case
  SSAAssign var expr -> SSAAssign var (renameParamsInExpr renames expr)
  SSAReturn mExpr -> SSAReturn (fmap (renameParamsInExpr renames) mExpr)
  SSABranch cond t f -> SSABranch (renameParamsInExpr renames cond) t f
  SSAExprStmt expr -> SSAExprStmt (renameParamsInExpr renames expr)
  SSAFieldStore obj field idx val ->
    SSAFieldStore (renameParamsInExpr renames obj) field idx (renameParamsInExpr renames val)
  other -> other

-- | Rename parameter uses in an expression
renameParamsInExpr :: [(SSAVar, SSAVar)] -> SSAExpr -> SSAExpr
renameParamsInExpr renames = \case
  SSAUse var -> SSAUse (renameVar renames var)
  SSAUnary op e -> SSAUnary op (renameParamsInExpr renames e)
  SSABinary op l r -> SSABinary op (renameParamsInExpr renames l) (renameParamsInExpr renames r)
  SSATernary c t e -> SSATernary (renameParamsInExpr renames c)
                                 (renameParamsInExpr renames t)
                                 (renameParamsInExpr renames e)
  SSACall name args -> SSACall name (map (renameParamsInExpr renames) args)
  SSAInstanceCall obj m args -> SSAInstanceCall (renameParamsInExpr renames obj) m
                                                (map (renameParamsInExpr renames) args)
  SSANewObject cn args -> SSANewObject cn (map (renameParamsInExpr renames) args)
  SSAFieldAccess obj f -> SSAFieldAccess (renameParamsInExpr renames obj) f
  other -> other

-- | Rename a variable if it matches a parameter
renameVar :: [(SSAVar, SSAVar)] -> SSAVar -> SSAVar
renameVar renames var =
  case lookup var renames of
    Just newVar -> newVar
    Nothing -> var

-- | Add phi nodes for parameters at the loop header
addParamPhis :: [SSAVar] -> BlockId -> Map.Map BlockId TailCallInfo -> SSABlock -> SSABlock
addParamPhis params preheaderBid tailCallBlocks block@SSABlock{..} =
  let -- Get all blocks that jump to this header via tail calls
      tailCallPreds = Map.keys tailCallBlocks

      -- Create phi for each parameter
      paramPhis = zipWith (mkParamPhi preheaderBid tailCallPreds params) [0..] params

  in block { blockPhis = paramPhis ++ blockPhis }

-- | Create a phi node for a parameter
-- The phi receives:
--   - From preheader: the original parameter
--   - From each tail call block: the temporary variable holding the new argument value
mkParamPhi :: BlockId -> [BlockId] -> [SSAVar] -> Int -> SSAVar -> PhiNode
mkParamPhi preheaderBid tailCallPreds params paramIdx param =
  let -- New version for the phi result
      phiVar = param { ssaVersion = ssaVersion param + 100 }  -- Use high version to avoid conflicts

      -- Preheader provides the original parameter
      preheaderArg = (preheaderBid, param)

      -- Each tail call block provides a temporary variable
      -- (created by replaceTailCall with name "__tco_<param>")
      tempVarName = "__tco_" ++ varNameString (ssaName param)
      tailCallArgs = [(bid, SSAVar (varName tempVarName) 0 (ssaVarType param))
                     | bid <- tailCallPreds
                     , paramIdx < length params]

  in PhiNode phiVar (preheaderArg : tailCallArgs)

-- | Transform a block for tail call optimization
transformBlock :: [SSAVar] -> BlockId -> BlockId -> Map.Map BlockId TailCallInfo -> SSABlock -> SSABlock
transformBlock params loopHeaderBid _preheaderBid tailCallBlocks block@SSABlock{..} =
  case Map.lookup blockLabel tailCallBlocks of
    Nothing -> block  -- Not a tail call block
    Just tc ->
      -- Replace the tail call with assignments for new values + jump
      let newInstrs = replaceTailCall params loopHeaderBid tc blockInstrs
      in block { blockInstrs = newInstrs }

-- | Replace tail call instruction with assignments + jump
-- Creates assignments for each argument to a temporary variable, then jumps
replaceTailCall :: [SSAVar] -> BlockId -> TailCallInfo -> [SSAInstr] -> [SSAInstr]
replaceTailCall params loopHeaderBid tc instrs =
  let idx = tcInstrIndex tc
      -- Keep instructions before the tail call
      prefix = take idx instrs
      -- Create assignments for each argument value
      argAssigns = zipWith mkArgAssign params (tcArgs tc)
      jump = SSAJump loopHeaderBid
  in prefix ++ argAssigns ++ [jump]
  where
    mkArgAssign param argExpr =
      let tempVarName = "__tco_" ++ varNameString (ssaName param)
          tempVar = SSAVar (varName tempVarName) 0 (ssaVarType param)
      in SSAAssign tempVar argExpr

--------------------------------------------------------------------------------
-- Legacy Implementation (without proper phi handling)
--------------------------------------------------------------------------------

-- | Legacy self-recursive optimization (kept for backwards compatibility)
optimizeSelfRecursiveLegacy :: String -> String -> [SSABlock] -> [TailCallInfo] -> ([SSABlock], Int)
optimizeSelfRecursiveLegacy _className _methodName blocks tailCalls =
  let entryBlock = case blocks of
        (b:_) -> blockLabel b
        [] -> blockId "entry"
      optimized = map (optimizeBlockTailCallsLegacy entryBlock tailCalls) blocks
  in (optimized, length tailCalls)

-- | Legacy block optimization
optimizeBlockTailCallsLegacy :: BlockId -> [TailCallInfo] -> SSABlock -> SSABlock
optimizeBlockTailCallsLegacy entryBlock tailCalls block@SSABlock{..} =
  let relevantCalls = filter (\tc -> tcBlock tc == blockLabel) tailCalls
  in if null relevantCalls
     then block
     else block { blockInstrs = optimizeInstrsLegacy entryBlock relevantCalls blockInstrs }

-- | Legacy instruction optimization
optimizeInstrsLegacy :: BlockId -> [TailCallInfo] -> [SSAInstr] -> [SSAInstr]
optimizeInstrsLegacy entryBlock tailCalls = go 0
  where
    go _ [] = []
    go idx (instr : rest) =
      case findTailCallAt idx tailCalls of
        Just _tc ->
          -- Simple jump back to entry (phi nodes handle values)
          [SSAJump entryBlock]
        Nothing ->
          instr : go (idx + 1) rest

    findTailCallAt idx = foldl' (\acc tc -> if tcInstrIndex tc == idx then Just tc else acc) Nothing
