{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RecordWildCards #-}

-- | Function Inlining Optimization.
-- Replaces function calls with the function body, eliminating call overhead
-- and enabling further optimizations.
--
-- __Status: EXPERIMENTAL__ - This module is not yet integrated into the
-- optimization pipeline. Return value handling is incomplete.
module LiveOak.Inline
  ( -- * Inlining
    inlineFunctions
  , InlineResult(..)

    -- * Inlining Decisions
  , shouldInline
  , InlineHeuristics(..)
  , defaultHeuristics
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

-- | Inlining heuristics configuration
data InlineHeuristics = InlineHeuristics
  { maxInlineSize :: !Int           -- ^ Maximum instruction count to inline
  , maxInlineDepth :: !Int          -- ^ Maximum nesting depth for inlining
  , inlineThreshold :: !Int         -- ^ Cost threshold for inlining decision
  , alwaysInlineSize :: !Int        -- ^ Always inline if smaller than this
  , neverInlineRecursive :: !Bool   -- ^ Never inline recursive functions
  } deriving (Show)

-- | Default inlining heuristics
defaultHeuristics :: InlineHeuristics
defaultHeuristics = InlineHeuristics
  { maxInlineSize = 50              -- Max 50 instructions
  , maxInlineDepth = 3              -- Max 3 levels of inlining
  , inlineThreshold = 100           -- Cost threshold
  , alwaysInlineSize = 5            -- Always inline tiny functions
  , neverInlineRecursive = True     -- Don't inline recursive calls
  }

-- | Result of inlining pass
data InlineResult = InlineResult
  { inlineOptProgram :: !SSAProgram   -- ^ Program with inlined functions
  , inlineCount :: !Int               -- ^ Number of call sites inlined
  , inlinedFunctions :: ![String]     -- ^ Names of inlined functions
  } deriving (Show)

-- | Method info for inlining decisions
data MethodInfo = MethodInfo
  { miName :: !String
  , miClassName :: !String
  , miSize :: !Int                    -- ^ Instruction count
  , miCallCount :: !Int               -- ^ Number of call sites
  , miIsRecursive :: !Bool            -- ^ Calls itself?
  , miBlocks :: ![SSABlock]           -- ^ Method blocks
  , miParams :: ![SSAVar]             -- ^ Parameters
  } deriving (Show)

--------------------------------------------------------------------------------
-- Inlining Analysis
--------------------------------------------------------------------------------

-- | Analyze a program to collect method information
analyzeProgram :: SSAProgram -> Map String MethodInfo
analyzeProgram (SSAProgram classes) =
  Map.fromList $ concatMap analyzeClass classes
  where
    analyzeClass cls =
      [(fullName cls m, analyzeMethod cls m) | m <- ssaClassMethods cls]

    fullName cls m = ssaClassName cls ++ "_" ++ ssaMethodName m

    analyzeMethod cls m =
      let blocks = ssaMethodBlocks m
          size = sum [length (blockInstrs b) + length (blockPhis b) | b <- blocks]
          calls = countCalls blocks
          isRec = isRecursive (ssaClassName cls) (ssaMethodName m) blocks
      in MethodInfo
        { miName = ssaMethodName m
        , miClassName = ssaClassName cls
        , miSize = size
        , miCallCount = calls
        , miIsRecursive = isRec
        , miBlocks = blocks
        , miParams = ssaMethodParams m
        }

-- | Count call sites in blocks
countCalls :: [SSABlock] -> Int
countCalls blocks = sum [countBlockCalls b | b <- blocks]
  where
    countBlockCalls SSABlock{..} = sum [countInstrCalls i | i <- blockInstrs]

    countInstrCalls = \case
      SSAAssign _ expr -> countExprCalls expr
      SSAReturn (Just expr) -> countExprCalls expr
      SSAExprStmt expr -> countExprCalls expr
      _ -> 0

    countExprCalls = \case
      SSACall _ _ -> 1
      SSAInstanceCall _ _ _ -> 1
      SSAUnary _ e -> countExprCalls e
      SSABinary _ l r -> countExprCalls l + countExprCalls r
      SSATernary c t e -> countExprCalls c + countExprCalls t + countExprCalls e
      _ -> 0

-- | Check if a method is recursive
isRecursive :: String -> String -> [SSABlock] -> Bool
isRecursive className methodName blocks =
  any (blockIsRecursive className methodName) blocks
  where
    blockIsRecursive cn mn SSABlock{..} =
      any (instrIsRecursive cn mn) blockInstrs

    instrIsRecursive cn mn = \case
      SSAAssign _ expr -> exprIsRecursive cn mn expr
      SSAReturn (Just expr) -> exprIsRecursive cn mn expr
      SSAExprStmt expr -> exprIsRecursive cn mn expr
      _ -> False

    exprIsRecursive cn mn = \case
      SSACall name _ -> name == cn ++ "_" ++ mn || name == mn
      SSAInstanceCall _ method _ -> method == mn
      SSAUnary _ e -> exprIsRecursive cn mn e
      SSABinary _ l r -> exprIsRecursive cn mn l || exprIsRecursive cn mn r
      SSATernary c t e -> exprIsRecursive cn mn c || exprIsRecursive cn mn t || exprIsRecursive cn mn e
      _ -> False

--------------------------------------------------------------------------------
-- Inlining Decisions
--------------------------------------------------------------------------------

-- | Decide whether to inline a function
shouldInline :: InlineHeuristics -> MethodInfo -> Bool
shouldInline h info
  -- Never inline recursive functions (if configured)
  | neverInlineRecursive h && miIsRecursive info = False
  -- Always inline tiny functions
  | miSize info <= alwaysInlineSize h = True
  -- Don't inline large functions
  | miSize info > maxInlineSize h = False
  -- Use cost/benefit analysis
  | otherwise = inlineBenefit h info > 0

-- | Calculate inlining benefit (positive = should inline)
inlineBenefit :: InlineHeuristics -> MethodInfo -> Int
inlineBenefit h info =
  let -- Benefit: eliminate call overhead (estimated at 10 instructions)
      callOverhead = 10
      benefit = miCallCount info * callOverhead
      -- Cost: code size increase
      cost = (miCallCount info - 1) * miSize info  -- -1 because we keep one copy
  in benefit - cost

--------------------------------------------------------------------------------
-- Inlining Transformation
--------------------------------------------------------------------------------

-- | Inline functions in a program
inlineFunctions :: InlineHeuristics -> SSAProgram -> InlineResult
inlineFunctions heuristics prog@(SSAProgram classes) =
  let methodInfos = analyzeProgram prog
      -- Find methods to inline
      toInline = Map.filter (shouldInline heuristics) methodInfos
      -- Perform inlining
      (optimized, count) = inlineInProgram toInline classes
  in InlineResult
    { inlineOptProgram = SSAProgram optimized
    , inlineCount = count
    , inlinedFunctions = Map.keys toInline
    }

-- | Inline calls in program
inlineInProgram :: Map String MethodInfo -> [SSAClass] -> ([SSAClass], Int)
inlineInProgram toInline classes =
  let results = map (inlineInClass toInline) classes
  in (map fst results, sum (map snd results))

-- | Inline calls in a class
inlineInClass :: Map String MethodInfo -> SSAClass -> (SSAClass, Int)
inlineInClass toInline cls =
  let results = map (inlineInMethod toInline) (ssaClassMethods cls)
      methods' = map fst results
      count = sum (map snd results)
  in (cls { ssaClassMethods = methods' }, count)

-- | Inline calls in a method
inlineInMethod :: Map String MethodInfo -> SSAMethod -> (SSAMethod, Int)
inlineInMethod toInline method =
  let (blocks', count) = inlineInBlocks toInline 0 (ssaMethodBlocks method)
  in (method { ssaMethodBlocks = blocks' }, count)

-- | Inline calls in blocks
inlineInBlocks :: Map String MethodInfo -> Int -> [SSABlock] -> ([SSABlock], Int)
inlineInBlocks toInline labelCounter blocks =
  let (accRev, count) = foldl' inlineBlock ([], 0) blocks
  in (reverse accRev, count)
  where
    inlineBlock (acc, count) block =
      let (block', newBlocks, c) = inlineBlockCalls toInline labelCounter block
          -- Prepend in reverse order: newBlocks then block'
      in (reverse newBlocks ++ (block' : acc), count + c)

-- | Inline calls in a single block
inlineBlockCalls :: Map String MethodInfo -> Int -> SSABlock -> (SSABlock, [SSABlock], Int)
inlineBlockCalls toInline labelCounter block@SSABlock{..} =
  let (instrsRev, blocksRev, count) = foldl' inlineInstr ([], [], 0) blockInstrs
  in (block { blockInstrs = reverse instrsRev }, reverse blocksRev, count)
  where
    inlineInstr (acc, blocks, count) instr =
      case findInlineableCall toInline instr of
        Just (methodInfo, resultVar, args) ->
          -- Inline this call
          let (inlinedInstrs, newBlocks') = inlineCall methodInfo resultVar args labelCounter
              -- Prepend inlined instructions in reverse order
          in (reverse inlinedInstrs ++ acc, reverse newBlocks' ++ blocks, count + 1)
        Nothing ->
          (instr : acc, blocks, count)

-- | Find an inlineable call in an instruction
findInlineableCall :: Map String MethodInfo -> SSAInstr -> Maybe (MethodInfo, Maybe SSAVar, [SSAExpr])
findInlineableCall toInline = \case
  SSAAssign var (SSACall name args) ->
    case Map.lookup name toInline of
      Just info -> Just (info, Just var, args)
      Nothing -> Nothing
  SSAExprStmt (SSACall name args) ->
    case Map.lookup name toInline of
      Just info -> Just (info, Nothing, args)
      Nothing -> Nothing
  _ -> Nothing

-- | Inline a single call
inlineCall :: MethodInfo -> Maybe SSAVar -> [SSAExpr] -> Int -> ([SSAInstr], [SSABlock])
inlineCall info resultVar args labelCounter =
  let -- Create parameter assignments
      paramAssigns = zipWith mkParamAssign (miParams info) args
      -- Rename blocks to avoid conflicts
      renamedBlocks = renameBlocks labelCounter (miBlocks info)
      -- Handle return value
      -- (simplified - would need proper return handling)
  in (paramAssigns, renamedBlocks)
  where
    mkParamAssign param arg = SSAAssign param arg

-- | Rename blocks to avoid label conflicts
renameBlocks :: Int -> [SSABlock] -> [SSABlock]
renameBlocks counter = map (renameBlock counter)
  where
    renameBlock c block@SSABlock{..} =
      block { blockLabel = blockLabel ++ "_inline_" ++ show c }

--------------------------------------------------------------------------------
-- Inline Candidate Selection
--------------------------------------------------------------------------------

-- | Get list of functions that are good inline candidates
getInlineCandidates :: InlineHeuristics -> SSAProgram -> [String]
getInlineCandidates h prog =
  let infos = analyzeProgram prog
  in Map.keys $ Map.filter (shouldInline h) infos

-- | Estimate code size after inlining
estimateSizeAfterInlining :: Map String MethodInfo -> Int
estimateSizeAfterInlining infos =
  sum [miSize info * max 1 (miCallCount info) | info <- Map.elems infos]
