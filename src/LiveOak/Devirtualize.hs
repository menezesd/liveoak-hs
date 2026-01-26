{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RecordWildCards #-}

-- | Devirtualization - Converting indirect calls to direct calls.
-- When the receiver type is known statically, replace virtual dispatch
-- with a direct method call.
--
-- == Patterns Handled
-- 1. Known receiver type from allocation: `new Foo().bar()`
-- 2. Known receiver type from type analysis
-- 3. Known receiver type from dominating type test
--
module LiveOak.Devirtualize
  ( -- * Devirtualization
    devirtualize
  , DevirtResult(..)

    -- * Type Analysis
  , ReceiverTypeInfo
  , analyzeReceiverTypes
  ) where

import LiveOak.SSATypes
import LiveOak.CFG
import LiveOak.Dominance (DomTree, computeDominators)
import LiveOak.SSATypeInfer (TypeEnv, buildTypeEnv, inferSSAExprClassWithCtx)
import LiveOak.Symbol (ProgramSymbols)

import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Set (Set)
import qualified Data.Set as Set
import Data.List (foldl')
import Data.Maybe (fromMaybe)

--------------------------------------------------------------------------------
-- Types
--------------------------------------------------------------------------------

-- | Devirtualization result
data DevirtResult = DevirtResult
  { dvOptBlocks :: ![SSABlock]
  , dvDevirtualized :: !Int       -- ^ Number of calls devirtualized
  } deriving (Show)

-- | Receiver type information for a variable
data ReceiverType
  = RTExact !String              -- ^ Exactly this class
  | RTPossible !(Set String)     -- ^ Could be one of these classes
  | RTUnknown                    -- ^ Unknown type
  deriving (Eq, Show)

-- | Receiver type info for all variables
type ReceiverTypeInfo = Map VarKey ReceiverType

--------------------------------------------------------------------------------
-- Devirtualization
--------------------------------------------------------------------------------

-- | Devirtualize method calls
devirtualize :: ProgramSymbols -> SSAMethod -> DevirtResult
devirtualize syms method =
  let cfg = buildCFG method
      domTree = computeDominators cfg
      blocks = ssaMethodBlocks method
      typeEnv = buildTypeEnv blocks syms (ssaMethodClassName method) (ssaMethodParams method)

      -- Analyze receiver types
      receiverTypes = analyzeReceiverTypes blocks typeEnv

      -- Apply devirtualization
      (optimized, count) = devirtualizeBlocks syms (ssaMethodClassName method) typeEnv receiverTypes blocks
  in DevirtResult
    { dvOptBlocks = optimized
    , dvDevirtualized = count
    }

--------------------------------------------------------------------------------
-- Type Analysis
--------------------------------------------------------------------------------

-- | Analyze receiver types for all variables
analyzeReceiverTypes :: [SSABlock] -> TypeEnv -> ReceiverTypeInfo
analyzeReceiverTypes blocks typeEnv =
  let initial = Map.empty
      final = foldl' (analyzeBlock typeEnv) initial blocks
  in final

-- | Analyze a block for receiver types
analyzeBlock :: TypeEnv -> ReceiverTypeInfo -> SSABlock -> ReceiverTypeInfo
analyzeBlock _typeEnv info SSABlock{..} =
  let info1 = foldl' analyzePhi info blockPhis
      info2 = foldl' analyzeInstr info1 blockInstrs
  in info2

-- | Analyze phi node
analyzePhi :: ReceiverTypeInfo -> PhiNode -> ReceiverTypeInfo
analyzePhi info PhiNode{..} =
  let varKey = (ssaName phiVar, ssaVersion phiVar)
      argTypes = [lookupType (ssaName v, ssaVersion v) info | (_, v) <- phiArgs]
      merged = foldl' meetTypes RTUnknown argTypes
  in Map.insert varKey merged info

-- | Analyze instruction for receiver type
analyzeInstr :: ReceiverTypeInfo -> SSAInstr -> ReceiverTypeInfo
analyzeInstr info = \case
  -- New object: exact type known
  SSAAssign var (SSANewObject className _) ->
    let varKey = (ssaName var, ssaVersion var)
    in Map.insert varKey (RTExact className) info

  -- Variable use: propagate type
  SSAAssign var (SSAUse src) ->
    let varKey = (ssaName var, ssaVersion var)
        srcKey = (ssaName src, ssaVersion src)
        srcType = lookupType srcKey info
    in Map.insert varKey srcType info

  -- Field access: could narrow type based on field's declared type
  SSAAssign var (SSAFieldAccess _ _) ->
    let varKey = (ssaName var, ssaVersion var)
    in Map.insert varKey RTUnknown info

  -- Method call: return type narrows the possibilities
  SSAAssign var (SSAInstanceCall _ _ _) ->
    let varKey = (ssaName var, ssaVersion var)
    in Map.insert varKey RTUnknown info

  _ -> info

-- | Lookup receiver type
lookupType :: VarKey -> ReceiverTypeInfo -> ReceiverType
lookupType key info = Map.findWithDefault RTUnknown key info

-- | Meet two receiver types
meetTypes :: ReceiverType -> ReceiverType -> ReceiverType
meetTypes RTUnknown t = t
meetTypes t RTUnknown = t
meetTypes (RTExact c1) (RTExact c2)
  | c1 == c2 = RTExact c1
  | otherwise = RTPossible (Set.fromList [c1, c2])
meetTypes (RTExact c) (RTPossible cs) = RTPossible (Set.insert c cs)
meetTypes (RTPossible cs) (RTExact c) = RTPossible (Set.insert c cs)
meetTypes (RTPossible cs1) (RTPossible cs2) = RTPossible (Set.union cs1 cs2)

--------------------------------------------------------------------------------
-- Devirtualization Transform
--------------------------------------------------------------------------------

-- | Apply devirtualization to blocks
devirtualizeBlocks :: ProgramSymbols -> String -> TypeEnv -> ReceiverTypeInfo
                   -> [SSABlock] -> ([SSABlock], Int)
devirtualizeBlocks syms className typeEnv receiverTypes blocks =
  let results = map (devirtualizeBlock syms className typeEnv receiverTypes) blocks
  in (map fst results, sum (map snd results))

-- | Devirtualize a single block
devirtualizeBlock :: ProgramSymbols -> String -> TypeEnv -> ReceiverTypeInfo
                  -> SSABlock -> (SSABlock, Int)
devirtualizeBlock syms className typeEnv receiverTypes block@SSABlock{..} =
  let (instrs', counts) = unzip $ map (devirtualizeInstr syms className typeEnv receiverTypes) blockInstrs
  in (block { blockInstrs = instrs' }, sum counts)

-- | Devirtualize an instruction
devirtualizeInstr :: ProgramSymbols -> String -> TypeEnv -> ReceiverTypeInfo
                  -> SSAInstr -> (SSAInstr, Int)
devirtualizeInstr syms className typeEnv receiverTypes = \case
  -- Instance call: try to devirtualize
  SSAAssign var (SSAInstanceCall target method args) ->
    case inferReceiverClass syms className typeEnv receiverTypes target of
      Just receiverClass ->
        -- Convert to direct call
        let directCall = SSACall (receiverClass ++ "_" ++ method) (target : args)
        in (SSAAssign var directCall, 1)
      Nothing ->
        (SSAAssign var (SSAInstanceCall target method args), 0)

  -- Expression statement with instance call
  SSAExprStmt (SSAInstanceCall target method args) ->
    case inferReceiverClass syms className typeEnv receiverTypes target of
      Just receiverClass ->
        let directCall = SSACall (receiverClass ++ "_" ++ method) (target : args)
        in (SSAExprStmt directCall, 1)
      Nothing ->
        (SSAExprStmt (SSAInstanceCall target method args), 0)

  -- Return with instance call
  SSAReturn (Just (SSAInstanceCall target method args)) ->
    case inferReceiverClass syms className typeEnv receiverTypes target of
      Just receiverClass ->
        let directCall = SSACall (receiverClass ++ "_" ++ method) (target : args)
        in (SSAReturn (Just directCall), 1)
      Nothing ->
        (SSAReturn (Just (SSAInstanceCall target method args)), 0)

  other -> (other, 0)

-- | Infer the class of a receiver expression
inferReceiverClass :: ProgramSymbols -> String -> TypeEnv -> ReceiverTypeInfo
                   -> SSAExpr -> Maybe String
inferReceiverClass syms className typeEnv receiverTypes = \case
  -- 'this' receiver: use current class
  SSAThis -> Just className

  -- New object: exact class known
  SSANewObject cn _ -> Just cn

  -- Variable: check receiver type analysis
  SSAUse var ->
    let varKey = (ssaName var, ssaVersion var)
    in case lookupType varKey receiverTypes of
      RTExact cn -> Just cn
      _ -> inferSSAExprClassWithCtx (Just className) syms typeEnv (SSAUse var)

  -- Field access: check type environment
  expr -> inferSSAExprClassWithCtx (Just className) syms typeEnv expr
