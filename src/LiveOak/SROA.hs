{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RecordWildCards #-}

-- | Scalar Replacement of Aggregates (SROA).
-- Replaces non-escaping object allocations with scalar variables for each field.
-- This avoids heap allocation and enables further scalar optimizations.
--
-- == Prerequisites
--
-- Uses escape analysis results from LiveOak.Escape to identify candidates.
--
-- == Algorithm
--
-- 1. Run escape analysis to find non-escaping allocations
-- 2. For each non-escaping object:
--    a. Create scalar variables for each field
--    b. Replace field accesses with scalar variable uses
--    c. Replace field stores with scalar variable assignments
--    d. Remove the allocation instruction
--
-- == Limitations
--
-- - Only handles objects whose class structure is known at compile time
-- - Requires all field accesses to be statically resolvable
-- - Does not handle objects passed to unknown methods
--
module LiveOak.SROA
  ( -- * Scalar Replacement
    scalarReplace
  , SROAResult(..)
  ) where

import LiveOak.SSATypes
import LiveOak.CFG
import LiveOak.Escape (analyzeEscape, EscapeResult(..), EscapeState(..))
import LiveOak.Symbol (ProgramSymbols, lookupClass, csFieldOrder, lookupField, vsType)

import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Set (Set)
import qualified Data.Set as Set
import Data.List (foldl')
import Data.Maybe (mapMaybe, fromMaybe)

--------------------------------------------------------------------------------
-- Types
--------------------------------------------------------------------------------

-- | SROA result
data SROAResult = SROAResult
  { sroaOptBlocks :: ![SSABlock]      -- ^ Optimized blocks
  , sroaReplacedAllocs :: !Int        -- ^ Number of replaced allocations
  , sroaScalarVars :: ![String]       -- ^ New scalar variables created
  } deriving (Show)

-- | Scalar replacement info for an allocation
data ScalarInfo = ScalarInfo
  { siObjVar :: !String               -- ^ Original object variable
  , siClassName :: !String            -- ^ Class name
  , siFieldScalars :: !(Map String SSAVar) -- ^ Field -> scalar variable
  } deriving (Show)

--------------------------------------------------------------------------------
-- Scalar Replacement
--------------------------------------------------------------------------------

-- | Apply scalar replacement to method blocks
scalarReplace :: ProgramSymbols -> SSAMethod -> SROAResult
scalarReplace syms method@SSAMethod{..} =
  let cfg = buildCFG method
      escapeResult = analyzeEscape cfg ssaMethodBlocks

      -- Find non-escaping allocations
      candidates = escapeStackCandidates escapeResult

      -- Build scalar replacement info for each candidate
      replacements = mapMaybe (buildScalarInfo syms ssaMethodBlocks) candidates

      -- Apply replacements
      (optimized, scalarVars) = applyReplacements replacements ssaMethodBlocks
  in SROAResult
    { sroaOptBlocks = optimized
    , sroaReplacedAllocs = length replacements
    , sroaScalarVars = scalarVars
    }

-- | Build scalar info for a non-escaping allocation
buildScalarInfo :: ProgramSymbols -> [SSABlock] -> String -> Maybe ScalarInfo
buildScalarInfo syms blocks objVar = do
  -- Find the allocation instruction
  (className, _args) <- findAllocation blocks objVar

  -- Look up class fields
  classSyms <- lookupClass className syms
  let fields = csFieldOrder classSyms

  -- Create scalar variable for each field
  let fieldScalars = Map.fromList
        [ (field, SSAVar
            { ssaName = varName ("__sroa_" ++ objVar ++ "_" ++ field)
            , ssaVersion = 0
            , ssaVarType = fmap vsType (lookupField field classSyms)
            })
        | field <- fields
        ]

  return ScalarInfo
    { siObjVar = objVar
    , siClassName = className
    , siFieldScalars = fieldScalars
    }

-- | Find allocation instruction for a variable
findAllocation :: [SSABlock] -> String -> Maybe (String, [SSAExpr])
findAllocation blocks objVar = go blocks
  where
    go [] = Nothing
    go (SSABlock{..}:rest) =
      case findInBlock blockInstrs of
        Just result -> Just result
        Nothing -> go rest

    findInBlock [] = Nothing
    findInBlock (SSAAssign var (SSANewObject cn args) : _)
      | varNameString (ssaName var) == objVar = Just (cn, args)
    findInBlock (_ : rest) = findInBlock rest

-- | Apply scalar replacements to blocks
applyReplacements :: [ScalarInfo] -> [SSABlock] -> ([SSABlock], [String])
applyReplacements infos blocks =
  let -- Build lookup map: object var -> scalar info
      infoMap = Map.fromList [(siObjVar info, info) | info <- infos]
      -- Transform blocks
      transformed = map (transformBlock infoMap) blocks
      -- Collect scalar variable names
      scalarVars = [varNameString (ssaName v) | info <- infos, v <- Map.elems (siFieldScalars info)]
  in (transformed, scalarVars)

-- | Transform a block with scalar replacements
transformBlock :: Map String ScalarInfo -> SSABlock -> SSABlock
transformBlock infoMap block@SSABlock{..} =
  block
    { blockInstrs = concatMap (transformInstr infoMap) blockInstrs
    , blockPhis = map (transformPhi infoMap) blockPhis
    }

-- | Transform a phi node
transformPhi :: Map String ScalarInfo -> PhiNode -> PhiNode
transformPhi infoMap phi@PhiNode{..} =
  phi { phiArgs = map transformArg phiArgs }
  where
    transformArg (bid, var) =
      -- If the variable is a replaced object, we need field-specific phis
      -- For now, just keep the phi as-is (full SROA would need to split phis)
      (bid, var)

-- | Transform an instruction
transformInstr :: Map String ScalarInfo -> SSAInstr -> [SSAInstr]
transformInstr infoMap = \case
  -- Remove allocations for replaced objects
  SSAAssign var (SSANewObject cn args)
    | Map.member (varNameString (ssaName var)) infoMap ->
        -- Initialize scalar fields (for now, skip - constructors should handle this)
        []

  -- Replace field stores with scalar assignments
  SSAFieldStore target field _idx value ->
    case getObjVar target of
      Just objVar | Just info <- Map.lookup objVar infoMap ->
        case Map.lookup field (siFieldScalars info) of
          Just scalarVar -> [SSAAssign scalarVar (transformExpr infoMap value)]
          Nothing -> [SSAFieldStore (transformExpr infoMap target) field _idx (transformExpr infoMap value)]
      _ -> [SSAFieldStore (transformExpr infoMap target) field _idx (transformExpr infoMap value)]

  -- Transform other instructions
  SSAAssign var expr ->
    [SSAAssign var (transformExpr infoMap expr)]

  SSAReturn mexpr ->
    [SSAReturn (fmap (transformExpr infoMap) mexpr)]

  SSABranch cond t f ->
    [SSABranch (transformExpr infoMap cond) t f]

  SSAExprStmt expr ->
    [SSAExprStmt (transformExpr infoMap expr)]

  other -> [other]

-- | Transform an expression
transformExpr :: Map String ScalarInfo -> SSAExpr -> SSAExpr
transformExpr infoMap = \case
  -- Replace field accesses with scalar uses
  SSAFieldAccess target field ->
    case getObjVar target of
      Just objVar | Just info <- Map.lookup objVar infoMap ->
        case Map.lookup field (siFieldScalars info) of
          Just scalarVar -> SSAUse scalarVar
          Nothing -> SSAFieldAccess (transformExpr infoMap target) field
      _ -> SSAFieldAccess (transformExpr infoMap target) field

  -- Recursive cases
  SSAUnary op e -> SSAUnary op (transformExpr infoMap e)
  SSABinary op l r -> SSABinary op (transformExpr infoMap l) (transformExpr infoMap r)
  SSATernary c t e -> SSATernary (transformExpr infoMap c) (transformExpr infoMap t) (transformExpr infoMap e)
  SSACall name args -> SSACall name (map (transformExpr infoMap) args)
  SSAInstanceCall target m args ->
    SSAInstanceCall (transformExpr infoMap target) m (map (transformExpr infoMap) args)
  SSANewObject cn args -> SSANewObject cn (map (transformExpr infoMap) args)

  other -> other

-- | Get object variable name from expression
getObjVar :: SSAExpr -> Maybe String
getObjVar = \case
  SSAUse var -> Just $ varNameString (ssaName var)
  SSAThis -> Just "this"
  _ -> Nothing
