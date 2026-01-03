{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RecordWildCards #-}

-- | Escape Analysis.
-- Determines whether objects "escape" their allocation site, enabling
-- stack allocation for non-escaping objects.
module LiveOak.Escape
  ( -- * Escape Analysis
    analyzeEscape
  , EscapeResult(..)
  , EscapeState(..)

    -- * Queries
  , doesEscape
  , canStackAllocate
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

-- | Escape state of an object
data EscapeState
  = NoEscape        -- ^ Object does not escape, can be stack-allocated
  | ArgEscape       -- ^ Object escapes as argument to another method
  | GlobalEscape    -- ^ Object escapes to global state (field, return, etc.)
  deriving (Eq, Ord, Show)

-- | Allocation site information
data AllocationSite = AllocationSite
  { asBlock :: !BlockId       -- ^ Block where allocation occurs
  , asVar :: !String          -- ^ Variable holding the allocated object
  , asClass :: !String        -- ^ Class being instantiated
  , asEscape :: !EscapeState  -- ^ Escape state
  } deriving (Show)

-- | Escape analysis result
data EscapeResult = EscapeResult
  { escapeAllocations :: !(Map String AllocationSite)  -- ^ All allocations
  , escapeNoEscape :: ![String]                        -- ^ Non-escaping allocations
  , escapeStackCandidates :: ![String]                 -- ^ Can be stack-allocated
  } deriving (Show)

--------------------------------------------------------------------------------
-- Escape Analysis
--------------------------------------------------------------------------------

-- | Analyze escape for a method
analyzeEscape :: CFG -> [SSABlock] -> EscapeResult
analyzeEscape cfg blocks =
  let -- Find all allocation sites
      allocations = findAllocations blocks
      -- Analyze escape for each allocation
      analyzed = Map.map (analyzeAllocation cfg blocks) allocations
      -- Filter non-escaping
      noEscape = [asVar a | a <- Map.elems analyzed, asEscape a == NoEscape]
      stackCandidates = [asVar a | a <- Map.elems analyzed, canStackAllocate a]
  in EscapeResult
    { escapeAllocations = analyzed
    , escapeNoEscape = noEscape
    , escapeStackCandidates = stackCandidates
    }

-- | Find all allocation sites
findAllocations :: [SSABlock] -> Map String AllocationSite
findAllocations blocks =
  Map.fromList $ concatMap findBlockAllocations blocks
  where
    findBlockAllocations SSABlock{..} =
      [(ssaName var, AllocationSite blockLabel (ssaName var) cn NoEscape)
      | SSAAssign var (SSANewObject cn _) <- blockInstrs]

-- | Analyze escape state of an allocation
analyzeAllocation :: CFG -> [SSABlock] -> AllocationSite -> AllocationSite
analyzeAllocation cfg blocks site =
  let varName = asVar site
      escapeState = computeEscapeState cfg blocks varName
  in site { asEscape = escapeState }

-- | Compute escape state of a variable
computeEscapeState :: CFG -> [SSABlock] -> String -> EscapeState
computeEscapeState _cfg blocks varName =
  let uses = findAllUses blocks varName
      escapeStates = map classifyUse uses
  in if null escapeStates
     then NoEscape
     else maximum escapeStates  -- Most conservative escape state

-- | Information about a use site
data UseSite
  = UseLocal !BlockId !Int          -- ^ Local use (in expression)
  | UseArg !BlockId !String         -- ^ Passed as argument
  | UseReturn !BlockId              -- ^ Returned from method
  | UseStore !BlockId !String !Int  -- ^ Stored to field
  | UseGlobal !BlockId              -- ^ Other global escape
  deriving (Show)

-- | Find all uses of a variable
findAllUses :: [SSABlock] -> String -> [UseSite]
findAllUses blocks varName = concatMap (findBlockUses varName) blocks

-- | Find uses in a block
findBlockUses :: String -> SSABlock -> [UseSite]
findBlockUses varName SSABlock{..} =
  concatMap (findInstrUses blockLabel varName) (zip [0..] blockInstrs)

-- | Find uses in an instruction
findInstrUses :: BlockId -> String -> (Int, SSAInstr) -> [UseSite]
findInstrUses bid varName (idx, instr) = case instr of
  SSAAssign _ expr -> findExprUses bid idx varName expr

  SSAReturn (Just expr) ->
    if exprUsesVar varName expr
    then [UseReturn bid]
    else []

  SSAFieldStore target field _ value ->
    let targetUses = if exprUsesVar varName target then [UseStore bid field idx] else []
        valueUses = if exprUsesVar varName value then [UseStore bid field idx] else []
    in targetUses ++ valueUses

  SSAExprStmt expr -> findExprUses bid idx varName expr

  _ -> []

-- | Find uses in an expression
findExprUses :: BlockId -> Int -> String -> SSAExpr -> [UseSite]
findExprUses bid idx varName = \case
  SSAUse var | ssaName var == varName -> [UseLocal bid idx]
  SSAUnary _ e -> findExprUses bid idx varName e
  SSABinary _ l r ->
    findExprUses bid idx varName l ++ findExprUses bid idx varName r
  SSATernary c t e ->
    findExprUses bid idx varName c ++
    findExprUses bid idx varName t ++
    findExprUses bid idx varName e
  SSACall _ args ->
    [UseArg bid name | (i, arg) <- zip [0..] args
                     , exprUsesVar varName arg
                     , let name = "arg" ++ show i]
  SSAInstanceCall target method args ->
    let targetUses = if exprUsesVar varName target then [UseArg bid method] else []
        argUses = [UseArg bid method | arg <- args, exprUsesVar varName arg]
    in targetUses ++ argUses
  SSANewObject _ args ->
    [UseArg bid "constructor" | arg <- args, exprUsesVar varName arg]
  SSAFieldAccess target _ ->
    if exprUsesVar varName target then [UseLocal bid idx] else []
  _ -> []

-- | Check if expression uses a variable
exprUsesVar :: String -> SSAExpr -> Bool
exprUsesVar varName = \case
  SSAUse var -> ssaName var == varName
  SSAUnary _ e -> exprUsesVar varName e
  SSABinary _ l r -> exprUsesVar varName l || exprUsesVar varName r
  SSATernary c t e -> exprUsesVar varName c || exprUsesVar varName t || exprUsesVar varName e
  SSACall _ args -> any (exprUsesVar varName) args
  SSAInstanceCall target _ args -> exprUsesVar varName target || any (exprUsesVar varName) args
  SSANewObject _ args -> any (exprUsesVar varName) args
  SSAFieldAccess target _ -> exprUsesVar varName target
  _ -> False

-- | Classify a use site into an escape state
classifyUse :: UseSite -> EscapeState
classifyUse = \case
  UseLocal _ _ -> NoEscape        -- Local use doesn't cause escape
  UseArg _ _ -> ArgEscape         -- Passing as argument may cause escape
  UseReturn _ -> GlobalEscape     -- Returning causes global escape
  UseStore _ _ _ -> GlobalEscape  -- Storing to field causes escape
  UseGlobal _ -> GlobalEscape     -- Other global uses

--------------------------------------------------------------------------------
-- Queries
--------------------------------------------------------------------------------

-- | Check if an allocation escapes
doesEscape :: EscapeResult -> String -> Bool
doesEscape result varName =
  case Map.lookup varName (escapeAllocations result) of
    Just site -> asEscape site /= NoEscape
    Nothing -> True  -- Unknown, assume escapes

-- | Check if an allocation can be stack-allocated
canStackAllocate :: AllocationSite -> Bool
canStackAllocate site = asEscape site == NoEscape

--------------------------------------------------------------------------------
-- Stack Allocation Transformation
--------------------------------------------------------------------------------

-- | Transform allocations to stack allocations where possible
stackAllocate :: EscapeResult -> [SSABlock] -> [SSABlock]
stackAllocate result = map transformBlock
  where
    stackVars = Set.fromList (escapeStackCandidates result)

    transformBlock block@SSABlock{..} =
      block { blockInstrs = map transformInstr blockInstrs }

    transformInstr = \case
      SSAAssign var (SSANewObject cn args)
        | Set.member (ssaName var) stackVars ->
            -- Mark as stack allocation (implementation-specific)
            -- For now, keep as heap allocation but mark for later
            SSAAssign var (SSANewObject ("__stack__" ++ cn) args)
      other -> other

--------------------------------------------------------------------------------
-- Inter-procedural Escape Analysis
--------------------------------------------------------------------------------

-- | Method summary for escape analysis
data MethodEscapeSummary = MethodEscapeSummary
  { mesName :: !String                    -- ^ Method name
  , mesParamEscape :: ![EscapeState]      -- ^ Escape state of each parameter
  , mesReturnEscape :: !Bool              -- ^ Does method return an escaping value?
  } deriving (Show)

-- | Compute method escape summary
computeMethodSummary :: String -> [SSAVar] -> [SSABlock] -> MethodEscapeSummary
computeMethodSummary name params blocks =
  let paramStates = map (computeParamEscape blocks) params
      returnEscapes = any (blockHasEscapingReturn blocks) blocks
  in MethodEscapeSummary
    { mesName = name
    , mesParamEscape = paramStates
    , mesReturnEscape = returnEscapes
    }

-- | Compute escape state of a parameter
computeParamEscape :: [SSABlock] -> SSAVar -> EscapeState
computeParamEscape blocks param =
  let varName = ssaName param
      uses = findAllUses blocks varName
      escapeStates = map classifyUse uses
  in if null escapeStates then NoEscape else maximum escapeStates

-- | Check if any return in the block returns an escaping value
blockHasEscapingReturn :: [SSABlock] -> SSABlock -> Bool
blockHasEscapingReturn blocks SSABlock{..} =
  any isEscapingReturn blockInstrs
  where
    isEscapingReturn = \case
      SSAReturn (Just (SSANewObject _ _)) -> True
      SSAReturn (Just (SSAUse var)) ->
        -- Check if variable is a non-escaping allocation
        let allocSites = findAllocations blocks
        in case Map.lookup (ssaName var) allocSites of
          Just _ -> True  -- Returning allocated object
          Nothing -> False
      _ -> False
