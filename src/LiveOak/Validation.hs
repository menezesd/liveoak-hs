{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RecordWildCards #-}

-- | Validation module for LiveOak.
-- Consolidates all validation logic in one place.
module LiveOak.Validation
  ( -- * Entry Point Validation
    validateEntrypoint
  , validateEntrypointErrors

    -- * Program Validation
  , validateProgram
  , validateNoDuplicates

    -- * SSA Validation
  , validateSSAMethod
  , validateSSAProgram
  , SSAError(..)

    -- * Constants
  , entryClass
  , entryMethod
  ) where

import LiveOak.Ast (ClassDecl(..), MethodDecl(..))
import LiveOak.Symbol (ProgramSymbols, lookupClass, lookupMethod, expectedUserArgs, numParams)
import LiveOak.Diag (Diag(..), Result, ok)
import LiveOak.SSATypes
import LiveOak.CFG (CFG, buildCFG, predecessors)
import LiveOak.SSAUtils (blockMapFromList)
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Data.List (foldl')

--------------------------------------------------------------------------------
-- Constants
--------------------------------------------------------------------------------

-- | Entry class name.
entryClass :: String
entryClass = "Main"

-- | Entry method name.
entryMethod :: String
entryMethod = "main"

--------------------------------------------------------------------------------
-- Entry Point Validation
--------------------------------------------------------------------------------

-- | Validate entry point, returning list of errors.
-- This is the primary implementation - validateEntrypoint wraps this.
validateEntrypointErrors :: ProgramSymbols -> [Diag]
validateEntrypointErrors syms =
  case lookupClass entryClass syms of
    Nothing -> [ResolveError ("Missing " ++ entryClass ++ " class") 0 0]
    Just mainClass ->
      case lookupMethod entryMethod mainClass of
        Nothing -> [ResolveError (entryClass ++ "." ++ entryMethod ++ " method not found") 0 0]
        Just mainMethod ->
          let userArgs = expectedUserArgs mainMethod
              argErr =
                [SyntaxError (entryClass ++ "." ++ entryMethod ++ " must not have parameters") 0 0 |
                  userArgs /= 0]
              instanceErr =
                [SyntaxError (entryClass ++ "." ++ entryMethod ++ " must be an instance method") 0 0 |
                  numParams mainMethod <= 0]
          in argErr ++ instanceErr

-- | Validate that the entry point exists.
-- Wraps validateEntrypointErrors and fails on first error.
validateEntrypoint :: ProgramSymbols -> Result ()
validateEntrypoint syms =
  case validateEntrypointErrors syms of
    [] -> ok ()
    (err:_) -> Left err

--------------------------------------------------------------------------------
-- Program Validation
--------------------------------------------------------------------------------

-- | Validate program structure, returning list of errors.
validateProgram :: [ClassDecl] -> ProgramSymbols -> [Diag]
validateProgram classes syms =
  validateNoDuplicates classes ++ validateEntrypointErrors syms

-- | Check for duplicate class/method/field definitions.
validateNoDuplicates :: [ClassDecl] -> [Diag]
validateNoDuplicates classes =
  duplicateClassErrors ++ concatMap duplicateMethodErrors classes ++ concatMap duplicateFieldErrors classes
  where
    -- Check for duplicate classes
    classNames = map className classes
    duplicateClassNames = findDuplicates classNames
    duplicateClassErrors =
      [SyntaxError ("Duplicate class definition: " ++ name) 0 0 | name <- duplicateClassNames]

    -- Check for duplicate methods within each class
    duplicateMethodErrors ClassDecl{..} =
      let methodNames = map methodName classMethods
          dups = findDuplicates methodNames
      in [SyntaxError ("Duplicate method " ++ m ++ " in class " ++ className) 0 0 | m <- dups]

    -- Check for duplicate fields within each class
    duplicateFieldErrors ClassDecl{..} =
      let fieldNames = map fst classFields
          dups = findDuplicates fieldNames
      in [SyntaxError ("Duplicate field " ++ f ++ " in class " ++ className) 0 0 | f <- dups]

    -- Find duplicates in a list (O(n) using Map)
    findDuplicates :: Ord a => [a] -> [a]
    findDuplicates xs =
      let counts = Map.fromListWith (+) [(x, 1 :: Int) | x <- xs]
      in Map.keys $ Map.filter (> 1) counts

--------------------------------------------------------------------------------
-- SSA Validation
--------------------------------------------------------------------------------

-- | SSA validation error types
data SSAError
  = PhiPredMismatch !BlockId !VarKey ![BlockId] ![BlockId]
    -- ^ Phi node predecessors don't match CFG predecessors
    -- (block, variable, phi preds, actual preds)
  | PhiDuplicateDef !BlockId !VarKey
    -- ^ Multiple phi nodes define the same variable in a block
  | UndefinedVariable !BlockId !VarKey
    -- ^ Use of undefined variable in a block
  | DuplicateBlockId !BlockId
    -- ^ Multiple blocks with same ID
  | OrphanBlock !BlockId
    -- ^ Block not reachable from entry
  | MissingEntry !BlockId
    -- ^ Entry block doesn't exist
  | TerminatorNotLast !BlockId
    -- ^ Block has instructions after terminator
  deriving (Eq, Show)

-- | Validate an SSA program
validateSSAProgram :: SSAProgram -> [SSAError]
validateSSAProgram (SSAProgram classes) =
  concatMap validateSSAClass classes

-- | Validate an SSA class
validateSSAClass :: SSAClass -> [SSAError]
validateSSAClass SSAClass{..} =
  concatMap validateSSAMethod ssaClassMethods

-- | Validate an SSA method
-- Returns list of validation errors (empty if valid)
validateSSAMethod :: SSAMethod -> [SSAError]
validateSSAMethod method@SSAMethod{..} =
  let blocks = ssaMethodBlocks
      blockMap = blockMapFromList blocks
      cfg = buildCFG method
      -- Check for duplicate block IDs
      dupBlockErrors = checkDuplicateBlocks blocks
      -- Check entry block exists
      entryErrors = checkEntryBlock ssaEntryBlock blockMap
      -- Check phi nodes
      phiErrors = concatMap (checkBlockPhis cfg blockMap) blocks
      -- Check variable definitions (all uses must be defined)
      defErrors = checkDefinitions method
      -- Check terminators
      termErrors = concatMap checkBlockTerminator blocks
  in dupBlockErrors ++ entryErrors ++ phiErrors ++ defErrors ++ termErrors

-- | Check for duplicate block IDs
checkDuplicateBlocks :: [SSABlock] -> [SSAError]
checkDuplicateBlocks blocks =
  let blockIds = map blockLabel blocks
      counts = Map.fromListWith (+) [(bid, 1 :: Int) | bid <- blockIds]
      dups = Map.keys $ Map.filter (> 1) counts
  in [DuplicateBlockId bid | bid <- dups]

-- | Check entry block exists
checkEntryBlock :: BlockId -> Map.Map BlockId SSABlock -> [SSAError]
checkEntryBlock entry blockMap
  | Map.member entry blockMap = []
  | otherwise = [MissingEntry entry]

-- | Check phi nodes in a block
checkBlockPhis :: CFG -> Map.Map BlockId SSABlock -> SSABlock -> [SSAError]
checkBlockPhis cfg _blockMap SSABlock{..} =
  let -- Get CFG predecessors
      cfgPreds = Set.fromList $ predecessors cfg blockLabel
      -- Check each phi node
      phiErrors = concatMap (checkPhi blockLabel cfgPreds) blockPhis
      -- Check for duplicate definitions
      phiVars = [(ssaName (phiVar phi), ssaVersion (phiVar phi)) | phi <- blockPhis]
      dupDefs = findDuplicateKeys phiVars
      dupErrors = [PhiDuplicateDef blockLabel vk | vk <- dupDefs]
  in phiErrors ++ dupErrors

-- | Check a single phi node
checkPhi :: BlockId -> Set.Set BlockId -> PhiNode -> [SSAError]
checkPhi bid cfgPreds PhiNode{..} =
  let -- Get predecessors from phi arguments
      phiPreds = Set.fromList [p | (p, _) <- phiArgs]
      -- Phi preds should match CFG preds (or be subset for unoptimized code)
      vk = (ssaName phiVar, ssaVersion phiVar)
  in if phiPreds == cfgPreds || Set.isSubsetOf phiPreds cfgPreds
     then []
     else [PhiPredMismatch bid vk (Set.toList phiPreds) (Set.toList cfgPreds)]

-- | Check that all variables are defined before use
checkDefinitions :: SSAMethod -> [SSAError]
checkDefinitions SSAMethod{..} =
  let -- Start with parameters as defined
      paramDefs = Set.fromList [(ssaName p, ssaVersion p) | p <- ssaMethodParams]
      -- Collect definitions from all blocks
      allDefs = foldl' collectDefs paramDefs ssaMethodBlocks
      -- Check all uses against definitions
  in concatMap (checkBlockUses allDefs) ssaMethodBlocks

-- | Collect all definitions in a block
collectDefs :: Set.Set VarKey -> SSABlock -> Set.Set VarKey
collectDefs defs SSABlock{..} =
  let phiDefs = [(ssaName (phiVar phi), ssaVersion (phiVar phi)) | phi <- blockPhis]
      instrDefs = [(ssaName v, ssaVersion v) | SSAAssign v _ <- blockInstrs]
  in Set.union defs (Set.fromList $ phiDefs ++ instrDefs)

-- | Check uses in a block against known definitions
-- This validates that all variable uses reference defined variables.
-- Note: We check against all definitions in the method, not just those that
-- dominate the use. This is a conservative check - a more precise check would
-- verify dominance, but catching completely undefined variables is still useful.
checkBlockUses :: Set.Set VarKey -> SSABlock -> [SSAError]
checkBlockUses defs SSABlock{..} =
  let -- Get all uses from phi nodes (from all incoming edges)
      phiUses = [varKey v | phi <- blockPhis, (_, v) <- phiArgs phi]
      -- Get all uses from instructions
      instrUses = concatMap instrVarUses blockInstrs
      -- Filter to undefined uses
      undefinedPhiUses = [vk | vk <- phiUses, not (Set.member vk defs)]
      undefinedInstrUses = [vk | vk <- instrUses, not (Set.member vk defs)]
  in [UndefinedVariable blockLabel vk | vk <- undefinedPhiUses ++ undefinedInstrUses]

-- | Get variable uses from an instruction
instrVarUses :: SSAInstr -> [VarKey]
instrVarUses = \case
  SSAAssign _ e -> exprVarUses e
  SSAFieldStore t _ _ v -> exprVarUses t ++ exprVarUses v
  SSAReturn (Just e) -> exprVarUses e
  SSAReturn Nothing -> []
  SSABranch c _ _ -> exprVarUses c
  SSAExprStmt e -> exprVarUses e
  SSAJump _ -> []

-- | Get variable uses from an expression
exprVarUses :: SSAExpr -> [VarKey]
exprVarUses = \case
  SSAUse v -> [varKey v]
  SSAInt _ -> []
  SSABool _ -> []
  SSAStr _ -> []
  SSANull -> []
  SSAThis -> []
  SSAUnary _ e -> exprVarUses e
  SSABinary _ l r -> exprVarUses l ++ exprVarUses r
  SSATernary c t e -> exprVarUses c ++ exprVarUses t ++ exprVarUses e
  SSACall _ args -> concatMap exprVarUses args
  SSAInstanceCall t _ args -> exprVarUses t ++ concatMap exprVarUses args
  SSANewObject _ args -> concatMap exprVarUses args
  SSAFieldAccess t _ -> exprVarUses t

-- | Check that terminator is the last instruction
checkBlockTerminator :: SSABlock -> [SSAError]
checkBlockTerminator SSABlock{..} =
  case findTerminatorPosition blockInstrs of
    Nothing -> []  -- No terminator is OK (implicit fallthrough)
    Just pos | pos == length blockInstrs - 1 -> []  -- Terminator is last
    Just _ -> [TerminatorNotLast blockLabel]
  where
    findTerminatorPosition instrs =
      let indexed = zip [0..] instrs
          termIdx = [(i, instr) | (i, instr) <- indexed, isTerminator instr]
      in case termIdx of
        [(i, _)] -> Just i
        _ -> Nothing

    isTerminator = \case
      SSAJump _ -> True
      SSABranch _ _ _ -> True
      SSAReturn _ -> True
      _ -> False

-- | Find duplicate keys in a list
findDuplicateKeys :: Ord a => [a] -> [a]
findDuplicateKeys xs =
  let counts = Map.fromListWith (+) [(x, 1 :: Int) | x <- xs]
  in Map.keys $ Map.filter (> 1) counts
