{-# LANGUAGE OverloadedStrings #-}

-- | Main compiler module for LiveOak.
-- Orchestrates the compilation pipeline: parse -> validate -> semantic check -> optimize -> codegen.
module LiveOak.Compiler
  ( -- * Compilation
    compile
  , compileWithWarnings
  , compileCollectAllErrors
  , compileFile

    -- * SSA-based Compilation
  , compileWithSSA
  , compileWithSSAOptimizations

    -- * Compilation Stages
  , CompilationStage (..)

    -- * Re-exports
  , module LiveOak.Diag
  ) where

import Data.Text (Text)
import qualified Data.Text.IO as TIO

import LiveOak.Symbol
import LiveOak.Diag
import LiveOak.Parser (parseProgram)
import LiveOak.Semantic (checkProgram, checkProgramCollectErrors)
import LiveOak.Warnings (collectWarnings)
import LiveOak.Optimize (optimize)
import LiveOak.Validation (validateEntrypoint, validateEntrypointErrors)
import qualified LiveOak.Peephole as Peephole
import qualified LiveOak.SSA as SSA
import qualified LiveOak.SSACodegen as SSACodegen

-- | Compilation stages.
data CompilationStage
  = StageSymbols   -- ^ Building symbol table
  | StageValidate  -- ^ Validating entry point
  | StageParse     -- ^ Parsing program
  | StageCodegen   -- ^ Generating code
  deriving (Eq, Show)

-- | Compile source text to SAM assembly.
compile :: FilePath -> Text -> Result Text
compile path source = fst <$> compileWithWarnings path source

-- | Compile source text to SAM assembly, also returning warnings.
compileWithWarnings :: FilePath -> Text -> Result (Text, [Warning])
compileWithWarnings path source = do
  -- Parse program and build symbol table
  (program, symbols) <- parseProgram path source

  -- Validate entry point
  validateEntrypoint symbols

  -- Semantic analysis
  checkProgram program symbols

  -- Collect warnings
  let warnings = collectWarnings program symbols

  -- Use SSA-based codegen with SSA optimizations
  let optimizedProgram = optimize symbols program
      ssaProg = SSA.toSSAWithCFG symbols optimizedProgram
      optimizedSSA = SSA.optimizeSSAProgram ssaProg
  code <- SSACodegen.generateFromSSA optimizedSSA symbols

  -- Peephole optimize SAM code
  let optimizedCode = Peephole.optimizeText code

  return (optimizedCode, warnings)

-- | Compile and collect ALL errors instead of stopping at first.
-- Returns either (code, warnings) on success, or list of all errors on failure.
compileCollectAllErrors :: FilePath -> Text -> Either [Diag] (Text, [Warning])
compileCollectAllErrors path source =
  case parseProgram path source of
    Left parseErr -> Left [parseErr]
    Right (program, symbols) ->
      let entryErrors = validateEntrypointErrors symbols
          semanticErrors = checkProgramCollectErrors program symbols
          allErrors = entryErrors ++ semanticErrors
      in if null allErrors
         then let optimizedProgram = optimize symbols program
                  ssaProg = SSA.toSSAWithCFG symbols optimizedProgram
              in case SSACodegen.generateFromSSA ssaProg symbols of
                   Left codegenErr -> Left [codegenErr]
                   Right code ->
                     let optimizedCode = Peephole.optimizeText code
                     in Right (optimizedCode, collectWarnings program symbols)
         else Left allErrors

-- | Compile a file to SAM assembly.
compileFile :: FilePath -> IO (Result Text)
compileFile path = do
  source <- TIO.readFile path
  return $ compile path source

--------------------------------------------------------------------------------
-- SSA-based Compilation
--------------------------------------------------------------------------------

-- | Compile using SSA-based code generation (SSACodegen fully debugged).
-- SSACodegen bugs fixed:
--  ✓ Method epilogue: JUMPIND -> RST
--  ✓ Stack offsets: totalParams includes 'this'
--  ✓ Stack discipline: Don't pop after STOREOFF
--  ✓ Return values: Don't pop after storing in return slot
--  ✓ Local cleanup: Pop locals before UNLINK
-- SSA conversion issues:
--  ✓ Fixed: While loop blocks now created in correct order
--  ✓ Fixed: Statements after control flow placed correctly
--  ✗ Remaining: While loops need CFG-based SSA with proper phi node renaming
-- Status: SSACodegen works perfectly; basic SSA conversion needs phi nodes for loops.
compileWithSSA :: FilePath -> Text -> Result Text
compileWithSSA path source = do
  (program, symbols) <- parseProgram path source
  validateEntrypoint symbols
  checkProgram program symbols
  let optimizedProgram = optimize symbols program
      ssaProg = SSA.toSSAWithCFG symbols optimizedProgram
  code <- SSACodegen.generateFromSSA ssaProg symbols
  let optimizedCode = Peephole.optimizeText code
  return optimizedCode

-- | Compile with SSA optimization pipeline (EXPERIMENTAL - has runtime issues).
-- Infrastructure status:
--  ✓ Field offset resolution via symbol table threading
--  ✓ Method labels qualified with class names
--  ✓ Type tracking through SSA transformations
--  ✓ Stack offset calculations fixed (totalParams includes 'this')
--  ✓ Method epilogue fixed (JUMPIND -> RST)
--  ✗ Return value handling needs debugging (values incorrect)
compileWithSSAOptimizations :: FilePath -> Text -> Result Text
compileWithSSAOptimizations path source = do
  (program, symbols) <- parseProgram path source
  validateEntrypoint symbols
  checkProgram program symbols
  let optimizedProgram = optimize symbols program
      ssaProg = SSA.toSSAWithCFG symbols optimizedProgram
      optimizedSSA = SSA.optimizeSSAProgram ssaProg
  code <- SSACodegen.generateFromSSA optimizedSSA symbols
  let optimizedCode = Peephole.optimizeText code
  return optimizedCode
