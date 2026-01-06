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

    -- * x86_64 Compilation
  , compileToX86
  , compileToX86WithWarnings

    -- * Compilation Stages
  , CompilationStage (..)

    -- * Re-exports
  , module LiveOak.Diag
  ) where

import Data.Text (Text)
import qualified Data.Text.IO as TIO

import LiveOak.Diag
import LiveOak.Parser (parseProgram)
import LiveOak.Semantic (checkProgram, checkProgramCollectErrors)
import LiveOak.Warnings (collectWarnings)
import LiveOak.Optimize (optimize)
import LiveOak.Validation (validateEntrypoint, validateEntrypointErrors)
import qualified LiveOak.Peephole as Peephole
import qualified LiveOak.SSA as SSA
import qualified LiveOak.SSACodegen as SSACodegen
import qualified LiveOak.X86Codegen as X86Codegen

-- | Compilation stages.
data CompilationStage
  = StageSymbols   -- ^ Building symbol table
  | StageValidate  -- ^ Validating entry point
  | StageParse     -- ^ Parsing program
  | StageCodegen   -- ^ Generating code
  deriving (Eq, Show)

-- | Compilation configuration.
newtype CompileConfig = CompileConfig
  { ccOptimizeSSA :: Bool      -- ^ Apply SSA-level optimizations
  }

-- | Default configuration: SSA optimizations enabled.
defaultConfig :: CompileConfig
defaultConfig = CompileConfig { ccOptimizeSSA = True }

-- | Core compilation pipeline with configuration.
-- All compilation functions route through this to avoid duplication.
compileCore :: CompileConfig -> FilePath -> Text -> Result (Text, [Warning])
compileCore config path source = do
  -- Parse program and build symbol table
  (program, symbols) <- parseProgram path source

  -- Validate entry point
  validateEntrypoint symbols

  -- Semantic analysis
  checkProgram program symbols

  -- Collect warnings
  let warnings = collectWarnings program symbols

  -- AST optimization and SSA conversion
  let optimizedProgram = optimize symbols program
      ssaProg = SSA.toSSAWithCFG symbols optimizedProgram
      -- Apply SSA optimizations if configured (including SROA which needs symbols)
      finalSSA = if ccOptimizeSSA config
                 then SSA.optimizeSSAProgramWithSymbols symbols ssaProg
                 else ssaProg

  -- Code generation
  code <- SSACodegen.generateFromSSA finalSSA symbols

  -- Peephole optimize SAM code
  let optimizedCode = Peephole.optimizeText code

  return (optimizedCode, warnings)

-- | Compile source text to SAM assembly.
compile :: FilePath -> Text -> Result Text
compile path source = fst <$> compileWithWarnings path source

-- | Compile source text to SAM assembly, also returning warnings.
compileWithWarnings :: FilePath -> Text -> Result (Text, [Warning])
compileWithWarnings = compileCore defaultConfig

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

-- | Compile using SSA-based code generation without SSA-level optimizations.
-- Useful for debugging or when SSA optimizations cause issues.
compileWithSSA :: FilePath -> Text -> Result Text
compileWithSSA path source =
  fst <$> compileCore (CompileConfig { ccOptimizeSSA = False }) path source

-- | Compile with full SSA optimization pipeline.
-- This is equivalent to the default compile, but explicit about SSA opts.
compileWithSSAOptimizations :: FilePath -> Text -> Result Text
compileWithSSAOptimizations path source =
  fst <$> compileCore defaultConfig path source

--------------------------------------------------------------------------------
-- x86_64 Compilation
--------------------------------------------------------------------------------

-- | Compile source text to x86_64 assembly (GAS syntax).
compileToX86 :: FilePath -> Text -> Result Text
compileToX86 path source = fst <$> compileToX86WithWarnings path source

-- | Compile source text to x86_64 assembly, also returning warnings.
compileToX86WithWarnings :: FilePath -> Text -> Result (Text, [Warning])
compileToX86WithWarnings path source = do
  -- Parse program and build symbol table
  (program, symbols) <- parseProgram path source

  -- Validate entry point
  validateEntrypoint symbols

  -- Semantic analysis
  checkProgram program symbols

  -- Collect warnings
  let warnings = collectWarnings program symbols

  -- AST optimization and SSA conversion
  let optimizedProgram = optimize symbols program
      ssaProg = SSA.toSSAWithCFG symbols optimizedProgram
      -- Use safe SSA pipeline for x86 (excludes loop unrolling and LICM)
      finalSSA = SSA.ssaX86SafePipeline ssaProg

  -- x86_64 code generation
  code <- X86Codegen.generateX86FromSSA finalSSA symbols

  return (code, warnings)
