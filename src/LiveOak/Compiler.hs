{-# LANGUAGE OverloadedStrings #-}

-- | Main compiler module for LiveOak.
-- Orchestrates the compilation pipeline: parse -> validate -> semantic check -> optimize -> codegen.
module LiveOak.Compiler
  ( -- * Compilation
    compile
  , compileWithWarnings
  , compileCollectAllErrors
  , compileFile

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
import LiveOak.Codegen (generateCode)

-- | Compilation stages.
data CompilationStage
  = StageSymbols   -- ^ Building symbol table
  | StageValidate  -- ^ Validating entry point
  | StageParse     -- ^ Parsing program
  | StageCodegen   -- ^ Generating code
  deriving (Eq, Show)

-- | Entry class name.
entryClass :: String
entryClass = "Main"

-- | Entry method name.
entryMethod :: String
entryMethod = "main"

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

  -- Optimize
  let optimizedProgram = optimize program

  -- Generate code
  code <- generateCode optimizedProgram symbols

  return (code, warnings)

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
         then case generateCode (optimize program) symbols of
           Left codegenErr -> Left [codegenErr]
           Right code -> Right (code, collectWarnings program symbols)
         else Left allErrors

-- | Validate entry point, returning list of errors.
validateEntrypointErrors :: ProgramSymbols -> [Diag]
validateEntrypointErrors syms =
  case lookupClass entryClass syms of
    Nothing -> [ResolveError ("Missing " ++ entryClass ++ " class") 0 0]
    Just mainClass ->
      case lookupMethod entryMethod mainClass of
        Nothing -> [ResolveError (entryClass ++ "." ++ entryMethod ++ " method not found") 0 0]
        Just mainMethod ->
          let userArgs = expectedUserArgs mainMethod
              argErr = if userArgs /= 0
                       then [SyntaxError (entryClass ++ "." ++ entryMethod ++ " must not have parameters") 0 0]
                       else []
              instanceErr = if numParams mainMethod <= 0
                            then [SyntaxError (entryClass ++ "." ++ entryMethod ++ " must be an instance method") 0 0]
                            else []
          in argErr ++ instanceErr

-- | Compile a file to SAM assembly.
compileFile :: FilePath -> IO (Result Text)
compileFile path = do
  source <- TIO.readFile path
  return $ compile path source

-- | Validate that the entry point exists.
validateEntrypoint :: ProgramSymbols -> Result ()
validateEntrypoint syms = do
  -- Check Main class exists
  mainClass <- case lookupClass entryClass syms of
    Nothing -> resolveErr ("Missing " ++ entryClass ++ " class") 0 0
    Just cs -> ok cs

  -- Check main method exists
  mainMethod <- case lookupMethod entryMethod mainClass of
    Nothing -> resolveErr (entryClass ++ "." ++ entryMethod ++ " method not found") 0 0
    Just ms -> ok ms

  -- Check main has correct signature (no user parameters)
  let userArgs = expectedUserArgs mainMethod
  require (userArgs == 0) $
    SyntaxError (entryClass ++ "." ++ entryMethod ++ " must not have parameters") 0 0

  -- Check main is an instance method (has 'this')
  require (numParams mainMethod > 0) $
    SyntaxError (entryClass ++ "." ++ entryMethod ++ " must be an instance method") 0 0

  ok ()
