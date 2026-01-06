{-# LANGUAGE RecordWildCards #-}

-- | Main entry point for the LiveOak compiler CLI.
module Main (main) where

import System.Environment (getArgs)
import System.Exit (exitFailure)
import System.IO (hPutStrLn, stderr)
import Control.Monad (forM_)
import Data.List (stripPrefix)
import qualified Data.Text as T
import qualified Data.Text.IO as TIO

import LiveOak.Compiler

-- | Compilation target
data Target = TargetSAM | TargetX86_64
  deriving (Eq, Show)

-- | Parse command-line arguments
data Options = Options
  { optTarget :: Target
  , optInput :: FilePath
  , optOutput :: Maybe FilePath
  }

-- | Main entry point.
main :: IO ()
main = do
  args <- getArgs
  case parseArgs args of
    Left err -> do
      hPutStrLn stderr err
      printUsage
      exitFailure
    Right opts -> compileWithOptions opts

-- | Parse command-line arguments
parseArgs :: [String] -> Either String Options
parseArgs args =
  let (flags, files) = partition isFlag args
      target = parseTarget flags
  in case (target, files) of
    (Left err, _) -> Left err
    (Right t, [input]) -> Right $ Options t input Nothing
    (Right t, [input, output]) -> Right $ Options t input (Just output)
    (_, []) -> Left "Error: No input file specified"
    (_, _) -> Left "Error: Too many arguments"
  where
    isFlag arg = "--" `isPrefixOf` arg || "-" `isPrefixOf` arg
    isPrefixOf needle haystack = take (length needle) haystack == needle

-- | Check if string is a flag
partition :: (a -> Bool) -> [a] -> ([a], [a])
partition p xs = (filter p xs, filter (not . p) xs)

-- | Parse target from flags
parseTarget :: [String] -> Either String Target
parseTarget flags =
  case mapMaybe parseTargetFlag flags of
    [] -> Right TargetSAM  -- Default
    [t] -> Right t
    _ -> Left "Error: Multiple --target flags specified"
  where
    parseTargetFlag flag =
      case stripPrefix "--target=" flag of
        Just "sam" -> Just TargetSAM
        Just "x86_64" -> Just TargetX86_64
        Just "x86" -> Just TargetX86_64
        Just other -> Nothing  -- Will cause error below if no valid target
        Nothing -> Nothing

    mapMaybe _ [] = []
    mapMaybe f (x:xs) = case f x of
      Just y -> y : mapMaybe f xs
      Nothing -> mapMaybe f xs

-- | Compile with the given options
compileWithOptions :: Options -> IO ()
compileWithOptions Options{..} = do
  source <- TIO.readFile optInput
  let compiler = case optTarget of
        TargetSAM -> compileCollectAllErrors
        TargetX86_64 -> compileX86CollectAllErrors
  let result = compiler optInput source
  case result of
    Right (code, warnings) -> do
      forM_ warnings $ \w ->
        hPutStrLn stderr $ formatWarningWithSource source w
      case optOutput of
        Just outputFile -> TIO.writeFile outputFile code
        Nothing -> TIO.putStr code
    Left diags -> do
      forM_ diags $ \d ->
        hPutStrLn stderr $ formatDiagWithSource source d
      hPutStrLn stderr $ "Compilation failed with " ++ show (length diags) ++ " error(s)"
      exitFailure

-- | Compile to x86_64 and collect all errors
compileX86CollectAllErrors :: FilePath -> T.Text -> Either [Diag] (T.Text, [Warning])
compileX86CollectAllErrors path source =
  case compileToX86WithWarnings path source of
    Left err -> Left [err]
    Right result -> Right result

-- | Print usage information
printUsage :: IO ()
printUsage = do
  hPutStrLn stderr ""
  hPutStrLn stderr "Usage: liveoak [--target=TARGET] <input.lo> [output]"
  hPutStrLn stderr ""
  hPutStrLn stderr "Compiles a LiveOak source file."
  hPutStrLn stderr ""
  hPutStrLn stderr "Options:"
  hPutStrLn stderr "  --target=TARGET  Set compilation target:"
  hPutStrLn stderr "                     sam     - SAM assembly (default)"
  hPutStrLn stderr "                     x86_64  - x86_64 assembly (GAS syntax)"
  hPutStrLn stderr ""
  hPutStrLn stderr "Arguments:"
  hPutStrLn stderr "  input.lo   Input LiveOak source file"
  hPutStrLn stderr "  output     Output file (optional, prints to stdout if omitted)"
  hPutStrLn stderr ""
  hPutStrLn stderr "Examples:"
  hPutStrLn stderr "  liveoak program.lo program.sam"
  hPutStrLn stderr "  liveoak --target=x86_64 program.lo program.s"
