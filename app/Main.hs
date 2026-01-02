-- | Main entry point for the LiveOak compiler CLI.
module Main (main) where

import System.Environment (getArgs)
import System.Exit (exitFailure)
import System.IO (hPutStrLn, stderr)
import Control.Monad (forM_)
import qualified Data.Text.IO as TIO

import LiveOak.Compiler

-- | Main entry point.
main :: IO ()
main = do
  args <- getArgs
  case args of
    [inputFile, outputFile] -> do
      source <- TIO.readFile inputFile
      let result = compileCollectAllErrors inputFile source
      case result of
        Right (samCode, warnings) -> do
          forM_ warnings $ \w ->
            hPutStrLn stderr $ formatWarningWithSource source w
          TIO.writeFile outputFile samCode
        Left diags -> do
          forM_ diags $ \d ->
            hPutStrLn stderr $ formatDiagWithSource source d
          hPutStrLn stderr $ "Compilation failed with " ++ show (length diags) ++ " error(s)"
          exitFailure

    [inputFile] -> do
      source <- TIO.readFile inputFile
      let result = compileCollectAllErrors inputFile source
      case result of
        Right (samCode, warnings) -> do
          forM_ warnings $ \w ->
            hPutStrLn stderr $ formatWarningWithSource source w
          TIO.putStr samCode
        Left diags -> do
          forM_ diags $ \d ->
            hPutStrLn stderr $ formatDiagWithSource source d
          hPutStrLn stderr $ "Compilation failed with " ++ show (length diags) ++ " error(s)"
          exitFailure

    _ -> do
      hPutStrLn stderr "Usage: liveoak <input.lo> [output.sam]"
      hPutStrLn stderr ""
      hPutStrLn stderr "Compiles a LiveOak source file to SAM assembly."
      hPutStrLn stderr ""
      hPutStrLn stderr "Arguments:"
      hPutStrLn stderr "  input.lo    Input LiveOak source file"
      hPutStrLn stderr "  output.sam  Output SAM assembly file (optional, prints to stdout if omitted)"
      exitFailure
