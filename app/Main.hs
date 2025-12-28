-- | Main entry point for the LiveOak compiler CLI.
module Main (main) where

import System.Environment (getArgs)
import System.Exit (exitFailure)
import System.IO (hPutStrLn, stderr)
import qualified Data.Text.IO as TIO

import LiveOak.Compiler

-- | Main entry point.
main :: IO ()
main = do
  args <- getArgs
  case args of
    [inputFile, outputFile] -> do
      result <- compileFile inputFile
      case result of
        Right samCode -> TIO.writeFile outputFile samCode
        Left diag -> do
          hPutStrLn stderr $ "Error: " ++ formatDiag diag
          exitFailure

    [inputFile] -> do
      result <- compileFile inputFile
      case result of
        Right samCode -> TIO.putStr samCode
        Left diag -> do
          hPutStrLn stderr $ "Error: " ++ formatDiag diag
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
