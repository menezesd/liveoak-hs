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

    -- * Constants
  , entryClass
  , entryMethod
  ) where

import LiveOak.Ast (ClassDecl(..), MethodDecl(..))
import LiveOak.Symbol (ProgramSymbols, lookupClass, lookupMethod, expectedUserArgs, numParams)
import LiveOak.Diag (Diag(..), Result, ok)
import qualified Data.Map.Strict as Map

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
              argErr = if userArgs /= 0
                       then [SyntaxError (entryClass ++ "." ++ entryMethod ++ " must not have parameters") 0 0]
                       else []
              instanceErr = if numParams mainMethod <= 0
                            then [SyntaxError (entryClass ++ "." ++ entryMethod ++ " must be an instance method") 0 0]
                            else []
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
