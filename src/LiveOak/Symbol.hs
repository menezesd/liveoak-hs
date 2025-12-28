{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RecordWildCards #-}

-- | Symbol table structures for LiveOak.
-- Provides immutable representations of program symbols: variables, methods, classes.
module LiveOak.Symbol
  ( -- * Variable Symbols
    VarSymbol (..)
  , stackAddress

    -- * Method Symbols
  , MethodSymbol (..)
  , numParams
  , numLocals
  , expectedUserArgs
  , returnAddressOffset
  , lookupVar
  , getReturnSig

    -- * Class Symbols
  , ClassSymbol (..)
  , FieldInfo (..)
  , lookupField
  , lookupMethod
  , fieldOffset
  , getFieldInfo

    -- * Program Symbols
  , ProgramSymbols (..)
  , emptySymbols
  , lookupClass
  , lookupProgramMethod
  , getEntrypoint
  ) where

import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.List (find, elemIndex)

import LiveOak.Types
import LiveOak.Ast (ReturnSig (..))

-- | Variable symbol: represents a parameter or local variable.
data VarSymbol = VarSymbol
  { vsName     :: !String      -- ^ Variable name
  , vsType     :: !ValueType   -- ^ Variable type
  , vsIsParam  :: !Bool        -- ^ True if parameter, False if local
  , vsIndex    :: !Int         -- ^ 0-based index within params or locals
  , vsLine     :: !Int         -- ^ Source line (-1 if unknown)
  , vsColumn   :: !Int         -- ^ Source column (-1 if unknown)
  } deriving (Eq, Show)

-- | Calculate stack address for a variable.
-- Parameters have negative offsets, locals have positive offsets.
--
-- Stack frame layout (FBR at offset 0):
--   offset 0:  return value slot
--   offset -1: 'this' (param 0)
--   offset -2: arg1 (param 1)
--   ...
--   offset -(N+1): argN (param N)
--   offset 1: local0
--   offset 2: local1
--   ...
stackAddress :: Int -> VarSymbol -> Int
stackAddress totalParams vs
  | vsIsParam vs = -(totalParams - vsIndex vs)
  | otherwise    = 2 + vsIndex vs

-- | Method symbol: represents a method definition.
data MethodSymbol = MethodSymbol
  { msName           :: !String            -- ^ Method name
  , msParams         :: ![VarSymbol]       -- ^ Parameters (includes implicit 'this' at index 0)
  , msLocals         :: ![VarSymbol]       -- ^ Local variables
  , msReturnType     :: !(Maybe ValueType) -- ^ Return type (Nothing = void)
  , msBodyStartLine  :: !Int               -- ^ Source line where body starts
  , msReturnTypeLine :: !Int               -- ^ Source line of return type
  , msReturnTypeCol  :: !Int               -- ^ Source column of return type
  } deriving (Eq, Show)

-- | Get the number of parameters (including implicit 'this').
numParams :: MethodSymbol -> Int
numParams = length . msParams

-- | Get the number of local variables.
numLocals :: MethodSymbol -> Int
numLocals = length . msLocals

-- | Get the expected number of user-provided arguments (excludes 'this').
expectedUserArgs :: MethodSymbol -> Int
expectedUserArgs ms = max 0 (numParams ms - 1)

-- | Calculate the return address offset.
returnAddressOffset :: MethodSymbol -> Int
returnAddressOffset ms = -(1 + numParams ms)

-- | Look up a variable by name in method scope (params first, then locals).
lookupVar :: String -> MethodSymbol -> Maybe VarSymbol
lookupVar name ms =
  find ((== name) . vsName) (msParams ms) <|>
  find ((== name) . vsName) (msLocals ms)
  where
    Nothing <|> b = b
    a       <|> _ = a

-- | Get the return signature from a method symbol.
getReturnSig :: MethodSymbol -> ReturnSig
getReturnSig ms = case msReturnType ms of
  Nothing -> Void
  Just (PrimitiveType t)  -> RetPrim t
  Just (ObjectRefType ot) -> RetObj (getClassName ot)

-- | Field info: resolved field with offset and type.
data FieldInfo = FieldInfo
  { fiOffset :: !Int         -- ^ Field offset (0-based)
  , fiType   :: !ValueType   -- ^ Field type
  , fiSymbol :: !VarSymbol   -- ^ Original var symbol
  } deriving (Eq, Show)

-- | Class symbol: represents a class definition.
data ClassSymbol = ClassSymbol
  { csName       :: !String                    -- ^ Class name
  , csFields     :: ![VarSymbol]               -- ^ Field declarations
  , csMethods    :: !(Map String MethodSymbol) -- ^ Methods by name
  , csFieldOrder :: ![String]                  -- ^ Field names in declaration order
  } deriving (Eq, Show)

-- | Look up a field by name.
lookupField :: String -> ClassSymbol -> Maybe VarSymbol
lookupField name cs = find ((== name) . vsName) (csFields cs)

-- | Look up a method by name.
lookupMethod :: String -> ClassSymbol -> Maybe MethodSymbol
lookupMethod name cs = Map.lookup name (csMethods cs)

-- | Get field offset (index in field order).
fieldOffset :: String -> ClassSymbol -> Maybe Int
fieldOffset name cs = elemIndex name (csFieldOrder cs)

-- | Get complete field info.
getFieldInfo :: String -> ClassSymbol -> Maybe FieldInfo
getFieldInfo name cs = do
  vs <- lookupField name cs
  off <- fieldOffset name cs
  return FieldInfo
    { fiOffset = off
    , fiType   = vsType vs
    , fiSymbol = vs
    }

-- | Program symbols: the complete symbol table.
newtype ProgramSymbols = ProgramSymbols
  { psClasses :: Map String ClassSymbol
  } deriving (Eq, Show)

-- | Empty program symbols.
emptySymbols :: ProgramSymbols
emptySymbols = ProgramSymbols Map.empty

-- | Look up a class by name.
lookupClass :: String -> ProgramSymbols -> Maybe ClassSymbol
lookupClass name ps = Map.lookup name (psClasses ps)

-- | Look up a method in a specific class.
lookupProgramMethod :: String -> String -> ProgramSymbols -> Maybe MethodSymbol
lookupProgramMethod className methodName ps = do
  cs <- lookupClass className ps
  lookupMethod methodName cs

-- | Get the Main.main entry point.
getEntrypoint :: ProgramSymbols -> Maybe MethodSymbol
getEntrypoint = lookupProgramMethod "Main" "main"

-- | Check if a class exists.
classExists :: String -> ProgramSymbols -> Bool
classExists name ps = Map.member name (psClasses ps)

-- | Get all classes.
allClasses :: ProgramSymbols -> [ClassSymbol]
allClasses = Map.elems . psClasses

-- | Number of fields in a class.
numFields :: ClassSymbol -> Int
numFields = length . csFieldOrder
