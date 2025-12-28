{-# LANGUAGE LambdaCase #-}

-- | Core type system for LiveOak.
-- Defines primitive types (int, bool, String) and object reference types.
module LiveOak.Types
  ( -- * Primitive Types
    Type (..)
  , typeName
  , parseType

    -- * Object Types
  , ObjectType (..)

    -- * Value Types (union of primitive and object)
  , ValueType (..)
  , isPrimitive
  , isObject
  , primitiveType
  , objectType
  , typeClassName
  , ofPrimitive
  , ofObject
  , isCompatible
  ) where

import Data.Maybe (isJust)

-- | Primitive types in LiveOak.
data Type
  = TInt     -- ^ Integer type
  | TBool    -- ^ Boolean type
  | TString  -- ^ String type
  deriving (Eq, Ord, Show)

-- | Get the source-level name of a type.
typeName :: Type -> String
typeName = \case
  TInt    -> "int"
  TBool   -> "bool"
  TString -> "String"

-- | Parse a type name string.
parseType :: String -> Maybe Type
parseType = \case
  "int"    -> Just TInt
  "bool"   -> Just TBool
  "String" -> Just TString
  _        -> Nothing

-- | Object reference type (class name).
newtype ObjectType = ObjectType
  { getClassName :: String
  } deriving (Eq, Ord, Show)

-- | Value types: either a primitive or an object reference.
data ValueType
  = PrimitiveType Type
  | ObjectRefType ObjectType
  deriving (Eq, Ord, Show)

-- | Check if a value type is primitive.
isPrimitive :: ValueType -> Bool
isPrimitive (PrimitiveType _) = True
isPrimitive _                 = False

-- | Check if a value type is an object reference.
isObject :: ValueType -> Bool
isObject (ObjectRefType _) = True
isObject _                 = False

-- | Extract primitive type if present.
primitiveType :: ValueType -> Maybe Type
primitiveType (PrimitiveType t) = Just t
primitiveType _                 = Nothing

-- | Extract object type if present.
objectType :: ValueType -> Maybe ObjectType
objectType (ObjectRefType ot) = Just ot
objectType _                  = Nothing

-- | Extract class name if object type.
typeClassName :: ValueType -> Maybe String
typeClassName = fmap getClassName . objectType

-- | Construct a primitive value type.
ofPrimitive :: Type -> ValueType
ofPrimitive = PrimitiveType

-- | Construct an object value type from class name.
ofObject :: String -> ValueType
ofObject = ObjectRefType . ObjectType

-- | Check if two value types are compatible.
-- Primitive types must match exactly.
-- Object types must have the same class name.
isCompatible :: ValueType -> ValueType -> Bool
isCompatible (PrimitiveType t1) (PrimitiveType t2) = t1 == t2
isCompatible (ObjectRefType o1) (ObjectRefType o2) = getClassName o1 == getClassName o2
isCompatible _ _ = False

-- | Parse a raw type string into a ValueType.
-- Returns PrimitiveType for known primitives, ObjectRefType for anything else.
parseValueType :: String -> ValueType
parseValueType s = case parseType s of
  Just t  -> PrimitiveType t
  Nothing -> ObjectRefType (ObjectType s)
