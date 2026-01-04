module LiveOak.MapUtils
  ( lookupSet
  , lookupList
  , lookupIntWith
  , lookupInt
  ) where

import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Set (Set)
import qualified Data.Set as Set

lookupSet :: Ord k => k -> Map k (Set v) -> Set v
lookupSet = Map.findWithDefault Set.empty

lookupList :: Ord k => k -> Map k [v] -> [v]
lookupList = Map.findWithDefault []

lookupIntWith :: Ord k => Int -> k -> Map k Int -> Int
lookupIntWith = Map.findWithDefault

lookupInt :: Ord k => k -> Map k Int -> Int
lookupInt = lookupIntWith 0
