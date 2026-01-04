module LiveOak.MapUtils
  ( lookupSet
  , lookupList
  ) where

import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Set (Set)
import qualified Data.Set as Set

lookupSet :: Ord k => k -> Map k (Set v) -> Set v
lookupSet key m = Map.findWithDefault Set.empty key m

lookupList :: Ord k => k -> Map k [v] -> [v]
lookupList key m = Map.findWithDefault [] key m
