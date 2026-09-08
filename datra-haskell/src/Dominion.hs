module Dominion
  ( Dominion
  , rank
  , unrank
  , unsafeDominion
  , finiteSetDominion
  , CountableSet
  , elementAt
  , embed
  ) where

import Data.Set (Set)
import Data.Tuple (swap)
import Numeric.Natural (Natural)

import qualified Data.Map.Strict as Map
import qualified Data.Set as Set

data Dominion a = Dominion
  { rank   :: a -> Maybe Natural
  , unrank :: Natural -> Maybe a
  }

-- Expected law:
--
--   rank x == Just n  <=>  unrank n == Just x
unsafeDominion
  :: (a -> Maybe Natural)
  -> (Natural -> Maybe a)
  -> Dominion a
unsafeDominion = Dominion

finiteSetDominion :: Ord a => Set a -> Dominion a
finiteSetDominion set =
  Dominion
    { rank   = (`Map.lookup` ranksByValue)
    , unrank = (`Map.lookup` valuesByRank)
    }
  where
    numbered = zip [0 ..] (Set.toAscList set)

    valuesByRank = Map.fromList numbered

    ranksByValue = Map.fromList (map swap numbered)

newtype CountableSet a = CountableSet
  { elementAt :: Natural -> Maybe a
  }

embed :: Dominion a -> CountableSet a
embed dominion =
  CountableSet
    { elementAt = unrank dominion
    }
