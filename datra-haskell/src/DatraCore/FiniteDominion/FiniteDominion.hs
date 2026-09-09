{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE RoleAnnotations #-}

-- | Type-safe finite carriers constructed from runtime sets.
--
-- Lean can use a subtype for set membership and @Fin n@ for bounded indices.
-- Here a rank-2 scope token provides the corresponding separation: only
-- values refined through this finite carrier can be ranked, and indices from
-- distinct carriers cannot be mixed.
module FiniteDominion
  ( FiniteDominion
  , FiniteElement
  , FiniteIndex
  , finiteSetDominion
  , finiteAsDominion
  , finiteMember
  , finiteValue
  , finiteCardinality
  , finiteIndex
  , finiteIndexValue
  , finiteRank
  , finiteUnrank
  ) where

import Data.Kind (Type)
import Data.Set (Set)
import Dominion (Dominion, dominion)
import Numeric.Natural (Natural)

import qualified Data.Map.Strict as Map
import qualified Data.Set as Set

-- | A finite carrier created from a runtime 'Set'.
type role FiniteDominion nominal nominal
data FiniteDominion (scope :: Type) a = FiniteDominion
  { finiteValuesByRank :: Map.Map Natural a
  , finiteRanksByValue :: Map.Map a Natural
  , finiteCardinality :: Natural
  }

-- | An element carrying evidence that it belongs to one finite carrier.
type role FiniteElement nominal representational
data FiniteElement (scope :: Type) a = FiniteElement Natural a
  deriving (Eq, Show)

-- | An index known to be below one finite carrier's cardinality.
type role FiniteIndex nominal representational
data FiniteIndex (scope :: Type) a = FiniteIndex Natural a
  deriving (Eq, Show)

-- | Introduce a finite carrier with a fresh abstract scope. The continuation
-- prevents its membership and bounded-index evidence from escaping.
finiteSetDominion
  :: Ord a
  => Set a
  -> (forall scope. FiniteDominion scope a -> result)
  -> result
finiteSetDominion set useFinite =
  useFinite
    FiniteDominion
      { finiteValuesByRank = Map.fromList numbered
      , finiteRanksByValue = Map.fromList
          (map (\(valueRank, value) -> (value, valueRank)) numbered)
      , finiteCardinality = fromIntegral (Set.size set)
      }
  where
    numbered = zip [0 ..] (Set.toAscList set)

-- | Safely refine an ordinary value to an element of this finite carrier.
finiteMember
  :: Ord a
  => FiniteDominion scope a
  -> a
  -> Maybe (FiniteElement scope a)
finiteMember finite value =
  (`FiniteElement` value)
    <$> Map.lookup value (finiteRanksByValue finite)

-- | Forget the finite-carrier membership evidence.
finiteValue :: FiniteElement scope a -> a
finiteValue (FiniteElement _ value) = value

-- | Safely refine a natural number to an index below this carrier's
-- cardinality.
finiteIndex
  :: FiniteDominion scope a
  -> Natural
  -> Maybe (FiniteIndex scope a)
finiteIndex finite valueRank =
  FiniteIndex valueRank
    <$> Map.lookup valueRank (finiteValuesByRank finite)

-- | Forget the proof that an index is in bounds.
finiteIndexValue :: FiniteIndex scope a -> Natural
finiteIndexValue (FiniteIndex valueRank _) = valueRank

-- | The bounded rank of a finite carrier element.
finiteRank :: FiniteElement scope a -> FiniteIndex scope a
finiteRank (FiniteElement valueRank value) = FiniteIndex valueRank value

-- | Total inverse of 'finiteRank'. Its input type contains the evidence that
-- the index is below the cardinality of this particular carrier.
finiteUnrank :: FiniteIndex scope a -> FiniteElement scope a
finiteUnrank (FiniteIndex valueRank value) = FiniteElement valueRank value

-- This is the finite construction's trusted boundary: Data.Map is opaque to
-- LiquidHaskell, while enabling the plugin here would also trigger version
-- 0.9.4's broken cross-module loading of Dominion's dependent record. The
-- scoped GHC types still make every executable operation total on its input.
finiteAsDominion
  :: FiniteDominion scope a
  -> Dominion (FiniteElement scope a)
finiteAsDominion finite =
  dominion
    (finiteIndexValue . finiteRank)
    (fmap finiteUnrank . finiteIndex finite)
    (const ())
