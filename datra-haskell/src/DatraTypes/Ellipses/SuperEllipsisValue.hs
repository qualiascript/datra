{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeFamilies #-}

-- | Individual ordinal values represented as singleton super-ellipsis ranges.
module SuperEllipsisValue
  ( SuperEllipsisValue
  , SuperEllipsisValueElement
  , superEllipsisValue
  , canonicalSuperEllipsisValue
  , minimumSuperEllipsisValueRank
  , superEllipsisValueRange
  , superEllipsisValueOrdinal
  , superEllipsisValueInsertion
  ) where

import DatraOrdinal
  ( Ordinal
  , addOrdinals
  , finiteOrdinal
  )
import Data.Kind (Type)
import MapOperators.OrderedAtlasMap (HasOrderedAtlasMap (..))
import SuperEllipsis
  ( SuperEllipsisRank
  , SuperEllipsisTarget
  , minimumSuperEllipsisValueRank
  , superEllipsisRankLevel
  , withMinimalSuperEllipsisOrdinal
  )
import SuperEllipsisInsertion
  ( HasSuperEllipsisInsertion (..)
  , SuperEllipsisInsertion
  )
import SuperEllipsisRange
  ( SuperEllipsisRange
  , SuperEllipsisRangeElement
  , SuperEllipsisRangeTarget (GivenTarget)
  , superEllipsisRange
  , superEllipsisRangeLowerBound
  , superEllipsisRangeInsertion
  , superEllipsisSingletonRange
  )

-- | A single value below one finite-rank super ellipsis.
--
-- This is deliberately nominal rather than a synonym for
-- 'SuperEllipsisRange': arbitrary ranges must not type-check as numerical
-- values.  The hidden constructor records that the wrapped range was created
-- by 'superEllipsisValue' and is therefore a singleton.
newtype SuperEllipsisValue (target :: Type) scope = SuperEllipsisValue
  { superEllipsisValueRange :: SuperEllipsisRange target scope
  }

type SuperEllipsisValueElement = SuperEllipsisRangeElement

-- | Introduce an ordinal at its uniquely determined minimal rank. The target
-- is existential so callers cannot request or observe a non-minimal carrier.
canonicalSuperEllipsisValue
  :: Ordinal
  -> (forall target scope.
        SuperEllipsisTarget target
        => SuperEllipsisValue target scope
        -> result)
  -> result
canonicalSuperEllipsisValue value useValue =
  withMinimalSuperEllipsisOrdinal value $ \minimalValue ->
    superEllipsisSingletonRange minimalValue (useValue . SuperEllipsisValue)

-- | Introduce the singleton range containing one ordinal value.
superEllipsisValue
  :: SuperEllipsisRank target
  -> Ordinal
  -> (forall scope. SuperEllipsisValue target scope -> result)
  -> Maybe result
superEllipsisValue valueRank value useValue
  | suppliedRank /= requiredRank =
      Nothing
  | otherwise =
      superEllipsisRange
        valueRank
        value
        (GivenTarget (addOrdinals value (finiteOrdinal 1)))
        (useValue . SuperEllipsisValue)
  where
    suppliedRank = superEllipsisRankLevel valueRank
    requiredRank = minimumSuperEllipsisValueRank value

-- | Recover the represented ordinal.  The hidden constructor makes this
-- projection total.
superEllipsisValueOrdinal
  :: SuperEllipsisValue target scope
  -> Ordinal
superEllipsisValueOrdinal =
  superEllipsisRangeLowerBound . superEllipsisValueRange

superEllipsisValueInsertion
  :: SuperEllipsisValue target scope
  -> SuperEllipsisInsertion
       target (SuperEllipsisValueElement target scope)
superEllipsisValueInsertion =
  superEllipsisRangeInsertion . superEllipsisValueRange

instance HasSuperEllipsisInsertion (SuperEllipsisValue target scope) where
  type InsertionTarget (SuperEllipsisValue target scope) = target
  type InsertionSource (SuperEllipsisValue target scope) =
    SuperEllipsisValueElement target scope
  superEllipsisInsertionOf = superEllipsisValueInsertion

instance HasOrderedAtlasMap (SuperEllipsisValue target scope) where
  type OrderedAtlasElement (SuperEllipsisValue target scope) =
    SuperEllipsisValueElement target scope
  orderedAtlasMap = orderedAtlasMap . superEllipsisValueRange
