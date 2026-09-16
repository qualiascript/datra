{-# LANGUAGE RankNTypes #-}

-- | Individual ordinal values represented as singleton super-ellipsis ranges.
module SuperEllipsisValue
  ( SuperEllipsisValue
  , SuperEllipsisValueElement
  , superEllipsisValue
  , superEllipsisValueOrdinal
  , superEllipsisValueInsertion
  ) where

import DatraOrdinal (Ordinal, addOrdinals, finiteOrdinal)
import SuperEllipsis (SuperEllipsisRank)
import SuperEllipsisInsertion (SuperEllipsisInsertion)
import SuperEllipsisRange
  ( SuperEllipsisRange
  , SuperEllipsisRangeElement
  , SuperEllipsisRangeTarget (GivenTarget)
  , superEllipsisRange
  , superEllipsisRangeLowerBound
  , superEllipsisRangeUpperBound
  , superEllipsisRangeInsertion
  )

-- | A single value below one finite-rank super ellipsis.
type SuperEllipsisValue = SuperEllipsisRange

type SuperEllipsisValueElement = SuperEllipsisRangeElement

-- | Introduce the singleton range containing one ordinal value.
superEllipsisValue
  :: SuperEllipsisRank target
  -> Ordinal
  -> (forall scope. SuperEllipsisValue target scope -> result)
  -> Maybe result
superEllipsisValue valueRank value =
  superEllipsisRange
    valueRank
    value
    (GivenTarget (addOrdinals value (finiteOrdinal 1)))

-- | Recover the represented ordinal, checking the singleton-range invariant.
superEllipsisValueOrdinal
  :: SuperEllipsisValue target scope
  -> Maybe Ordinal
superEllipsisValueOrdinal value = do
  upper <- superEllipsisRangeUpperBound value
  let lower = superEllipsisRangeLowerBound value
  if upper == addOrdinals lower (finiteOrdinal 1)
    then Just lower
    else Nothing

superEllipsisValueInsertion
  :: SuperEllipsisValue target scope
  -> SuperEllipsisInsertion
       target (SuperEllipsisValueElement target scope)
superEllipsisValueInsertion = superEllipsisRangeInsertion
