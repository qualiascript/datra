{-# LANGUAGE RankNTypes #-}

-- | Individual ordinal values represented as singleton super-ellipsis ranges.
module SuperEllipsisValue
  ( SuperEllipsisValue
  , SuperEllipsisValueElement
  , superEllipsisValue
  , superEllipsisValueInsertion
  ) where

import DatraOrdinal (Ordinal, addOrdinals, finiteOrdinal)
import SuperEllipsis (SuperEllipsisRank)
import SuperEllipsisInsertion (SuperEllipsisInsertion)
import SuperEllipsisRange
  ( SuperEllipsisRange
  , SuperEllipsisRangeElement
  , SuperEllipsisRangeTarget (FiniteTarget)
  , superEllipsisRange
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
    (Just value)
    (FiniteTarget (addOrdinals value (finiteOrdinal 1)))

superEllipsisValueInsertion
  :: SuperEllipsisValue target scope
  -> SuperEllipsisInsertion
       target (SuperEllipsisValueElement target scope)
superEllipsisValueInsertion = superEllipsisRangeInsertion
