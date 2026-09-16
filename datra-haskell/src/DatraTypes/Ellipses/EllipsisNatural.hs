{-# LANGUAGE RankNTypes #-}

-- | Natural numbers represented as singleton ellipsis ranges.
module EllipsisNatural
  ( EllipsisNatural
  , EllipsisNaturalElement
  , ellipsisNatural
  , ellipsisNaturalInsertion
  ) where

import EllipsisInsertion (EllipsisInsertion)
import EllipsisNaturalRange
  ( EllipsisNaturalRange
  , EllipsisNaturalRangeElement
  , ellipsisNaturalRange
  , ellipsisNaturalRangeInsertion
  )
import Numeric.Natural (Natural)

-- | A natural number represented by the singleton ellipsis range @[m,m+1)@.
type EllipsisNatural = EllipsisNaturalRange

-- | The sole member of one ellipsis-natural singleton range.
type EllipsisNaturalElement = EllipsisNaturalRangeElement

-- | Construct the singleton range containing exactly @m@, including when
-- @m@ is zero.
ellipsisNatural
  :: Natural
  -> (forall scope. EllipsisNatural scope -> result)
  -> Maybe result
ellipsisNatural value =
  ellipsisNaturalRange (Just value) (Just (value + 1))

-- | Insert this singleton natural into 'Ellipsis'.
ellipsisNaturalInsertion
  :: EllipsisNatural scope
  -> EllipsisInsertion (EllipsisNaturalElement scope)
ellipsisNaturalInsertion = ellipsisNaturalRangeInsertion
