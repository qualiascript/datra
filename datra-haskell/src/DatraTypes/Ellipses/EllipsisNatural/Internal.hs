{-# LANGUAGE RankNTypes #-}

-- | Hidden implementation of naturals as singleton ellipsis ranges.
module EllipsisNatural.Internal
  ( EllipsisNatural
  , EllipsisNaturalElement
  , ellipsisNatural
  , ellipsisNaturalInsertion
  ) where

import EllipsisInsertion.Internal (EllipsisInsertion)
import EllipsisRange.Internal
  ( EllipsisRange
  , EllipsisRangeElement
  , ellipsisRange
  , ellipsisRangeInsertion
  )
import Numeric.Natural (Natural)

-- | A natural number represented by the singleton ellipsis range @[m,m+1)@.
type EllipsisNatural = EllipsisRange

-- | The sole member of one ellipsis-natural singleton range.
type EllipsisNaturalElement = EllipsisRangeElement

-- | Construct the singleton range containing exactly @m@, including when
-- @m@ is zero.
ellipsisNatural
  :: Natural
  -> (forall scope. EllipsisNatural scope -> result)
  -> Maybe result
ellipsisNatural value =
  ellipsisRange (Just value) (Just (value + 1))

-- | Insert this singleton natural into 'Ellipsis'.
ellipsisNaturalInsertion
  :: EllipsisNatural scope
  -> EllipsisInsertion (EllipsisNaturalElement scope)
ellipsisNaturalInsertion = ellipsisRangeInsertion
