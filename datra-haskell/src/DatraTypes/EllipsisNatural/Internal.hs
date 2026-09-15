{-# LANGUAGE RankNTypes #-}

-- | Hidden implementation of naturals as singleton ellipsis ranges.
module EllipsisNatural.Internal
  ( EllipsisNatural
  , ellipsisNatural
  ) where

import EllipsisRange.Internal (EllipsisRange, ellipsisRange)
import Numeric.Natural (Natural)

-- | A natural number represented by the singleton ellipsis range @[m,m+1)@.
type EllipsisNatural = EllipsisRange

-- | Construct the singleton range containing exactly @m@, including when
-- @m@ is zero.
ellipsisNatural
  :: Natural
  -> (forall scope. EllipsisNatural scope -> result)
  -> Maybe result
ellipsisNatural value =
  ellipsisRange (Just value) (Just (value + 1))
