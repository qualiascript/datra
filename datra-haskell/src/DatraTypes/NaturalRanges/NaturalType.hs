{-# LANGUAGE RankNTypes #-}

-- | The natural type, canonically written @Nat@.
module NaturalType
  ( NaturalType
  , naturalType
  , naturalTypeEither
  ) where

import EllipsisNatural (ellipsisNaturalTotal)
import NaturalRange (upwards)
import ValuedNaturalRange
  ( ValuedNaturalRange
  , valuedNaturalRangeEither
  )
import SuperEllipsisRange (SuperEllipsisRangeError)

-- | @Nat@ is the valued natural range @from 0 upwards@.
type NaturalType = ValuedNaturalRange

naturalType
  :: (forall rangeScope federationScope.
       NaturalType rangeScope federationScope
       -> result)
  -> Maybe result
naturalType useNaturalType = do
  case naturalTypeEither useNaturalType of
    Left _ -> Nothing
    Right result -> Just result

naturalTypeEither
  :: (forall rangeScope federationScope.
       NaturalType rangeScope federationScope
       -> result)
  -> Either SuperEllipsisRangeError result
naturalTypeEither useNaturalType =
  ellipsisNaturalTotal 0 $ \zero ->
    valuedNaturalRangeEither zero upwards useNaturalType
