{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE RoleAnnotations #-}

-- | Hidden ellipsis-range representation and scoped operations.
module EllipsisRange.Internal
  ( EllipsisRange (..)
  , EllipsisRangeElement (..)
  , ellipsisRange
  , ellipsisRangeElement
  , ellipsisRangeInsertion
  ) where

import Data.Kind (Type)
import DomanialInsertion.Internal (DomanialInsertion, domanialInsertion)
import Ellipsis.Internal (Ellipsis (Terminal), terminalRank)
import Numeric.Natural (Natural)

-- | A half-open interval of ellipsis ranks. A missing bound leaves that side
-- unrestricted.
type role EllipsisRange nominal
data EllipsisRange (scope :: Type) = EllipsisRange
  { ellipsisRangeLowerBound :: Maybe Natural
  , ellipsisRangeUpperBound :: Maybe Natural
  }

-- | An ellipsis rank known to belong to one particular range.
type role EllipsisRangeElement nominal
newtype EllipsisRangeElement (scope :: Type) = EllipsisRangeElement
  { ellipsisRangeElementRank :: Natural
  }
  deriving (Eq, Show)

-- | Validate optional positive bounds and introduce the resulting range with
-- a fresh abstract scope. When both bounds are present, the lower bound must
-- be strictly smaller than the upper bound.
ellipsisRange
  :: Maybe Natural
  -> Maybe Natural
  -> (forall scope. EllipsisRange scope -> result)
  -> Maybe result
ellipsisRange lower upper useRange
  | validPositiveBound lower
      && validPositiveBound upper
      && validOrder lower upper =
      Just (useRange (EllipsisRange lower upper))
  | otherwise = Nothing

-- | Refine an absolute ellipsis rank to membership in this range.
ellipsisRangeElement
  :: EllipsisRange scope
  -> Natural
  -> Maybe (EllipsisRangeElement scope)
ellipsisRangeElement valueRange rankValue
  | rankInRange valueRange rankValue =
      Just (EllipsisRangeElement rankValue)
  | otherwise = Nothing

-- | Insert exactly the terminals in the half-open range into 'Ellipsis'.
ellipsisRangeInsertion
  :: EllipsisRange scope
  -> DomanialInsertion (EllipsisRangeElement scope) Ellipsis
ellipsisRangeInsertion valueRange =
  domanialInsertion
    (Terminal . ellipsisRangeElementRank)
    (ellipsisRangeElement valueRange . terminalRank)
    (const ())

validPositiveBound :: Maybe Natural -> Bool
validPositiveBound = maybe True (> 0)

validOrder :: Maybe Natural -> Maybe Natural -> Bool
validOrder (Just lower) (Just upper) = lower < upper
validOrder _ _ = True

rankInRange :: EllipsisRange scope -> Natural -> Bool
rankInRange valueRange rankValue =
  maybe True (<= rankValue)
    (ellipsisRangeLowerBound valueRange)
    && maybe True (rankValue <)
      (ellipsisRangeUpperBound valueRange)
