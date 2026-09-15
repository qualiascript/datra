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
import Data.Maybe (fromMaybe)
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

-- | Validate optional natural-number bounds and introduce the resulting range
-- with a fresh abstract scope. The range must be nonempty, treating a missing
-- lower bound as zero.
ellipsisRange
  :: Maybe Natural
  -> Maybe Natural
  -> (forall scope. EllipsisRange scope -> result)
  -> Maybe result
ellipsisRange lower upper useRange
  | validOrder lower upper =
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

validOrder :: Maybe Natural -> Maybe Natural -> Bool
validOrder maybeLower (Just upper) = fromMaybe 0 maybeLower < upper
validOrder _ Nothing = True

rankInRange :: EllipsisRange scope -> Natural -> Bool
rankInRange valueRange rankValue =
  maybe True (<= rankValue)
    (ellipsisRangeLowerBound valueRange)
    && maybe True (rankValue <)
      (ellipsisRangeUpperBound valueRange)
