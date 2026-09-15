{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE RoleAnnotations #-}

-- | Nonempty half-open ranges of ellipsis ranks and their merge operations.
module EllipsisRange
  ( EllipsisRange
  , EllipsisRangeElement
  , NonOverlappingEllipsisRanges
  , EllipsisRangeMergeKind (..)
  , EllipsisRangeMerge (..)
  , SomeEllipsisRangeMerge (..)
  , ellipsisRange
  , ellipsisRangeLowerBound
  , ellipsisRangeUpperBound
  , ellipsisRangeElement
  , ellipsisRangeElementRank
  , ellipsisRangeInsertion
  , nonOverlappingEllipsisRanges
  , mergeEllipsisRanges
  , mergeSeparatedEllipsisRanges
  , withMergedEllipsisRange
  ) where

import Data.Kind (Type)
import Data.Maybe (fromMaybe)
import DomanialInsertion (applyInsertion, preimage)
import Ellipsis (Ellipsis (Terminal), terminalRank)
import EllipsisInsertion
  ( EllipsisInsertion
  , ellipsisInsertion
  )
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

-- | The relative order of two ranges whose images do not overlap.
data EllipsisRangeOrder
  = FirstBeforeSecond
  | SecondBeforeFirst

-- | Evidence that two ranges do not overlap. Its constructor is hidden from
-- the public API, so it can only be obtained after checking their bounds.
data NonOverlappingEllipsisRanges leftScope rightScope =
  NonOverlappingEllipsisRanges
    (EllipsisRange leftScope)
    (EllipsisRange rightScope)
    EllipsisRangeOrder

-- | The type-level classification of a range merge result.
data EllipsisRangeMergeKind
  = EllipsisRangeMergeResult
  | EllipsisInsertionMergeResult

-- | A merge result indexed by whether its image is itself a contiguous range.
data EllipsisRangeMerge
    (kind :: EllipsisRangeMergeKind)
    leftScope
    rightScope where
  MergedEllipsisRange
    :: EllipsisRange unionScope
    -> EllipsisRangeMerge 'EllipsisRangeMergeResult leftScope rightScope
  MergedEllipsisInsertion
    :: EllipsisInsertion
        (Either
          (EllipsisRangeElement leftScope)
          (EllipsisRangeElement rightScope))
    -> EllipsisRangeMerge 'EllipsisInsertionMergeResult leftScope rightScope

-- | Existentially package the result kind selected from runtime bounds.
data SomeEllipsisRangeMerge leftScope rightScope where
  SomeEllipsisRangeMerge
    :: EllipsisRangeMerge kind leftScope rightScope
    -> SomeEllipsisRangeMerge leftScope rightScope

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
  -> EllipsisInsertion (EllipsisRangeElement scope)
ellipsisRangeInsertion valueRange =
  ellipsisInsertion
    (Terminal . ellipsisRangeElementRank)
    (ellipsisRangeElement valueRange . terminalRank)
    (const ())

-- | Check that the two ranges do not overlap and retain their relative order
-- as evidence required by 'mergeEllipsisRanges'. Touching ranges are allowed.
nonOverlappingEllipsisRanges
  :: EllipsisRange leftScope
  -> EllipsisRange rightScope
  -> Maybe (NonOverlappingEllipsisRanges leftScope rightScope)
nonOverlappingEllipsisRanges first second
  | rangeBefore first second =
      Just (NonOverlappingEllipsisRanges first second FirstBeforeSecond)
  | rangeBefore second first =
      Just (NonOverlappingEllipsisRanges first second SecondBeforeFirst)
  | otherwise = Nothing

-- | Merge two non-overlapping ranges. Adjacent ranges produce a range at the
-- result type; ranges separated by a gap produce the more general ellipsis
-- insertion whose source is their disjoint union.
mergeEllipsisRanges
  :: NonOverlappingEllipsisRanges leftScope rightScope
  -> SomeEllipsisRangeMerge leftScope rightScope
mergeEllipsisRanges
    (NonOverlappingEllipsisRanges first second order)
  | rangesTouch first second order =
      SomeEllipsisRangeMerge
        (MergedEllipsisRange (combinedRange first second order))
  | otherwise =
      SomeEllipsisRangeMerge
        (MergedEllipsisInsertion (disjointInsertion first second))

-- | Merge ranges only when they are separated by a gap. Overlapping or
-- adjacent inputs return 'Nothing'; adjacency is represented by a range merge
-- rather than an insertion merge.
mergeSeparatedEllipsisRanges
  :: EllipsisRange leftScope
  -> EllipsisRange rightScope
  -> Maybe
      (EllipsisInsertion
        (Either
          (EllipsisRangeElement leftScope)
          (EllipsisRangeElement rightScope)))
mergeSeparatedEllipsisRanges first second = do
  nonOverlapping <- nonOverlappingEllipsisRanges first second
  case mergeEllipsisRanges nonOverlapping of
    SomeEllipsisRangeMerge (MergedEllipsisInsertion insertion) ->
      Just insertion
    SomeEllipsisRangeMerge (MergedEllipsisRange _) -> Nothing

-- | Eliminate a merge result known at the type level to be a contiguous
-- range. The continuation keeps the merged range's fresh scope from escaping.
withMergedEllipsisRange
  :: EllipsisRangeMerge
      'EllipsisRangeMergeResult
      leftScope
      rightScope
  -> (forall unionScope. EllipsisRange unionScope -> result)
  -> result
withMergedEllipsisRange (MergedEllipsisRange valueRange) useRange =
  useRange valueRange

validOrder :: Maybe Natural -> Maybe Natural -> Bool
validOrder maybeLower (Just upper) = fromMaybe 0 maybeLower < upper
validOrder _ Nothing = True

rankInRange :: EllipsisRange scope -> Natural -> Bool
rankInRange valueRange rankValue =
  maybe True (<= rankValue)
    (ellipsisRangeLowerBound valueRange)
    && maybe True (rankValue <)
      (ellipsisRangeUpperBound valueRange)

rangeBefore
  :: EllipsisRange firstScope
  -> EllipsisRange secondScope
  -> Bool
rangeBefore first second =
  case ellipsisRangeUpperBound first of
    Nothing -> False
    Just firstUpper ->
      firstUpper <= fromMaybe 0 (ellipsisRangeLowerBound second)

rangesTouch
  :: EllipsisRange leftScope
  -> EllipsisRange rightScope
  -> EllipsisRangeOrder
  -> Bool
rangesTouch first second FirstBeforeSecond =
  ellipsisRangeUpperBound first
    == Just (fromMaybe 0 (ellipsisRangeLowerBound second))
rangesTouch first second SecondBeforeFirst =
  ellipsisRangeUpperBound second
    == Just (fromMaybe 0 (ellipsisRangeLowerBound first))

combinedRange
  :: EllipsisRange leftScope
  -> EllipsisRange rightScope
  -> EllipsisRangeOrder
  -> EllipsisRange unionScope
combinedRange first second FirstBeforeSecond =
  EllipsisRange
    (ellipsisRangeLowerBound first)
    (ellipsisRangeUpperBound second)
combinedRange first second SecondBeforeFirst =
  EllipsisRange
    (ellipsisRangeLowerBound second)
    (ellipsisRangeUpperBound first)

disjointInsertion
  :: EllipsisRange leftScope
  -> EllipsisRange rightScope
  -> EllipsisInsertion
      (Either
        (EllipsisRangeElement leftScope)
        (EllipsisRangeElement rightScope))
disjointInsertion first second =
  ellipsisInsertion forward backward (const ())
  where
    firstInsertion = ellipsisRangeInsertion first
    secondInsertion = ellipsisRangeInsertion second

    forward (Left element) = applyInsertion firstInsertion element
    forward (Right element) = applyInsertion secondInsertion element

    backward terminal =
      case preimage firstInsertion terminal of
        Just element -> Just (Left element)
        Nothing -> Right <$> preimage secondInsertion terminal
