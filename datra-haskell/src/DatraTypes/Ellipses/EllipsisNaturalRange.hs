{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE RoleAnnotations #-}

-- | Nonempty half-open natural ranges of Ellipsis regions and their merges.
module EllipsisNaturalRange
  ( EllipsisNaturalRange
  , EllipsisNaturalRangeElement
  , NonOverlappingEllipsisNaturalRanges
  , EllipsisNaturalRangeMergeKind (..)
  , EllipsisNaturalRangeMerge (..)
  , SomeEllipsisNaturalRangeMerge (..)
  , ellipsisNaturalRange
  , ellipsisNaturalRangeLowerBound
  , ellipsisNaturalRangeUpperBound
  , ellipsisNaturalRangeElement
  , ellipsisNaturalRangeElementRank
  , ellipsisNaturalRangeInsertion
  , nonOverlappingEllipsisNaturalRanges
  , mergeEllipsisNaturalRanges
  , mergeSeparatedEllipsisNaturalRanges
  , withMergedEllipsisNaturalRange
  ) where

import Data.Kind (Type)
import Data.Maybe (fromMaybe)
import Ellipsis (EllipsisTerminal (Terminal), terminalRank)
import EllipsisInsertion
  ( EllipsisInsertion
  , applyEllipsisInsertion
  , ellipsisInsertion
  , ellipsisInsertionPreimage
  )
import Numeric.Natural (Natural)

-- | A half-open interval of ellipsis ranks. A missing bound leaves that side
-- unrestricted.
type role EllipsisNaturalRange nominal
data EllipsisNaturalRange (scope :: Type) = EllipsisNaturalRange
  { ellipsisNaturalRangeLowerBound :: Maybe Natural
  , ellipsisNaturalRangeUpperBound :: Maybe Natural
  }

-- | An ellipsis rank known to belong to one particular range.
type role EllipsisNaturalRangeElement nominal
newtype EllipsisNaturalRangeElement (scope :: Type) = EllipsisNaturalRangeElement
  { ellipsisNaturalRangeElementRank :: Natural
  }
  deriving (Eq, Show)

-- | The relative order of two ranges whose images do not overlap.
data EllipsisNaturalRangeOrder
  = FirstBeforeSecond
  | SecondBeforeFirst

-- | Evidence that two ranges do not overlap. Its constructor is hidden from
-- the public API, so it can only be obtained after checking their bounds.
data NonOverlappingEllipsisNaturalRanges leftScope rightScope =
  NonOverlappingEllipsisNaturalRanges
    (EllipsisNaturalRange leftScope)
    (EllipsisNaturalRange rightScope)
    EllipsisNaturalRangeOrder

-- | The type-level classification of a range merge result.
data EllipsisNaturalRangeMergeKind
  = EllipsisNaturalRangeMergeResult
  | EllipsisInsertionMergeResult

-- | A merge result indexed by whether its image is itself a contiguous range.
data EllipsisNaturalRangeMerge
    (kind :: EllipsisNaturalRangeMergeKind)
    leftScope
    rightScope where
  MergedEllipsisNaturalRange
    :: EllipsisNaturalRange unionScope
    -> EllipsisNaturalRangeMerge 'EllipsisNaturalRangeMergeResult leftScope rightScope
  MergedEllipsisInsertion
    :: EllipsisInsertion
        (Either
          (EllipsisNaturalRangeElement leftScope)
          (EllipsisNaturalRangeElement rightScope))
    -> EllipsisNaturalRangeMerge 'EllipsisInsertionMergeResult leftScope rightScope

-- | Existentially package the result kind selected from runtime bounds.
data SomeEllipsisNaturalRangeMerge leftScope rightScope where
  SomeEllipsisNaturalRangeMerge
    :: EllipsisNaturalRangeMerge kind leftScope rightScope
    -> SomeEllipsisNaturalRangeMerge leftScope rightScope

-- | Validate optional natural-number bounds and introduce the resulting range
-- with a fresh abstract scope. The range must be nonempty, treating a missing
-- lower bound as zero.
ellipsisNaturalRange
  :: Maybe Natural
  -> Maybe Natural
  -> (forall scope. EllipsisNaturalRange scope -> result)
  -> Maybe result
ellipsisNaturalRange lower upper useRange
  | validOrder lower upper =
      Just (useRange (EllipsisNaturalRange lower upper))
  | otherwise = Nothing

-- | Refine an absolute ellipsis rank to membership in this range.
ellipsisNaturalRangeElement
  :: EllipsisNaturalRange scope
  -> Natural
  -> Maybe (EllipsisNaturalRangeElement scope)
ellipsisNaturalRangeElement valueRange rankValue
  | rankInRange valueRange rankValue =
      Just (EllipsisNaturalRangeElement rankValue)
  | otherwise = Nothing

-- | Insert exactly the terminals in the half-open range into 'Ellipsis'.
ellipsisNaturalRangeInsertion
  :: EllipsisNaturalRange scope
  -> EllipsisInsertion (EllipsisNaturalRangeElement scope)
ellipsisNaturalRangeInsertion valueRange =
  ellipsisInsertion
    (Terminal . ellipsisNaturalRangeElementRank)
    (ellipsisNaturalRangeElement valueRange . terminalRank)
    (const ())

-- | Check that the two ranges do not overlap and retain their relative order
-- as evidence required by 'mergeEllipsisNaturalRanges'. Touching ranges are
-- allowed.
nonOverlappingEllipsisNaturalRanges
  :: EllipsisNaturalRange leftScope
  -> EllipsisNaturalRange rightScope
  -> Maybe (NonOverlappingEllipsisNaturalRanges leftScope rightScope)
nonOverlappingEllipsisNaturalRanges first second
  | rangeBefore first second =
      Just (NonOverlappingEllipsisNaturalRanges first second FirstBeforeSecond)
  | rangeBefore second first =
      Just (NonOverlappingEllipsisNaturalRanges first second SecondBeforeFirst)
  | otherwise = Nothing

-- | Merge two non-overlapping ranges. Adjacent ranges produce a range at the
-- result type; ranges separated by a gap produce the more general ellipsis
-- insertion whose source is their disjoint union.
mergeEllipsisNaturalRanges
  :: NonOverlappingEllipsisNaturalRanges leftScope rightScope
  -> SomeEllipsisNaturalRangeMerge leftScope rightScope
mergeEllipsisNaturalRanges
    (NonOverlappingEllipsisNaturalRanges first second order)
  | rangesTouch first second order =
      SomeEllipsisNaturalRangeMerge
        (MergedEllipsisNaturalRange (combinedRange first second order))
  | otherwise =
      SomeEllipsisNaturalRangeMerge
        (MergedEllipsisInsertion (disjointInsertion first second))

-- | Merge ranges only when they are separated by a gap. Overlapping or
-- adjacent inputs return 'Nothing'; adjacency is represented by a range merge
-- rather than an insertion merge.
mergeSeparatedEllipsisNaturalRanges
  :: EllipsisNaturalRange leftScope
  -> EllipsisNaturalRange rightScope
  -> Maybe
      (EllipsisInsertion
        (Either
          (EllipsisNaturalRangeElement leftScope)
          (EllipsisNaturalRangeElement rightScope)))
mergeSeparatedEllipsisNaturalRanges first second = do
  nonOverlapping <- nonOverlappingEllipsisNaturalRanges first second
  case mergeEllipsisNaturalRanges nonOverlapping of
    SomeEllipsisNaturalRangeMerge (MergedEllipsisInsertion insertion) ->
      Just insertion
    SomeEllipsisNaturalRangeMerge (MergedEllipsisNaturalRange _) -> Nothing

-- | Eliminate a merge result known at the type level to be a contiguous
-- range. The continuation keeps the merged range's fresh scope from escaping.
withMergedEllipsisNaturalRange
  :: EllipsisNaturalRangeMerge
      'EllipsisNaturalRangeMergeResult
      leftScope
      rightScope
  -> (forall unionScope. EllipsisNaturalRange unionScope -> result)
  -> result
withMergedEllipsisNaturalRange (MergedEllipsisNaturalRange valueRange) useRange =
  useRange valueRange

validOrder :: Maybe Natural -> Maybe Natural -> Bool
validOrder maybeLower (Just upper) = fromMaybe 0 maybeLower < upper
validOrder _ Nothing = True

rankInRange :: EllipsisNaturalRange scope -> Natural -> Bool
rankInRange valueRange rankValue =
  maybe True (<= rankValue)
    (ellipsisNaturalRangeLowerBound valueRange)
    && maybe True (rankValue <)
      (ellipsisNaturalRangeUpperBound valueRange)

rangeBefore
  :: EllipsisNaturalRange firstScope
  -> EllipsisNaturalRange secondScope
  -> Bool
rangeBefore first second =
  case ellipsisNaturalRangeUpperBound first of
    Nothing -> False
    Just firstUpper ->
      firstUpper <= fromMaybe 0 (ellipsisNaturalRangeLowerBound second)

rangesTouch
  :: EllipsisNaturalRange leftScope
  -> EllipsisNaturalRange rightScope
  -> EllipsisNaturalRangeOrder
  -> Bool
rangesTouch first second FirstBeforeSecond =
  ellipsisNaturalRangeUpperBound first
    == Just (fromMaybe 0 (ellipsisNaturalRangeLowerBound second))
rangesTouch first second SecondBeforeFirst =
  ellipsisNaturalRangeUpperBound second
    == Just (fromMaybe 0 (ellipsisNaturalRangeLowerBound first))

combinedRange
  :: EllipsisNaturalRange leftScope
  -> EllipsisNaturalRange rightScope
  -> EllipsisNaturalRangeOrder
  -> EllipsisNaturalRange unionScope
combinedRange first second FirstBeforeSecond =
  EllipsisNaturalRange
    (ellipsisNaturalRangeLowerBound first)
    (ellipsisNaturalRangeUpperBound second)
combinedRange first second SecondBeforeFirst =
  EllipsisNaturalRange
    (ellipsisNaturalRangeLowerBound second)
    (ellipsisNaturalRangeUpperBound first)

disjointInsertion
  :: EllipsisNaturalRange leftScope
  -> EllipsisNaturalRange rightScope
  -> EllipsisInsertion
      (Either
        (EllipsisNaturalRangeElement leftScope)
        (EllipsisNaturalRangeElement rightScope))
disjointInsertion first second =
  ellipsisInsertion forward backward (const ())
  where
    firstInsertion = ellipsisNaturalRangeInsertion first
    secondInsertion = ellipsisNaturalRangeInsertion second

    forward (Left element) = applyEllipsisInsertion firstInsertion element
    forward (Right element) = applyEllipsisInsertion secondInsertion element

    backward terminal =
      case ellipsisInsertionPreimage firstInsertion terminal of
        Just element -> Just (Left element)
        Nothing -> Right <$> ellipsisInsertionPreimage secondInsertion terminal
