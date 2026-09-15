-- | Public ellipsis-range API backed by the hidden implementation.
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

import EllipsisRange.Internal
  ( EllipsisRangeMerge (..)
  , EllipsisRangeMergeKind (..)
  , EllipsisRange
  , EllipsisRangeElement
  , NonOverlappingEllipsisRanges
  , SomeEllipsisRangeMerge (..)
  , ellipsisRange
  , ellipsisRangeElement
  , ellipsisRangeElementRank
  , ellipsisRangeInsertion
  , ellipsisRangeLowerBound
  , mergeEllipsisRanges
  , mergeSeparatedEllipsisRanges
  , ellipsisRangeUpperBound
  , nonOverlappingEllipsisRanges
  , withMergedEllipsisRange
  )
