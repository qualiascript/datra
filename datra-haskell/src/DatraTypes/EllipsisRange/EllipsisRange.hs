-- | Public ellipsis-range API backed by the hidden implementation.
module EllipsisRange
  ( EllipsisRange
  , EllipsisRangeElement
  , ellipsisRange
  , ellipsisRangeLowerBound
  , ellipsisRangeUpperBound
  , ellipsisRangeElement
  , ellipsisRangeElementRank
  , ellipsisRangeInsertion
  ) where

import EllipsisRange.Internal
  ( EllipsisRange
  , EllipsisRangeElement
  , ellipsisRange
  , ellipsisRangeElement
  , ellipsisRangeElementRank
  , ellipsisRangeInsertion
  , ellipsisRangeLowerBound
  , ellipsisRangeUpperBound
  )
