-- | Rank-one name for a super-ellipsis range.
module EllipsisRange
  ( EllipsisRange
  ) where

import Ellipsis (Ellipsis)
import SuperEllipsisRange (SuperEllipsisRange)

type EllipsisRange = SuperEllipsisRange Ellipsis
