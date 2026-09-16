-- | Rank-one name for a super-ellipsis insertion.
module EllipsisInsertion
  ( EllipsisInsertion
  ) where

import Ellipsis (Ellipsis)
import SuperEllipsisInsertion (SuperEllipsisInsertion)

type EllipsisInsertion = SuperEllipsisInsertion Ellipsis
