-- | The first successor in the super-ellipsis hierarchy.
module Ellipsis
  ( Ellipsis
  , ellipsis
  ) where

import Dot (Dot, dot)
import StableConfederalData (StableConfederalData)
import SuperEllipsis (SuperEllipsis, superEllipsis)

-- | @Ellipsis = SuperEllipsis Dot@, with no rank-one-specific wrapper.
type Ellipsis = SuperEllipsis Dot

-- | The rank-one Ellipsis formulation.
ellipsis :: StableConfederalData Ellipsis
ellipsis = superEllipsis dot
