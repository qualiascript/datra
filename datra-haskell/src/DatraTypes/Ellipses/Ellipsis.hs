-- | The first successor in the super-ellipsis hierarchy.
module Ellipsis
  ( Ellipsis
  ) where

import Dot (Dot)
import SuperEllipsis (SuperEllipsis)

-- | @Ellipsis = SuperEllipsis Dot@, with no rank-one-specific wrapper.
type Ellipsis = SuperEllipsis Dot
