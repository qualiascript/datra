-- | Infix syntax for the horizontal sum of stable confederal data.
module HorizontalSum.Syntax
  ( (|+|)
  ) where

import HorizontalSum (HorizontalSumValues, horizontalSum)
import StableConfederalData (StableConfederalData)

-- | Infix alias for 'horizontalSum'.
infixr 6 |+|

(|+|)
  :: StableConfederalData left
  -> StableConfederalData right
  -> StableConfederalData (HorizontalSumValues left right)
(|+|) = horizontalSum
