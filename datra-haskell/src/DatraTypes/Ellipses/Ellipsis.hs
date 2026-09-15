-- | A countably infinite dominion whose elements are all terminal.
module Ellipsis
  ( Ellipsis (Terminal)
  , terminalRank
  , ellipsis
  ) where

import Dominion (Dominion, dominion)
import Numeric.Natural (Natural)

-- | A terminal element of 'ellipsis', uniquely identified by its rank.
newtype Ellipsis = Terminal
  { terminalRank :: Natural
  }
  deriving (Eq, Show)

-- | The dominion of terminal elements indexed by every natural number.
-- Its total unranking function witnesses cardinality omega.
ellipsis :: Dominion Ellipsis
ellipsis = dominion terminalRank (Just . Terminal) (const ())
