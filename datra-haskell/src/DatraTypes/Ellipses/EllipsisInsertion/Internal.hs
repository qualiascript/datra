-- | Hidden specialization of domanial insertions into 'Ellipsis'.
module EllipsisInsertion.Internal
  ( EllipsisInsertion
  , ellipsisInsertion
  ) where

import DomanialInsertion.Internal
  ( DomanialInsertion
  , domanialInsertion
  )
import Ellipsis.Internal (Ellipsis)

-- | Any domanial insertion whose codomain is the broadest ellipsis dominion.
type EllipsisInsertion source = DomanialInsertion source Ellipsis

-- | Construct an insertion into 'Ellipsis' from its forward map, executable
-- preimage, and left-inverse witness.
ellipsisInsertion
  :: (source -> Ellipsis)
  -> (Ellipsis -> Maybe source)
  -> (source -> ())
  -> EllipsisInsertion source
ellipsisInsertion = domanialInsertion
