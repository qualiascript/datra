-- | Hidden specialization of domanial insertions into 'Ellipsis'.
module EllipsisInsertion.Internal
  ( EllipsisInsertion
  , EllipsisInsertionElement (..)
  , ellipsisInsertion
  , mergeDisjointEllipsisInsertions
  , ellipsisInsertionDominion
  ) where

import DomanialInsertion.Internal
  ( DomanialInsertion
  , applyInsertion
  , domanialInsertion
  , preimage
  )
import Dominion.Internal (Dominion, dominion, unrank)
import Ellipsis.Internal (Ellipsis (Terminal), terminalRank)

-- | Any domanial insertion whose codomain is the broadest ellipsis dominion.
type EllipsisInsertion source = DomanialInsertion source Ellipsis

-- | An element of a dominion restricted to the ranks in an ellipsis
-- insertion. The source value witnesses membership in the insertion image.
data EllipsisInsertionElement source value = EllipsisInsertionElement
  { ellipsisInsertionElementSource :: source
  , ellipsisInsertionElementValue :: value
  }
  deriving (Eq, Show)

-- | Construct an insertion into 'Ellipsis' from its forward map, executable
-- preimage, and left-inverse witness.
ellipsisInsertion
  :: (source -> Ellipsis)
  -> (Ellipsis -> Maybe source)
  -> (source -> ())
  -> EllipsisInsertion source
ellipsisInsertion = domanialInsertion

-- | Merge insertions with disjoint images. The disjointness precondition is
-- necessary so that the tagged source remains injective.
mergeDisjointEllipsisInsertions
  :: EllipsisInsertion left
  -> EllipsisInsertion right
  -> EllipsisInsertion (Either left right)
mergeDisjointEllipsisInsertions first second =
  ellipsisInsertion forward backward (const ())
  where
    forward (Left value) = applyInsertion first value
    forward (Right value) = applyInsertion second value

    backward terminal =
      case preimage first terminal of
        Just value -> Just (Left value)
        Nothing -> Right <$> preimage second terminal

-- | Restrict a dominion to the absolute ranks selected by an ellipsis
-- insertion. The insertion's image is expected to lie within the input
-- dominion; in particular, its highest rank must be present there.
ellipsisInsertionDominion
  :: Dominion value
  -> EllipsisInsertion source
  -> Dominion (EllipsisInsertionElement source value)
ellipsisInsertionDominion valueDominion insertion =
  dominion selectedRank selectedAt (const ())
  where
    selectedRank =
      terminalRank
        . applyInsertion insertion
        . ellipsisInsertionElementSource

    selectedAt rankValue = do
      source <- preimage insertion (Terminal rankValue)
      value <- unrank valueDominion rankValue
      pure (EllipsisInsertionElement source value)
