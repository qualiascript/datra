-- | Stable Atlas transversals whose codomain represents 'Ellipsis'.
module EllipsisInsertion
  ( EllipsisInsertion
  , EllipsisInsertionElement
  , ellipsisInsertion
  , ellipsisInsertionTraversal
  , applyEllipsisInsertion
  , ellipsisInsertionPreimage
  , ellipsisInsertionLeftInverse
  , mergeDisjointEllipsisInsertions
  , ellipsisInsertionDominion
  , ellipsisInsertionElementSource
  , ellipsisInsertionElementValue
  ) where

import DomanialInclusion (DominionAtlasObject)
import DomanialInsertion
  ( DomanialInsertion
  , applyInsertion
  , domanialInsertion
  , insertionLeftInverse
  , preimage
  )
import Dominion (Dominion, dominion, unrank)
import Ellipsis
  ( EllipsisTerminal (Terminal)
  , EllipsisAtlasObject
  , ellipsisDominion
  , terminalRank
  )
import RankedDominionAtlas (rankedDominionInsertionTraversal)
import StableAtlasTransversal (StableAtlasTransversal)

-- | An insertion into Ellipsis is represented categorically by a stable Atlas
-- transversal from the one-page atlas of its source dominion to the
-- cardinality-two Ellipsis Atlas map. Its domanial insertion retains the
-- executable presentation from which DatraCore constructs that traversal.
data EllipsisInsertion source = EllipsisInsertion
  { ellipsisInsertionTraversal
      :: StableAtlasTransversal
           (DominionAtlasObject source)
           EllipsisAtlasObject
  , ellipsisInsertionDomanial
      :: DomanialInsertion source EllipsisTerminal
  }

-- | An element of a dominion restricted to the regions selected by an
-- Ellipsis insertion. The source value witnesses membership in its image.
data EllipsisInsertionElement source value = EllipsisInsertionElement
  { ellipsisInsertionElementSource :: source
  , ellipsisInsertionElementValue :: value
  }
  deriving (Eq, Show)

-- | Construct the stable Atlas transversal selected by an injective map of
-- source values to Ellipsis regions.
ellipsisInsertion
  :: (source -> EllipsisTerminal)
  -> (EllipsisTerminal -> Maybe source)
  -> (source -> ())
  -> EllipsisInsertion source
ellipsisInsertion forward backward leftInverse =
  EllipsisInsertion
    { ellipsisInsertionTraversal =
        rankedDominionInsertionTraversal
          ellipsisDominion
          insertion
    , ellipsisInsertionDomanial = insertion
    }
  where
    insertion = domanialInsertion forward backward leftInverse

-- | Apply the executable domanial presentation underlying the traversal.
applyEllipsisInsertion
  :: EllipsisInsertion source
  -> source
  -> EllipsisTerminal
applyEllipsisInsertion insertion =
  applyInsertion (ellipsisInsertionDomanial insertion)

-- | Recover a source value from an Ellipsis terminal when it lies in the
-- traversal's image.
ellipsisInsertionPreimage
  :: EllipsisInsertion source
  -> EllipsisTerminal
  -> Maybe source
ellipsisInsertionPreimage insertion =
  preimage (ellipsisInsertionDomanial insertion)

-- | Invoke the insertion's left-inverse witness.
ellipsisInsertionLeftInverse
  :: EllipsisInsertion source
  -> source
  -> ()
ellipsisInsertionLeftInverse =
  insertionLeftInverse . ellipsisInsertionDomanial

-- | Merge insertions with disjoint images. The disjointness precondition is
-- necessary so that the tagged source remains injective.
mergeDisjointEllipsisInsertions
  :: EllipsisInsertion left
  -> EllipsisInsertion right
  -> EllipsisInsertion (Either left right)
mergeDisjointEllipsisInsertions first second =
  ellipsisInsertion forward backward (const ())
  where
    forward (Left value) = applyEllipsisInsertion first value
    forward (Right value) = applyEllipsisInsertion second value

    backward terminal =
      case ellipsisInsertionPreimage first terminal of
        Just value -> Just (Left value)
        Nothing -> Right <$> ellipsisInsertionPreimage second terminal

-- | Restrict a dominion to the absolute ranks selected by an Ellipsis Atlas
-- transversal. The traversal's image is expected to lie within the input
-- dominion.
ellipsisInsertionDominion
  :: Dominion value
  -> EllipsisInsertion source
  -> Dominion (EllipsisInsertionElement source value)
ellipsisInsertionDominion valueDominion insertion =
  dominion selectedRank selectedAt (const ())
  where
    selectedRank =
      terminalRank
        . applyEllipsisInsertion insertion
        . ellipsisInsertionElementSource

    selectedAt rankValue = do
      source <- ellipsisInsertionPreimage insertion (Terminal rankValue)
      value <- unrank valueDominion rankValue
      pure (EllipsisInsertionElement source value)
