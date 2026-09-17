-- | Stable Atlas transversals into any finite-rank 'SuperEllipsis'.
module SuperEllipsisInsertion
  ( SuperEllipsisInsertion
  , SuperEllipsisInsertionMap (..)
  , SuperEllipsisAtlasMap
  , SuperEllipsisInsertionElement
  , superEllipsisInsertion
  , superEllipsisInsertionMap
  , fullSuperEllipsisInsertion
  , superEllipsisInsertionRank
  , superEllipsisInsertionFirst
  , superEllipsisInsertionChain
  , superEllipsisInsertionTraversal
  , applySuperEllipsisInsertion
  , superEllipsisInsertionPosition
  , superEllipsisInsertionPreimage
  , superEllipsisInsertionLeftInverse
  , mergeDisjointSuperEllipsisInsertions
  , superEllipsisInsertionSourceDominion
  , superEllipsisInsertionDominion
  , superEllipsisInsertionElementSource
  , superEllipsisInsertionElementValue
  ) where

import Chain (Chain, sumChains)
import ChainedDominionAtlas (chainedDominionInsertionTraversal)
import DatraOrdinal (Ordinal)
import DomanialInclusion (DominionAtlasObject)
import DomanialInsertion
  ( DomanialInsertion
  , applyInsertion
  , domanialInsertion
  , insertionLeftInverse
  , preimage
  )
import Dominion (Dominion, dominion, rank, unrank)
import MapOperators.IndexedAtlasMap
  ( IndexedAtlasMap
  , indexedAtlasMapFromChain
  )
import StableAtlasTransversal (StableAtlasTransversal)
import StableConfederalData
  ( EmptyMapValues
  , StableConfederalData
  , emptyMap
  )
import SuperEllipsis
  ( SuperEllipsisAtlasObject
  , SuperEllipsisRank
  , SuperEllipsisTerminal
  , superEllipsisChain
  , superEllipsisDominion
  , superEllipsisTerminalPosition
  , superEllipsisZeroTerminal
  )

-- | An ordered insertion into the ordinal positions of one super ellipsis.
data SuperEllipsisInsertion target source = SuperEllipsisInsertion
  { superEllipsisInsertionRank :: SuperEllipsisRank target
  , superEllipsisInsertionFirst :: Maybe source
  , superEllipsisInsertionChain :: Chain source
  , superEllipsisInsertionTraversal
      :: StableAtlasTransversal
           (DominionAtlasObject source)
           (SuperEllipsisAtlasObject target)
  , superEllipsisInsertionDomanial
      :: DomanialInsertion source (SuperEllipsisTerminal target)
  }

-- | The Atlas map presented by an insertion.  Empty insertions present the
-- empty map; nonempty insertions retain their source values and chain order in
-- an indexed chained Atlas map.
data SuperEllipsisInsertionMap source
  = EmptySuperEllipsisInsertionMap
      (StableConfederalData EmptyMapValues)
  | IndexedSuperEllipsisInsertionMap (IndexedAtlasMap source)

-- | General name for the Atlas map underlying an insertion or insertion-like
-- value.
type SuperEllipsisAtlasMap = SuperEllipsisInsertionMap

-- | A value restricted to positions selected by an insertion.
data SuperEllipsisInsertionElement target source value =
  SuperEllipsisInsertionElement
    { superEllipsisInsertionElementSource :: source
    , superEllipsisInsertionElementValue :: value
    }
  deriving (Eq, Show)

-- | Construct an insertion from mutually inverse certified-terminal maps.
-- Ordinals are refined before this boundary, so applying an insertion is
-- total and cannot fail at runtime.
superEllipsisInsertion
  :: SuperEllipsisRank target
  -> Maybe source
  -> Chain source
  -> (source -> SuperEllipsisTerminal target)
  -> (SuperEllipsisTerminal target -> Maybe source)
  -> (source -> ())
  -> SuperEllipsisInsertion target source
superEllipsisInsertion
    valueRank first sourceChain forward backward leftInverse =
  SuperEllipsisInsertion
    { superEllipsisInsertionRank = valueRank
    , superEllipsisInsertionFirst = first
    , superEllipsisInsertionChain = sourceChain
    , superEllipsisInsertionTraversal =
        chainedDominionInsertionTraversal
          zero
          (superEllipsisChain valueRank)
          targetDominion
          insertion
    , superEllipsisInsertionDomanial = insertion
    }
  where
    targetDominion = superEllipsisDominion valueRank
    insertion = domanialInsertion forward backward leftInverse
    zero = superEllipsisZeroTerminal valueRank

-- | Convert an insertion to the Atlas map presented by its ordered source
-- chain.  Unlike indexed maps, the empty map needs no first-element witness.
superEllipsisInsertionMap
  :: SuperEllipsisInsertion target source
  -> SuperEllipsisAtlasMap source
superEllipsisInsertionMap insertion =
  case superEllipsisInsertionFirst insertion of
    Nothing -> EmptySuperEllipsisInsertionMap emptyMap
    Just first ->
      IndexedSuperEllipsisInsertionMap
        (indexedAtlasMapFromChain
          first
          (superEllipsisInsertionChain insertion)
          (superEllipsisInsertionSourceDominion insertion))

-- | The identity insertion of every position in a super-ellipsis target.
-- This is the insertion underlying the corresponding formulation and may
-- therefore have a transfinite order type.
fullSuperEllipsisInsertion
  :: SuperEllipsisRank target
  -> SuperEllipsisInsertion target (SuperEllipsisTerminal target)
fullSuperEllipsisInsertion valueRank =
  superEllipsisInsertion
    valueRank
    (Just (superEllipsisZeroTerminal valueRank))
    (superEllipsisChain valueRank)
    id
    Just
    (const ())

applySuperEllipsisInsertion
  :: SuperEllipsisInsertion target source
  -> source
  -> SuperEllipsisTerminal target
applySuperEllipsisInsertion insertion =
  applyInsertion (superEllipsisInsertionDomanial insertion)

-- | Read the absolute ordinal position selected by a source value.
superEllipsisInsertionPosition
  :: SuperEllipsisInsertion target source
  -> source
  -> Ordinal
superEllipsisInsertionPosition insertion =
  superEllipsisTerminalPosition . applySuperEllipsisInsertion insertion

superEllipsisInsertionPreimage
  :: SuperEllipsisInsertion target source
  -> SuperEllipsisTerminal target
  -> Maybe source
superEllipsisInsertionPreimage insertion =
  preimage (superEllipsisInsertionDomanial insertion)

superEllipsisInsertionLeftInverse
  :: SuperEllipsisInsertion target source
  -> source
  -> ()
superEllipsisInsertionLeftInverse =
  insertionLeftInverse . superEllipsisInsertionDomanial

mergeDisjointSuperEllipsisInsertions
  :: SuperEllipsisInsertion target left
  -> SuperEllipsisInsertion target right
  -> SuperEllipsisInsertion target (Either left right)
mergeDisjointSuperEllipsisInsertions first second =
  superEllipsisInsertion
    (superEllipsisInsertionRank first)
    (case superEllipsisInsertionFirst first of
      Just value -> Just (Left value)
      Nothing -> Right <$> superEllipsisInsertionFirst second)
    (sumChains
      (superEllipsisInsertionChain first)
      (superEllipsisInsertionChain second))
    forward
    backward
    (const ())
  where
    forward (Left value) = applySuperEllipsisInsertion first value
    forward (Right value) = applySuperEllipsisInsertion second value

    backward terminal =
      case superEllipsisInsertionPreimage first terminal of
        Just value -> Just (Left value)
        Nothing -> Right <$> superEllipsisInsertionPreimage second terminal

-- | The insertion source as a dominion, ranked through its absolute target
-- position.
superEllipsisInsertionSourceDominion
  :: SuperEllipsisInsertion target source
  -> Dominion source
superEllipsisInsertionSourceDominion insertion =
  dominion sourceRank sourceAt (const ())
  where
    targetDominion =
      superEllipsisDominion (superEllipsisInsertionRank insertion)
    sourceRank =
      rank targetDominion . applySuperEllipsisInsertion insertion
    sourceAt valueRank = do
      terminal <- unrank targetDominion valueRank
      superEllipsisInsertionPreimage insertion terminal

-- | Restrict a dominion indexed by the canonical natural enumeration of the
-- target rank to the insertion image.
superEllipsisInsertionDominion
  :: Dominion value
  -> SuperEllipsisInsertion target source
  -> Dominion (SuperEllipsisInsertionElement target source value)
superEllipsisInsertionDominion valueDominion insertion =
  dominion selectedRank selectedAt (const ())
  where
    targetDominion =
      superEllipsisDominion (superEllipsisInsertionRank insertion)

    selectedRank =
      rank targetDominion
        . applySuperEllipsisInsertion insertion
        . superEllipsisInsertionElementSource

    selectedAt rankValue = do
      terminal <- unrank targetDominion rankValue
      source <- superEllipsisInsertionPreimage insertion terminal
      value <- unrank valueDominion rankValue
      pure (SuperEllipsisInsertionElement source value)
