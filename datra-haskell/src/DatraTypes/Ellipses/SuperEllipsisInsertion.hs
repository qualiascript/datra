{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeFamilies #-}

-- | Stable Atlas transversals into any finite-rank 'SuperEllipsis'.
module SuperEllipsisInsertion
  ( SuperEllipsisInsertion
  , SuperEllipsisInsertionElement
  , HasSuperEllipsisInsertion
      ( InsertionTarget
      , InsertionSource
      , superEllipsisInsertionOf
      )
  , superEllipsisInsertion
  , superEllipsisInsertionOrderedMap
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

import Chain
  ( Chain
  , chainIndex
  , chainObjectAt
  , sumChains
  )
import ChainedDominionAtlas (chainedDominionInsertionTraversal)
import DatraOrdinal (Ordinal, finiteOrdinal)
import Data.Kind (Type)
import DomanialInclusion (DominionAtlasObject)
import DomanialInsertion
  ( DomanialInsertion
  , applyInsertion
  , domanialInsertion
  , insertionLeftInverse
  , preimage
  )
import Dominion (Dominion, dominion, rank, unrank)
import MapOperators.IndexedAtlasMap (indexedAtlasMapFromChain)
import MapOperators.OrderedAtlasMap
  ( HasOrderedAtlasMap (..)
  , OrderedAtlasMap (..)
  )
import StableAtlasTransversal (StableAtlasTransversal)
import StableConfederalData (StableConfederalData)
import SuperEllipsis
  ( SuperEllipsisAtlasObject
  , SuperEllipsisRank
  , SuperEllipsisTerminal
  , SuperEllipsisTarget
  , superEllipsisChain
  , superEllipsisDominion
  , superEllipsisTerminalPosition
  , superEllipsisTargetRank
  , superEllipsisZeroTerminal
  )

-- | An ordered insertion into the ordinal positions of one super ellipsis.
data SuperEllipsisInsertion (target :: Type) source = SuperEllipsisInsertion
  { superEllipsisInsertionRank :: SuperEllipsisRank target
  , superEllipsisInsertionChain :: Chain source
  , superEllipsisInsertionTraversal
      :: StableAtlasTransversal
           (DominionAtlasObject source)
           (SuperEllipsisAtlasObject target)
  , superEllipsisInsertionDomanial
      :: DomanialInsertion source (SuperEllipsisTerminal target)
  }

-- | A value restricted to positions selected by an insertion.
data SuperEllipsisInsertionElement (target :: Type) source value =
  SuperEllipsisInsertionElement
    { superEllipsisInsertionElementSource :: source
    , superEllipsisInsertionElementValue :: value
    }
  deriving (Eq, Show)

-- | A value with an ordered, injective presentation into one super ellipsis.
class HasSuperEllipsisInsertion operand where
  type InsertionTarget operand :: Type
  type InsertionSource operand :: Type
  superEllipsisInsertionOf
    :: operand
    -> SuperEllipsisInsertion
         (InsertionTarget operand)
         (InsertionSource operand)

instance HasSuperEllipsisInsertion (SuperEllipsisInsertion target source) where
  type InsertionTarget (SuperEllipsisInsertion target source) = target
  type InsertionSource (SuperEllipsisInsertion target source) = source
  superEllipsisInsertionOf = id

instance SuperEllipsisTarget target =>
    HasSuperEllipsisInsertion (StableConfederalData target) where
  type InsertionTarget (StableConfederalData target) = target
  type InsertionSource (StableConfederalData target) =
    SuperEllipsisTerminal target
  superEllipsisInsertionOf _ =
    fullSuperEllipsisInsertion superEllipsisTargetRank

-- | Construct an insertion from mutually inverse certified-terminal maps.
-- Ordinals are refined before this boundary, so applying an insertion is
-- total and cannot fail at runtime.
superEllipsisInsertion
  :: SuperEllipsisRank target
  -> Chain source
  -> (source -> SuperEllipsisTerminal target)
  -> (SuperEllipsisTerminal target -> Maybe source)
  -> (source -> ())
  -> SuperEllipsisInsertion target source
superEllipsisInsertion
    valueRank sourceChain forward backward leftInverse =
  SuperEllipsisInsertion
    { superEllipsisInsertionRank = valueRank
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

-- | The first source value, derived from the chain so emptiness and the
-- nonempty witness cannot disagree.
superEllipsisInsertionFirst
  :: SuperEllipsisInsertion target source
  -> Maybe source
superEllipsisInsertionFirst insertion =
  chainObjectAt
    <$> chainIndex
      (superEllipsisInsertionChain insertion)
      (finiteOrdinal 0)

-- | Convert an insertion to the Atlas map presented by its ordered source
-- chain.  Unlike indexed maps, the empty map needs no first-element witness.
superEllipsisInsertionOrderedMap
  :: SuperEllipsisInsertion target source
  -> OrderedAtlasMap source
superEllipsisInsertionOrderedMap insertion =
  case superEllipsisInsertionFirst insertion of
    Nothing -> EmptyOrderedAtlasMap
    Just first ->
      NonEmptyOrderedAtlasMap
        (indexedAtlasMapFromChain
          first
          (superEllipsisInsertionChain insertion)
          (superEllipsisInsertionSourceDominion insertion))

instance HasOrderedAtlasMap (SuperEllipsisInsertion target source) where
  type OrderedAtlasElement (SuperEllipsisInsertion target source) = source
  orderedAtlasMap = superEllipsisInsertionOrderedMap

-- | The identity insertion of every position in a super-ellipsis target.
-- This is the insertion underlying the corresponding formulation and may
-- therefore have a transfinite order type.
fullSuperEllipsisInsertion
  :: SuperEllipsisRank target
  -> SuperEllipsisInsertion target (SuperEllipsisTerminal target)
fullSuperEllipsisInsertion valueRank =
  superEllipsisInsertion
    valueRank
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
