{-# LANGUAGE RoleAnnotations #-}

-- | Ordered access to the final page of a finite Atlas map.
--
-- An 'EllipsisInsertion' supplies both the absolute final-page indices and
-- the order in which they are requested.  Successful access constructs a
-- fresh two-page chained Atlas map in precisely that order.  Failure means
-- that the insertion was empty, non-finite, or named an index outside the
-- left Atlas's final cardinality.
module MapOperators.AccessOperator
  ( IndexedAtlasMap
  , indexedAtlasMap
  , indexedAtlasAtlas
  , indexedAtlasAtlasMap
  , indexedAtlasChain
  , indexedAtlasDominion
  , indexedAtlasCardinality
  , indexedAtlasValueAt
  , AccessElement
  , accessElementPosition
  , accessElementSource
  , accessElementValue
  , accessOperator
  , (<@>)
  ) where

import AtlasMap (AtlasMap)
import Chain
  ( Chain
  , chain
  , chainIndex
  , chainObjectAt
  , chainOrderType
  )
import ChainedDominionAtlas
  ( ChainedDominionAtlas
  , ChainedDominionAtlasObject
  , chainedDominionAtlas
  , chainedDominionAtlasMap
  )
import Control.Arrow ((&&&))
import Control.Monad ((>=>))
import DatraOrdinal (finiteOrdinal, naturalAtOrdinal)
import Dominion (Dominion, dominion, rank, unrank)
import Ellipsis (terminalRank)
import EllipsisInsertion
  ( EllipsisInsertion
  , applyEllipsisInsertion
  , ellipsisInsertionChain
  )
import Numeric.Natural (Natural)

import qualified Data.Map.Strict as Map

-- | A finite, nonempty value-indexed Atlas map.  The explicit chain is the
-- final page of the underlying two-page chained Atlas.
type role IndexedAtlasMap nominal
data IndexedAtlasMap value = IndexedAtlasMap
  { indexedAtlasCardinality :: Natural
  , indexedAtlasChain :: Chain value
  , indexedAtlasDominion :: Dominion value
  , indexedAtlasAtlas :: ChainedDominionAtlas value
  , indexedAtlasAtlasMap
      :: AtlasMap (ChainedDominionAtlasObject value)
  }

-- | Build a two-page indexed Atlas map from a dense finite dominion.
-- The supplied first value is nonemptiness evidence.
indexedAtlasMap
  :: Natural
  -> value
  -> Dominion value
  -> IndexedAtlasMap value
indexedAtlasMap cardinality first valueDominion =
  IndexedAtlasMap
    { indexedAtlasCardinality = cardinality
    , indexedAtlasChain = valueChain
    , indexedAtlasDominion = valueDominion
    , indexedAtlasAtlas =
        chainedDominionAtlas first valueChain valueDominion
    , indexedAtlasAtlasMap =
        chainedDominionAtlasMap first valueChain valueDominion
    }
  where
    valueChain =
      chain
        (finiteOrdinal cardinality)
        (finiteOrdinal . rank valueDominion)
        (naturalAtOrdinal >=> unrank valueDominion)
        (const ())
        (\_ _ -> ())
        (const ())

-- | Look up a final-page value by its finite page index.
indexedAtlasValueAt
  :: IndexedAtlasMap value
  -> Natural
  -> Maybe value
indexedAtlasValueAt valueAtlas valueRank
  | valueRank < indexedAtlasCardinality valueAtlas =
      unrank (indexedAtlasDominion valueAtlas) valueRank
  | otherwise = Nothing

-- | A selected final-page value together with the insertion source that
-- requested it and its new position in the accessed map.
type role AccessElement representational representational
data AccessElement source value = AccessElement
  { accessElementPosition :: Natural
  , accessElementSource :: source
  , accessElementValue :: value
  }
  deriving (Eq, Show)

-- | Access final-page indices in insertion-chain order.  In particular, the
-- insertion's image need not be monotone, so this operation can reorder the
-- source Atlas's values.
accessOperator
  :: IndexedAtlasMap value
  -> EllipsisInsertion source
  -> Maybe (IndexedAtlasMap (AccessElement source value))
accessOperator valueAtlas insertion = do
  requestedCardinality <-
    naturalAtOrdinal (chainOrderType (ellipsisInsertionChain insertion))
  if requestedCardinality == 0
    then Nothing
    else do
      selected <- collect 0 requestedCardinality
      case selected of
        [] -> Nothing
        first : _ ->
          let selectedByRank = Map.fromList
                (map (accessElementPosition &&& id) selected)
              selectedDominion = dominion
                accessElementPosition
                (`Map.lookup` selectedByRank)
                (const ())
          in Just
              (indexedAtlasMap
                requestedCardinality
                first
                selectedDominion)
  where
    collect position cardinality
      | position == cardinality = Just []
      | otherwise = do
          sourceIndex <-
            chainIndex
              (ellipsisInsertionChain insertion)
              (finiteOrdinal position)
          let source = chainObjectAt sourceIndex
              requestedIndex =
                terminalRank (applyEllipsisInsertion insertion source)
          value <- indexedAtlasValueAt valueAtlas requestedIndex
          remaining <- collect (position + 1) cardinality
          pure (AccessElement position source value : remaining)

infixl 8 <@>

-- | Infix form of 'accessOperator'.
(<@>)
  :: IndexedAtlasMap value
  -> EllipsisInsertion source
  -> Maybe (IndexedAtlasMap (AccessElement source value))
(<@>) = accessOperator
