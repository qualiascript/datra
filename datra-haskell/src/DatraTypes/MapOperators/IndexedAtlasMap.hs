-- | Atlas maps whose final page is indexed by an explicit ordinal chain.
module MapOperators.IndexedAtlasMap
  ( IndexedAtlasMap
  , indexedAtlasMap
  , indexedAtlasMapFromChain
  , indexedAtlasAtlas
  , indexedAtlasAtlasMap
  , indexedAtlasChain
  , indexedAtlasDominion
  , indexedAtlasCardinality
  , indexedAtlasValueAt
  , indexedAtlasValueAtOrdinal
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
import Control.Monad ((>=>))
import DatraOrdinal (Ordinal, finiteOrdinal, naturalAtOrdinal)
import Dominion (Dominion, rank, unrank)
import Numeric.Natural (Natural)

-- | A nonempty value-indexed Atlas map whose final chain may have any order
-- type below omega to the omega.
data IndexedAtlasMap value = IndexedAtlasMap
  { indexedAtlasCardinality :: Ordinal
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
  indexedAtlasMapFromChain first valueChain valueDominion
  where
    valueChain =
      chain
        (finiteOrdinal cardinality)
        (finiteOrdinal . rank valueDominion)
        (naturalAtOrdinal >=> unrank valueDominion)
        (const ())
        (\_ _ -> ())
        (const ())

-- | Build an indexed Atlas map from an arbitrary nonempty ordinal chain and
-- a countable dominion of the same values.
indexedAtlasMapFromChain
  :: value
  -> Chain value
  -> Dominion value
  -> IndexedAtlasMap value
indexedAtlasMapFromChain first valueChain valueDominion =
  IndexedAtlasMap
    { indexedAtlasCardinality = chainOrderType valueChain
    , indexedAtlasChain = valueChain
    , indexedAtlasDominion = valueDominion
    , indexedAtlasAtlas =
        chainedDominionAtlas first valueChain valueDominion
    , indexedAtlasAtlasMap =
        chainedDominionAtlasMap first valueChain valueDominion
    }

-- | Look up a final-page value by its finite page index.
indexedAtlasValueAt
  :: IndexedAtlasMap value
  -> Natural
  -> Maybe value
indexedAtlasValueAt valueAtlas =
  indexedAtlasValueAtOrdinal valueAtlas . finiteOrdinal

-- | Look up a final-page value by an arbitrary ordinal page index.
indexedAtlasValueAtOrdinal
  :: IndexedAtlasMap value
  -> Ordinal
  -> Maybe value
indexedAtlasValueAtOrdinal valueAtlas position =
  chainObjectAt <$> chainIndex (indexedAtlasChain valueAtlas) position
