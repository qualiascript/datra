{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}

-- | Atlas maps whose final page is indexed by an explicit ordinal chain.
module MapOperators.IndexedAtlasMap
  ( IndexedAtlasMap
  , indexedAtlasMap
  , indexedAtlasMapFromChain
  , withIndexedAtlas
  , indexedAtlasChain
  , indexedAtlasDominion
  , indexedAtlasCardinality
  , indexedAtlasValueAt
  , indexedAtlasValueAtOrdinal
  ) where


import Chain
  ( Chain
  , chain
  , chainIndex
  , chainObjectAt
  , chainOrderType
  )
import ChainedDominionAtlas
  ( ChainedDominionAtlas
  , withChainedDominionAtlas
  )
import Control.Monad ((>=>))
import DatraOrdinal (Ordinal, finiteOrdinal, naturalAtOrdinal)
import Dominion (Dominion, rank, unrank)
import Numeric.Natural (Natural)

-- | A nonempty value-indexed Atlas map whose final chain may have any order
-- type below omega to the omega.
data IndexedAtlasMap value where
  IndexedAtlasMap :: Ordinal -> Chain value -> Dominion value
    -> ChainedDominionAtlas owner scope value -> IndexedAtlasMap value

indexedAtlasCardinality :: IndexedAtlasMap value -> Ordinal
indexedAtlasCardinality (IndexedAtlasMap cardinality _ _ _) = cardinality

indexedAtlasChain :: IndexedAtlasMap value -> Chain value
indexedAtlasChain (IndexedAtlasMap _ valueChain _ _) = valueChain

indexedAtlasDominion :: IndexedAtlasMap value -> Dominion value
indexedAtlasDominion (IndexedAtlasMap _ _ valueDominion _) = valueDominion

-- | All observations in the callback share the stored construction's owners.
withIndexedAtlas :: IndexedAtlasMap value
  -> (forall owner scope. ChainedDominionAtlas owner scope value -> result) -> result
withIndexedAtlas (IndexedAtlasMap _ _ _ owner) useOwner = useOwner owner

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
  withChainedDominionAtlas first valueChain valueDominion $
    IndexedAtlasMap (chainOrderType valueChain) valueChain valueDominion

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
