{-# LANGUAGE EmptyCase #-}
{-# LANGUAGE RankNTypes #-}

-- | Hidden implementation of the canonical empty Atlas.
module EmptyAtlas.Internal
  ( EmptyAtlasDatum
  , emptyAtlas
  ) where

import Atlas (Atlas, atlas, atlasDataAction)
import Chain (Chain, chain)
import DatraOrdinal (finiteOrdinal)
import DomanialInsertion (DomanialInsertion, domanialInsertion)
import Dominion (Dominion, dominion)
import Folio (singletonFolio)
import PageElements (PageElement, PageElementArrow)
import qualified Pagination

unitChain :: Chain ()
unitChain =
  chain
    (finiteOrdinal 1)
    (const (finiteOrdinal 0))
    (\position ->
      if position == finiteOrdinal 0 then Just () else Nothing)
    (const ())
    (\_ _ -> ())
    (const ())

-- | The uninhabited data family of the empty Atlas.
data EmptyAtlasDatum object

-- | Introduce the canonical Atlas whose only page has no data.
emptyAtlas
  :: (forall atlasScope paginationScope.
       Atlas atlasScope paginationScope EmptyAtlasDatum () ()
       -> result)
  -> result
emptyAtlas useAtlas =
  Pagination.pagination (singletonFolio unitChain) $ \valuePagination ->
    atlas
      valuePagination
      (atlasDataAction emptyDominionAt emptyDataMap)
      (\_ impossible -> absurdEmptyDatum impossible)
      (\_ _ _ impossible -> absurdEmptyDatum impossible)
      (\_ _ _ impossible -> absurdEmptyDatum impossible)
      (\_ _ _ _ _ impossible _ -> absurdEmptyDatum impossible)
      useAtlas
  where
    emptyDominionAt
      :: PageElement scope object
      -> Dominion (EmptyAtlasDatum object)
    emptyDominionAt _ =
      dominion absurdEmptyDatum (const Nothing) absurdEmptyDatum

    emptyDataMap
      :: PageElementArrow scope source target
      -> DomanialInsertion
           (EmptyAtlasDatum source)
           (EmptyAtlasDatum target)
    emptyDataMap _ =
      domanialInsertion
        absurdEmptyDatum
        (const Nothing)
        absurdEmptyDatum

absurdEmptyDatum :: EmptyAtlasDatum object -> result
absurdEmptyDatum impossible = case impossible of {}
