{-# LANGUAGE CPP #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE RankNTypes #-}
#include "../../../../LiquidPlugin.h"
{-@ LIQUID "--higherorder" @-}

-- | Hidden implementation of the canonical empty Atlas.
module EmptyAtlas.Internal
  ( EmptyAtlasDatum
  , emptyAtlas
  ) where

import Atlas (Atlas, atlas, atlasDataAction)
import Chain.Singleton (singletonChain)
import Data.Kind (Type)
import Data.Void (Void, absurd)
import DomanialInsertion (DomanialInsertion, domanialInsertion)
import Dominion (Dominion, dominion)
import Folio (singletonFolio)
import PageElements (PageElement, PageElementArrow)
import qualified Pagination

-- | The empty Atlas's cell-indexed carrier contains an impossible Void witness.
data EmptyAtlasDatum (object :: Type) = EmptyAtlasDatum Void

-- | Introduce the canonical Atlas whose only page has no data.
-- ALIGN: EMPTY-ATLAS-CONSTRUCTOR.
-- ALIGN: EMPTY-ATLAS-UNRANK.
-- ALIGN: EMPTY-ATLAS-PREIMAGE.
-- ALIGN: EMPTY-ATLAS-INTERPRETATION.
-- ALIGN: EMPTY-ATLAS-STABLE-INTERPRETATION.
emptyAtlas
  :: (forall atlasScope paginationScope.
       Atlas atlasScope paginationScope EmptyAtlasDatum () ()
       -> result)
  -> result
emptyAtlas useAtlas =
  Pagination.pagination (singletonFolio singletonChain) $ \valuePagination ->
    atlas
      valuePagination
      (atlasDataAction (Pagination.paginationPageElements valuePagination) emptyDominionAt emptyDataMap)
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

-- ALIGN: EMPTY-ATLAS-NO-DATA.
absurdEmptyDatum :: EmptyAtlasDatum object -> result
absurdEmptyDatum (EmptyAtlasDatum impossible) = absurd impossible
