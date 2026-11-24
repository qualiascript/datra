{-# LANGUAGE CPP #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RoleAnnotations #-}
#include "../../../LiquidPlugin.h"
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}

-- | Stable occurrence categories for fixed, instance-defined folios.
module PageElements.Construction
  ( PageElementsConstruction (..)
  , ConstructedPageElementsScope
  , constructPageElements
  ) where

import Data.Proxy (Proxy)
import Data.Kind (Type)
import Folio (Folio)
import PageElements (PageElements, pageElementsFolio)
import qualified PageElements.Internal as Internal (pageElementsWithScope)

-- | A recipe has no runtime configuration. Its instance fixes the complete
-- folio, so repeated construction has the same owner. Runtime folios instead
-- use the generative 'PageElements.pageElements' interface.
class PageElementsConstruction (recipe :: Type) origin final where
  pageElementsRecipe :: Proxy recipe -> Folio origin final

type role ConstructedPageElementsScope nominal nominal nominal
data ConstructedPageElementsScope recipe origin final

-- ALIGN: PE-FIXED-CONSTRUCTION.
-- ALIGN: PE-FIXED-FOLIO.
{-@ opaque-reflect pageElementsRecipe @-}
{-@ constructPageElements :: PageElementsConstruction recipe origin final
      => recipe:Proxy recipe
      -> {category:PageElements (ConstructedPageElementsScope recipe origin final) origin final |
           pageElementsFolio category == pageElementsRecipe recipe} @-}
constructPageElements :: PageElementsConstruction recipe origin final
  => Proxy recipe -> PageElements (ConstructedPageElementsScope recipe origin final) origin final
constructPageElements recipe = Internal.pageElementsWithScope (pageElementsRecipe recipe)
