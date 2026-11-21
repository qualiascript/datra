{-# LANGUAGE CPP #-}
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
import Folio (Folio)
import PageElements (PageElements)
import qualified PageElements.Internal as Internal (pageElementsWithScope)

-- | A recipe has no runtime configuration. Its instance fixes the complete
-- folio, so repeated construction has the same owner. Runtime folios instead
-- use the generative 'PageElements.pageElements' interface.
class PageElementsConstruction recipe origin final where
  pageElementsRecipe :: Proxy recipe -> Folio origin final

type role ConstructedPageElementsScope nominal nominal nominal
data ConstructedPageElementsScope recipe origin final

-- ALIGN: PE-FIXED-CONSTRUCTION.
constructPageElements :: PageElementsConstruction recipe origin final
  => Proxy recipe -> PageElements (ConstructedPageElementsScope recipe origin final) origin final
constructPageElements recipe = Internal.pageElementsWithScope (pageElementsRecipe recipe)
