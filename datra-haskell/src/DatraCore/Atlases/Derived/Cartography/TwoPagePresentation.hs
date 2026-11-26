{-# LANGUAGE CPP #-}
#include "../../../LiquidPlugin.h"
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}
{-@ LIQUID "--higherorder" @-}

-- | Shared occurrence and arrow normalization for two-page presentations.
module TwoPagePresentation
  ( twoPageRegionPosition, twoPageArrowPosition, normalizedArrow ) where

import Folio (folioLength)
import PageElements
  ( PageElements, pageElementsFolio, normalizePageElement, normalizePageElementArrow
  , pageElementTraceValid, pageElementTraceValidNormalize, pageElementSamePagePosition )
import PageElements.Structure
  ( PageElement, PageElementArrow (..), arrowSource, arrowTarget
  , pageElementPage, pageElementPosition, clampPage )

-- ALIGN: CHAINED-TWO-PAGE-REGION.
{-@ twoPageRegionPosition :: category:{PageElements scope origin final |
           folioLength (pageElementsFolio category) == 2}
      -> occurrence:{PageElement scope object | pageElementPage occurrence > 0}
      -> {pageElementPage (normalizePageElement category occurrence) == 1} @-}
twoPageRegionPosition :: PageElements scope origin final -> PageElement scope object -> ()
twoPageRegionPosition category occurrence =
  normalizePageElement category occurrence `seq`
    if pageElementPage occurrence <= 1 then () else ()

-- ALIGN: TWO-PAGE-ARROW-POSITION.
{-@ twoPageArrowPosition :: category:{PageElements scope origin final |
           folioLength (pageElementsFolio category) == 2}
      -> arrow:{PageElementArrow scope source target |
           pageElementTraceValid category (arrowSource arrow)
           && pageElementTraceValid category (arrowTarget arrow)
           && pageElementPage (arrowSource arrow) > 0
           && pageElementPage (arrowTarget arrow) > 0}
      -> {pageElementPosition (arrowSource arrow) == pageElementPosition (arrowTarget arrow)} @-}
twoPageArrowPosition :: PageElements scope origin final -> PageElementArrow scope source target -> ()
twoPageArrowPosition category arrow@(PageElementArrow _ _) =
  twoPageRegionPosition category (arrowSource arrow) `seq`
  twoPageRegionPosition category (arrowTarget arrow) `seq`
  pageElementTraceValidNormalize category (arrowSource arrow) `seq`
  pageElementTraceValidNormalize category (arrowTarget arrow) `seq`
  pageElementSamePagePosition category (normalizePageElementArrow category arrow)

-- ALIGN: CHAINED-ARROW-NORMALIZATION.
{-@ normalizedArrow :: category:PageElements scope origin final
      -> arrow:{PageElementArrow scope source target |
           pageElementTraceValid category (arrowSource arrow)
           && pageElementTraceValid category (arrowTarget arrow)}
      -> {result:PageElementArrow scope source target |
           result == normalizePageElementArrow category arrow
           && pageElementTraceValid category (arrowSource result)
           && pageElementTraceValid category (arrowTarget result)
           && arrowSource result == normalizePageElement category (arrowSource arrow)
           && arrowTarget result == normalizePageElement category (arrowTarget arrow)} @-}
normalizedArrow :: PageElements scope origin final -> PageElementArrow scope source target
  -> PageElementArrow scope source target
normalizedArrow category arrow =
  pageElementTraceValidNormalize category (arrowSource arrow) `seq`
  pageElementTraceValidNormalize category (arrowTarget arrow) `seq`
  normalizePageElementArrow category arrow

