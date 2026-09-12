{-# LANGUAGE CPP #-}
{-# LANGUAGE GADTs #-}
#include "../LiquidPlugin.h"
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}

-- | LiquidHaskell-verified folio representation and coherence primitives.
module Folio.LiquidInternal
  ( SingletonOrigin (..)
  , PageOrder (..)
  , pageOrder
  , FolioData (..)
  , folioData
  , appendPageData
  , folioLengthData
  , originPageData
  , originValueData
  , originUniqueData
  , lastPageData
  , identityFolioMap
  , composeFolioMaps
  , folioMapIdentity
  , folioMapComposition
  ) where

import Consolidation.LiquidInternal
import Numeric.Natural (Natural)

{-@ embed Natural as int @-}

-- | The selected origin and the evidence that its carrier is a singleton.
{-@
data SingletonOrigin origin = SingletonOrigin
  { selectedOrigin :: origin
  , singletonOriginUnique :: value:origin ->
      { proof:() | value == selectedOrigin }
  }
@-}
data SingletonOrigin origin = SingletonOrigin
  { selectedOrigin :: origin
  , singletonOriginUnique :: origin -> ()
  }

-- | A proof-carrying ordered pair of indices on the spine.
{-@
data PageOrder = PageOrder
  { pageOrderSource :: Natural
  , pageOrderTarget :: { target:Natural | pageOrderSource <= target }
  }
@-}
data PageOrder = PageOrder
  { pageOrderSource :: Natural
  , pageOrderTarget :: Natural
  }
  deriving (Eq, Show)

-- | Refine two dynamic indices to a spine-order certificate.
pageOrder :: Natural -> Natural -> Maybe PageOrder
pageOrder source target
  | source <= target = Just (PageOrder source target)
  | otherwise = Nothing

-- | A type-aligned, nonempty sequence parameterized by its page container.
-- GHC checks that every coconsolidation joins the carrier of the preceding
-- page to the carrier of the next page.
data FolioData page origin final where
  OriginFolio
    :: Natural
    -> page origin
    -> SingletonOrigin origin
    -> FolioData page origin origin
  SnocPage
    :: Natural
    -> FolioData page origin previous
    -> page next
    -> Coconsolidation previous next
    -> FolioData page origin next

-- | Construct the singleton origin page. LiquidHaskell checks that the
-- supplied witness identifies every origin value with the selected value.
{-@
folioData
  :: page origin
  -> selectedOrigin:origin
  -> (value:origin -> { proof:() | value == selectedOrigin })
  -> FolioData page origin origin
@-}
folioData
  :: page origin
  -> origin
  -> (origin -> ())
  -> FolioData page origin origin
folioData page selected unique =
  OriginFolio 1 page (SingletonOrigin selected unique)

-- | Append a genuine page and its generating coconsolidation.
appendPageData
  :: FolioData page origin previous
  -> page next
  -> Coconsolidation previous next
  -> FolioData page origin next
appendPageData pages = SnocPage (folioLengthData pages + 1) pages

-- | The number of genuine pages.
{-@ reflect folioLengthData @-}
folioLengthData :: FolioData page origin final -> Natural
folioLengthData (OriginFolio count _ _) = count
folioLengthData (SnocPage count _ _ _) = count

-- | The first page.
originPageData :: FolioData page origin final -> page origin
originPageData (OriginFolio _ value _) = value
originPageData (SnocPage _ pages _ _) = originPageData pages

-- | The distinguished value of the singleton origin page.
{-@ reflect originValueData @-}
originValueData :: FolioData page origin final -> origin
originValueData (OriginFolio _ _ witness) = selectedOrigin witness
originValueData (SnocPage _ pages _ _) = originValueData pages

-- | Every value of the origin carrier is its distinguished value.
{-@
originUniqueData
  :: pages:FolioData page origin final
  -> value:origin
  -> { proof:() | value == originValueData pages }
@-}
originUniqueData :: FolioData page origin final -> origin -> ()
originUniqueData (OriginFolio _ _ witness) value =
  singletonOriginUnique witness value
originUniqueData (SnocPage _ pages _ _) value = originUniqueData pages value

-- | The final genuine page.
lastPageData :: FolioData page origin final -> page final
lastPageData (OriginFolio _ value _) = value
lastPageData (SnocPage _ _ value _) = value

-- | The identity map used for every identity interval in a folio.
{-@ reflect identityFolioMap @-}
identityFolioMap :: Coconsolidation page page
identityFolioMap = op identityConsolidation

-- | Identity intervals transport every page value to itself.
{-@
folioMapIdentity
  :: value:page ->
     { proof:() |
       applyConsolidation (unop identityFolioMap) value == value }
@-}
folioMapIdentity :: page -> ()
folioMapIdentity = coconsolidationIdentity

-- | The composition operation used to derive every non-adjacent folio map.
{-@ reflect composeFolioMaps @-}
composeFolioMaps
  :: Coconsolidation middle target
  -> Coconsolidation source middle
  -> Coconsolidation source target
composeFolioMaps = composeCoconsolidations

-- | Composed intervals transport exactly by the two constituent maps.
{-@
folioMapComposition
  :: second:Coconsolidation middle target
  -> first:Coconsolidation source middle
  -> value:target
  -> { proof:() |
       applyConsolidation (unop (composeFolioMaps second first)) value
         == applyConsolidation (unop first)
              (applyConsolidation (unop second) value) }
@-}
folioMapComposition
  :: Coconsolidation middle target
  -> Coconsolidation source middle
  -> target
  -> ()
folioMapComposition = coconsolidationComposition
