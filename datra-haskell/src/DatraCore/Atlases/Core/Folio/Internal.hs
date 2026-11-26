{-# LANGUAGE CPP #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}

#include "../../../LiquidPlugin.h"
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}
{-@ LIQUID "--higherorder" @-}

-- | Hidden representation of folios.
module Folio.Internal
  ( Folio
  , PageOrder (..)
  , folio
  , singletonFolio
  , appendPage
  , folioLength
  , originChain
  , originValue
  , originUnique
  , folioMapIdentity
  , folioMapComposition
  , folioOriginToFinal
  , lastChain
  , paddedIndex
  , pageOrder
  , withPageAt
  , withFolioMap
  , withPageDataAt
  ) where

import Chain (Chain)
import Chain.Order (chainPrecedes)
import Consolidation.Core (Coconsolidation, unop)
import Consolidation.Ordered
  ( OrderedConsolidation, orderedSource, orderedTarget, orderedOpposite
  , orderedConsolidation, identityOrderedConsolidation, composeOrderedConsolidations )
import Folio.Presentation
  ( FolioData (..)
  , FolioStep (..)
  , PageOrder (..)
  , appendPageData
  , folioData
  , folioLengthData
  , folioMapComposition
  , folioMapIdentity
  , lastPageData
  , stepSource
  , originPageData
  , originUniqueData
  , originValueData
  , pageOrder
  )
import Numeric.Natural (Natural)

{-@ embed Natural as int @-}
{-@ invariant {value:Natural | value >= 0} @-}

-- | Datra folios retain certified maps between their actual page chains.
type Folio origin final = FolioData origin final

{-@ folio :: Chain origin -> selected:origin
      -> (value:origin -> {value == selected}) -> Folio origin origin @-}
folio
  :: Chain origin
  -> origin
  -> (origin -> ())
  -> Folio origin origin
folio = folioData

singletonFolio :: Chain () -> Folio () ()
singletonFolio origin = folio origin () (\() -> ())

{-@ appendPage :: pages:Folio origin previous -> next:Chain next
      -> Coconsolidation
           <{\earlier later -> chainPrecedes (lastChain pages) earlier later},
            {\earlier later -> chainPrecedes next earlier later}> previous next
      -> Folio origin next @-}
appendPage
  :: Folio origin previous
  -> Chain next
  -> Coconsolidation previous next
  -> Folio origin next
appendPage pages next transition =
  appendPageData pages next (orderedConsolidation next (lastChain pages) (unop transition))

{-@ reflect folioLength @-}
{-@ folioLength :: Folio origin final -> {n:Natural | n > 0} @-}
folioLength :: Folio origin final -> Natural
folioLength = folioLengthData

{-@ reflect originChain @-}
originChain :: Folio origin final -> Chain origin
originChain = originPageData

{-@ reflect originValue @-}
originValue :: Folio origin final -> origin
originValue = originValueData

{-@ originUnique :: pages:Folio origin final -> value:origin -> {value == originValue pages} @-}
originUnique :: Folio origin final -> origin -> ()
originUnique = originUniqueData

{-@ reflect lastChain @-}
lastChain :: Folio origin final -> Chain final
lastChain = lastPageData

-- | Compose every generating page map into the canonical coconsolidation
-- from the origin page to the final genuine page.
{-@ folioOriginToFinal :: pages:Folio origin final
      -> Coconsolidation
           <{\earlier later -> chainPrecedes (originChain pages) earlier later},
            {\earlier later -> chainPrecedes (lastChain pages) earlier later}> origin final @-}
folioOriginToFinal
  :: Folio origin final
  -> Coconsolidation origin final
folioOriginToFinal pages = orderedOpposite (folioOriginMap pages)

{-@ folioOriginMap :: pages:Folio origin final
      -> {mapping:OrderedConsolidation final origin |
           orderedSource mapping == lastChain pages && orderedTarget mapping == originChain pages} @-}
folioOriginMap :: Folio origin final -> OrderedConsolidation final origin
folioOriginMap (OriginFolio _ page _) = identityOrderedConsolidation page
folioOriginMap (SnocPage step@(FolioStep _ previous transition)) =
  stepSource step `seq` composeOrderedConsolidations (folioOriginMap previous) transition

-- | Clamp a spine index to the final genuine page.
paddedIndex :: Folio origin final -> Natural -> Natural
paddedIndex pages index = min index (folioLength pages - 1)

-- | Eliminate the existential carrier of a page on the infinite spine.  Every
-- index after the finite presentation denotes its final page.
withPageAt
  :: Folio origin final
  -> Natural
  -> (forall page. Chain page -> result)
  -> result
withPageAt pages index usePage =
  withPageDataAt pages index $ \prefix _ ->
    usePage (lastChain prefix)

-- | Eliminate the page carriers and coherent coconsolidation for an ordered
-- interval on the infinite spine.  The 'PageOrder' argument certifies that the
-- source index is no later than the target; both indices are automatically
-- padded past the finite presentation.
-- ALIGN: FOLIO-SEMANTIC-INTERVAL.
{-@ withFolioMap :: Folio origin final -> PageOrder
      -> (forall source target. sourceChain:Chain source -> targetChain:Chain target
           -> {mapping:OrderedConsolidation target source |
                orderedSource mapping == targetChain && orderedTarget mapping == sourceChain}
           -> result)
      -> result @-}
withFolioMap
  :: Folio origin final
  -> PageOrder
  -> (forall source target.
        Chain source
        -> Chain target
        -> OrderedConsolidation target source
        -> result)
  -> result
withFolioMap pages (PageOrder sourceIndex targetIndex) useMap =
  withPageDataAt pages targetIndex $ \targetPrefix _ ->
    mapFromIndex targetPrefix (paddedIndex pages sourceIndex) $ \sourcePage mapToTarget ->
      useMap sourcePage (lastChain targetPrefix) mapToTarget

-- | Internal eliminator retaining the typed prefix behind a padded page.  The
-- natural supplied to the callback counts how many repeated final pages occur
-- after that prefix.
{-@ withPageDataAt
      :: pages:Folio origin final -> index:Natural
      -> (forall page. prefix:{Folio origin page |
            originPageData prefix == originPageData pages
            && originValueData prefix == originValueData pages
            && folioLengthData prefix == (if index + 1 < folioLengthData pages then index + 1 else folioLengthData pages)}
          -> padding:{Natural | padding + folioLengthData prefix == index + 1}
          -> result)
      -> result @-}
withPageDataAt
  :: Folio origin final
  -> Natural
  -> (forall page. Folio origin page -> Natural -> result)
  -> result
withPageDataAt pages@(OriginFolio {}) index usePage =
  usePage pages index
withPageDataAt pages@(SnocPage (FolioStep _ previous _)) index usePage
  | index >= folioLength previous =
      usePage pages (index - folioLength previous)
  | otherwise = withPageDataAt previous index usePage

-- ALIGN: FOLIO-INTERVAL-IDENTITY.
-- ALIGN: FOLIO-INTERVAL-COMPOSITION.
{-@ mapFromIndex :: pages:Folio origin target -> Natural
      -> (forall source. sourceChain:Chain source
           -> {mapping:OrderedConsolidation target source |
                orderedSource mapping == lastChain pages && orderedTarget mapping == sourceChain}
           -> result)
      -> result @-}
mapFromIndex
  :: Folio origin target
  -> Natural
  -> (forall source. Chain source -> OrderedConsolidation target source -> result)
  -> result
mapFromIndex pages@(OriginFolio {}) _ useMap =
  useMap (lastChain pages) (identityOrderedConsolidation (lastChain pages))
mapFromIndex (SnocPage step@(FolioStep _ previous transition)) sourceIndex useMap
  | sourceIndex >= folioLength previous =
      useMap (stepSource step) (identityOrderedConsolidation (stepSource step))
  | otherwise =
      stepSource step `seq` mapFromIndex previous sourceIndex (\sourcePage sourceToPrevious ->
        useMap sourcePage (composeOrderedConsolidations sourceToPrevious transition))
