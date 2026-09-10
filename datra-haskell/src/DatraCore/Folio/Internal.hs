{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}

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
  , lastChain
  , paddedIndex
  , pageOrder
  , withPageAt
  , withFolioMap
  , withPageDataAt
  ) where

import Chain (Chain)
import Consolidation (Coconsolidation)
import Folio.LiquidInternal
  ( FolioData (..)
  , PageOrder (..)
  , appendPageData
  , composeFolioMaps
  , folioData
  , folioLengthData
  , folioMapComposition
  , folioMapIdentity
  , identityFolioMap
  , lastPageData
  , originPageData
  , originUniqueData
  , originValueData
  , pageOrder
  )
import Numeric.Natural (Natural)

-- | Datra folios specialize the verified type-aligned representation to
-- chains as their page container.
type Folio origin final = FolioData Chain origin final

folio
  :: Chain origin
  -> origin
  -> (origin -> ())
  -> Folio origin origin
folio = folioData

singletonFolio :: Chain () -> Folio () ()
singletonFolio origin = folio origin () (const ())

appendPage
  :: Folio origin previous
  -> Chain next
  -> Coconsolidation previous next
  -> Folio origin next
appendPage = appendPageData

folioLength :: Folio origin final -> Natural
folioLength = folioLengthData

originChain :: Folio origin final -> Chain origin
originChain = originPageData

originValue :: Folio origin final -> origin
originValue = originValueData

originUnique :: Folio origin final -> origin -> ()
originUnique = originUniqueData

lastChain :: Folio origin final -> Chain final
lastChain = lastPageData

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
withFolioMap
  :: Folio origin final
  -> PageOrder
  -> (forall source target.
        Chain source
        -> Chain target
        -> Coconsolidation source target
        -> result)
  -> result
withFolioMap pages (PageOrder sourceIndex targetIndex) useMap =
  withPageDataAt pages targetIndex $ \targetPrefix _ ->
    case mapFromIndex targetPrefix (paddedIndex pages sourceIndex) of
      SomeMapTo sourcePage mapToTarget ->
        useMap sourcePage (lastChain targetPrefix) mapToTarget

-- | Internal eliminator retaining the typed prefix behind a padded page.  The
-- natural supplied to the callback counts how many repeated final pages occur
-- after that prefix.
withPageDataAt
  :: Folio origin final
  -> Natural
  -> (forall page. Folio origin page -> Natural -> result)
  -> result
withPageDataAt pages@(OriginFolio {}) index usePage =
  usePage pages index
withPageDataAt pages@(SnocPage _ previous _ _) index usePage
  | index >= folioLength previous =
      usePage pages (index - folioLength previous)
  | otherwise = withPageDataAt previous index usePage

data SomeMapTo target where
  SomeMapTo
    :: Chain source
    -> Coconsolidation source target
    -> SomeMapTo target

mapFromIndex
  :: Folio origin target
  -> Natural
  -> SomeMapTo target
mapFromIndex (OriginFolio _ page _) _ =
  SomeMapTo page identityFolioMap
mapFromIndex (SnocPage _ previous page transition) sourceIndex
  | sourceIndex >= folioLength previous =
      SomeMapTo page identityFolioMap
  | otherwise =
      case mapFromIndex previous sourceIndex of
        SomeMapTo sourcePage sourceToPrevious ->
          SomeMapTo sourcePage
            (composeFolioMaps transition sourceToPrevious)
