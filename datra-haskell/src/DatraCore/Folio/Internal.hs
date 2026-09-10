{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}

-- | Hidden representation of folios.
module Folio.Internal
  ( Folio
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
  , withPageAt
  , withPaddedPage
  , withFolioMap
  , withPaddedFolioMap
  ) where

import Chain (Chain)
import Consolidation (Coconsolidation)
import Folio.LiquidInternal
  ( FolioData (..)
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

-- | Eliminate the existential carrier of a genuine page at a zero-based index.
withPageAt
  :: Folio origin final
  -> Natural
  -> (forall page. Chain page -> result)
  -> Maybe result
withPageAt pages index usePage = do
  SomePrefix prefix <- prefixAt pages index
  pure (usePage (lastChain prefix))

-- | Like 'withPageAt', but repeat the final genuine page for every later spine
-- index.
withPaddedPage
  :: Folio origin final
  -> Natural
  -> (forall page. Chain page -> result)
  -> result
withPaddedPage pages index usePage =
  case withPageAt pages (paddedIndex pages index) usePage of
    Just result -> result
    Nothing -> error "Folio.withPaddedPage: impossible empty folio"

-- | Eliminate the page carriers and coherent coconsolidation for an interval.
-- Returns 'Nothing' unless both indices name genuine pages and @source <=
-- target@.  The callback receives the source chain, target chain, and the
-- functorial map from source to target in @CoCon@.
withFolioMap
  :: Folio origin final
  -> Natural
  -> Natural
  -> (forall source target.
        Chain source
        -> Chain target
        -> Coconsolidation source target
        -> result)
  -> Maybe result
withFolioMap pages sourceIndex targetIndex useMap
  | sourceIndex > targetIndex = Nothing
  | otherwise = do
      SomePrefix targetPrefix <- prefixAt pages targetIndex
      SomeMapTo sourcePage mapToTarget <-
        mapFromIndex targetPrefix sourceIndex
      pure
        (useMap sourcePage (lastChain targetPrefix) mapToTarget)

-- | Eliminate a map in the full eventually constant spine presentation.
-- Indices after the finite core are clamped to its final page. Returns
-- 'Nothing' only when @source > target@, where the spine has no arrow.
withPaddedFolioMap
  :: Folio origin final
  -> Natural
  -> Natural
  -> (forall source target.
        Chain source
        -> Chain target
        -> Coconsolidation source target
        -> result)
  -> Maybe result
withPaddedFolioMap pages sourceIndex targetIndex useMap
  | sourceIndex > targetIndex = Nothing
  | otherwise =
      withFolioMap
        pages
        (paddedIndex pages sourceIndex)
        (paddedIndex pages targetIndex)
        useMap

data SomePrefix origin where
  SomePrefix :: Folio origin page -> SomePrefix origin

prefixAt
  :: Folio origin final
  -> Natural
  -> Maybe (SomePrefix origin)
prefixAt pages index
  | index >= folioLength pages = Nothing
prefixAt pages@(OriginFolio {}) _ = Just (SomePrefix pages)
prefixAt pages@(SnocPage _ previous _ _) index
  | index == folioLength previous = Just (SomePrefix pages)
  | otherwise = prefixAt previous index

data SomeMapTo target where
  SomeMapTo
    :: Chain source
    -> Coconsolidation source target
    -> SomeMapTo target

mapFromIndex
  :: Folio origin target
  -> Natural
  -> Maybe (SomeMapTo target)
mapFromIndex pages sourceIndex
  | sourceIndex >= folioLength pages = Nothing
mapFromIndex (OriginFolio _ page _) _ =
  Just (SomeMapTo page identityFolioMap)
mapFromIndex (SnocPage _ previous page transition) sourceIndex
  | sourceIndex == folioLength previous =
      Just (SomeMapTo page identityFolioMap)
  | otherwise = do
      SomeMapTo sourcePage sourceToPrevious <-
        mapFromIndex previous sourceIndex
      pure
        (SomeMapTo sourcePage
          (composeFolioMaps transition sourceToPrevious))
