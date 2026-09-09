{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}

-- | Hidden representation of folios.
module Folio.Internal
  ( Folio (..)
  , folio
  , singletonFolio
  , appendPage
  , folioLength
  , originChain
  , originValue
  , originUnique
  , lastChain
  , paddedIndex
  , withPageAt
  , withPaddedPage
  , withFolioMap
  , withPaddedFolioMap
  ) where

import Chains (Chain)
import Consolidation
  ( Coconsolidation
  , composeCoconsolidations
  , identityConsolidation
  )
import Numeric.Natural (Natural)

import qualified Consolidation

-- | A nonempty, finite presentation of an eventually constant spine functor.
--
-- @Folio origin final@ exposes the carrier types of its first and final pages.
-- Intermediate page carriers are existential.  Every appended arrow is a
-- coconsolidation from the preceding page to the new page.
data Folio origin final where
  OriginFolio
    :: Natural
    -> Chain origin
    -> origin
    -> (origin -> ())
    -> Folio origin origin
  SnocPage
    :: Natural
    -> Folio origin previous
    -> Chain next
    -> Coconsolidation previous next
    -> Folio origin next

-- | Construct the one-page core of a folio.
--
-- The callback is proof-shaped runtime data.  Its intended law is:
--
-- @forall value. value == selectedOrigin@
--
-- Equivalently, the origin carrier is isomorphic to @()@.  The law is only
-- documented for now and is not checked by LiquidHaskell.
folio
  :: Chain origin
  -> origin
  -> (origin -> ())
  -> Folio origin origin
folio = OriginFolio 1

-- | Construct a folio whose first (and currently only) carrier is @()@.
singletonFolio :: Chain () -> Folio () ()
singletonFolio origin = folio origin () (const ())

-- | Append one genuine page and its generating coconsolidation.
--
-- Required coherence conditions (documented, not LiquidHaskell-checked):
--
-- * the underlying consolidation is monotone from @next@ to @previous@;
-- * it is point-surjective onto @previous@;
-- * the map for an identity interval is the identity coconsolidation;
-- * for @i <= j <= k@, the map @i -> k@ equals the composite of the maps
--   @i -> j@ and @j -> k@.
--
-- The first two conditions belong to 'Consolidation'.  The latter two hold by
-- construction because 'withFolioMap' uses identity and categorical
-- composition rather than storing redundant long-range arrows.
appendPage
  :: Folio origin previous
  -> Chain next
  -> Coconsolidation previous next
  -> Folio origin next
appendPage pages = SnocPage (folioLength pages + 1) pages

-- | The number of genuine pages in the least finite presentation.
folioLength :: Folio origin final -> Natural
folioLength (OriginFolio count _ _ _) = count
folioLength (SnocPage count _ _ _) = count

-- | The first page's chain.
originChain :: Folio origin final -> Chain origin
originChain (OriginFolio _ value _ _) = value
originChain (SnocPage _ pages _ _) = originChain pages

-- | The distinguished value of the singleton origin page.
originValue :: Folio origin final -> origin
originValue (OriginFolio _ _ value _) = value
originValue (SnocPage _ pages _ _) = originValue pages

-- | Invoke the proof-shaped singleton-origin witness.
originUnique :: Folio origin final -> origin -> ()
originUnique (OriginFolio _ _ _ unique) = unique
originUnique (SnocPage _ pages _ _) = originUnique pages

-- | The final genuine page's chain.
lastChain :: Folio origin final -> Chain final
lastChain (OriginFolio _ value _ _) = value
lastChain (SnocPage _ _ value _) = value

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
mapFromIndex (OriginFolio _ page _ _) _ =
  Just (SomeMapTo page (Consolidation.op identityConsolidation))
mapFromIndex (SnocPage _ previous page transition) sourceIndex
  | sourceIndex == folioLength previous =
      Just (SomeMapTo page (Consolidation.op identityConsolidation))
  | otherwise = do
      SomeMapTo sourcePage sourceToPrevious <-
        mapFromIndex previous sourceIndex
      pure
        (SomeMapTo sourcePage
          (composeCoconsolidations transition sourceToPrevious))
