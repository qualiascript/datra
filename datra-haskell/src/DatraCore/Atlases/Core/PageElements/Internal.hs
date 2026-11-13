{-# LANGUAGE CPP #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE RoleAnnotations #-}

#include "../../../LiquidPlugin.h"
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}
{-@ LIQUID "--higherorder" @-}

-- | Hidden representation of the category of cell occurrences.
module PageElements.Internal
  ( PageElements
  , PageElementIndex
  , PageElement
  , SomePageElement (..)
  , PageElementArrow
  , pageElements
  , pageElementsWithScope
  , pageElementsFolio
  , pageElementIndex
  , pageElementIndexOrigin
  , pageElementIndexPage
  , pageElementIndexPosition
  , pageElement
  , originPageElement
  , lastPageElement
  , pageElementPage
  , pageElementPosition
  , withPageElement
  , withPageElementValue
  , somePageElementPrecedes
  , somePageElementTransported
  , somePageElementTransportedReflexive
  , pageElementArrow
  , pageElementTransported
  , arrowSource
  , arrowTarget
  , identityPageElementArrow
  , composePageElementArrows
  , pageElementArrowEndpoints
  , pageElementArrowThin
  , pageElementArrowLeftIdentity
  , pageElementArrowRightIdentity
  , pageElementArrowAssociativity
  , normalizePageElement
  , normalizeSomePageElement
  , normalizePageElementArrow
  , normalizePageElementIdempotent
  ) where

import Chain.Internal
  ( Chain
  , ChainIndex
  , chainIndex
  , chainIndexPosition
  , chainObjectAt
  , chainPosition
  )
import Consolidation
  ( runConsolidationTransport
  , transportCoconsolidation
  )
import DatraOrdinal (Ordinal)
import Data.Kind (Type)
import Folio.Internal
  ( Folio
  , folioLength
  , lastChain
  , originChain
  , originValue
  , originUnique
  , withPageDataAt
  )
import Folio.LiquidInternal (FolioData (..))
import Numeric.Natural (Natural)
import PageElements.LiquidInternal
  ( PageElement (..)
  , PageElementCell (..)
  , PageElementArrow
  , SomePageElement (..)
  , arrowSource
  , arrowTarget
  , composePageElementArrows
  , identityPageElementArrow
  , pageElementAt
  , pageElementArrow
  , pageElementArrowAssociativity
  , pageElementArrowEndpoints
  , pageElementArrowLeftIdentity
  , pageElementArrowRightIdentity
  , pageElementArrowThin
  , pageElementTransported
  , normalizePageElementArrowAt
  , normalizePageElementAt
  , normalizePageElementIdempotentAt
  , normalizeSomePageElementAt
  , somePageElementPrecedes
  , somePageElementTransported
  , somePageElementTransportedReflexive
  )

import qualified PageElements.LiquidInternal as Trace

{-@ embed Natural as int @-}
{-@ invariant {value:Natural | value >= 0} @-}

-- | A folio viewed as its category of cell occurrences.  The generative
-- @scope@ prevents occurrences belonging to different folios from being
-- compared or composed.
type role PageElements nominal nominal nominal
newtype PageElements (scope :: Type) origin final =
  PageElements (Folio origin final)

-- | Evidence that an ordinal indexes an object of one page on this folio's
-- infinite spine.  The nominal scope prevents evidence from one folio from
-- being used to construct an element of another.
type role PageElementIndex nominal
data PageElementIndex (scope :: Type) where
  PageElementIndex :: PageElementIndexData origin current -> PageElementIndex scope

-- | Keep the selected value and its position in a monomorphic record before
-- hiding the prefix's carrier types in 'PageElementIndex'.
{-@ data PageElementIndexData origin current = PageElementIndexData
      { indexedPage :: Natural
      , indexedPrefix :: Folio origin current
      , indexedPadding :: {padding:Natural | padding + folioLength indexedPrefix == indexedPage + 1}
      , indexedPosition :: Ordinal
      , indexedValue :: {value:current | chainPosition (lastChain indexedPrefix) value == indexedPosition}
      } @-}
data PageElementIndexData origin current = PageElementIndexData
  { indexedPage :: Natural
  , indexedPrefix :: Folio origin current
  , indexedPadding :: Natural
  , indexedPosition :: Ordinal
  , indexedValue :: current
  }

-- | Introduce the occurrence category of a folio with a fresh abstract scope.
pageElements
  :: Folio origin final
  -> (forall scope.
        PageElements scope origin final -> result)
  -> result
pageElements pages useCategory =
  useCategory (pageElementsWithScope pages)

-- | Internal, deterministically scoped variant used by derived functors whose
-- object action must return the same type-level category on every call.
{-@ reflect pageElementsWithScope @-}
pageElementsWithScope
  :: Folio origin final
  -> PageElements scope origin final
pageElementsWithScope = PageElements

-- | The single folio underlying this category of occurrences.
{-@ reflect pageElementsFolio @-}
pageElementsFolio :: PageElements scope origin final -> Folio origin final
pageElementsFolio (PageElements pages) = pages

-- | Refine a page number and ordinal to an index of this folio's page-element
-- category.  Pages after the finite presentation repeat its final chain, so
-- this fails exactly when 'chainIndex' rejects the ordinal.
-- ALIGN: PE-CHECKED-LOOKUP-ROUNDTRIP.
-- ALIGN: PE-CHECKED-LOOKUP-BOUNDS.
-- ALIGN: PE-CHECKED-LOOKUP-POSITION.
{-@ pageElementIndex :: category:PageElements scope origin final
      -> page:Natural -> position:Ordinal
      -> Maybe ({index:PageElementIndex scope |
           pageElementIndexOrigin index == originPageElement category
           && pageElementIndexPage index == page
           && pageElementIndexPosition index == position}) @-}
pageElementIndex
  :: PageElements scope origin final
  -> Natural
  -> Ordinal
  -> Maybe (PageElementIndex scope)
pageElementIndex (PageElements pages) page position =
  withPageDataAt pages page (indexFromPrefix pages page position)

{-@ indexFromPrefix :: pages:Folio origin final -> page:Natural -> position:Ordinal
      -> prefix:{Folio origin current |
           originChain prefix == originChain pages
           && originValue prefix == originValue pages}
      -> padding:{Natural | padding + folioLength prefix == page + 1}
      -> Maybe ({index:PageElementIndex scope |
           pageElementIndexOrigin index == folioOriginElement pages
           && pageElementIndexPage index == page
           && pageElementIndexPosition index == position}) @-}
indexFromPrefix
  :: Folio origin final -> Natural -> Ordinal -> Folio origin current -> Natural
  -> Maybe (PageElementIndex scope)
indexFromPrefix _ page position prefix padding =
  case chainIndex (lastChain prefix) position of
    Nothing -> Nothing
    Just index -> Just (PageElementIndex
      (PageElementIndexData page prefix padding (chainIndexPosition index) (chainObjectAt index)))

-- | The origin carried by the typed prefix retained in a checked index.
{-@ reflect pageElementIndexOrigin @-}
pageElementIndexOrigin :: PageElementIndex scope -> SomePageElement scope
pageElementIndexOrigin (PageElementIndex index) =
  folioOriginElement (indexedPrefix index)

{-@ reflect pageElementIndexPage @-}
pageElementIndexPage :: PageElementIndex scope -> Natural
pageElementIndexPage (PageElementIndex index) = indexedPage index

{-@ reflect pageElementIndexPosition @-}
pageElementIndexPosition :: PageElementIndex scope -> Ordinal
pageElementIndexPosition (PageElementIndex index) =
  indexedPosition index

-- | Construct an occurrence from a certified index.  This is total: the only
-- partial step is refining an unchecked ordinal with 'pageElementIndex'.
--
-- The result @x@ satisfies:
--
-- @
-- pageElementPage x == page
-- pageElementPosition x == position
-- @
--
-- Its hidden trace is computed from the folio itself: entry @i@ is the exact
-- cell obtained by transporting the requested cell to page @page - i@. This is
-- the runtime fact used by the LiquidHaskell arrow refinement.
-- ALIGN: PE-CONSTRUCTED-ORIGIN.
-- ALIGN: PE-CONSTRUCTED-POSITION.
-- ALIGN: PE-CONSTRUCTED-TRACE-LENGTH.
{-@ pageElement :: index:PageElementIndex scope
      -> {element:SomePageElement scope |
           somePageElementPrecedes element (pageElementIndexOrigin index)
           && somePageElementTransported element (pageElementIndexOrigin index)
           && Trace.somePageElementPage element == pageElementIndexPage index
           && Trace.somePageElementPosition element == pageElementIndexPosition index
           && len (Trace.somePageElementTrace element) == pageElementIndexPage index + 1} @-}
pageElement
  :: PageElementIndex scope
  -> SomePageElement scope
pageElement (PageElementIndex index) =
  SomePageElement
    (PageElement
      (indexedPage index)
      (chainPosition (lastChain prefix) value)
      (pageElementTraceAt prefix (indexedPadding index) value)
      (PageElementCell (lastChain prefix) value))
  where
    prefix = indexedPrefix index
    value = indexedValue index

-- | The unique origin cell as an object of the page-element category.
-- ALIGN: PE-ORIGIN-INTERPRETATION.
{-@ reflect originPageElement @-}
originPageElement
  :: PageElements scope origin final
  -> SomePageElement scope
originPageElement (PageElements pages) = folioOriginElement pages

{-@ reflect folioOriginElement @-}
folioOriginElement :: Folio origin final -> SomePageElement scope
folioOriginElement pages =
  SomePageElement
    (pageElementAt
      0
      []
      (PageElementCell (originChain pages) (originValue pages)))

-- | A certified cell of the final genuine page as a page element.
-- ALIGN: PE-LAST-INTERPRETATION.
{-@ lastPageElement :: category:PageElements scope origin final
      -> index:{ChainIndex final |
           chainPosition (lastChain (pageElementsFolio category)) (chainObjectAt index)
                == chainIndexPosition index}
      -> SomePageElement scope @-}
lastPageElement
  :: PageElements scope origin final
  -> ChainIndex final
  -> SomePageElement scope
lastPageElement (PageElements pages) index =
  pageElement
    (PageElementIndex
      (PageElementIndexData (folioLength pages - 1) pages 0
        (chainIndexPosition index) (chainObjectAt index)))

-- | The exact trace of the unique origin occurrence.
{-@ reflect folioOriginTrace @-}
folioOriginTrace :: Folio origin final -> [Ordinal]
folioOriginTrace pages = [chainPosition (originChain pages) (originValue pages)]

-- | Build the complete sequence of exact adjacent transports from one cell
-- back through every earlier page to the origin.  The head is the requested
-- occurrence; every following position is computed using the corresponding
-- coconsolidation in the folio.
-- ALIGN: FOLIO-PADDED-TRACE-NORMALIZE.
-- ALIGN: PE-TRACE-TRANSPORT.
-- ALIGN: FOLIO-PADDED-TRACE-ORIGIN.
{-@ pageElementTraceAt :: pages:Folio origin page -> padding:Natural -> page
      -> {positions:[Ordinal] | Trace.traceSuffix positions (folioOriginTrace pages)
           && len positions == padding + folioLength pages} @-}
pageElementTraceAt
  :: Folio origin page
  -> Natural
  -> page
  -> [Ordinal]
pageElementTraceAt pages padding value =
  let genuine = genuinePageElementTrace pages value
      positions = prependCopies padding (chainPosition (lastChain pages) value) genuine
  in Trace.traceSuffixTransitive positions genuine (folioOriginTrace pages) `seq` positions

-- | Build the trace through the stored finite presentation.  Its input is an
-- actual cell, rather than an unchecked ordinal, so every transport is total.
-- ALIGN: FOLIO-TRACE-LENGTH.
-- ALIGN: FOLIO-TRACE-ORIGIN.
{-@ genuinePageElementTrace :: pages:Folio origin page -> value:page
      -> {positions:[Ordinal] | Trace.traceSuffix positions (folioOriginTrace pages)
           && len positions == folioLength pages
           && Trace.traceStartsWith (chainPosition (lastChain pages) value) positions} @-}
genuinePageElementTrace
  :: Folio origin page
  -> page
  -> [Ordinal]
genuinePageElementTrace pages@(OriginFolio _ pageChain _) = \value ->
  originUnique pages value `seq` [chainPosition pageChain value]
genuinePageElementTrace
  (SnocPage _ previous pageChain transition) = \value ->
    let earlierValue = runConsolidationTransport (transportCoconsolidation transition) value
    in
    chainPosition pageChain value
      : genuinePageElementTrace previous earlierValue

{-@ prependCopies :: count:Natural -> Ordinal -> values:[Ordinal]
      -> {positions:[Ordinal] | Trace.traceSuffix positions values && len positions == count + len values} @-}
prependCopies :: Natural -> Ordinal -> [Ordinal] -> [Ordinal]
prependCopies 0 _ values = values
prependCopies count value values =
  value : prependCopies (count - 1) value values

-- | Eliminate the existential object identity of a dynamically looked-up page
-- element.  The callback receives a fresh @object@ type that can index total
-- arrow operations without escaping its scope.
{-@ withPageElement :: selected:SomePageElement scope
      -> (forall object. occurrence:{PageElement scope object | SomePageElement occurrence == selected
           && pageElementPage occurrence == Trace.somePageElementPage selected
           && pageElementPosition occurrence == Trace.somePageElementPosition selected
           && pageElementTrace occurrence == Trace.somePageElementTrace selected} -> result)
      -> result @-}
withPageElement
  :: SomePageElement scope
  -> (forall object. PageElement scope object -> result)
  -> result
withPageElement (SomePageElement element) useElement = useElement element

-- | Recover the existential page carrier and cell value represented by a page
-- element for the duration of a rank-2 callback.
withPageElementValue
  :: PageElement scope object
  -> (forall cell. Chain cell -> cell -> result)
  -> result
withPageElementValue
  (PageElement _ _ _ (PageElementCell pageChain value))
  useCell =
    useCell pageChain value

-- | Collapse an occurrence on the infinite padded spine to its coherent
-- representative at the final genuine page.
{-@ reflect normalizePageElement @-}
normalizePageElement
  :: PageElements scope origin final
  -> PageElement scope object
  -> PageElement scope object
normalizePageElement (PageElements pages) =
  normalizePageElementAt
    (folioLength pages - 1)
    (fromIntegral (folioLength pages))

-- | Normalize an existential page element.
normalizeSomePageElement
  :: PageElements scope origin final
  -> SomePageElement scope
  -> SomePageElement scope
normalizeSomePageElement (PageElements pages) =
  normalizeSomePageElementAt
    (folioLength pages - 1)
    (fromIntegral (folioLength pages))

-- | Normalize both endpoints of a page-element arrow.
{-@ reflect normalizePageElementArrow @-}
normalizePageElementArrow
  :: PageElements scope origin final
  -> PageElementArrow scope source target
  -> PageElementArrow scope source target
normalizePageElementArrow (PageElements pages) =
  normalizePageElementArrowAt
    (folioLength pages - 1)
    (fromIntegral (folioLength pages))

-- | Pointwise witness that page-element normalization is idempotent.
normalizePageElementIdempotent
  :: PageElements scope origin final
  -> PageElement scope object
  -> ()
normalizePageElementIdempotent (PageElements pages) =
  normalizePageElementIdempotentAt
    (folioLength pages - 1)
    (fromIntegral (folioLength pages))
