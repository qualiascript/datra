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
  , PageElementDomain
  , pageElementDomain
  , pageElementDomainContains
  , pageElementDomainFinalPage
  , pageElementDomainTraceLimit
  , pageElementDomainNormalizeValid
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
  , pageElementIndexTrace
  , pageElementIndexTraceResult
  , folioTraceLookup
  , prefixTraceLookup
  , prefixTraceLookupPosition
  , pageElementTraceAt
  , genuinePageElementTrace
  , prependCopies
  , folioTraceLengthPositive
  , folioOriginTrace
  , traceLookupPresent
  , folioPageOrderType
  , folioTraceLookupBounded
  , traceLookupStartsWith
  , folioTraceLookupHead
  , pageElementTraceValid
  , pageElementTraceValidShape
  , pageElementValidArrowPosition
  , pageElementTraceValidNormalize
  , somePageElementTraceValid
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
  , chainOrderType
  , chainOrdinalLT
  , chainIndexPosition
  , chainObjectAt
  , chainPosition
  , chainLookup
  , chainPositionBelow
  , chainPositionInjective
  , chainPositionSurjective
  )
import Consolidation
  ( Coconsolidation
  , runConsolidationTransport
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
  )
import Folio.Presentation (FolioData (..), SingletonOrigin (..))
import Numeric.Natural (Natural)
import PageElements.Structure
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

import qualified PageElements.Structure as Trace

{-@ embed Natural as int @-}
{-@ invariant {value:Natural | value >= 0} @-}

-- | A folio viewed as its category of cell occurrences.  The generative
-- @scope@ prevents occurrences belonging to different folios from being
-- compared or composed.
type role PageElements nominal nominal nominal
newtype PageElements (scope :: Type) origin final =
  PageElements (Folio origin final)

-- | Retain the actual owning folio while hiding only its endpoint carriers.
-- Atlas actions use this package as their input domain.
type role PageElementDomain nominal
data PageElementDomain scope where
  PageElementDomain :: PageElements scope origin final -> PageElementDomain scope

{-@ reflect pageElementDomain @-}
pageElementDomain :: PageElements scope origin final -> PageElementDomain scope
pageElementDomain = PageElementDomain

-- ALIGN: PE-ACTION-DOMAIN.
{-@ reflect pageElementDomainContains @-}
pageElementDomainContains :: PageElementDomain scope -> PageElement scope object -> Bool
pageElementDomainContains (PageElementDomain category) occurrence =
  pageElementTraceValid category occurrence

{-@ reflect pageElementDomainFinalPage @-}
pageElementDomainFinalPage :: PageElementDomain scope -> Natural
pageElementDomainFinalPage (PageElementDomain category) =
  folioLength (pageElementsFolio category) - 1

{-@ reflect pageElementDomainTraceLimit @-}
pageElementDomainTraceLimit :: PageElementDomain scope -> Int
pageElementDomainTraceLimit (PageElementDomain category) =
  fromIntegral (folioLength (pageElementsFolio category))

-- ALIGN: PE-ACTION-DOMAIN-NORMALIZATION.
{-@ pageElementDomainNormalizeValid :: domain:PageElementDomain scope
      -> occurrence:{PageElement scope object | pageElementDomainContains domain occurrence}
      -> {pageElementDomainContains domain
           (normalizePageElementAt (pageElementDomainFinalPage domain)
             (pageElementDomainTraceLimit domain) occurrence)} @-}
pageElementDomainNormalizeValid :: PageElementDomain scope -> PageElement scope object -> ()
pageElementDomainNormalizeValid (PageElementDomain category) occurrence =
  pageElementTraceValidNormalize category occurrence

-- | Evidence that an ordinal indexes an object of one page on this folio's
-- infinite spine.  The nominal scope prevents evidence from one folio from
-- being used to construct an element of another.
type role PageElementIndex nominal
data PageElementIndex (scope :: Type) where
  PageElementIndex :: PageElementIndexData origin current -> PageElementIndex scope

-- | Check the selected value, position, and exact transport trace in a
-- monomorphic record before hiding the prefix's carrier types.
{-@ data PageElementIndexData origin current = PageElementIndexData
      { indexedPage :: Natural
      , indexedPrefix :: Folio origin current
      , indexedPadding :: {padding:Natural | padding + folioLength indexedPrefix == indexedPage + 1}
      , indexedPosition :: Ordinal
      , indexedValue :: {value:current | chainPosition (lastChain indexedPrefix) value == indexedPosition}
      , indexedTrace :: {positions:[Ordinal] |
           len positions == indexedPage + 1
           && Trace.traceStartsWith indexedPosition positions
           && Trace.traceSuffix positions (folioOriginTrace indexedPrefix)
           && positions == pageElementTraceAt indexedPrefix indexedPadding indexedValue}
      } @-}
data PageElementIndexData origin current = PageElementIndexData
  { indexedPage :: Natural
  , indexedPrefix :: Folio origin current
  , indexedPadding :: Natural
  , indexedPosition :: Ordinal
  , indexedValue :: current
  , indexedTrace :: [Ordinal]
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
      -> {result:Maybe ({index:PageElementIndex scope |
           pageElementIndexOrigin index == originPageElement category
           && pageElementIndexPage index == page
           && pageElementIndexPosition index == position
           && folioTraceLookup (pageElementsFolio category) page position == Just (pageElementIndexTrace index)}) |
           pageElementIndexTraceResult result == folioTraceLookup (pageElementsFolio category) page position} @-}
pageElementIndex
  :: PageElements scope origin final
  -> Natural
  -> Ordinal
  -> Maybe (PageElementIndex scope)
pageElementIndex (PageElements pages) page position =
  indexInFolio pages page position

-- | The canonical transport trace selected by this folio's page lookup.
{-@ reflect folioTraceLookup @-}
{-@ folioTraceLookup :: pages:Folio origin final -> page:Natural -> position:Ordinal
      -> Maybe ({positions:[Ordinal] | len positions == page + 1}) @-}
folioTraceLookup :: Folio origin final -> Natural -> Ordinal -> Maybe [Ordinal]
folioTraceLookup (OriginFolio count pageChain witness) page position =
  prefixTraceLookup (OriginFolio count pageChain witness) page position
folioTraceLookup pages@(SnocPage _ previous _ _) page position
  | page >= folioLength previous =
      prefixTraceLookup pages (page - folioLength previous) position
  | otherwise = folioTraceLookup previous page position

{-@ reflect prefixTraceLookup @-}
{-@ prefixTraceLookup :: prefix:Folio origin current -> padding:Natural -> position:Ordinal
      -> Maybe ({positions:[Ordinal] | len positions == padding + folioLength prefix}) @-}
prefixTraceLookup :: Folio origin current -> Natural -> Ordinal -> Maybe [Ordinal]
prefixTraceLookup prefix padding position =
  case chainIndex (lastChain prefix) position of
    Nothing -> Nothing
    Just index -> Just (pageElementTraceAt prefix padding (chainObjectAt index))

-- | Native prefix lookup reconstructs the trace of every actual final-page value.
{-@ prefixTraceLookupPosition :: prefix:Folio origin current -> padding:Natural -> value:current
      -> {prefixTraceLookup prefix padding (chainPosition (lastChain prefix) value)
           == Just (pageElementTraceAt prefix padding value)} @-}
prefixTraceLookupPosition :: Folio origin current -> Natural -> current -> ()
prefixTraceLookupPosition prefix _ value =
  let pageChain = lastChain prefix
      position = chainPosition pageChain value
  in chainPositionBelow pageChain value `seq`
      chainPositionSurjective pageChain position `seq`
        case chainLookup pageChain position of
          Nothing -> ()
          Just candidate -> chainPositionInjective pageChain candidate value

-- | The scalar success observation shared by page-chain constructors.
{-@ reflect traceLookupPresent @-}
traceLookupPresent :: Maybe [Ordinal] -> Bool
traceLookupPresent Nothing = False
traceLookupPresent (Just _) = True

-- ALIGN: PE-PREFIX-LOOKUP-BOUNDS.
{-@ prefixTraceLookupBounded :: prefix:Folio origin current -> padding:Natural -> position:Ordinal
      -> {traceLookupPresent (prefixTraceLookup prefix padding position)
           == chainOrdinalLT position (chainOrderType (lastChain prefix))} @-}
prefixTraceLookupBounded :: Folio origin current -> Natural -> Ordinal -> ()
prefixTraceLookupBounded prefix _ position
  | chainOrdinalLT position (chainOrderType (lastChain prefix)) =
      chainPositionSurjective (lastChain prefix) position `seq`
        case chainLookup (lastChain prefix) position of
          Nothing -> ()
          Just _ -> ()
  | otherwise = ()

-- | The ordinal of the actual page selected from the owning finite folio.
{-@ reflect folioPageOrderType @-}
folioPageOrderType :: Folio origin final -> Natural -> Ordinal
folioPageOrderType (OriginFolio _ pageChain _) _ = chainOrderType pageChain
folioPageOrderType (SnocPage _ previous pageChain _) page
  | page >= folioLength previous = chainOrderType pageChain
  | otherwise = folioPageOrderType previous page

-- ALIGN: PE-NATIVE-LOOKUP-BOUNDS.
{-@ folioTraceLookupBounded :: pages:Folio origin final -> page:Natural -> position:Ordinal
      -> {traceLookupPresent (folioTraceLookup pages page position)
           == chainOrdinalLT position (folioPageOrderType pages page)} @-}
folioTraceLookupBounded :: Folio origin final -> Natural -> Ordinal -> ()
folioTraceLookupBounded (OriginFolio count pageChain witness) page position =
  prefixTraceLookupBounded (OriginFolio count pageChain witness) page position
folioTraceLookupBounded pages@(SnocPage _ previous _ _) page position
  | page >= folioLength previous =
      prefixTraceLookupBounded pages (page - folioLength previous) position
  | otherwise = folioTraceLookupBounded previous page position

{-@ reflect traceLookupStartsWith @-}
traceLookupStartsWith :: Ordinal -> Maybe [Ordinal] -> Bool
traceLookupStartsWith _ Nothing = True
traceLookupStartsWith position (Just positions) = Trace.traceStartsWith position positions

-- ALIGN: PE-NATIVE-LOOKUP-HEAD.
{-@ folioTraceLookupHead :: pages:Folio origin final -> page:Natural -> position:Ordinal
      -> {traceLookupStartsWith position (folioTraceLookup pages page position)} @-}
folioTraceLookupHead :: Folio origin final -> Natural -> Ordinal -> ()
folioTraceLookupHead pages page position =
  case indexInFolio pages page position of
    Nothing -> ()
    Just index -> pageElement index `seq` ()

{-@ reflect trimLookupTrace @-}
trimLookupTrace :: Int -> Maybe [Ordinal] -> Maybe [Ordinal]
trimLookupTrace _ Nothing = Nothing
trimLookupTrace limit (Just positions) = Just (Trace.trimTrace limit positions)

{-@ prefixTraceLookupTrim :: pages:Folio origin final -> padding:Natural -> position:Ordinal
      -> limit:{Int | limit == folioLength pages}
      -> {trimLookupTrace limit (prefixTraceLookup pages padding position)
           == prefixTraceLookup pages 0 position} @-}
prefixTraceLookupTrim :: Folio origin final -> Natural -> Ordinal -> Int -> ()
prefixTraceLookupTrim pages padding position limit =
  case chainIndex (lastChain pages) position of
    Nothing -> ()
    Just index ->
      let value = chainObjectAt index
      in Trace.trimTraceToSuffix (pageElementTraceAt pages padding value)
           (genuinePageElementTrace pages value) limit

-- ALIGN: PE-LOOKUP-NORMALIZATION.
{-@ folioTraceLookupNormalize :: pages:Folio origin final -> page:Natural -> position:Ordinal
      -> limit:{Int | limit == folioLength pages}
      -> {folioTraceLookup pages (Trace.clampPage page (folioLength pages - 1)) position
           == trimLookupTrace limit (folioTraceLookup pages page position)} @-}
folioTraceLookupNormalize :: Folio origin final -> Natural -> Ordinal -> Int -> ()
folioTraceLookupNormalize (OriginFolio count pageChain witness) page position limit =
  prefixTraceLookupTrim (OriginFolio count pageChain witness) page position limit
folioTraceLookupNormalize pages@(SnocPage _ previous _ _) page position limit
  | page < folioLength pages =
      case folioTraceLookup pages page position of
        Nothing -> ()
        Just positions -> Trace.trimTraceWithinLength limit positions
  | otherwise =
      prefixTraceLookupTrim pages (page - folioLength previous) position limit

-- ALIGN: PE-LOOKUP-OWNING-TRACE.
-- ALIGN: PE-LOOKUP-STORED-PREFIX.
-- ALIGN: PE-NATIVE-LOOKUP-POSITION.
{-@ indexInFolio :: pages:Folio origin final -> page:Natural -> position:Ordinal
      -> {result:Maybe ({index:PageElementIndex scope |
           pageElementIndexOrigin index == folioOriginElement pages
           && pageElementIndexPage index == page
           && pageElementIndexPosition index == position
           && folioTraceLookup pages page position == Just (pageElementIndexTrace index)}) |
           pageElementIndexTraceResult result == folioTraceLookup pages page position} @-}
indexInFolio :: Folio origin final -> Natural -> Ordinal -> Maybe (PageElementIndex scope)
indexInFolio (OriginFolio count pageChain witness) page position =
  lookupPrefixIndex page position (OriginFolio count pageChain witness) page
    (originElementTrace pageChain witness)
indexInFolio pages@(SnocPage _ previous pageChain transition) page position
  | page >= folioLength previous =
      lookupPrefixIndex page position pages
        (page - folioLength previous) (snocElementTrace previous pageChain transition)
  | otherwise = indexInFolio previous page position

-- | Scalar trace validity against the owning folio, including its exact
-- adjacent transports and final-page padding.
-- ALIGN: PE-TRACE-OWNER-VALIDITY.
{-@ reflect pageElementTraceValid @-}
pageElementTraceValid :: PageElements scope origin final -> PageElement scope object -> Bool
pageElementTraceValid category occurrence =
  folioTraceLookup (pageElementsFolio category) (pageElementPage occurrence)
    (pageElementPosition occurrence) == Just (Trace.pageElementTrace occurrence)

-- | Eliminate the native lookup certificate before its cell type is hidden.
-- Both failure and success agree with the canonical owning-folio lookup.
-- ALIGN: PE-TRACE-VALID-SHAPE.
{-@ pageElementTraceValidShape :: category:PageElements scope origin final
      -> occurrence:{PageElement scope object | pageElementTraceValid category occurrence}
      -> {len (Trace.pageElementTrace occurrence) == pageElementPage occurrence + 1
           && Trace.traceStartsWith (pageElementPosition occurrence) (Trace.pageElementTrace occurrence)} @-}
pageElementTraceValidShape :: PageElements scope origin final -> PageElement scope object -> ()
pageElementTraceValidShape category occurrence =
  case pageElementIndex category (pageElementPage occurrence) (pageElementPosition occurrence) of
    Nothing -> ()
    Just index -> pageElement index `seq` ()

-- ALIGN: PE-OWNER-ARROW-POSITION.
{-@ pageElementValidArrowPosition :: category:PageElements scope origin final
      -> arrow:{PageElementArrow scope source target |
           pageElementTraceValid category (arrowSource arrow)
           && pageElementTraceValid category (arrowTarget arrow)}
      -> {Trace.positionAtPage (pageElementPage (arrowTarget arrow)) (arrowSource arrow)
           == Just (pageElementPosition (arrowTarget arrow))} @-}
pageElementValidArrowPosition
  :: PageElements scope origin final -> PageElementArrow scope source target -> ()
pageElementValidArrowPosition category arrow =
  pageElementTraceValidShape category (arrowSource arrow) `seq`
    pageElementTraceValidShape category (arrowTarget arrow) `seq`
      Trace.pageElementArrowPosition arrow

-- ALIGN: PE-TRACE-VALID-NORMALIZATION.
{-@ pageElementTraceValidNormalize :: category:PageElements scope origin final
      -> occurrence:{PageElement scope object | pageElementTraceValid category occurrence}
      -> {pageElementTraceValid category (normalizePageElement category occurrence)} @-}
pageElementTraceValidNormalize :: PageElements scope origin final -> PageElement scope object -> ()
pageElementTraceValidNormalize category occurrence =
  let pages = pageElementsFolio category
  in folioTraceLookupNormalize pages (pageElementPage occurrence) (pageElementPosition occurrence)
       (fromIntegral (folioLength pages))

{-@ reflect somePageElementTraceValid @-}
somePageElementTraceValid :: PageElements scope origin final -> SomePageElement scope -> Bool
somePageElementTraceValid category (SomePageElement occurrence) =
  pageElementTraceValid category occurrence

{-@ lookupPrefixIndex :: page:Natural -> position:Ordinal -> prefix:Folio origin current
      -> padding:{Natural | padding + folioLength prefix == page + 1}
      -> makeTrace:(value:current -> {positions:[Ordinal] |
           Trace.traceSuffix positions (folioOriginTrace prefix)
           && len positions == folioLength prefix
           && Trace.traceStartsWith (chainPosition (lastChain prefix) value) positions
           && positions == genuinePageElementTrace prefix value})
      -> {result:Maybe ({index:PageElementIndex scope |
           pageElementIndexOrigin index == folioOriginElement prefix
           && pageElementIndexPage index == page
           && pageElementIndexPosition index == position
           && prefixTraceLookup prefix padding position == Just (pageElementIndexTrace index)}) |
           pageElementIndexTraceResult result == prefixTraceLookup prefix padding position} @-}
lookupPrefixIndex
  :: Natural -> Ordinal -> Folio origin current -> Natural
  -> (current -> [Ordinal]) -> Maybe (PageElementIndex scope)
lookupPrefixIndex page position prefix padding makeTrace =
  case chainIndex (lastChain prefix) position of
    Nothing -> Nothing
    Just index ->
      let value = chainObjectAt index
      in Just (PageElementIndex (indexWithTrace page prefix padding value (makeTrace value)))

-- ALIGN: PE-INDEX-TRACE-CACHE.
{-@ indexWithTrace :: page:Natural -> prefix:Folio origin current
      -> padding:{Natural | padding + folioLength prefix == page + 1}
      -> value:current
      -> genuine:{positions:[Ordinal] |
           Trace.traceSuffix positions (folioOriginTrace prefix)
           && len positions == folioLength prefix
           && Trace.traceStartsWith (chainPosition (lastChain prefix) value) positions
           && positions == genuinePageElementTrace prefix value}
      -> {index:PageElementIndexData origin current |
           indexedPage index == page && indexedPrefix index == prefix
           && indexedPosition index == chainPosition (lastChain prefix) value
           && indexedTrace index == pageElementTraceAt prefix padding value} @-}
indexWithTrace
  :: Natural -> Folio origin current -> Natural -> current -> [Ordinal]
  -> PageElementIndexData origin current
indexWithTrace page prefix padding value genuine =
  let position = chainPosition (lastChain prefix) value
      positions = prependCopies padding position genuine
  in Trace.traceSuffixTransitive positions genuine (folioOriginTrace prefix) `seq`
      PageElementIndexData page prefix padding position value positions

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

{-@ reflect pageElementIndexTrace @-}
pageElementIndexTrace :: PageElementIndex scope -> [Ordinal]
pageElementIndexTrace (PageElementIndex index) = indexedTrace index

-- | Observe success and failure without exposing either hidden carrier type.
{-@ reflect pageElementIndexTraceResult @-}
pageElementIndexTraceResult :: Maybe (PageElementIndex scope) -> Maybe [Ordinal]
pageElementIndexTraceResult Nothing = Nothing
pageElementIndexTraceResult (Just index) = Just (pageElementIndexTrace index)

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
-- ALIGN: PE-CONSTRUCTED-TRACE-HEAD.
{-@ pageElement :: index:PageElementIndex scope
      -> {element:SomePageElement scope |
           somePageElementPrecedes element (pageElementIndexOrigin index)
           && somePageElementTransported element (pageElementIndexOrigin index)
           && Trace.somePageElementPage element == pageElementIndexPage index
           && Trace.somePageElementPosition element == pageElementIndexPosition index
           && len (Trace.somePageElementTrace element) == pageElementIndexPage index + 1
           && Trace.traceStartsWith (pageElementIndexPosition index) (Trace.somePageElementTrace element)
           && Trace.somePageElementTrace element == pageElementIndexTrace index} @-}
pageElement
  :: PageElementIndex scope
  -> SomePageElement scope
pageElement (PageElementIndex index) =
  SomePageElement
    (PageElement
      (indexedPage index)
      (chainPosition (lastChain prefix) value)
      (indexedTrace index)
      (PageElementCell (lastChain prefix) value))
  where
    prefix = indexedPrefix index
    value = indexedValue index

-- | The unique origin cell as an object of the page-element category.
-- ALIGN: PE-ORIGIN-INTERPRETATION.
{-@ reflect originPageElement @-}
{-@ originPageElement :: category:PageElements scope origin final
      -> {origin:SomePageElement scope | somePageElementTraceValid category origin} @-}
originPageElement
  :: PageElements scope origin final
  -> SomePageElement scope
originPageElement (PageElements pages) =
  folioOriginTraceLookup pages `seq` folioOriginElement pages

-- ALIGN: PE-NATIVE-ORIGIN-LOOKUP.
{-@ folioOriginTraceLookup :: pages:Folio origin final
      -> {folioTraceLookup pages 0 (chainPosition (originChain pages) (originValue pages))
           == Just (folioOriginTrace pages)} @-}
folioOriginTraceLookup :: Folio origin final -> ()
folioOriginTraceLookup (OriginFolio _ pageChain witness) =
  let position = chainPosition pageChain (selectedOrigin witness)
  in chainPositionBelow pageChain (selectedOrigin witness) `seq`
      chainPositionSurjective pageChain position `seq`
        case chainLookup pageChain position of
          Nothing -> ()
          Just value -> singletonOriginUnique witness value
folioOriginTraceLookup (SnocPage _ previous _ _) =
  folioTraceLengthPositive previous `seq` folioOriginTraceLookup previous

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
lastPageElement (PageElements (OriginFolio count pageChain witness)) index =
  let prefix = OriginFolio count pageChain witness
      value = chainObjectAt index
  in pageElement (PageElementIndex (indexWithTrace 0 prefix 0 value
       (originElementTrace pageChain witness value)))
lastPageElement (PageElements (SnocPage count previous pageChain transition)) index =
  let prefix = SnocPage count previous pageChain transition
      value = chainObjectAt index
  in pageElement (PageElementIndex (indexWithTrace (count - 1) prefix 0 value
       (snocElementTrace previous pageChain transition value)))

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
-- ALIGN: PE-PREFIX-TRACE-TRANSPORT.
-- ALIGN: PE-PADDED-TRACE-POSITION.
{-@ reflect pageElementTraceAt @-}
{-@ pageElementTraceAt :: pages:Folio origin page -> padding:Natural -> value:page
      -> {positions:[Ordinal] | Trace.traceSuffix positions (folioOriginTrace pages)
           && Trace.traceSuffix positions (genuinePageElementTrace pages value)
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
{-@ reflect genuinePageElementTrace @-}
{-@ genuinePageElementTrace :: pages:Folio origin page -> page
      -> {positions:[Ordinal] | Trace.traceSuffix positions (folioOriginTrace pages)
           && len positions == folioLength pages} / [folioLength pages, 0] @-}
genuinePageElementTrace :: Folio origin page -> page -> [Ordinal]
genuinePageElementTrace (OriginFolio _ pageChain witness) value =
  originElementTrace pageChain witness value
genuinePageElementTrace (SnocPage _ previous pageChain transition) value =
  snocElementTrace previous pageChain transition value

{-@ reflect originElementTrace @-}
{-@ originElementTrace :: pageChain:Chain origin -> witness:SingletonOrigin origin -> value:origin
      -> {positions:[Ordinal] | len positions == 1
           && Trace.traceStartsWith (chainPosition pageChain value) positions
           && Trace.traceSuffix positions [chainPosition pageChain (selectedOrigin witness)]} @-}
originElementTrace :: Chain origin -> SingletonOrigin origin -> origin -> [Ordinal]
originElementTrace pageChain witness value =
  singletonOriginUnique witness value `seq` [chainPosition pageChain value]

{-@ reflect snocElementTrace @-}
{-@ snocElementTrace :: previous:Folio origin earlier -> pageChain:Chain current
      -> transition:Coconsolidation earlier current -> value:current
      -> {positions:[Ordinal] | len positions == folioLength previous + 1
           && Trace.traceStartsWith (chainPosition pageChain value) positions
           && Trace.traceSuffix positions (folioOriginTrace previous)} / [folioLength previous, 1] @-}
snocElementTrace
  :: Folio origin earlier -> Chain current -> Coconsolidation earlier current
  -> current -> [Ordinal]
snocElementTrace previous pageChain transition value =
  let earlierValue = runConsolidationTransport (transportCoconsolidation transition) value
  in folioTraceLengthPositive previous `seq`
      (chainPosition pageChain value : genuinePageElementTrace previous earlierValue)

{-@ folioTraceLengthPositive :: pages:Folio origin current -> {folioLength pages > 0} @-}
folioTraceLengthPositive :: Folio origin current -> ()
folioTraceLengthPositive pages = folioLength pages `seq` ()

{-@ reflect prependCopies @-}
{-@ prependCopies :: count:Natural -> value:Ordinal -> values:[Ordinal]
      -> {positions:[Ordinal] | Trace.traceSuffix positions values && len positions == count + len values
           && (Trace.traceStartsWith value values => Trace.traceStartsWith value positions)} @-}
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
normalizePageElement category occurrence =
  let pages = pageElementsFolio category
  in normalizePageElementAt
       (folioLength pages - 1)
       (fromIntegral (folioLength pages)) occurrence

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
