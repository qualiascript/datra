{-# LANGUAGE CPP #-}
#include "../../../LiquidPlugin.h"
{-@ LIQUID "--reflection" @-}

-- | The category of cell occurrences of a folio.
module PageElements
  ( PageElements
  , pageElementsFolio
  , originPageElement
  , lastPageElement
  , somePageElementTraceValid
  , PageElementDomain
  , pageElementDomain
  , pageElementDomainContains
  , pageElementDomainFinalPage
  , pageElementDomainTraceLimit
  , pageElementTraceValid
  , pageElementTraceValidNormalize
  , pageElementTraceValidShape
  , pageElementTraceValidOrigin
  , pageElementValidArrowPosition
  , traceLookupPresent
  , folioPageOrderType
  , genuinePageElementTrace
  , appendedEarlierLookup
  , appendedPageTrace
  , snocElementTrace
  , folioOriginTrace
  , folioTraceLookup
  , folioFinalPrefixLookup
  , prefixTraceLookup
  , prefixTraceLookupObject
  , finalPageTraceLookup
  , prependCopies
  , PageElementIndex
  , PageElement
  , SomePageElement
  , PageElementArrow
  , pageElements
  , pageElementIndex
  , pageElementIndexPage
  , pageElementIndexOrigin
  , pageElementIndexTrace
  , pageElementIndexPosition
  , pageElement
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

import PageElements.Internal
  ( PageElement
  , pageElementsFolio
  , originPageElement
  , somePageElementTraceValid
  , PageElementDomain
  , pageElementDomain
  , pageElementDomainContains
  , pageElementDomainFinalPage
  , pageElementDomainTraceLimit
  , pageElementTraceValid
  , pageElementTraceValidNormalize
  , pageElementTraceValidShape
  , pageElementValidArrowPosition
  , traceLookupPresent
  , folioPageOrderType
  , genuinePageElementTrace
  , appendedEarlierLookup
  , appendedPageTrace
  , snocElementTrace
  , folioOriginTrace
  , folioTraceLookup
  , folioFinalPrefixLookup
  , prefixTraceLookup
  , finalPageTraceLookup
  , prependCopies
  , PageElementIndex
  , PageElementArrow
  , PageElements
  , SomePageElement
  , arrowSource
  , arrowTarget
  , pageElement
  , pageElementIndex
  , pageElementIndexPage
  , pageElementIndexOrigin
  , pageElementIndexTrace
  , pageElementIndexPosition
  , pageElementArrow
  , pageElements
  , composePageElementArrows
  , identityPageElementArrow
  , pageElementArrowAssociativity
  , pageElementArrowEndpoints
  , pageElementArrowLeftIdentity
  , pageElementArrowRightIdentity
  , pageElementArrowThin
  , pageElementTransported
  , normalizePageElement
  , normalizeSomePageElement
  , normalizePageElementArrow
  , normalizePageElementIdempotent
  , pageElementPage
  , pageElementPosition
  , withPageElement
  , withPageElementValue
  , somePageElementPrecedes
  , somePageElementTransported
  , somePageElementTransportedReflexive
  )

import qualified PageElements.Internal as Internal (prefixTraceLookupObject, pageElementTraceValidOrigin, lastPageElement)
import PageElements.Structure (SomePageElement (..))
import Chain (ChainIndex, chainPosition, chainObjectAt, chainIndexPosition)
import DatraOrdinal (Ordinal)
import Folio (Folio, lastChain, folioLength)
import qualified PageElements.Structure as Trace

-- | Decode a prefix position while retaining the checked object and success
-- contracts across the exposed interface.
{-@ prefixTraceLookupObject :: prefix:Folio origin current -> position:Ordinal
      -> {result:Maybe {value:current | chainPosition (lastChain prefix) value == position} |
           traceLookupPresent result == traceLookupPresent (prefixTraceLookup prefix 0 position)} @-}
prefixTraceLookupObject :: Folio origin current -> Ordinal -> Maybe current
prefixTraceLookupObject = Internal.prefixTraceLookupObject

-- | The owning lookup certifies the scalar arrow back to the origin.
-- ALIGN: PE-TRACE-VALID-ORIGIN.
{-@ pageElementTraceValidOrigin :: category:PageElements scope origin final
      -> occurrence:{PageElement scope object | pageElementTraceValid category occurrence}
      -> {somePageElementPrecedes (SomePageElement occurrence) (originPageElement category)
           && somePageElementTransported (SomePageElement occurrence) (originPageElement category)} @-}
{-@ ple pageElementTraceValidOrigin @-}
pageElementTraceValidOrigin :: PageElements scope origin final -> PageElement scope object -> ()
pageElementTraceValidOrigin = Internal.pageElementTraceValidOrigin

-- | Select a final-page cell and retain its owning-trace certificate.
{-@ lastPageElement :: category:PageElements scope origin final
      -> index:{ChainIndex final | chainPosition (lastChain (pageElementsFolio category)) (chainObjectAt index)
           == chainIndexPosition index}
      -> {result:SomePageElement scope | somePageElementTraceValid category result
           && Trace.somePageElementPage result == folioLength (pageElementsFolio category) - 1} @-}
lastPageElement :: PageElements scope origin final -> ChainIndex final -> SomePageElement scope
lastPageElement = Internal.lastPageElement
