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

import qualified PageElements.Internal as Internal (prefixTraceLookupObject)
import Chain (chainPosition)
import DatraOrdinal (Ordinal)
import Folio (Folio, lastChain)

-- | Decode a prefix position while retaining the checked object and success
-- contracts across the exposed interface.
{-@ prefixTraceLookupObject :: prefix:Folio origin current -> position:Ordinal
      -> {result:Maybe {value:current | chainPosition (lastChain prefix) value == position} |
           traceLookupPresent result == traceLookupPresent (prefixTraceLookup prefix 0 position)} @-}
prefixTraceLookupObject :: Folio origin current -> Ordinal -> Maybe current
prefixTraceLookupObject = Internal.prefixTraceLookupObject
