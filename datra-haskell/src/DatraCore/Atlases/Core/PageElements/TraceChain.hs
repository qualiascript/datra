{-# LANGUAGE CPP #-}
{-# LANGUAGE GADTs #-}
#include "../../../LiquidPlugin.h"
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}
{-@ LIQUID "--higherorder" @-}

-- | A page chain whose carrier consists of its canonical transport traces.
module PageElements.TraceChain
  ( pageTraceChain
  , pageTraceContains
  , traceHead
  , previousTrace
  , pageTracePrevious
  ) where

import Chain.Internal (Chain, chain, chainOrdinalLT, chainIndex, chainObjectAt, chainPosition, positionMatches)
import DatraOrdinal.Internal (Ordinal, finiteOrdinal)
import Folio.Internal (Folio, folioLength, lastChain)
import Consolidation (runConsolidationTransport, transportCoconsolidation)
import Folio.LiquidInternal (FolioData (..))
import Numeric.Natural (Natural)
import PageElements.Internal
  ( folioTraceLookup
  , folioTraceLookupHead
  , prefixTraceLookupPosition
  , prefixTraceLookup
  , prependCopies
  , folioTraceLengthPositive
  , genuinePageElementTrace
  , pageElementTraceAt
  , traceLookupPresent
  , traceLookupStartsWith
  , folioPageOrderType
  , folioTraceLookupBounded
  )
import PageElements.LiquidInternal (traceStartsWith)

{-@ embed Natural as int @-}
{-@ invariant {value:Natural | value >= 0} @-}

{-@ reflect traceHead @-}
traceHead :: [Ordinal] -> Ordinal
traceHead [] = finiteOrdinal 0
traceHead (position : _) = position

{-@ traceHeadMatches :: position:Ordinal -> positions:{[Ordinal] | traceStartsWith position positions}
      -> {traceHead positions == position} @-}
traceHeadMatches :: Ordinal -> [Ordinal] -> ()
traceHeadMatches _ [] = ()
traceHeadMatches _ (_ : _) = ()

{-@ reflect pageTraceContains @-}
pageTraceContains :: Folio origin final -> Natural -> [Ordinal] -> Bool
pageTraceContains pages page positions =
  folioTraceLookup pages page (traceHead positions) == Just positions

{-@ reflect pageTraceLookup @-}
{-@ pageTraceLookup :: pages:Folio origin final -> page:Natural
      -> lookupTrace:(position:Ordinal -> {result:Maybe [Ordinal] |
           result == folioTraceLookup pages page position})
      -> position:Ordinal
      -> {result:Maybe ({positions:[Ordinal] | pageTraceContains pages page positions
           && traceHead positions == position}) | result == lookupTrace position} @-}
pageTraceLookup
  :: Folio origin final -> Natural -> (Ordinal -> Maybe [Ordinal]) -> Ordinal -> Maybe [Ordinal]
pageTraceLookup pages page lookupTrace position =
  folioTraceLookupHead pages page position `seq`
    case lookupTrace position of
      Nothing -> Nothing
      Just positions -> traceHeadMatches position positions `seq` Just positions

{-@ pageTracePositionBelow :: pages:Folio origin final -> page:Natural -> order:Ordinal
      -> lookupTrace:(position:Ordinal -> {result:Maybe [Ordinal] |
           result == folioTraceLookup pages page position
           && traceLookupPresent result == chainOrdinalLT position order})
      -> positions:{[Ordinal] | pageTraceContains pages page positions}
      -> {chainOrdinalLT (traceHead positions) order} @-}
pageTracePositionBelow
  :: Folio origin final -> Natural -> Ordinal -> (Ordinal -> Maybe [Ordinal]) -> [Ordinal] -> ()
pageTracePositionBelow _ _ _ lookupTrace positions = lookupTrace (traceHead positions) `seq` ()

{-@ pageTracePositionInjective :: pages:Folio origin final -> page:Natural
      -> first:{[Ordinal] | pageTraceContains pages page first}
      -> second:{[Ordinal] | pageTraceContains pages page second}
      -> {traceHead first == traceHead second => first == second} @-}
pageTracePositionInjective :: Folio origin final -> Natural -> [Ordinal] -> [Ordinal] -> ()
pageTracePositionInjective _ _ _ _ = ()

{-@ pageTracePositionSurjective :: pages:Folio origin final -> page:Natural -> order:Ordinal
      -> lookupTrace:(position:Ordinal -> {result:Maybe [Ordinal] |
           result == folioTraceLookup pages page position
           && traceLookupPresent result == chainOrdinalLT position order})
      -> position:Ordinal
      -> {chainOrdinalLT position order =>
           positionMatches traceHead position (pageTraceLookup pages page lookupTrace position)} @-}
pageTracePositionSurjective
  :: Folio origin final -> Natural -> Ordinal -> (Ordinal -> Maybe [Ordinal]) -> Ordinal -> ()
pageTracePositionSurjective pages page _ lookupTrace position =
  lookupTrace position `seq`
    case pageTraceLookup pages page lookupTrace position of
      Nothing -> ()
      Just _ -> ()

-- | Restrict the carrier before passing it to the proof-bearing Chain constructor.
-- ALIGN: PE-TRACE-CHAIN.
{-@ pageTraceChain :: pages:Folio origin final -> page:Natural
      -> Chain {positions:[Ordinal] | pageTraceContains pages page positions} @-}
pageTraceChain :: Folio origin final -> Natural -> Chain [Ordinal]
pageTraceChain pages page =
  pageTraceChainAtOrder pages page (folioPageOrderType pages page) (boundedFolioTraceLookup pages page)

{-@ boundedFolioTraceLookup :: pages:Folio origin final -> page:Natural -> position:Ordinal
      -> {result:Maybe [Ordinal] | result == folioTraceLookup pages page position
           && traceLookupPresent result == chainOrdinalLT position (folioPageOrderType pages page)} @-}
boundedFolioTraceLookup :: Folio origin final -> Natural -> Ordinal -> Maybe [Ordinal]
boundedFolioTraceLookup pages page position =
  folioTraceLookupBounded pages page position `seq` folioTraceLookup pages page position

{-@ pageTraceChainAtOrder :: pages:Folio origin final -> page:Natural -> order:Ordinal
      -> lookupTrace:(position:Ordinal -> {result:Maybe [Ordinal] |
           result == folioTraceLookup pages page position
           && traceLookupPresent result == chainOrdinalLT position order})
      -> Chain {positions:[Ordinal] | pageTraceContains pages page positions} @-}
pageTraceChainAtOrder :: Folio origin final -> Natural -> Ordinal -> (Ordinal -> Maybe [Ordinal]) -> Chain [Ordinal]
pageTraceChainAtOrder pages page order lookupTrace =
    chain
      order
      traceHead
      (pageTraceLookup pages page lookupTrace)
      (pageTracePositionBelow pages page order lookupTrace)
      (pageTracePositionInjective pages page)
      (pageTracePositionSurjective pages page order lookupTrace)

-- | Drop one transport step, leaving a singleton origin trace fixed.
{-@ reflect previousTrace @-}
previousTrace :: [Ordinal] -> [Ordinal]
previousTrace (_ : rest@(_ : _)) = rest
previousTrace positions = positions

{-@ previousTraceCons :: position:Ordinal -> positions:{[Ordinal] | len positions > 0}
      -> {previousTrace (prependCopies 1 position positions) == positions} @-}
previousTraceCons :: Ordinal -> [Ordinal] -> ()
previousTraceCons _ [] = ()
previousTraceCons _ (_ : _) = ()

-- | The native genuine trace belongs to its final page at its own head.
{-@ genuineTraceNative :: pages:Folio origin final -> value:final
      -> {pageTraceContains pages (folioLength pages - 1) (genuinePageElementTrace pages value)} @-}
genuineTraceNative :: Folio origin final -> final -> ()
genuineTraceNative (OriginFolio count pageChain witness) value =
  prefixTraceLookupPosition (OriginFolio count pageChain witness) 0 value
genuineTraceNative pages@(SnocPage {}) value =
  prefixTraceLookupPosition pages 0 value

{-@ reflect previousLookup @-}
previousLookup :: Maybe [Ordinal] -> Maybe [Ordinal]
previousLookup Nothing = Nothing
previousLookup (Just positions) = Just (previousTrace positions)

{-@ prefixLookupPrevious :: prefix:Folio origin current -> padding:{Natural | padding > 0} -> position:Ordinal
      -> {previousLookup (prefixTraceLookup prefix padding position)
           == prefixTraceLookup prefix (padding - 1) position} @-}
prefixLookupPrevious :: Folio origin current -> Natural -> Ordinal -> ()
prefixLookupPrevious prefix padding position =
  folioTraceLengthPositive prefix `seq`
  case chainIndex (lastChain prefix) position of
    Nothing -> ()
    Just index ->
      let value = chainObjectAt index
      in previousTraceCons (chainPosition (lastChain prefix) value)
           (pageElementTraceAt prefix (padding - 1) value)

{-@ folioLookupPreviousPadded :: pages:Folio origin final
      -> page:{Natural | page >= folioLength pages} -> position:Ordinal
      -> {previousLookup (folioTraceLookup pages page position)
           == folioTraceLookup pages (page - 1) position} @-}
folioLookupPreviousPadded :: Folio origin final -> Natural -> Ordinal -> ()
folioLookupPreviousPadded (OriginFolio count pageChain witness) page position =
  prefixLookupPrevious (OriginFolio count pageChain witness) page position
folioLookupPreviousPadded pages@(SnocPage _ previous _ _) page position =
  prefixLookupPrevious pages (page - folioLength previous) position

{-@ reflect previousLookupValid @-}
previousLookupValid :: Folio origin final -> Natural -> Maybe [Ordinal] -> Bool
previousLookupValid _ _ Nothing = True
previousLookupValid pages page (Just positions) = pageTraceContains pages page (previousTrace positions)

{-@ paddedLookupPreviousValid :: pages:Folio origin final
      -> page:{Natural | page >= folioLength pages} -> position:Ordinal
      -> {previousLookupValid pages (page - 1) (folioTraceLookup pages page position)} @-}
paddedLookupPreviousValid :: Folio origin final -> Natural -> Ordinal -> ()
paddedLookupPreviousValid pages page position =
  folioLookupPreviousPadded pages page position `seq`
    folioTraceLookupHead pages (page - 1) position `seq`
      case folioTraceLookup pages page position of
        Nothing -> ()
        Just positions -> traceHeadMatches position (previousTrace positions)

{-@ folioLookupPreviousValid :: pages:Folio origin final -> page:Natural -> position:Ordinal
      -> {previousLookupValid pages page (folioTraceLookup pages (page + 1) position)} @-}
folioLookupPreviousValid :: Folio origin final -> Natural -> Ordinal -> ()
folioLookupPreviousValid pages@(OriginFolio {}) page position =
  paddedLookupPreviousValid pages (page + 1) position
folioLookupPreviousValid pages@(SnocPage _ previous pageChain transition) page position
  | page + 1 >= folioLength pages = paddedLookupPreviousValid pages (page + 1) position
  | page + 1 == folioLength previous =
      case chainIndex pageChain position of
        Nothing -> ()
        Just index ->
          let value = chainObjectAt index
              earlier = runConsolidationTransport (transportCoconsolidation transition) value
              earlierTrace = genuinePageElementTrace previous earlier
          in previousTraceCons (chainPosition pageChain value) earlierTrace `seq`
              genuineTraceNative previous earlier
  | otherwise =
      folioLookupPreviousValid previous page position `seq`
        case folioTraceLookup previous (page + 1) position of
          Nothing -> ()
          Just _ -> ()

-- ALIGN: PE-TRACE-PREVIOUS-VALID.
{-@ pageTracePrevious :: pages:Folio origin final -> page:Natural
      -> positions:{[Ordinal] | pageTraceContains pages (page + 1) positions}
      -> {pageTraceContains pages page (previousTrace positions)} @-}
pageTracePrevious :: Folio origin final -> Natural -> [Ordinal] -> ()
pageTracePrevious pages page positions = folioLookupPreviousValid pages page (traceHead positions)
