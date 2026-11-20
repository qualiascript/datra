{-# LANGUAGE CPP #-}
{-# LANGUAGE GADTs #-}
#include "../../../LiquidPlugin.h"
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}
{-@ LIQUID "--higherorder" @-}
{-@ qualif TraceAccepted(v:@(0), p:func(0, [@(0); bool])) { p v } @-}

-- | A page chain whose carrier consists of its canonical transport traces.
module PageElements.TraceChain
  ( pageTraceChain
  , pageTraceContains
  , pageTraceOrigin
  , traceHead
  , traceHeadMatches
  , previousTrace
  , previousTraceSuffix
  , genuineTraceHead
  , folioLookupPaddedStep
  , folioLookupPaddedPrevious
  , folioPageOrderTypePadded
  , paddedPreviousHead
  , pageTracePrevious
  , tracePrecedes
  , pageTracePreviousMonotone
  , pageTraceTransition
  , pageTraceNext
  , previousPageTrace
  ) where

import Chain.Order (chainPrecedes)
import Chain (Chain, chain, chainOrdinalLT, chainIndex, chainObjectAt, chainPosition, chainOrderType, positionMatches)
import DatraOrdinal (Ordinal, finiteOrdinal)
import DatraOrdinal.Laws (ordinalLTIrreflexive)
import Folio (Folio, folioLength, lastChain)
import Consolidation.Core (Consolidation, applyConsolidation, consolidationPreimage, restrictedConsolidation)
import Consolidation.Ordered (OrderedConsolidation, orderedSource, orderedTarget, orderedApply, orderedPreimage, orderedPreimageProof, orderedMonotone, orderedConsolidation)
import Folio.Presentation (FolioData (..), FolioStep (..), stepSource
  , SingletonOrigin (..))
import Numeric.Natural (Natural)
import PageElements.Internal
  ( folioTraceLookup
  , folioTraceLookupHead
  , prefixTraceLookupPosition
  , prefixTraceLookup
  , prependCopies
  , folioTraceLengthPositive
  , folioOriginTrace
  , folioOriginTraceLookup
  , genuinePageElementTrace
  , pageElementTraceAt
  , traceLookupPresent
  , folioPageOrderType
  , folioTraceLookupBounded
  )
import PageElements.Structure (traceStartsWith, traceSuffix)

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

-- ALIGN: PE-TRACE-ORIGIN.
{-@ pageTraceOrigin :: pages:Folio origin final
      -> {positions:[Ordinal] | pageTraceContains pages 0 positions && positions == folioOriginTrace pages} @-}
pageTraceOrigin :: Folio origin final -> [Ordinal]
pageTraceOrigin pages = folioOriginTraceLookup pages `seq` folioOriginTrace pages

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
      -> {result:Chain {positions:[Ordinal] | pageTraceContains pages page positions} |
           chainPosition result == traceHead && chainOrderType result == folioPageOrderType pages page} @-}
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
      -> {result:Chain {positions:[Ordinal] | pageTraceContains pages page positions} |
           chainPosition result == traceHead && chainOrderType result == order} @-}
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

-- ALIGN: PE-TRACE-PREVIOUS-SUFFIX.
{-@ previousTraceSuffix :: positions:[Ordinal] -> {traceSuffix positions (previousTrace positions)} @-}
previousTraceSuffix :: [Ordinal] -> ()
previousTraceSuffix [] = ()
previousTraceSuffix (_ : []) = ()
previousTraceSuffix (_ : _ : _) = ()

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
genuineTraceNative pages@(SnocPage step@(FolioStep _ _ _)) value =
  stepSource step `seq` prefixTraceLookupPosition pages 0 value

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
folioLookupPreviousPadded pages@(SnocPage (FolioStep _ previous _)) page position =
  prefixLookupPrevious pages (page - folioLength previous) position

-- ALIGN: PE-PADDED-LOOKUP-PREVIOUS.
{-@ folioLookupPaddedPrevious :: pages:Folio origin final
      -> page:{Natural | page >= folioLength pages} -> position:Ordinal
      -> positions:{[Ordinal] | folioTraceLookup pages page position == Just positions}
      -> {folioTraceLookup pages (page - 1) position == Just (previousTrace positions)} @-}
folioLookupPaddedPrevious :: Folio origin final -> Natural -> Ordinal -> [Ordinal] -> ()
folioLookupPaddedPrevious pages page position _ = folioLookupPreviousPadded pages page position

-- | Padding adds the requested position to the preceding complete trace.
-- ALIGN: PE-PADDED-LOOKUP-STEP.
{-@ folioLookupPaddedStep :: pages:Folio origin final
      -> page:{Natural | page >= folioLength pages} -> position:Ordinal
      -> previous:{[Ordinal] | folioTraceLookup pages (page - 1) position == Just previous}
      -> {folioTraceLookup pages page position == Just (prependCopies 1 position previous)} @-}
folioLookupPaddedStep :: Folio origin final -> Natural -> Ordinal -> [Ordinal] -> ()
folioLookupPaddedStep pages page position _ =
  folioTraceLengthPositive pages `seq` folioLookupPreviousPadded pages page position `seq`
    folioTraceLookupHead pages page position `seq`
    case folioTraceLookup pages page position of
      Nothing -> ()
      Just positions -> rebuildPreviousTrace position positions

{-@ rebuildPreviousTrace :: position:Ordinal
      -> positions:{[Ordinal] | len positions > 1 && traceStartsWith position positions}
      -> {positions == prependCopies 1 position (previousTrace positions)} @-}
rebuildPreviousTrace :: Ordinal -> [Ordinal] -> ()
rebuildPreviousTrace _ [] = ()
rebuildPreviousTrace _ (_ : []) = ()
rebuildPreviousTrace _ (_ : _ : _) = ()

-- ALIGN: PE-PADDED-PAGE-ORDER-TYPE.
{-@ folioPageOrderTypePadded :: pages:Folio origin final
      -> page:{Natural | page >= folioLength pages}
      -> {folioPageOrderType pages page == folioPageOrderType pages (page - 1)} @-}
folioPageOrderTypePadded :: Folio origin final -> Natural -> ()
folioPageOrderTypePadded (OriginFolio {}) _ = ()
folioPageOrderTypePadded (SnocPage (FolioStep _ _ _)) _ = ()

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
folioLookupPreviousValid pages@(SnocPage step@(FolioStep _ previous transition)) page position
  | page + 1 >= folioLength pages = paddedLookupPreviousValid pages (page + 1) position
  | page + 1 == folioLength previous =
      case chainIndex (stepSource step) position of
        Nothing -> ()
        Just index ->
          let value = chainObjectAt index
              earlier = orderedApply transition value
              earlierTrace = genuinePageElementTrace previous earlier
          in previousTraceCons (chainPosition (stepSource step) value) earlierTrace `seq`
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

-- | Compare native trace positions in their executable chain order.
-- ALIGN: PE-TRACE-ORDER.
{-@ reflect tracePrecedes @-}
tracePrecedes :: [Ordinal] -> [Ordinal] -> Bool
tracePrecedes earlier later = not (chainOrdinalLT (traceHead later) (traceHead earlier))

{-@ genuineTraceHead :: pages:{Folio origin final | folioLength pages > 1} -> value:final
      -> {traceHead (genuinePageElementTrace pages value) == chainPosition (lastChain pages) value} @-}
genuineTraceHead :: Folio origin final -> final -> ()
genuineTraceHead pages value =
  let position = chainPosition (lastChain pages) value
  in prefixTraceLookupPosition pages 0 value `seq`
       finalPrefixLookup pages position `seq`
       folioTraceLookupHead pages (folioLength pages - 1) position `seq`
       traceHeadMatches position (genuinePageElementTrace pages value)

{-@ finalPrefixLookup :: pages:{Folio origin final | folioLength pages > 1} -> position:Ordinal
      -> {prefixTraceLookup pages 0 position == folioTraceLookup pages (folioLength pages - 1) position} @-}
finalPrefixLookup :: Folio origin final -> Ordinal -> ()
finalPrefixLookup (OriginFolio {}) _ = ()
finalPrefixLookup (SnocPage (FolioStep _ _ _)) _ = ()

-- ALIGN: PE-PADDED-PREVIOUS-HEAD.
{-@ paddedPreviousHead :: pages:Folio origin final
      -> page:{Natural | page >= folioLength pages}
      -> positions:{[Ordinal] | pageTraceContains pages page positions}
      -> {traceHead (previousTrace positions) == traceHead positions} @-}
paddedPreviousHead :: Folio origin final -> Natural -> [Ordinal] -> ()
paddedPreviousHead pages page positions =
  folioLookupPreviousPadded pages page (traceHead positions) `seq`
    folioTraceLookupHead pages (page - 1) (traceHead positions) `seq`
      traceHeadMatches (traceHead positions) (previousTrace positions)

-- | Adjacent transport preserves the order supplied by the actual page chains.
-- ALIGN: PE-TRACE-PREVIOUS-MONOTONE.
{-@ pageTracePreviousMonotone :: pages:Folio origin final -> page:Natural
      -> first:{[Ordinal] | pageTraceContains pages (page + 1) first}
      -> second:{[Ordinal] | pageTraceContains pages (page + 1) second && tracePrecedes first second}
      -> {tracePrecedes (previousTrace first) (previousTrace second)} @-}
pageTracePreviousMonotone :: Folio origin final -> Natural -> [Ordinal] -> [Ordinal] -> ()
pageTracePreviousMonotone pages@(OriginFolio {}) page first second =
  paddedPreviousHead pages (page + 1) first `seq` paddedPreviousHead pages (page + 1) second
pageTracePreviousMonotone pages@(SnocPage step@(FolioStep _ previous transition)) page first second
  | page + 1 >= folioLength pages =
      paddedPreviousHead pages (page + 1) first `seq` paddedPreviousHead pages (page + 1) second
  | page + 1 == folioLength previous =
      case previous of
        OriginFolio {} ->
          pageTracePrevious pages page first `seq` pageTracePrevious pages page second `seq`
            originTraceUnique pages (previousTrace first) `seq`
            originTraceUnique pages (previousTrace second) `seq`
            ordinalLTIrreflexive (traceHead (previousTrace first))
        SnocPage (FolioStep _ _ _) ->
          case chainIndex (stepSource step) (traceHead first) of
            Nothing -> ()
            Just firstIndex ->
              case chainIndex (stepSource step) (traceHead second) of
                Nothing -> ()
                Just secondIndex ->
                  let left = chainObjectAt firstIndex
                      right = chainObjectAt secondIndex
                      earlierLeft = orderedApply transition left
                      earlierRight = orderedApply transition right
                      leftTrace = genuinePageElementTrace previous earlierLeft
                      rightTrace = genuinePageElementTrace previous earlierRight
                  in orderedMonotone transition left right `seq`
                       folioTraceLengthPositive previous `seq`
                       previousTraceCons (chainPosition (stepSource step) left) leftTrace `seq`
                       previousTraceCons (chainPosition (stepSource step) right) rightTrace `seq`
                       genuineTraceHead previous earlierLeft `seq` genuineTraceHead previous earlierRight
  | otherwise = pageTracePreviousMonotone previous page first second

{-@ originTraceUnique :: pages:Folio origin final
      -> positions:{[Ordinal] | pageTraceContains pages 0 positions}
      -> {positions == folioOriginTrace pages} @-}
originTraceUnique :: Folio origin final -> [Ordinal] -> ()
originTraceUnique (OriginFolio _ pageChain witness) positions =
  case chainIndex pageChain (traceHead positions) of
    Nothing -> ()
    Just index -> singletonOriginUnique witness (chainObjectAt index)
originTraceUnique (SnocPage (FolioStep _ previous _)) positions =
  folioTraceLengthPositive previous `seq` originTraceUnique previous positions

-- | Choose the next value while the preceding page's carrier is still known.
{-@ prefixNextLookup :: prefix:Folio origin current -> nextChain:Chain next
      -> transition:{OrderedConsolidation next current |
           orderedSource transition == nextChain && orderedTarget transition == lastChain prefix} -> position:Ordinal
      -> {result:Maybe {positions:[Ordinal] |
            pageTraceContains (SnocPage (FolioStep (folioLength prefix + 1) prefix transition))
              (folioLength prefix) positions} |
            previousLookup result == prefixTraceLookup prefix 0 position} @-}
prefixNextLookup
  :: Folio origin current -> Chain next -> OrderedConsolidation next current -> Ordinal -> Maybe [Ordinal]
prefixNextLookup prefix nextChain transition position =
  case chainIndex (lastChain prefix) position of
    Nothing -> Nothing
    Just index ->
      let value = chainObjectAt index
          nextValue = orderedPreimage transition value
          nextPages = SnocPage (FolioStep (folioLength prefix + 1) prefix transition)
          positions = genuinePageElementTrace nextPages nextValue
      in orderedPreimageProof transition value `seq`
          folioTraceLengthPositive prefix `seq`
          previousTraceCons (chainPosition nextChain nextValue)
            (genuinePageElementTrace prefix value) `seq`
          genuineTraceNative nextPages nextValue `seq`
          Just positions

{-@ genuineNextLookup :: prefix:Folio origin current -> nextChain:Chain next
      -> transition:{OrderedConsolidation next current |
           orderedSource transition == nextChain && orderedTarget transition == lastChain prefix} -> position:Ordinal
      -> {result:Maybe {positions:[Ordinal] |
            pageTraceContains (SnocPage (FolioStep (folioLength prefix + 1) prefix transition))
              (folioLength prefix) positions} |
            previousLookup result == folioTraceLookup prefix (folioLength prefix - 1) position} @-}
genuineNextLookup
  :: Folio origin current -> Chain next -> OrderedConsolidation next current -> Ordinal -> Maybe [Ordinal]
genuineNextLookup prefix@(OriginFolio count pageChain witness) nextChain transition position =
  case chainIndex pageChain position of
    Nothing -> Nothing
    Just index ->
      let value = chainObjectAt index
          nextValue = orderedPreimage transition value
          nextPages = SnocPage (FolioStep (folioLength prefix + 1) prefix transition)
          positions = genuinePageElementTrace nextPages nextValue
          nativePrefix = OriginFolio count pageChain witness
      in genuineTraceNative nextPages nextValue `seq`
          pageTracePrevious nextPages 0 positions `seq`
          originTraceUnique prefix (previousTrace positions) `seq`
          genuineTraceNative nativePrefix value `seq`
          originTraceUnique nativePrefix (genuinePageElementTrace nativePrefix value) `seq`
          Just positions
genuineNextLookup prefix@(SnocPage (FolioStep _ _ _)) nextChain transition position =
  prefixNextLookup prefix nextChain transition position

{-@ paddedNextLookup :: pages:Folio origin final
      -> page:{Natural | page + 1 >= folioLength pages} -> position:Ordinal
      -> {result:Maybe {positions:[Ordinal] | pageTraceContains pages (page + 1) positions} |
            previousLookup result == folioTraceLookup pages page position} @-}
paddedNextLookup :: Folio origin final -> Natural -> Ordinal -> Maybe [Ordinal]
paddedNextLookup pages page position =
  folioLookupPreviousPadded pages (page + 1) position `seq`
    folioTraceLookupHead pages (page + 1) position `seq`
      case folioTraceLookup pages (page + 1) position of
        Nothing -> Nothing
        Just positions -> traceHeadMatches position positions `seq` Just positions

{-@ folioNextLookup :: pages:Folio origin final -> page:Natural -> position:Ordinal
      -> {result:Maybe {positions:[Ordinal] | pageTraceContains pages (page + 1) positions} |
            previousLookup result == folioTraceLookup pages page position} @-}
folioNextLookup :: Folio origin final -> Natural -> Ordinal -> Maybe [Ordinal]
folioNextLookup pages@(OriginFolio {}) page position = paddedNextLookup pages page position
folioNextLookup pages@(SnocPage (FolioStep _ previous transition)) page position
  | page >= folioLength previous = paddedNextLookup pages page position
  | page + 1 == folioLength previous = genuineNextLookup previous (orderedSource transition) transition position
  | otherwise = case folioNextLookup previous page position of
      Nothing -> Nothing
      Just positions -> Just positions

-- | Canonical traces retain the stored choice of preimage and its right inverse.
-- ALIGN: PE-TRACE-NEXT-VALID.
-- ALIGN: PE-TRACE-NEXT-INVERSE.
{-@ reflect pageTraceNext @-}
{-@ pageTraceNext :: pages:Folio origin final -> page:Natural
      -> positions:{[Ordinal] | pageTraceContains pages page positions}
      -> {result:[Ordinal] | pageTraceContains pages (page + 1) result
            && previousTrace result == positions} @-}
pageTraceNext :: Folio origin final -> Natural -> [Ordinal] -> [Ordinal]
pageTraceNext pages page positions =
  case folioNextLookup pages page (traceHead positions) of
    Nothing -> positions
    Just next -> next

-- | The native predecessor as a total map between the accepted trace carriers.
{-@ reflect previousPageTrace @-}
{-@ previousPageTrace :: pages:Folio origin final -> page:Natural
      -> positions:{[Ordinal] | pageTraceContains pages (page + 1) positions}
      -> {result:[Ordinal] | pageTraceContains pages page result && result == previousTrace positions} @-}
previousPageTrace :: Folio origin final -> Natural -> [Ordinal] -> [Ordinal]
previousPageTrace pages page positions = pageTracePrevious pages page positions `seq` previousTrace positions

{-@ previousPageTraceMonotone :: pages:Folio origin final -> page:Natural
      -> first:{[Ordinal] | pageTraceContains pages (page + 1) first}
      -> mappedFirst:{[Ordinal] | pageTraceContains pages page mappedFirst
           && mappedFirst == previousPageTrace pages page first}
      -> second:{[Ordinal] | pageTraceContains pages (page + 1) second && tracePrecedes first second}
      -> {result:[Ordinal] | pageTraceContains pages page result && tracePrecedes mappedFirst result
           && result == previousPageTrace pages page second} @-}
previousPageTraceMonotone :: Folio origin final -> Natural -> [Ordinal] -> [Ordinal] -> [Ordinal] -> [Ordinal]
previousPageTraceMonotone pages page first _ second =
  pageTracePreviousMonotone pages page first second `seq` previousPageTrace pages page second

{-@ previousPageTraceSurjective :: pages:Folio origin final -> page:Natural
      -> next:(value:{[Ordinal] | pageTraceContains pages page value}
           -> {result:[Ordinal] | pageTraceContains pages (page + 1) result
                && previousTrace result == value})
      -> positions:{[Ordinal] | pageTraceContains pages page positions}
      -> {previousPageTrace pages page (next positions) == positions} @-}
previousPageTraceSurjective :: Folio origin final -> Natural -> ([Ordinal] -> [Ordinal]) -> [Ordinal] -> ()
previousPageTraceSurjective _ _ next positions = next positions `seq` ()

{-@ pageTraceConsolidation :: pages:Folio origin final -> page:Natural
      -> {result:Consolidation <{\earlier later -> tracePrecedes earlier later},
                        {\earlier later -> tracePrecedes earlier later}>
           {positions:[Ordinal] | pageTraceContains pages (page + 1) positions}
           {positions:[Ordinal] | pageTraceContains pages page positions} |
             applyConsolidation result == previousPageTrace pages page
             && consolidationPreimage result == pageTraceNext pages page} @-}
pageTraceConsolidation :: Folio origin final -> Natural -> Consolidation [Ordinal] [Ordinal]
pageTraceConsolidation pages page =
  let next = pageTraceNext pages page
  in restrictedConsolidation (pageTraceContains pages (page + 1)) (pageTraceContains pages page)
       (previousPageTrace pages page) next
       (previousPageTraceMonotone pages page) (previousPageTraceSurjective pages page next)

-- | Certify the native trace transport against supplied page chains. Their
-- position functions are checked to be the native trace heads.
-- ALIGN: PE-TRACE-CONSOLIDATION.
{-@ pageTraceTransition :: pages:Folio origin final -> page:Natural
      -> source:{Chain {positions:[Ordinal] | pageTraceContains pages (page + 1) positions} |
           chainPosition source == traceHead}
      -> target:{Chain {positions:[Ordinal] | pageTraceContains pages page positions} |
           chainPosition target == traceHead}
      -> {result:OrderedConsolidation
           {positions:[Ordinal] | pageTraceContains pages (page + 1) positions}
           {positions:[Ordinal] | pageTraceContains pages page positions} |
             orderedSource result == source && orderedTarget result == target
             && orderedApply result == previousPageTrace pages page
             && orderedPreimage result == pageTraceNext pages page} @-}
pageTraceTransition :: Folio origin final -> Natural -> Chain [Ordinal] -> Chain [Ordinal]
  -> OrderedConsolidation [Ordinal] [Ordinal]
pageTraceTransition pages page source target =
  orderedConsolidation source target (pageTraceConsolidation pages page)
