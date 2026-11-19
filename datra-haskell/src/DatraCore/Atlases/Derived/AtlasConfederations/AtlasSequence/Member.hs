{-# LANGUAGE CPP #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
#include "../../../../LiquidPlugin.h"
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple-local" @-}

-- | A sequence member retains the canonical carriers of its own folio.
module AtlasSequence.Member
  ( AtlasSequenceMember
  , atlasSequenceMember
  , withAtlasSequenceMember
  , memberLength
  , memberList
  , memberPageContains
  , memberPageOrder
  , memberPageChain
  , memberPageOrigin
  , memberPagePrevious
  , memberPageNext
  , memberPageTransition
  ) where

import Atlas.Internal (Atlas, atlasFolio)
import Chain.Internal (Chain, chainPosition, chainOrderType)
import Consolidation.Ordered (OrderedConsolidation, orderedSource, orderedTarget)
import Data.List.NonEmpty (NonEmpty (..))
import DatraOrdinal (Ordinal)
import Folio.Presentation (folioLengthData)
import Numeric.Natural (Natural)
import PageElements.Internal (folioPageOrderType)
import PageElements.TraceChain
  ( pageTraceContains, traceHead, pageTraceChain, pageTraceOrigin
  , previousTrace, pageTracePrevious, pageTraceNext, pageTraceTransition )

{-@ embed Natural as int @-}
{-@ invariant {value:Natural | value >= 0} @-}

-- | An existential Atlas retained as one member of a flattened sequence.
data AtlasSequenceMember where
  AtlasSequenceMember
    :: Atlas atlasScope paginationScope cellData origin final
    -> AtlasSequenceMember

atlasSequenceMember
  :: Atlas atlasScope paginationScope cellData origin final
  -> AtlasSequenceMember
atlasSequenceMember = AtlasSequenceMember

withAtlasSequenceMember
  :: AtlasSequenceMember
  -> (forall atlasScope paginationScope cellData origin final.
       Atlas atlasScope paginationScope cellData origin final
       -> result)
  -> result
withAtlasSequenceMember (AtlasSequenceMember valueAtlas) useAtlas =
  useAtlas valueAtlas

-- ALIGN: SEQUENCE-MEMBER-PAGE-MEMBERSHIP.
{-@ reflect memberPageContains @-}
memberPageContains :: AtlasSequenceMember -> Natural -> [Ordinal] -> Bool
memberPageContains (AtlasSequenceMember valueAtlas) page positions =
  pageTraceContains (atlasFolio valueAtlas) page positions

-- ALIGN: SEQUENCE-MEMBER-PAGE-ORDER.
{-@ reflect memberPageOrder @-}
memberPageOrder :: AtlasSequenceMember -> Natural -> Ordinal
memberPageOrder (AtlasSequenceMember valueAtlas) page =
  folioPageOrderType (atlasFolio valueAtlas) page

-- ALIGN: SEQUENCE-MEMBER-PAGE-CHAIN.
{-@ ple memberPageChain @-}
{-@ memberPageChain :: member:AtlasSequenceMember -> page:Natural
      -> {result:Chain {positions:[Ordinal] | memberPageContains member page positions} |
           chainPosition result == traceHead && chainOrderType result == memberPageOrder member page} @-}
memberPageChain :: AtlasSequenceMember -> Natural -> Chain [Ordinal]
memberPageChain (AtlasSequenceMember valueAtlas) page = pageTraceChain (atlasFolio valueAtlas) page

-- ALIGN: SEQUENCE-MEMBER-PAGE-ORIGIN.
{-@ ple memberPageOrigin @-}
{-@ memberPageOrigin :: member:AtlasSequenceMember
      -> {positions:[Ordinal] | memberPageContains member 0 positions} @-}
memberPageOrigin :: AtlasSequenceMember -> [Ordinal]
memberPageOrigin (AtlasSequenceMember valueAtlas) = pageTraceOrigin (atlasFolio valueAtlas)

-- ALIGN: SEQUENCE-MEMBER-PAGE-PREVIOUS.
{-@ ple memberPagePrevious @-}
{-@ memberPagePrevious :: member:AtlasSequenceMember -> page:Natural
      -> positions:{[Ordinal] | memberPageContains member (page + 1) positions}
      -> {memberPageContains member page (previousTrace positions)} @-}
memberPagePrevious :: AtlasSequenceMember -> Natural -> [Ordinal] -> ()
memberPagePrevious (AtlasSequenceMember valueAtlas) page = pageTracePrevious (atlasFolio valueAtlas) page

-- ALIGN: SEQUENCE-MEMBER-PAGE-NEXT.
{-@ ple memberPageNext @-}
{-@ memberPageNext :: member:AtlasSequenceMember -> page:Natural
      -> positions:{[Ordinal] | memberPageContains member page positions}
      -> {result:[Ordinal] | memberPageContains member (page + 1) result
           && previousTrace result == positions} @-}
memberPageNext :: AtlasSequenceMember -> Natural -> [Ordinal] -> [Ordinal]
memberPageNext (AtlasSequenceMember valueAtlas) page = pageTraceNext (atlasFolio valueAtlas) page

-- ALIGN: SEQUENCE-MEMBER-PAGE-TRANSITION.
{-@ ple memberPageTransition @-}
{-@ memberPageTransition :: member:AtlasSequenceMember -> page:Natural
      -> source:{Chain {positions:[Ordinal] | memberPageContains member (page + 1) positions} |
           chainPosition source == traceHead}
      -> target:{Chain {positions:[Ordinal] | memberPageContains member page positions} |
           chainPosition target == traceHead}
      -> {result:OrderedConsolidation
           {positions:[Ordinal] | memberPageContains member (page + 1) positions}
           {positions:[Ordinal] | memberPageContains member page positions} |
             orderedSource result == source && orderedTarget result == target} @-}
memberPageTransition :: AtlasSequenceMember -> Natural -> Chain [Ordinal] -> Chain [Ordinal]
  -> OrderedConsolidation [Ordinal] [Ordinal]
memberPageTransition (AtlasSequenceMember valueAtlas) page = pageTraceTransition (atlasFolio valueAtlas) page

-- ALIGN: SEQUENCE-MEMBER-LENGTH.
{-@ reflect memberLength @-}
{-@ memberLength :: AtlasSequenceMember -> {count:Natural | count > 0} @-}
memberLength :: AtlasSequenceMember -> Natural
memberLength (AtlasSequenceMember valueAtlas) = folioLengthData (atlasFolio valueAtlas)

-- ALIGN: SEQUENCE-MEMBER-LIST.
{-@ opaque-reflect memberList @-}
{-@ memberList :: NonEmpty AtlasSequenceMember -> {members:[AtlasSequenceMember] | len members > 0} @-}
memberList :: NonEmpty AtlasSequenceMember -> [AtlasSequenceMember]
memberList (first :| rest) = first : rest
