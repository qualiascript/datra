{-# LANGUAGE CPP #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
#include "../../../../LiquidPlugin.h"
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple-local" @-}
{-@ qualif MemberAccepted(v:@(0), p:func(0, [@(0); bool])) { p v } @-}

-- | A sequence member retains the canonical carriers of its own folio.
module AtlasSequence.Member
  ( AtlasSequenceMember
  , atlasSequenceMember
  , withMemberTrace
  , withAtlasSequenceMember
  , memberAt
  , memberLength
  , memberList
  , memberPageContains
  , memberPageOrder
  , memberPageChain
  , memberPageOrigin
  , memberPagePrevious
  , memberPreviousTrace
  , memberPageNext
  , memberPageTransition
  ) where

import Atlas.Internal (Atlas, atlasFolio, atlasPageElements)
import qualified AtlasExtent.Internal as Extent hiding
  (atlasCellOriginRankInsertion, cellContainsRankImage, cellOriginRankPreimageSound)
import Chain.Internal (Chain, chainPosition, chainOrderType)
import Consolidation.Ordered (OrderedConsolidation, orderedSource, orderedTarget,
  orderedApply, orderedPreimage, withConsolidationFunctions)
import Data.List.NonEmpty (NonEmpty (..))
import DatraOrdinal (Ordinal)
import Folio.Presentation (folioLengthData)
import Numeric.Natural (Natural)
import PageElements.Internal (folioPageOrderType, traceLookupPresent, pageElementsFolio)
import PageElements.Structure (PageElement (..))
import PageElements.TraceChain
  ( pageTraceContains, traceHead, pageTraceChain, pageTraceOrigin
  , previousTrace, previousPageTrace, pageTracePrevious, pageTraceNext, pageTraceTransition )

{-@ embed Natural as int @-}
{-@ invariant {value:Natural | value >= 0} @-}

-- | An existential Atlas retained as one member of a flattened sequence.
data AtlasSequenceMember where
  AtlasSequenceMember
    :: Atlas atlasScope paginationScope cellData origin final
    -> AtlasSequenceMember

{-@ reflect atlasSequenceMember @-}
atlasSequenceMember
  :: Atlas atlasScope paginationScope cellData origin final
  -> AtlasSequenceMember
atlasSequenceMember = AtlasSequenceMember

{-@ withAtlasSequenceMember :: member:AtlasSequenceMember
      -> (forall a s d o f. {owner:Atlas a s d o f | atlasSequenceMember owner == member} -> result)
      -> result @-}
{-@ ple withAtlasSequenceMember @-}
withAtlasSequenceMember
  :: AtlasSequenceMember
  -> (forall atlasScope paginationScope cellData origin final.
       Atlas atlasScope paginationScope cellData origin final
       -> result)
  -> result
withAtlasSequenceMember (AtlasSequenceMember valueAtlas) useAtlas =
  useAtlas valueAtlas

-- | Retain the selected existential member at its natural-number index.
{-@ reflect memberAt @-}
memberAt :: [AtlasSequenceMember] -> Natural -> Maybe AtlasSequenceMember
memberAt [] _ = Nothing
memberAt (member : rest) index
  | index == 0 = Just member
  | otherwise = memberAt rest (index - 1)

-- | Resolve an accepted native trace without losing its owning member.
-- ALIGN: SEQUENCE-MEMBER-TRACE-RESOLUTION.
{-@ withMemberTrace :: member:AtlasSequenceMember -> page:Natural
      -> positions:{[Ordinal] | memberPageContains member page positions}
      -> (forall a s d o f object.
           owner:Atlas a s d o f
           -> source:{PageElement s object | atlasSequenceMember owner == member
                && Extent.cellHasOrigin owner source
                && Extent.cellTraceValid owner source && pageElementPage source == page
                && pageElementPosition source == traceHead positions
                && pageElementTrace source == positions} -> result)
      -> {resolved:Maybe result | traceLookupPresent resolved} @-}
{-@ ple withMemberTrace @-}
withMemberTrace :: AtlasSequenceMember -> Natural -> [Ordinal]
  -> (forall a s d o f object. Atlas a s d o f -> PageElement s object -> result)
  -> Maybe result
withMemberTrace (AtlasSequenceMember owner) page positions useCell =
  Extent.withAtlasCellTrace owner page positions (\source -> useCell owner source)

-- ALIGN: SEQUENCE-MEMBER-PAGE-MEMBERSHIP.
{-@ reflect memberPageContains @-}
memberPageContains :: AtlasSequenceMember -> Natural -> [Ordinal] -> Bool
memberPageContains (AtlasSequenceMember valueAtlas) page positions =
  pageTraceContains (pageElementsFolio (atlasPageElements valueAtlas)) page positions

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

{-@ reflect memberPreviousTrace @-}
{-@ memberPreviousTrace :: member:AtlasSequenceMember -> page:Natural
      -> positions:{[Ordinal] | memberPageContains member (page + 1) positions}
      -> {result:[Ordinal] | memberPageContains member page result && result == previousTrace positions} @-}
memberPreviousTrace :: AtlasSequenceMember -> Natural -> [Ordinal] -> [Ordinal]
memberPreviousTrace member page positions =
  memberPagePrevious member page positions `seq` previousTrace positions

-- ALIGN: SEQUENCE-MEMBER-PAGE-NEXT.
{-@ reflect memberPageNext @-}
{-@ ple memberPageNext @-}
{-@ memberPageNext :: member:AtlasSequenceMember -> page:Natural
      -> positions:{[Ordinal] | memberPageContains member page positions}
      -> {result:[Ordinal] | memberPageContains member (page + 1) result
           && previousTrace result == positions} @-}
memberPageNext :: AtlasSequenceMember -> Natural -> [Ordinal] -> [Ordinal]
memberPageNext (AtlasSequenceMember valueAtlas) page = pageTraceNext (atlasFolio valueAtlas) page

-- ALIGN: SEQUENCE-MEMBER-PAGE-TRANSITION.
-- ALIGN: SEQUENCE-MEMBER-STORED-MAP.
-- ALIGN: SEQUENCE-MEMBER-STORED-PREIMAGE.
{-@ ple memberPageTransition @-}
{-@ memberPageTransition :: member:AtlasSequenceMember -> page:Natural
      -> source:{Chain {positions:[Ordinal] | memberPageContains member (page + 1) positions} |
           chainPosition source == traceHead}
      -> target:{Chain {positions:[Ordinal] | memberPageContains member page positions} |
           chainPosition target == traceHead}
      -> {result:OrderedConsolidation
           {positions:[Ordinal] | memberPageContains member (page + 1) positions}
           {positions:[Ordinal] | memberPageContains member page positions} |
             orderedSource result == source && orderedTarget result == target
             && orderedApply result == memberPreviousTrace member page
             && orderedPreimage result == memberPageNext member page} @-}
memberPageTransition :: AtlasSequenceMember -> Natural -> Chain [Ordinal] -> Chain [Ordinal]
  -> OrderedConsolidation [Ordinal] [Ordinal]
memberPageTransition member@(AtlasSequenceMember valueAtlas) page source target =
  let pages = atlasFolio valueAtlas
      mapping = pageTraceTransition pages page source target
  in withConsolidationFunctions (pageTraceContains pages (page + 1)) (pageTraceContains pages page)
       mapping (memberPreviousTrace member page) (memberPageNext member page)
       (\positions -> memberPreviousTrace member page positions `seq` previousPageTrace pages page positions `seq` ())
       (\positions -> memberPageNext member page positions `seq` ())

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
