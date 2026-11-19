{-# LANGUAGE CPP #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}

#include "../../../../LiquidPlugin.h"
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple-local" @-}

-- | Member selection and cell resolution with checked origin evidence.
module AtlasSequence.Resolution
  ( AtlasSequenceMember
  , atlasSequenceMember
  , withAtlasSequenceMember
  , withMemberAt
  , withSequenceNativeCell
  , sequenceSourceCell
  , sequenceCellContains
  ) where

import Atlas.Internal (Atlas)
import qualified AtlasExtent.Internal as Extent hiding
  (atlasCellOriginRankInsertion, cellContainsRankImage, cellOriginRankPreimageSound)
import AtlasSequence.Member (AtlasSequenceMember, atlasSequenceMember, withAtlasSequenceMember, memberAt, memberList, withMemberTrace)
import AtlasSequence.Page (AtlasSequencePageCell (..), sequencePageContains, sequenceCellMember, sequencePagePosition, atlasSequencePageChain)
import AtlasSequence.Data (AtlasSequenceDatum (..))
import Chain (chainIndex, chainObjectAt)
import Data.List.NonEmpty (NonEmpty, toList)
import Numeric.Natural (Natural)
-- Resolve the polymorphic success predicate in AtlasExtent's lookup contracts.
import PageElements.Internal (traceLookupPresent)
import PageElements.Structure (PageElement (..))

{-@ embed Natural as int @-}
{-@ invariant {value:Natural | value >= 0} @-}

withMemberAt
  :: [AtlasSequenceMember]
  -> Natural
  -> (forall atlasScope paginationScope cellData origin final.
       Atlas atlasScope paginationScope cellData origin final
       -> result)
  -> Maybe result
withMemberAt members index useAtlas =
  case memberAt members index of
    Nothing -> Nothing
    Just member -> Just (withAtlasSequenceMember member (\owner -> useAtlas owner))

-- | Consume the selected member's exact native trace from the sequence chain.
-- ALIGN: SEQUENCE-MEMBER-INDEX-BOUND.
-- ALIGN: SEQUENCE-NATIVE-CELL-RESOLUTION.
-- ALIGN: SEQUENCE-NATIVE-CELL-RESOLUTION-INTERPRETATION.
{-@ ple withSequenceNativeCell @-}
{-@ withSequenceNativeCell :: members:[AtlasSequenceMember] -> page:Natural
      -> cell:{AtlasSequencePageCell | sequencePageContains members page cell}
      -> (forall a s d o f object.
           index:{Natural | index < len members}
           -> owner:Atlas a s d o f
           -> source:{PageElement s object | memberAt members index == Just (atlasSequenceMember owner)
                && Extent.cellHasOrigin owner source
                && Extent.cellTraceValid owner source && pageElementPage source == page
                && cell == AtlasSequencePageCell index (pageElementTrace source)} -> result)
      -> {resolved:Maybe result | traceLookupPresent resolved} / [len members] @-}
withSequenceNativeCell :: forall result. [AtlasSequenceMember] -> Natural -> AtlasSequencePageCell
  -> (forall a s d o f object. Natural -> Atlas a s d o f -> PageElement s object -> result)
  -> Maybe result
withSequenceNativeCell members page cell@(AtlasSequencePageCell index positions) useCell =
  let member = sequenceCellMember members page cell
      {-@ resolve :: forall a s d o f object. selected:{AtlasSequenceMember |
                 memberAt members index == Just selected && index < len members}
            -> owner:Atlas a s d o f
            -> source:{PageElement s object | atlasSequenceMember owner == selected
                 && Extent.cellHasOrigin owner source && Extent.cellTraceValid owner source
                 && pageElementPage source == page && pageElementTrace source == positions} -> result @-}
      resolve :: forall a s d o f object. AtlasSequenceMember -> Atlas a s d o f -> PageElement s object -> result
      resolve _ owner source = useCell index owner source
  in withMemberTrace member page positions (resolve member)

-- ALIGN: SEQUENCE-COMPONENT-DECODER.
-- ALIGN: SEQUENCE-SOURCE-RESOLUTION.
-- ALIGN: SEQUENCE-SOURCE-RESOLUTION-EQUIV.
-- ALIGN: SEQUENCE-NORMALIZED-RESOLUTION.
{-@ ple sequenceSourceCell @-}
{-@ sequenceSourceCell
      :: members:NonEmpty AtlasSequenceMember
      -> occurrence:PageElement mergeScope object
      -> result
      -> (forall atlasScope scope cellData origin final sourceObject.
            index:{Natural | index < len (memberList members)}
            -> valueAtlas:Atlas atlasScope scope cellData origin final
            -> source:{PageElement scope sourceObject |
                 memberAt (memberList members) index == Just (atlasSequenceMember valueAtlas)
                 && Extent.cellHasOrigin valueAtlas source
                 && Extent.cellTraceValid valueAtlas source
                 && pageElementPage source + 1 == pageElementPage occurrence
                 && sequencePageContains (memberList members) (pageElementPage source)
                      (AtlasSequencePageCell index (pageElementTrace source))
                 && sequencePagePosition (memberList members) (pageElementPage source)
                      (AtlasSequencePageCell index (pageElementTrace source)) == pageElementPosition occurrence}
            -> result)
      -> Maybe result @-}
sequenceSourceCell
  :: NonEmpty AtlasSequenceMember
  -> PageElement mergeScope object
  -> result
  -> (forall atlasScope scope cellData origin final sourceObject.
        Natural -> Atlas atlasScope scope cellData origin final
        -> PageElement scope sourceObject -> result)
  -> Maybe result
sequenceSourceCell members occurrence atOrigin useMember
  | pageElementPage occurrence == 0 = Just atOrigin
  | otherwise =
      let sourcePage = pageElementPage occurrence - 1
          position = pageElementPosition occurrence
      in case chainIndex (atlasSequencePageChain (memberList members) sourcePage) position of
          Nothing -> Nothing
          Just selected -> withSequenceNativeCell (memberList members) sourcePage (chainObjectAt selected) (\index owner source -> useMember index owner source)

-- ALIGN: SEQUENCE-CELL-MEMBERSHIP.
-- ALIGN: SEQUENCE-CELL-ROOT-IMAGE.
-- ALIGN: SEQUENCE-RESOLVED-CELL.
-- ALIGN: SEQUENCE-FINITE-MEMBERSHIP.
sequenceCellContains
  :: NonEmpty AtlasSequenceMember
  -> PageElement mergeScope object
  -> AtlasSequenceDatum datumObject
  -> Bool
sequenceCellContains members occurrence (AtlasSequenceDatum datumMember valueRank) =
  case sequenceSourceCell members occurrence
    (case withMemberAt (toList members) datumMember (\valueAtlas -> Extent.extentContainsRank valueAtlas valueRank) of
      Nothing -> False
      Just contains -> contains)
    (\sourceMember valueAtlas source ->
      sourceMember == datumMember && Extent.cellContainsRank valueAtlas source valueRank) of
    Nothing -> False
    Just contains -> contains
