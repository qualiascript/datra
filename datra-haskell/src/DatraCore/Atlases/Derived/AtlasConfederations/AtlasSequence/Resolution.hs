{-# LANGUAGE CPP #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}

#include "../../../../LiquidPlugin.h"
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}
{-@ LIQUID "--higherorder" @-}

-- | Member selection and cell resolution with checked origin evidence.
module AtlasSequence.Resolution
  ( AtlasSequenceMember
  , atlasSequenceMember
  , withAtlasSequenceMember
  , withMemberAt
  , withMemberAtPosition
  , sequenceSourceCell
  , sequenceCellContains
  ) where

import Atlas.Internal (Atlas, atlasFolio)
import qualified AtlasExtent.Internal as Extent hiding
  (atlasCellOriginRankInsertion, cellContainsRankImage, cellOriginRankPreimageSound)
import AtlasSequence.LiquidInternal (AtlasSequenceDatum (..))
import Chain (chainOrderType)
import Data.List.NonEmpty (NonEmpty, toList)
import DatraOrdinal (Ordinal, ordinalLT, subtractOrdinal)
import Folio (withPageAt)
import Numeric.Natural (Natural)
import PageElements.LiquidInternal (PageElement (..))

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

withMemberAt
  :: [AtlasSequenceMember]
  -> Natural
  -> (forall atlasScope paginationScope cellData origin final.
       Atlas atlasScope paginationScope cellData origin final
       -> result)
  -> Maybe result
withMemberAt [] _ _ = Nothing
withMemberAt (member : _) 0 useAtlas =
  Just (withAtlasSequenceMember member useAtlas)
withMemberAt (_ : members) memberIndex useAtlas =
  withMemberAt members (memberIndex - 1) useAtlas

-- ALIGN: SEQUENCE-MEMBER-POSITION-RESOLVER.
-- ALIGN: SEQUENCE-MEMBER-POSITION-ROUNDTRIP.
-- ALIGN: SEQUENCE-MEMBER-POSITION-SOUND.
-- ALIGN: SEQUENCE-COMPONENT-DECODER.
-- ALIGN: SEQUENCE-MEMBER-INDEX-BOUND.
{-@ withMemberAtPosition
      :: members:[AtlasSequenceMember] -> Natural -> Ordinal
      -> (forall atlasScope paginationScope cellData origin final.
            memberIndex:{Natural | memberIndex < len members}
            -> Atlas atlasScope paginationScope cellData origin final
            -> Ordinal -> Maybe result)
      -> Maybe result @-}
withMemberAtPosition
  :: forall result.
     [AtlasSequenceMember]
  -> Natural
  -> Ordinal
  -> (forall atlasScope paginationScope cellData origin final.
       Natural
       -> Atlas atlasScope paginationScope cellData origin final
       -> Ordinal
       -> Maybe result)
  -> Maybe result
withMemberAtPosition = go 0
  where
    {-@ go :: offset:Natural -> rest:[AtlasSequenceMember] -> Natural -> Ordinal
          -> (forall atlasScope paginationScope cellData origin final.
                memberIndex:{Natural | offset <= memberIndex && memberIndex < offset + len rest}
                -> Atlas atlasScope paginationScope cellData origin final
                -> Ordinal -> Maybe result)
          -> Maybe result / [len rest] @-}
    go
      :: Natural
      -> [AtlasSequenceMember]
      -> Natural
      -> Ordinal
      -> (forall atlasScope paginationScope cellData origin final.
           Natural
           -> Atlas atlasScope paginationScope cellData origin final
           -> Ordinal
           -> Maybe result)
      -> Maybe result
    go _ [] _ _ _ = Nothing
    go memberIndex (member : members) pageNumber position usePosition =
      withAtlasSequenceMember member $ \valueAtlas ->
        withPageAt (atlasFolio valueAtlas) pageNumber $ \sourcePage ->
          let sourceOrder = chainOrderType sourcePage
          in if ordinalLT position sourceOrder
              then usePosition memberIndex valueAtlas position
              else do
                remaining <- subtractOrdinal sourceOrder position
                go
                  (memberIndex + 1)
                  members
                  pageNumber
                  remaining
                  usePosition

-- ALIGN: SEQUENCE-SOURCE-RESOLUTION.
-- ALIGN: SEQUENCE-SOURCE-RESOLUTION-EQUIV.
-- ALIGN: SEQUENCE-NORMALIZED-RESOLUTION.
{-@ sequenceSourceCell
      :: NonEmpty AtlasSequenceMember
      -> PageElement mergeScope object
      -> result
      -> (forall atlasScope scope cellData origin final sourceObject.
            Natural -> valueAtlas:Atlas atlasScope scope cellData origin final
            -> source:{PageElement scope sourceObject | Extent.cellHasOrigin valueAtlas source}
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
      in withMemberAtPosition (toList members) sourcePage position $
          \memberIndex valueAtlas sourcePosition ->
            Extent.withAtlasCellAt valueAtlas sourcePage sourcePosition (useMember memberIndex valueAtlas)

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
