{-# LANGUAGE CPP #-}
#include "../../../../LiquidPlugin.h"
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple-local" @-}
{-@ qualif SequenceAccepted(v:@(0), p:func(0, [@(0); bool])) { p v } @-}

-- | Assemble the sequence folio from checked native page transitions.
module AtlasSequence.Assembly
  ( atlasSequenceLength, atlasSequenceFolio, appendRemainingPages, appendRemainingLookup ) where

import AtlasSequence.Member (AtlasSequenceMember, memberLength, memberList, memberPageOrigin, memberPageContains)
import AtlasSequence.Page
  ( AtlasSequencePageCell (..), atlasSequencePageChain, sequencePageContains, sequencePagePosition, sequencePageTransition, headCell )
import Chain.Internal (chainPosition)
import Chain.Singleton (singletonChain)
import Data.List.NonEmpty (NonEmpty (..))
import Folio.Internal (Folio)
import Folio.Assembly (collapseToOrigin, extendPages, extendPagesLookup)
import Folio.Presentation (folioData, appendPageData, folioLengthData, lastPageData)
import Numeric.Natural (Natural)
import DatraOrdinal (Ordinal)
import PageElements.Internal (folioTraceLookup)

{-@ opaque-reflect memberList @-}

{-@ embed Natural as int @-}
{-@ invariant {value:Natural | value >= 0} @-}

-- ALIGN: SEQUENCE-NATIVE-DEPTH.
-- ALIGN: SEQUENCE-NATIVE-DEPTH-INTERPRETATION.
{-@ reflect sequenceDepth @-}
{-@ sequenceDepth :: members:[AtlasSequenceMember] -> {depth:Natural | len members > 0 => depth > 0} @-}
sequenceDepth :: [AtlasSequenceMember] -> Natural
sequenceDepth [] = 0
sequenceDepth (member : rest) = max (memberLength member) (sequenceDepth rest)

-- ALIGN: SEQUENCE-FOLIO-LENGTH.
-- ALIGN: SEQUENCE-FOLIO-LENGTH-INTERPRETATION.
{-@ reflect atlasSequenceLength @-}
{-@ atlasSequenceLength :: NonEmpty AtlasSequenceMember -> {count:Natural | count > 1} @-}
atlasSequenceLength :: NonEmpty AtlasSequenceMember -> Natural
atlasSequenceLength members = sequenceDepth (memberList members) + 1

-- ALIGN: SEQUENCE-FIRST-CELL.
{-@ firstSequenceCell :: members:NonEmpty AtlasSequenceMember
      -> {cell:AtlasSequencePageCell | sequencePageContains (memberList members) 0 cell} @-}
firstSequenceCell :: NonEmpty AtlasSequenceMember -> AtlasSequencePageCell
firstSequenceCell members = firstCellFromList (memberList members)

{-@ firstCellFromList :: members:{[AtlasSequenceMember] | len members > 0}
      -> {cell:AtlasSequencePageCell | sequencePageContains members 0 cell} @-}
firstCellFromList :: [AtlasSequenceMember] -> AtlasSequencePageCell
firstCellFromList [] = error "Empty sequence member list"
firstCellFromList members@(first : rest) =
  let cell = headCell (memberPageContains first 0) (sequencePageContains rest 0) (memberPageOrigin first)
  in sequencePageContains members 0 cell `seq` cell

-- ALIGN: SEQUENCE-FOLIO-PREFIX.
-- ALIGN: SEQUENCE-NATIVE-FOLIO-PREFIX.
{-@ reflect appendRemainingPages @-}
{-@ appendRemainingPages :: members:[AtlasSequenceMember]
      -> page:{Natural | page > 0} -> depth:{Natural | page <= depth}
      -> pages:{Folio () {cell:AtlasSequencePageCell | sequencePageContains members (page - 1) cell} |
           folioLengthData pages == page + 1
           && chainPosition (lastPageData pages) == sequencePagePosition members (page - 1)}
      -> {result:Folio () {cell:AtlasSequencePageCell | sequencePageContains members (depth - 1) cell} |
           folioLengthData result == depth + 1
           && chainPosition (lastPageData result) == sequencePagePosition members (depth - 1)}
      / [depth - page] @-}
appendRemainingPages :: [AtlasSequenceMember] -> Natural -> Natural
  -> Folio () AtlasSequencePageCell -> Folio () AtlasSequencePageCell
appendRemainingPages members page depth pages =
  extendPages (sequencePageContains members) (sequencePagePosition members)
    (sequencePageTransition members) page depth pages

-- ALIGN: SEQUENCE-PREFIX-LOOKUP-PRESERVED.
{-@ appendRemainingLookup :: members:[AtlasSequenceMember]
      -> page:{Natural | page > 0} -> depth:{Natural | page <= depth}
      -> pages:{Folio () {cell:AtlasSequencePageCell | sequencePageContains members (page - 1) cell} |
           folioLengthData pages == page + 1
           && chainPosition (lastPageData pages) == sequencePagePosition members (page - 1)}
      -> index:{Natural | index < folioLengthData pages} -> position:Ordinal
      -> {folioTraceLookup (appendRemainingPages members page depth pages) index position
           == folioTraceLookup pages index position} @-}
{-@ ple appendRemainingLookup @-}
appendRemainingLookup :: [AtlasSequenceMember] -> Natural -> Natural
  -> Folio () AtlasSequencePageCell -> Natural -> Ordinal -> ()
appendRemainingLookup members page depth pages index position =
  extendPagesLookup (sequencePageContains members) (sequencePagePosition members)
    (sequencePageTransition members) page depth pages index position

-- ALIGN: SEQUENCE-COLLAPSE-ORIGIN.
-- ALIGN: SEQUENCE-FOLIO.
-- ALIGN: SEQUENCE-NATIVE-FOLIO.
-- ALIGN: SEQUENCE-NATIVE-FOLIO-INTERPRETATION.
-- ALIGN: SEQUENCE-PADDED-PAGE-RESOLUTION.
-- ALIGN: SEQUENCE-FINITE-INDEX-INTERPRETATION.
-- ALIGN: SEQUENCE-FINITE-INTERVAL-INTERPRETATION.
{-@ atlasSequenceFolio :: members:NonEmpty AtlasSequenceMember
      -> {result:Folio () {cell:AtlasSequencePageCell |
           sequencePageContains (memberList members) (atlasSequenceLength members - 2) cell} |
             folioLengthData result == atlasSequenceLength members} @-}
atlasSequenceFolio :: NonEmpty AtlasSequenceMember -> Folio () AtlasSequencePageCell
atlasSequenceFolio members =
  let entries = memberList members
      depth = atlasSequenceLength members - 1
      origin = folioData singletonChain () (\() -> ())
      firstChain = atlasSequencePageChain entries 0
      firstTransition = collapseToOrigin (sequencePageContains entries 0)
        firstChain (lastPageData origin) (firstSequenceCell members)
      firstPage = appendPageData origin firstChain firstTransition
  in appendRemainingPages entries 1 depth firstPage
