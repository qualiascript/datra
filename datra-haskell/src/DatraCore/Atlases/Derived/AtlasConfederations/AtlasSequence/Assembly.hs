{-# LANGUAGE CPP #-}
#include "../../../../LiquidPlugin.h"
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple-local" @-}
{-@ qualif SequenceAccepted(v:@(0), p:func(0, [@(0); bool])) { p v } @-}

-- | Assemble the sequence folio from checked native page transitions.
module AtlasSequence.Assembly
  ( atlasSequenceLength, atlasSequenceFolio, atlasSequencePrefix, atlasSequencePrefixLookup, atlasSequencePageLookup, atlasSequenceCellLookup, atlasSequencePrefixTrace, atlasSequencePrefixOriginTrace
  , appendRemainingPages, appendRemainingLookup ) where

import AtlasSequence.Member (AtlasSequenceMember, memberLength, memberList, memberPageOrigin, memberPageContains)
import AtlasSequence.Page
  ( AtlasSequencePageCell (..), atlasSequencePageChain, sequencePageContains, sequencePagePosition, sequencePageTransition, previousSequenceCell, headCell )
import Chain (chainPosition)
import Data.List.NonEmpty (NonEmpty (..))
import Folio (Folio)
import Folio.Assembly (OriginExtension, extendOrigin, originExtensionPages, originExtensionTrace, firstPageTrace, extendPages, extendPagesLookup, extendPagesThroughLookup, extendPagesFinalTrace)
import Folio.Presentation (folioLengthData, lastPageData)
import Numeric.Natural (Natural)
import DatraOrdinal (Ordinal)
import PageElements (folioTraceLookup, genuinePageElementTrace, finalPageTraceLookup, prependCopies)

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

-- | The first member supplies the checked origin choice for every prefix.
{-@ opaque-reflect firstSequenceSeed @-}
{-@ firstSequenceSeed :: members:NonEmpty AtlasSequenceMember
      -> {result:OriginExtension {cell:AtlasSequencePageCell | sequencePageContains (memberList members) 0 cell} |
           chainPosition (lastPageData (originExtensionPages result)) == sequencePagePosition (memberList members) 0} @-}
firstSequenceSeed :: NonEmpty AtlasSequenceMember -> OriginExtension AtlasSequencePageCell
firstSequenceSeed members =
  let entries = memberList members
  in extendOrigin (sequencePageContains entries 0) (atlasSequencePageChain entries 0) (firstSequenceCell members)

{-@ reflect firstSequencePage @-}
{-@ firstSequencePage :: members:NonEmpty AtlasSequenceMember
      -> {result:Folio () {cell:AtlasSequencePageCell | sequencePageContains (memberList members) 0 cell} |
           folioLengthData result == 2
           && chainPosition (lastPageData result) == sequencePagePosition (memberList members) 0} @-}
firstSequencePage :: NonEmpty AtlasSequenceMember -> Folio () AtlasSequencePageCell
firstSequencePage members = originExtensionPages (firstSequenceSeed members)

-- ALIGN: SEQUENCE-PREFIX-TRACE-ORIGIN.
{-@ atlasSequencePrefixOriginTrace :: members:NonEmpty AtlasSequenceMember
      -> cell:{AtlasSequencePageCell | sequencePageContains (memberList members) 0 cell}
      -> {genuinePageElementTrace (atlasSequencePrefix members 1) cell
           == firstPageTrace (sequencePagePosition (memberList members) 0 cell)} @-}
{-@ ple atlasSequencePrefixOriginTrace @-}
atlasSequencePrefixOriginTrace :: NonEmpty AtlasSequenceMember -> AtlasSequencePageCell -> ()
atlasSequencePrefixOriginTrace members cell = originExtensionTrace (firstSequenceSeed members) cell

-- ALIGN: SEQUENCE-CONSTRUCTED-PREFIX.
{-@ reflect atlasSequencePrefix @-}
{-@ atlasSequencePrefix :: members:NonEmpty AtlasSequenceMember -> depth:{Natural | depth > 0}
      -> {result:Folio () {cell:AtlasSequencePageCell | sequencePageContains (memberList members) (depth - 1) cell} |
           folioLengthData result == depth + 1
           && chainPosition (lastPageData result) == sequencePagePosition (memberList members) (depth - 1)} @-}
atlasSequencePrefix :: NonEmpty AtlasSequenceMember -> Natural -> Folio () AtlasSequencePageCell
atlasSequencePrefix members depth = appendRemainingPages (memberList members) 1 depth (firstSequencePage members)

-- ALIGN: SEQUENCE-CONSTRUCTED-PREFIX-LOOKUP.
{-@ atlasSequencePrefixLookup :: members:NonEmpty AtlasSequenceMember
      -> middle:{Natural | middle > 0} -> depth:{Natural | middle <= depth}
      -> index:{Natural | index <= middle} -> position:Ordinal
      -> {folioTraceLookup (atlasSequencePrefix members depth) index position
           == folioTraceLookup (atlasSequencePrefix members middle) index position} @-}
{-@ ple atlasSequencePrefixLookup @-}
atlasSequencePrefixLookup :: NonEmpty AtlasSequenceMember -> Natural -> Natural -> Natural -> Ordinal -> ()
atlasSequencePrefixLookup members middle depth index position =
  let entries = memberList members
  in extendPagesThroughLookup (sequencePageContains entries) (sequencePagePosition entries)
    (sequencePageTransition entries) 1 middle depth (firstSequencePage members) index position

-- ALIGN: SEQUENCE-COLLAPSE-ORIGIN.
-- ALIGN: SEQUENCE-FOLIO.
-- ALIGN: SEQUENCE-NATIVE-FOLIO.
-- ALIGN: SEQUENCE-NATIVE-FOLIO-INTERPRETATION.
-- ALIGN: SEQUENCE-PADDED-PAGE-RESOLUTION.
-- ALIGN: SEQUENCE-FINITE-INDEX-INTERPRETATION.
-- ALIGN: SEQUENCE-FINITE-INTERVAL-INTERPRETATION.
{-@ reflect atlasSequenceFolio @-}
{-@ atlasSequenceFolio :: members:NonEmpty AtlasSequenceMember
      -> {result:Folio () {cell:AtlasSequencePageCell |
           sequencePageContains (memberList members) (atlasSequenceLength members - 2) cell} |
             folioLengthData result == atlasSequenceLength members} @-}
atlasSequenceFolio :: NonEmpty AtlasSequenceMember -> Folio () AtlasSequencePageCell
atlasSequenceFolio members = atlasSequencePrefix members (atlasSequenceLength members - 1)

-- ALIGN: SEQUENCE-GENUINE-PAGE-LOOKUP.
{-@ atlasSequencePageLookup :: members:NonEmpty AtlasSequenceMember
      -> page:{Natural | page > 0 && page < atlasSequenceLength members} -> position:Ordinal
      -> {folioTraceLookup (atlasSequenceFolio members) page position
           == folioTraceLookup (atlasSequencePrefix members page) page position} @-}
{-@ ple atlasSequencePageLookup @-}
atlasSequencePageLookup :: NonEmpty AtlasSequenceMember -> Natural -> Ordinal -> ()
atlasSequencePageLookup members page position =
  atlasSequencePrefixLookup members page (atlasSequenceLength members - 1) page position

-- ALIGN: SEQUENCE-GENUINE-CELL-LOOKUP.
{-@ atlasSequenceCellLookup :: members:NonEmpty AtlasSequenceMember
      -> page:{Natural | page > 0 && page < atlasSequenceLength members}
      -> cell:{AtlasSequencePageCell | sequencePageContains (memberList members) (page - 1) cell}
      -> {folioTraceLookup (atlasSequenceFolio members) page
             (sequencePagePosition (memberList members) (page - 1) cell)
           == Just (genuinePageElementTrace (atlasSequencePrefix members page) cell)} @-}
{-@ ple atlasSequenceCellLookup @-}
atlasSequenceCellLookup :: NonEmpty AtlasSequenceMember -> Natural -> AtlasSequencePageCell -> ()
atlasSequenceCellLookup members page cell =
  atlasSequencePageLookup members page (sequencePagePosition (memberList members) (page - 1) cell) `seq`
    finalPageTraceLookup (atlasSequencePrefix members page) cell

-- | Follow the last native sequence map into the preceding constructed prefix.
-- ALIGN: SEQUENCE-PREFIX-TRACE-STEP.
{-@ atlasSequencePrefixTrace :: members:NonEmpty AtlasSequenceMember
      -> depth:{Natural | depth > 0}
      -> cell:{AtlasSequencePageCell | sequencePageContains (memberList members) depth cell}
      -> {genuinePageElementTrace (atlasSequencePrefix members (depth + 1)) cell
           == prependCopies 1 (sequencePagePosition (memberList members) depth cell)
                (genuinePageElementTrace (atlasSequencePrefix members depth)
                  (previousSequenceCell (memberList members) depth cell))} @-}
{-@ ple atlasSequencePrefixTrace @-}
atlasSequencePrefixTrace :: NonEmpty AtlasSequenceMember -> Natural -> AtlasSequencePageCell -> ()
atlasSequencePrefixTrace members depth cell =
  let entries = memberList members
  in sequencePageTransition entries depth (lastPageData (atlasSequencePrefix members depth)) `seq`
    extendPagesFinalTrace (sequencePageContains entries) (sequencePagePosition entries)
      (sequencePageTransition entries) 1 depth (firstSequencePage members) cell
