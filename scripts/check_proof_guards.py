#!/usr/bin/env python3
"""Require LiquidHaskell to reject false Atlas, coverage, and inverse laws.

Each check compiles an isolated copy of the production module using the built
library's interfaces. No failed proof or expected-failure directive enters the
library, and the temporary sources and compiler artifacts are always removed.
Run after `make -C datra-haskell verify-liquid`.
"""
import argparse
import json
import os
import re
from pathlib import Path
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[1]
HASKELL = ROOT / "datra-haskell"
SOURCE = HASKELL / "src/DatraCore/DataTransformations/DataTransformations/DataTransformation/LiquidInternal.hs"
GUARDS = {
    "inhabited equality witnesses cannot prove False": """
{-@ proofGuard :: AtlasEquality a b -> { proof:() | False } @-}
proofGuard :: AtlasEquality a b -> ()
proofGuard (AtlasEquality Refl) = ()
""",
    "identity and composite constructors remain distinct": """
{-@
proofGuard :: () -> { proof:() |
  presheafIdentity == CompositeAtlasHom presheafIdentity presheafIdentity }
@-}
proofGuard :: () -> ()
proofGuard () = ()
""",
    "symbolic composition does not acquire a false left unit": """
{-@
proofGuard :: arrow:AtlasHom source target -> { proof:() |
  presheafCompose presheafIdentity arrow == arrow }
@-}
proofGuard :: AtlasHom source target -> ()
proofGuard (IdentityAtlasHom (AtlasEquality Refl)) = ()
proofGuard (PrimitiveAtlasHom _ _ _) = ()
proofGuard (CompositeAtlasHom _ _) = ()
""",
}

CHAIN_SOURCE = HASKELL / "src/DatraCore/Atlases/Core/Chain/Internal.hs"
CHAIN_GUARDS = {
    "chain reindexing rejects a constant carrier equivalence": """
proofGuard :: Chain Natural
proofGuard = reindexChain (const True) spine (const 0) (const 0) (const ()) (const ())
""",
}

PAGE_TRACE_SOURCE = HASKELL / "src/DatraCore/Atlases/Core/PageElements/TraceChain.hs"
PAGE_TRACE_GUARDS = {
    "native trace chains cannot widen their accepted carrier": """
{-@ proofGuard :: Folio origin final -> Natural -> Chain [Ordinal] @-}
proofGuard :: Folio origin final -> Natural -> Chain [Ordinal]
proofGuard = pageTraceChain
""",
}

MERGE_PAGE_SOURCE = HASKELL / "src/DatraCore/Atlases/Derived/AtlasConfederations/AtlasMerge/Page.hs"
MERGE_PAGE_GUARDS = {
    "merge page chains cannot accept arbitrary component traces": """
{-@ proofGuard :: Atlas la ls ld lo lf -> Atlas ra rs rd ro rf -> Natural -> Chain AtlasMergePageCell @-}
proofGuard :: Atlas la ls ld lo lf -> Atlas ra rs rd ro rf -> Natural -> Chain AtlasMergePageCell
proofGuard = atlasMergePageChain
""",
}


STABLE_SOURCE = HASKELL / "src/DatraCore/Atlases/Derived/AtlasTransposals/StableAtlasTransversal/Internal.hs"
STABLE_GUARDS = {
    "stable transversals reject an inverse that drops every image": """
{-@
proofGuard
  :: sourceAtlas:Atlas sa ss sd so sf
  -> targetAtlas:Atlas ta ts td to tf
  -> transversal:AtlasTransversal (AtlasObject sa ss sd) (AtlasObject ta ts td)
  -> { proof:() | stableOriginPreserved sourceAtlas targetAtlas transversal }
  -> StableAtlasTransversal (AtlasObject sa ss sd) (AtlasObject ta ts td)
@-}
proofGuard
  :: Atlas sa ss sd so sf
  -> Atlas ta ts td to tf
  -> AtlasTransversal (AtlasObject sa ss sd) (AtlasObject ta ts td)
  -> ()
  -> StableAtlasTransversal (AtlasObject sa ss sd) (AtlasObject ta ts td)
proofGuard sourceAtlas targetAtlas transversal originProof =
  stableAtlasTransversal sourceAtlas targetAtlas transversal originProof
    (const Nothing) (const ())
""",
}


DOMINC_SOURCE = HASKELL / "src/DatraCore/Atlases/Derived/Coalitions/DomanialInclusion/LiquidInternal.hs"
DOMINC_GUARDS = {
    "coalition components reject an inverse that drops every image": """
proofGuard
  :: Atlas atlasScope scope cellData origin final
  -> PageElement scope object
  -> (a -> CoalitionElement (AtlasObject atlasScope scope cellData))
  -> DomanialInsertion (DominionCellData a sourceObject) (cellData object)
proofGuard targetAtlas targetOccurrence forward =
  coalitionComponentInsertion targetAtlas targetOccurrence forward
    (const Nothing) (const ())
""",
}


TRANSVERSAL_SOURCE = HASKELL / "src/DatraCore/Atlases/Derived/AtlasTransposals/AtlasTransversal/Internal.hs"
TRANSVERSAL_GUARDS = {
    "transversals reject coverage evidence for the wrong image": """
{-@
proofGuard
  :: sourceAtlas:Atlas sa ss sd so sf
  -> targetAtlas:Atlas ta ts td to tf
  -> ordered:OrderedAtlasTransposal (AtlasObject sa ss sd) (AtlasObject ta ts td)
  -> badCoverage:(covered:AtlasCoveredPageElement (AtlasObject sa ss sd)
       -> {w:AtlasCoverageWitness (AtlasObject ta ts td) |
         not (transversalImageCovered sourceAtlas targetAtlas ordered covered w)})
  -> AtlasTransversal (AtlasObject sa ss sd) (AtlasObject ta ts td)
@-}
proofGuard
  :: Atlas sa ss sd so sf
  -> Atlas ta ts td to tf
  -> OrderedAtlasTransposal (AtlasObject sa ss sd) (AtlasObject ta ts td)
  -> (AtlasCoveredPageElement (AtlasObject sa ss sd)
       -> AtlasCoverageWitness (AtlasObject ta ts td))
  -> AtlasTransversal (AtlasObject sa ss sd) (AtlasObject ta ts td)
proofGuard sourceAtlas targetAtlas ordered badCoverage =
  atlasTransversal sourceAtlas targetAtlas ordered badCoverage
""",
}


CHARTER_SOURCE = HASKELL / "src/DatraCore/Atlases/Derived/Cartography/Charter/LiquidInternal.hs"
CHARTER_GUARDS = {
    "charted components reject a source inverse that drops every covered value": """
proofGuard
  :: DomanialInsertion (AtlasObjectCellData source sourceObject) (AtlasObjectCellData target targetObject)
  -> DomanialInsertion (ChartedCellData source sourceObject) (ChartedCellData target targetObject)
proofGuard original = chartMapInsertion original (const Nothing) (const ())
""",
    "chart counits reject an inverse that drops every covered value": """
proofGuard
  :: DomanialInsertion (ChartedCellData atlasObject object) (AtlasObjectCellData atlasObject object)
proofGuard = chartCounitInsertion (const Nothing) (const ())
""",
    "charted data rejects a witness that does not cover the datum": """
{-@
proofGuard
  :: valueAtlas:Atlas atlasScope scope cellData origin final
  -> occurrence:PageElement scope object
  -> datum:cellData object
  -> witness:{w:AtlasCoverageWitness (AtlasObject atlasScope scope cellData) |
       not (coverageWitnessCovers valueAtlas occurrence datum w)}
  -> ChartedCellData (AtlasObject atlasScope scope cellData) object
@-}
proofGuard
  :: Atlas atlasScope scope cellData origin final
  -> PageElement scope object
  -> cellData object
  -> AtlasCoverageWitness (AtlasObject atlasScope scope cellData)
  -> ChartedCellData (AtlasObject atlasScope scope cellData) object
proofGuard valueAtlas occurrence datum witness =
  chartCellData valueAtlas occurrence datum witness ()
""",
}


RANK_IMAGE_SOURCE = HASKELL / "src/DatraCore/Atlases/Core/DomanialInsertion/LiquidInternal.hs"
RANK_IMAGE_GUARDS = {
    "unranking does not certify a rank outside the Dominion image": """
{-@
proofGuard
  :: valueDominion:Dominion a
  -> valueRank:Natural
  -> {value:a | unrank valueDominion valueRank == Just value}
  -> {proof:() | rank valueDominion value == valueRank}
@-}
proofGuard :: Dominion a -> Natural -> a -> ()
proofGuard _ _ _ = ()
""",
    "a partial inverse does not certify a candidate outside the insertion image": """
{-@
proofGuard
  :: valueDominion:Dominion b
  -> insertion:DomanialInsertion a b
  -> root:b
  -> {value:a | preimage insertion root == Just value}
  -> {proof:() | rankImage valueDominion insertion value == rank valueDominion root}
@-}
proofGuard :: Dominion b -> DomanialInsertion a b -> b -> a -> ()
proofGuard _ _ _ _ = ()
""",
}


MERGE_SOURCE = HASKELL / "src/DatraCore/Atlases/Derived/AtlasConfederations/AtlasMerge/LiquidInternal.hs"
MERGE_GUARDS = {
    "merge unranking requires the datum's cell membership": """
{-@
proofGuard
  :: contains:(AtlasMergeDatum object -> Bool)
  -> datum:AtlasMergeDatum object
  -> { mergeDatumLookup contains (atlasMergeDatumRank datum) == Just datum }
@-}
proofGuard :: (AtlasMergeDatum object -> Bool) -> AtlasMergeDatum object -> ()
proofGuard contains datum = mergeDatumLookupRoundTrip contains datum
""",
    "merge insertions require target membership preservation": """
proofGuard :: AtlasMergeDatum source -> AtlasMergeDatum target
proofGuard = mergeDatumMap (const True) (const False) (const ())
""",
}

SEQUENCE_SOURCE = HASKELL / "src/DatraCore/Atlases/Derived/AtlasConfederations/AtlasSequence/LiquidInternal.hs"
SEQUENCE_GUARDS = {
    "sequence decoding requires a positive member count": """
proofGuard :: Natural -> AtlasSequenceDatum object
proofGuard = decodeSequenceDatum 0
""",
    "sequence roundtrips require a bounded member index": """
proofGuard :: Natural -> ()
proofGuard valueRank = decodeSequenceDatumRank 3 (AtlasSequenceDatum 3 valueRank)
""",
    "sequence unranking requires cell membership": """
proofGuard :: Natural -> ()
proofGuard valueRank = sequenceDatumLookupRoundTrip 3 (const False) (AtlasSequenceDatum 0 valueRank)
""",
    "sequence insertions require target membership preservation": """
proofGuard :: AtlasSequenceDatum source -> AtlasSequenceDatum target
proofGuard = sequenceDatumMap (const True) (const False) (const ())
""",
}


EXTENT_SOURCE = HASKELL / "src/DatraCore/Atlases/Derived/AtlasDerived/AtlasExtent/Internal.hs"
EXTENT_GUARDS = {
    "cell lookup cannot claim another Atlas transport trace": """
{-@ proofGuard :: Atlas a s d o f -> Atlas a s d o f -> Natural -> Ordinal
      -> Maybe ({answer:Bool | answer}) @-}
proofGuard :: Atlas a s d o f -> Atlas a s d o f -> Natural -> Ordinal -> Maybe Bool
proofGuard owner other page position =
  withAtlasCellAt owner page position (\\source -> cellTraceValid other source)
""",
    "cell membership disjointness requires distinct positions": """
{-@ proofGuard :: valueAtlas:Atlas a s d o f
      -> cell:{PageElement s object | cellHasOrigin valueAtlas cell && cellTraceValid valueAtlas cell
           && pageElementPage cell < Atlas.atlasCardinality valueAtlas}
      -> valueRank:{Natural | cellContainsRank valueAtlas cell valueRank}
      -> {not (cellContainsRank valueAtlas cell valueRank)} @-}
proofGuard :: Atlas a s d o f -> PageElement s object -> Natural -> ()
proofGuard valueAtlas cell valueRank = cellContainsRankDisjoint valueAtlas cell cell valueRank
""",
    "extent membership requires an accepted cell rank": """
{-@ proofGuard :: valueAtlas:Atlas a s d o f
      -> cell:{PageElement s object | cellHasOrigin valueAtlas cell && cellTraceValid valueAtlas cell}
      -> valueRank:Natural
      -> {extentContainsRank valueAtlas valueRank} @-}
proofGuard :: Atlas a s d o f -> PageElement s object -> Natural -> ()
proofGuard = cellContainsRankInExtent
""",
    "transport membership requires an accepted source rank": """
{-@ proofGuard :: valueAtlas:Atlas a s d o f
      -> arrow:{PageElementArrow s source target |
           cellHasOrigin valueAtlas (arrowSource arrow)
           && cellTraceValid valueAtlas (arrowSource arrow)
           && cellHasOrigin valueAtlas (arrowTarget arrow)
           && cellTraceValid valueAtlas (arrowTarget arrow)}
      -> valueRank:Natural
      -> {cellContainsRank valueAtlas (arrowTarget arrow) valueRank} @-}
proofGuard :: Atlas a s d o f -> PageElementArrow s source target -> Natural -> ()
proofGuard = cellContainsRankPreserved
""",
    "cell lookup cannot switch to an unrelated Atlas origin": """
{-@ proofGuard :: Atlas atlasScope scope cellData origin final
      -> Atlas atlasScope scope cellData origin final
      -> Natural -> Ordinal -> Natural -> Maybe Bool @-}
proofGuard :: Atlas atlasScope scope cellData origin final
  -> Atlas atlasScope scope cellData origin final
  -> Natural -> Ordinal -> Natural -> Maybe Bool
proofGuard owner other page position valueRank =
  withAtlasCellAt owner page position (\\source -> cellContainsRank other source valueRank)
""",
    "extent origin insertions require a valid origin arrow": """
{-@ proofGuard
      :: valueAtlas:Atlas atlasScope scope cellData origin final
      -> source:PageElement scope object
      -> DomanialInsertion ({datum:cellData object | atlasAcceptsDatum valueAtlas source datum}) Natural @-}
proofGuard
  :: Atlas atlasScope scope cellData origin final
  -> PageElement scope object -> DomanialInsertion (cellData object) Natural
proofGuard = atlasCellOriginRankInsertion
""",
    "extent inverse soundness requires a successful lookup": """
{-@ proofGuard
      :: valueAtlas:Atlas atlasScope scope cellData origin final
      -> source:{PageElement scope object | cellHasOrigin valueAtlas source && cellTraceValid valueAtlas source}
      -> valueRank:Natural
      -> datum:{cellData object | atlasAcceptsDatum valueAtlas source datum}
      -> {applyInsertion (atlasCellOriginRankInsertion valueAtlas source) datum == valueRank} @-}
proofGuard
  :: Atlas atlasScope scope cellData origin final
  -> PageElement scope object -> Natural -> cellData object -> ()
proofGuard = cellOriginRankPreimageSound
""",
}


FOLIO_SOURCE = HASKELL / "src/DatraCore/Atlases/Core/Folio/LiquidInternal.hs"
FOLIO_GUARDS = {
    "folio origins reject a zero cached length": """
proofGuard :: page origin -> SingletonOrigin origin -> FolioData page origin origin
proofGuard = OriginFolio 0
""",
    "folio origins reject a cached length greater than one": """
proofGuard :: page origin -> SingletonOrigin origin -> FolioData page origin origin
proofGuard = OriginFolio 2
""",
    "folio append rejects an unchanged cached length": """
proofGuard :: FolioData page origin previous -> page next
  -> Coconsolidation previous next -> FolioData page origin next
proofGuard pages = SnocPage (folioLengthData pages) pages
""",
}

PAGE_ARROW_SOURCE = HASKELL / "src/DatraCore/Atlases/Core/PageElements/LiquidInternal.hs"
PAGE_ARROW_GUARDS = {
    "arrow position requires the source trace shape": """
{-@ proofGuard :: arrow:{PageElementArrow scope source target |
      PageElementTraceShape (arrowTarget arrow)}
      -> {positionAtPage (pageElementPage (arrowTarget arrow)) (arrowSource arrow)
           == Just (pageElementPosition (arrowTarget arrow))} @-}
proofGuard :: PageElementArrow scope source target -> ()
proofGuard arrow = pageElementArrowPosition arrow
""",
    "arrow position requires the target trace shape": """
{-@ proofGuard :: arrow:{PageElementArrow scope source target |
      PageElementTraceShape (arrowSource arrow)}
      -> {positionAtPage (pageElementPage (arrowTarget arrow)) (arrowSource arrow)
           == Just (pageElementPosition (arrowTarget arrow))} @-}
proofGuard :: PageElementArrow scope source target -> ()
proofGuard arrow = pageElementArrowPosition arrow
""",
}

PAGE_INDEX_SOURCE = HASKELL / "src/DatraCore/Atlases/Core/PageElements/Internal.hs"
PAGE_INDEX_GUARDS = {
    "normalization cannot discard the owning trace": """
{-@ proofGuard :: category:PageElements scope origin final
      -> occurrence:{PageElement scope object | pageElementTraceValid category occurrence}
      -> {pageElementTraceValid category
           (normalizePageElementAt (folioLength (pageElementsFolio category) - 1) 0 occurrence)} @-}
proofGuard :: PageElements scope origin final -> PageElement scope object -> ()
proofGuard category occurrence = pageElementTraceValidNormalize category occurrence
""",
    "normalization evidence cannot prove False": """
{-@ proofGuard :: category:PageElements scope origin final
      -> occurrence:{PageElement scope object | pageElementTraceValid category occurrence}
      -> {proof:() | False} @-}
proofGuard :: PageElements scope origin final -> PageElement scope object -> ()
proofGuard category occurrence = pageElementTraceValidNormalize category occurrence
""",
    "page lookup cannot discard a successful owning trace": """
{-@ proofGuard :: category:PageElements scope origin final -> page:Natural -> position:Ordinal
      -> {result:Maybe (PageElementIndex scope) |
           pageElementIndexTraceResult result == folioTraceLookup (pageElementsFolio category) page position} @-}
proofGuard :: PageElements scope origin final -> Natural -> Ordinal -> Maybe (PageElementIndex scope)
proofGuard _ _ _ = Nothing
""",
    "trace shape requires the owning folio certificate": """
{-@ proofGuard :: category:PageElements scope origin final -> occurrence:PageElement scope object
      -> {len (Trace.pageElementTrace occurrence) == pageElementPage occurrence + 1
           && Trace.traceStartsWith (pageElementPosition occurrence) (Trace.pageElementTrace occurrence)} @-}
proofGuard :: PageElements scope origin final -> PageElement scope object -> ()
proofGuard category occurrence = pageElementTraceValidShape category occurrence
""",
    "page lookup cannot claim another owning folio": """
{-@ proofGuard :: PageElements scope origin final -> other:PageElements scope origin final
      -> page:Natural -> position:Ordinal
      -> Maybe ({index:PageElementIndex scope |
           folioTraceLookup (pageElementsFolio other) page position == Just (pageElementIndexTrace index)}) @-}
proofGuard :: PageElements scope origin final -> PageElements scope origin final
  -> Natural -> Ordinal -> Maybe (PageElementIndex scope)
proofGuard owner _ page position = pageElementIndex owner page position
""",
    "page indices reject a missing padding step": """
{-@ proofGuard :: pages:Folio origin page
      -> {index:ChainIndex page |
           chainPosition (lastChain pages) (chainObjectAt index) == chainIndexPosition index}
      -> PageElementIndex scope @-}
proofGuard :: Folio origin page -> ChainIndex page -> PageElementIndex scope
proofGuard pages index = PageElementIndex (PageElementIndexData (folioLength pages) pages 0
  (chainIndexPosition index) (chainObjectAt index) (pageElementTraceAt pages 0 (chainObjectAt index)))
""",
    "page indices require the selected chain position": """
{-@ proofGuard :: Folio origin page -> Ordinal -> page -> PageElementIndex scope @-}
proofGuard :: Folio origin page -> Ordinal -> page -> PageElementIndex scope
proofGuard pages position value = PageElementIndex
  (PageElementIndexData (folioLength pages - 1) pages 0 position value (pageElementTraceAt pages 0 value))
""",
    "page indices reject a forged cached transport trace": """
{-@ proofGuard :: index:PageElementIndexData origin current
      -> {positions:[Ordinal] | len positions == indexedPage index + 1
           && Trace.traceStartsWith (indexedPosition index) positions
           && Trace.traceSuffix positions (folioOriginTrace (indexedPrefix index))}
      -> PageElementIndex scope @-}
proofGuard :: PageElementIndexData origin current -> [Ordinal] -> PageElementIndex scope
proofGuard index positions = PageElementIndex (index {indexedTrace = positions})
""",
    "constructed page traces cannot start at a different position": """
{-@ proofGuard :: index:PageElementIndex scope
      -> {positions:[Ordinal] | not (Trace.traceStartsWith (pageElementIndexPosition index) positions)} @-}
proofGuard :: PageElementIndex scope -> [Ordinal]
proofGuard index = Trace.somePageElementTrace (pageElement index)
""",
    "last-page lookup requires the selected chain position": """
{-@ proofGuard :: PageElements scope origin final -> ChainIndex final -> SomePageElement scope @-}
proofGuard :: PageElements scope origin final -> ChainIndex final -> SomePageElement scope
proofGuard = lastPageElement
""",
    "page lookup cannot shift the requested page": """
{-@ proofGuard :: PageElements scope origin final -> page:Natural -> Ordinal
      -> Maybe ({index:PageElementIndex scope | pageElementIndexPage index == page}) @-}
proofGuard :: PageElements scope origin final -> Natural -> Ordinal -> Maybe (PageElementIndex scope)
proofGuard category page position = pageElementIndex category (page + 1) position
""",
    "page traces cannot discard the current occurrence": """
{-@ proofGuard :: pages:Folio origin page -> padding:Natural -> page
      -> {positions:[Ordinal] | len positions == padding + folioLength pages} @-}
proofGuard :: Folio origin page -> Natural -> page -> [Ordinal]
proofGuard pages padding value = Trace.traceTail (pageElementTraceAt pages padding value)
""",
    "page traces cannot discard the folio origin": """
{-@ proofGuard :: pages:Folio origin page -> page
      -> {positions:[Ordinal] | Trace.traceSuffix positions (folioOriginTrace pages)} @-}
proofGuard :: Folio origin page -> page -> [Ordinal]
proofGuard _ _ = []
""",
}


ATLAS_SOURCE = HASKELL / "src/DatraCore/Atlases/Core/Atlas/Internal.hs"
ATLAS_GUARDS = {
    "Atlas normalization cannot switch the owning folio": """
{-@ proofGuard :: owner:Atlas a s d o f -> other:Atlas a s d o f
      -> occurrence:{PageElement s object |
           Elements.pageElementTraceValid (atlasPageElements other) occurrence}
      -> {Elements.pageElementTraceValid (atlasPageElements owner) (normalizeAtlasElement owner occurrence)} @-}
proofGuard :: Atlas a s d o f -> Atlas a s d o f -> PageElement s object -> ()
proofGuard owner _ occurrence = normalizeAtlasElementTraceValid owner occurrence
""",
    "Atlas arrow normalization requires both endpoint certificates": """
{-@ proofGuard :: owner:Atlas a s d o f
      -> arrow:{PageElementArrow s source target |
           Elements.pageElementTraceValid (atlasPageElements owner) (arrowSource arrow)}
      -> {Elements.pageElementTraceValid (atlasPageElements owner)
           (arrowTarget (normalizeAtlasArrow owner arrow))} @-}
proofGuard :: Atlas a s d o f -> PageElementArrow s source target -> ()
proofGuard owner arrow = normalizeAtlasArrowTraceValid owner arrow
""",
    "Atlas lookup requires its owning folio trace": """
{-@ proofGuard :: owner:Atlas atlasScope scope cellData origin final
      -> {index:PageElementIndex scope | Elements.pageElementIndexOrigin index
           == Elements.originPageElement (atlasPageElements owner)}
      -> SomePageElement scope @-}
proofGuard :: Atlas atlasScope scope cellData origin final
  -> PageElementIndex scope -> SomePageElement scope
proofGuard = atlasPageCell
""",
    "Atlas data transport requires source membership": """
{-@ proofGuard :: owner:Atlas a s d o f
      -> arrow:{PageElementArrow s source target | AtlasValidArrow owner arrow}
      -> d source -> d target @-}
proofGuard :: Atlas a s d o f -> PageElementArrow s source target -> d source -> d target
proofGuard owner arrow datum = applyInsertion (mapAtlasData owner arrow) datum
""",
    "Atlas cannot store data for an unrelated folio": """
{-@ proofGuard :: paginationValue:Pagination scope origin final
      -> stored:{AtlasData scope cellData |
           atlasDataFinalPage stored == atlasFinalPage paginationValue
           && atlasDataTraceLimit stored == atlasTraceLimit paginationValue}
      -> Atlas atlasScope scope cellData origin final @-}
proofGuard :: Pagination scope origin final -> AtlasData scope cellData
  -> Atlas atlasScope scope cellData origin final
proofGuard = Atlas
""",
    "Atlas composition witnesses require matching arrow endpoints": """
{-@ proofGuard :: owner:Atlas a s d o f
      -> second:{PageElementArrow s middle target | AtlasValidArrow owner second}
      -> first:{PageElementArrow s source middle | AtlasValidArrow owner first}
      -> {datum:d source | atlasAcceptsDatum owner (arrowSource first) datum} -> () @-}
proofGuard :: Atlas a s d o f -> PageElementArrow s middle target
  -> PageElementArrow s source middle -> d source -> ()
proofGuard = atlasCompositionWitness
""",
    "Atlas coherence witnesses require the normalization arrow": """
{-@ proofGuard :: owner:Atlas a s d o f -> cell:{PageElement s object | AtlasValidCell owner cell}
      -> arrow:{PageElementArrow s object object | AtlasValidArrow owner arrow}
      -> {datum:d object | atlasAcceptsDatum owner cell datum} -> () @-}
proofGuard :: Atlas a s d o f -> PageElement s object
  -> PageElementArrow s object object -> d object -> ()
proofGuard = atlasCoherenceWitness
""",
    "Atlas disjointness witnesses require distinct cells on one genuine page": """
{-@ proofGuard :: owner:Atlas a s d o f
      -> left:{PageElement s left | AtlasValidCell owner left}
      -> right:{PageElement s right | AtlasValidCell owner right}
      -> leftArrow:{PageElementArrow s left origin | AtlasValidArrow owner leftArrow}
      -> rightArrow:{PageElementArrow s right origin | AtlasValidArrow owner rightArrow}
      -> {datum:d left | atlasAcceptsDatum owner left datum}
      -> {datum:d right | atlasAcceptsDatum owner right datum} -> () @-}
proofGuard :: Atlas a s d o f -> PageElement s left -> PageElement s right
  -> PageElementArrow s left origin -> PageElementArrow s right origin
  -> d left -> d right -> ()
proofGuard = atlasDisjointWitness
""",
    "Atlas lookup requires the index's origin to match": """
{-@ proofGuard :: Atlas atlasScope scope cellData origin final
      -> PageElementIndex scope -> SomePageElement scope @-}
proofGuard :: Atlas atlasScope scope cellData origin final
  -> PageElementIndex scope -> SomePageElement scope
proofGuard = atlasPageCell
""",
}


ATLAS_DATA_SOURCE = HASKELL / "src/DatraCore/Atlases/Core/Atlas/LiquidInternal.hs"
ATLAS_DATA_GUARDS = {
    "Atlas action lookup requires its declared domain": """
{-@ proofGuard :: action:AtlasAction scope cellData -> occurrence:PageElement scope object
      -> Dominion ({datum:cellData object | atlasActionAccepts action occurrence datum}) @-}
proofGuard :: AtlasAction scope cellData -> PageElement scope object -> Dominion (cellData object)
proofGuard action occurrence = atlasActionDataAt action occurrence
""",
    "Atlas action transport requires the target domain": """
{-@ proofGuard :: action:AtlasAction scope cellData
      -> arrow:{PageElementArrow scope source target | atlasActionElementValid action (arrowSource arrow)}
      -> DomanialInsertion
           ({datum:cellData source | atlasActionAccepts action (arrowSource arrow) datum})
           ({datum:cellData target | atlasActionAccepts action (arrowTarget arrow) datum}) @-}
proofGuard :: AtlasAction scope cellData -> PageElementArrow scope source target
  -> DomanialInsertion (cellData source) (cellData target)
proofGuard action arrow = atlasActionMap action arrow
""",
    "Atlas action lookup cannot discard cell membership": """
{-@ proofGuard :: action:AtlasAction scope cellData
      -> occurrence:{PageElement scope object | atlasActionElementValid action occurrence}
      -> Dominion (cellData object) @-}
proofGuard :: AtlasAction scope cellData -> PageElement scope object -> Dominion (cellData object)
proofGuard action occurrence = atlasActionDataAt action occurrence
""",
    "Atlas data cannot manufacture laws for an arbitrary action": """
{-@ proofGuard :: finalPage:Natural -> traceLimit:Int
      -> action:{AtlasAction scope cellData |
           pageElementDomainFinalPage (atlasActionDomain action) == finalPage
           && pageElementDomainTraceLimit (atlasActionDomain action) == traceLimit}
      -> AtlasData scope cellData @-}
proofGuard :: Natural -> Int -> AtlasAction scope cellData -> AtlasData scope cellData
proofGuard finalPage traceLimit action = AtlasData finalPage traceLimit action
  (\\_ _ -> ()) (\\_ _ _ -> ()) (\\_ _ _ -> ()) (\\_ _ _ _ _ _ -> ())
""",
}

MEMBERSHIP_DOMINION_SOURCE = HASKELL / "src/DatraCore/Atlases/Core/Dominion/Internal.hs"
MEMBERSHIP_DOMINION_GUARDS = {
    "existential Dominion packaging cannot discard membership": """
{-@ proofGuard :: MembershipDominion a -> Dominion a @-}
proofGuard :: MembershipDominion a -> Dominion a
proofGuard = memberDominion
""",
}


MERGE_RESOLUTION_SOURCE = HASKELL / "src/DatraCore/Atlases/Derived/AtlasConfederations/AtlasMerge/Resolution.hs"
MERGE_RESOLUTION_GUARDS = {
    "merge resolution cannot switch the left cell's owner": """
{-@ proofGuard :: Atlas la ls ld lo lf -> Atlas la ls ld lo lf
      -> Atlas ra rs rd ro rf -> PageElement ms object -> Maybe Bool @-}
proofGuard :: Atlas la ls ld lo lf -> Atlas la ls ld lo lf
  -> Atlas ra rs rd ro rf -> PageElement ms object -> Maybe Bool
proofGuard left other right occurrence =
  mergeSourceCell left right occurrence False
    (\\source -> Extent.cellContainsRank other source 0) (\\_ -> False)
""",
}

SEQUENCE_RESOLUTION_SOURCE = HASKELL / "src/DatraCore/Atlases/Derived/AtlasConfederations/AtlasSequence/Resolution.hs"
SEQUENCE_RESOLUTION_GUARDS = {
    "sequence member resolution cannot return an out-of-range index": """
{-@ proofGuard :: members:[AtlasSequenceMember] -> Natural -> Ordinal
      -> Maybe ({index:Natural | index >= len members}) @-}
proofGuard :: [AtlasSequenceMember] -> Natural -> Ordinal -> Maybe Natural
proofGuard members page position =
  withMemberAtPosition members page position (\\index _ _ -> Just index)
""",
    "sequence resolution cannot discard the selected cell's trace": """
{-@ proofGuard :: NonEmpty AtlasSequenceMember -> PageElement scope object -> Maybe Bool @-}
proofGuard :: NonEmpty AtlasSequenceMember -> PageElement scope object -> Maybe Bool
proofGuard members occurrence =
  sequenceSourceCell members occurrence False proofGuardCallback

{-@ proofGuardCallback :: Natural -> owner:Atlas a s d o f
      -> source:{PageElement s object | Extent.cellHasOrigin owner source} -> Bool @-}
proofGuardCallback :: Natural -> Atlas a s d o f -> PageElement s object -> Bool
proofGuardCallback _ owner source =
  Extent.cellContainsRank owner (source {pageElementTrace = []}) 0
""",
}


def run(pattern=None):
    plan = json.loads((HASKELL / "dist-newstyle/cache/plan.json").read_text())
    library = next(unit for unit in plan["install-plan"]
                   if unit.get("pkg-name") == "datra-haskell"
                   and unit.get("component-name") == "lib")
    if not any(dep.startswith("liquidhaskell-") for dep in library["depends"]):
        raise SystemExit("Build the library with -fliquid before checking proof guards")
    project = os.environ.get("CABAL_PROJECT", "cabal.project")
    with tempfile.TemporaryDirectory(prefix="datra-proof-guards-") as directory:
        temporary = Path(directory)
        target = temporary / "LiquidInternal.hs"
        command = ["cabal", f"--project-file={project}", "exec", "-fliquid", "--", "ghc",
                   "-v0", "-c", "-fforce-recomp", "-DDATRA_LIQUID",
                   "-hide-all-packages",
                   "-this-unit-id", library["id"],
                   "-i" + str(Path(library["dist-dir"]) / "build")]
        for dependency in library["depends"]:
            command.extend(["-package-id", dependency])
        for source_path, guards in [(SOURCE, GUARDS), (CHAIN_SOURCE, CHAIN_GUARDS),
                                    (PAGE_TRACE_SOURCE, PAGE_TRACE_GUARDS),
                                    (MERGE_PAGE_SOURCE, MERGE_PAGE_GUARDS),
                                    (STABLE_SOURCE, STABLE_GUARDS),
                                    (DOMINC_SOURCE, DOMINC_GUARDS),
                                    (TRANSVERSAL_SOURCE, TRANSVERSAL_GUARDS),
                                    (CHARTER_SOURCE, CHARTER_GUARDS),
                                    (RANK_IMAGE_SOURCE, RANK_IMAGE_GUARDS),
                                    (MERGE_SOURCE, MERGE_GUARDS),
                                    (SEQUENCE_SOURCE, SEQUENCE_GUARDS),
                                    (EXTENT_SOURCE, EXTENT_GUARDS),
                                    (FOLIO_SOURCE, FOLIO_GUARDS),
                                    (PAGE_ARROW_SOURCE, PAGE_ARROW_GUARDS),
                                    (PAGE_INDEX_SOURCE, PAGE_INDEX_GUARDS),
                                    (ATLAS_SOURCE, ATLAS_GUARDS),
                                    (ATLAS_DATA_SOURCE, ATLAS_DATA_GUARDS),
                                    (MEMBERSHIP_DOMINION_SOURCE, MEMBERSHIP_DOMINION_GUARDS),
                                    (MERGE_RESOLUTION_SOURCE, MERGE_RESOLUTION_GUARDS),
                                    (SEQUENCE_RESOLUTION_SOURCE, SEQUENCE_RESOLUTION_GUARDS)]:
            source = re.sub(r'#include "[^"]*LiquidPlugin.h"',
                            f'#include "{HASKELL / "src/DatraCore/LiquidPlugin.h"}"',
                            source_path.read_text())
            for description, guard in guards.items():
                if pattern and not re.search(pattern, description):
                    continue
                target.write_text(source + "\n" + guard)
                result = subprocess.run(command + [str(target)], cwd=HASKELL,
                                        text=True, capture_output=True)
                output = result.stdout + result.stderr
                error_lines = re.findall(re.escape(str(target)) + r":(\d+):\d+: error:", output)
                if (result.returncode == 0 or "Liquid Type Mismatch" not in output
                        or not any(int(line) > source.count("\n") for line in error_lines)):
                    raise SystemExit(f"Proof guard did not produce the required rejection: {description}\n{output}")
                print(f"Rejected false law: {description}")

        for source_path, datum_type, description in [
            (MERGE_SOURCE, "AtlasMergeDatum", "merge datums retain their cell identity"),
            (SEQUENCE_SOURCE, "AtlasSequenceDatum", "sequence datums retain their cell identity"),
        ]:
            if pattern and not re.search(pattern, description):
                continue
            source = re.sub(r'#include "[^"]*LiquidPlugin.h"',
                            f'#include "{HASKELL / "src/DatraCore/LiquidPlugin.h"}"',
                            source_path.read_text())
            source = source.replace("import Numeric.Natural", "import Data.Coerce (coerce)\nimport Numeric.Natural")
            target.write_text(source + f"\nproofGuard :: {datum_type} source -> {datum_type} target\n"
                              "proofGuard = coerce\n")
            result = subprocess.run(command + [str(target)], cwd=HASKELL, text=True, capture_output=True)
            output = result.stdout + result.stderr
            error_lines = re.findall(re.escape(str(target)) + r":(\d+):\d+: error:", output)
            if (result.returncode == 0 or "Couldn't match type" not in output or "coerce" not in output
                    or not any(int(line) > source.count("\n") for line in error_lines)):
                raise SystemExit(f"Cell-role guard did not produce the required rejection: {description}\n{output}")
            print(f"Rejected invalid coercion: {description}")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--filter", help="Run only guard descriptions matching this regular expression")
    run(parser.parse_args().filter)
