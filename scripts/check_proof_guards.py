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
SOURCE = HASKELL / "src/DatraCore/Atlases/Core/Atlas/Presheaf.hs"
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

DATA_TRANSFORMATION_SOURCE = HASKELL / "src/DatraCore/DataTransformations/DataTransformations/DataTransformation/LiquidInternal.hs"
DATA_TRANSFORMATION_GUARDS = {
    "presheaf packaging rejects dummy identity and composition laws": """
proofGuard :: (forall source target. AtlasHom source target
  -> DataTransformationValue values target -> DataTransformationValue values source)
  -> DataTransformation values
proofGuard action = dataTransformation action (\\_ -> ()) (\\_ _ _ -> ())
""",
    "natural transformation packaging rejects dummy naturality": """
proofGuard :: DataTransformation source -> DataTransformation target
  -> (forall atlas. DataTransformationValue source atlas -> DataTransformationValue target atlas)
  -> DataTransformationNatural source target
proofGuard source target component = dataTransformationNatural source target component (\\_ _ -> ())
""",
}

DATA_TRANSFORMATION_CORE_SOURCE = HASKELL / "src/DatraCore/DataTransformations/DataTransformations/DataTransformation/Core.hs"
DATA_TRANSFORMATION_CORE_GUARDS = {
    "core " + name: guard for name, guard in DATA_TRANSFORMATION_GUARDS.items()
}
DATA_TRANSFORMATION_CORE_GUARDS["Yoneda package retains its precomposition action"] = """
{-@ proofGuard :: arrow:AtlasHom source target -> value:Yoneda represented target
      -> {proof:() | mapDataTransformation yoneda arrow value /= mapYoneda arrow value} @-}
proofGuard :: forall represented source target. AtlasHom source target -> Yoneda represented target -> ()
proofGuard = yonedaActionAgrees
"""
DATA_TRANSFORMATION_GUARDS["Yoneda natural package retains its postcomposition component"] = """
{-@ proofGuard :: arrow:AtlasHom source target -> value:Yoneda source atlas
      -> {proof:() | mapDataTransformationNatural (yonedaNatural arrow) value /= mapYonedaNatural arrow value} @-}
proofGuard :: AtlasHom source target -> Yoneda source atlas -> ()
proofGuard = yonedaComponentAgrees
"""

NATURAL_SEARCH_SOURCE = HASKELL / "src/DatraCore/Atlases/Core/NaturalSearch.hs"
NATURAL_SEARCH_GUARDS = {
    "finite search congruence requires equality of the tested predicates": """
{-@ proofGuard :: left:(Natural -> Bool) -> right:(Natural -> Bool)
      -> candidate:Natural -> remaining:Natural
      -> {search left candidate remaining == search right candidate remaining} @-}
proofGuard :: (Natural -> Bool) -> (Natural -> Bool) -> Natural -> Natural -> ()
proofGuard left right = congruent left right (const ())
""",

    "finite search cannot return a rank beyond its interval": """
{-@ proofGuard :: matches:(Natural -> Bool) -> candidate:Natural -> remaining:Natural
      -> Maybe {found:Natural | found > candidate + remaining} @-}
proofGuard :: (Natural -> Bool) -> Natural -> Natural -> Maybe Natural
proofGuard = search
""",
    "finite search trimming requires the actually selected rank": """
{-@ proofGuard :: matches:(Natural -> Bool) -> candidate:Natural -> remaining:Natural
      -> found:{Natural | candidate <= found && matches found}
      -> {search matches candidate (found - candidate) == Just found} @-}
proofGuard :: (Natural -> Bool) -> Natural -> Natural -> Natural -> ()
proofGuard = trim
""",
    "canonical uniqueness requires least ranks, not merely successful ranks": """
{-@ proofGuard :: matches:(Natural -> Bool)
      -> left:{Natural | matches left} -> right:{Natural | matches right}
      -> {left == right} @-}
proofGuard :: (Natural -> Bool) -> Natural -> Natural -> ()
proofGuard = unique
""",
}

CHAIN_SOURCE = HASKELL / "src/DatraCore/Atlases/Core/Chain/Internal.hs"
CONSOLIDATION_SOURCE = HASKELL / "src/DatraCore/Atlases/Core/Consolidation/Core.hs"
CONSOLIDATION_GUARDS = {
    "restricted consolidations require accepted source values": """
{-@ proofGuard :: Consolidation {value:Int | value == 0} {value:Int | value == 0}
      -> Int -> Int @-}
proofGuard :: Consolidation Int Int -> Int -> Int
proofGuard mapping value = applyConsolidation mapping value
""",
    "opposite wrappers cannot change the preserved order": r"""
{-@ proofGuard :: Consolidation <{\x y -> x <= y}, {\x y -> x <= y}> Int Int
      -> Coconsolidation <{\x y -> x <= y}, {\x y -> x >= y}> Int Int @-}
proofGuard :: Consolidation Int Int -> Coconsolidation Int Int
proofGuard = op
""",
    "opposite monotonicity requires an ordered pair": r"""
{-@ proofGuard :: transition:Coconsolidation <{\x y -> x <= y}, {\x y -> x <= y}> Int Int
      -> left:Int -> right:Int
      -> {result:Int | result == applyConsolidation (unop transition) right
           && applyConsolidation (unop transition) left <= result} @-}
proofGuard :: Coconsolidation Int Int -> Int -> Int -> Int
proofGuard transition left right = coconsolidationMonotone transition left right
""",
}

CHAIN_GUARDS = {
    "chain reindexing rejects a constant carrier equivalence": """
proofGuard :: Chain Natural
proofGuard = reindexChain (const True) spine (const 0) (const 0) (const ()) (const ())
""",
}

CHAIN_SINGLETON_SOURCE = HASKELL / "src/DatraCore/Atlases/Core/Chain/Singleton.hs"
CHAIN_SINGLETON_GUARDS = {
    "singleton position requires evidence of a unique carrier": """
{-@ proofGuard :: page:Chain a -> selected:a -> value:a
      -> {chainPosition page value == finiteOrdinal 0} @-}
proofGuard :: Chain a -> a -> a -> ()
proofGuard page selected value = chainSingletonPosition page selected (const ()) value
""",
}

ORDERED_CONSOLIDATION_SOURCE = HASKELL / "src/DatraCore/Atlases/Core/Consolidation/Ordered.hs"
ORDERED_CONSOLIDATION_GUARDS = {
    "consolidation function replacement requires the forward equation": """
proofGuard :: OrderedConsolidation Int Int -> (Int -> Int) -> OrderedConsolidation Int Int
proofGuard mapping forward = withConsolidationFunctions (const True) (const True)
  mapping forward (orderedPreimage mapping) (const ()) (const ())
""",
    "consolidation function replacement retains the chosen preimage": """
proofGuard :: OrderedConsolidation Int Int -> (Int -> Int) -> OrderedConsolidation Int Int
proofGuard mapping backward = withConsolidationFunctions (const True) (const True)
  mapping (orderedApply mapping) backward (const ()) (const ())
""",

    "concrete consolidation monotonicity requires the source order": """
{-@ proofGuard :: value:OrderedConsolidation a b -> left:a -> right:a
      -> {chainPrecedes (orderedTarget value)
            (orderedApply value left) (orderedApply value right)} @-}
proofGuard :: OrderedConsolidation a b -> a -> a -> ()
proofGuard value left right = orderedMonotone value left right
""",
    "concrete consolidation composition requires matching chains": """
{-@ proofGuard :: OrderedConsolidation b c -> OrderedConsolidation a b
      -> OrderedConsolidation a c @-}
proofGuard :: OrderedConsolidation b c -> OrderedConsolidation a b -> OrderedConsolidation a c
proofGuard second first = composeOrderedConsolidations second first
""",
    "concrete consolidation identity cannot certify unrelated orders": """
{-@ proofGuard :: source:Chain a -> target:Chain a -> left:a
      -> right:{a | chainPrecedes source left right}
      -> {chainPrecedes target left right} @-}
proofGuard :: Chain a -> Chain a -> a -> a -> ()
proofGuard source target left right =
  orderedMonotone (orderedConsolidation source target identityConsolidation) left right
""",
}

POSITION_SOURCE = HASKELL / "src/DatraCore/Atlases/Core/Chain/Position.hs"
POSITION_GUARDS = {
    "chain position transport requires pointwise equality": """
{-@ proofGuard :: Chain a -> (a -> Ordinal) -> Chain a @-}
proofGuard :: Chain a -> (a -> Ordinal) -> Chain a
proofGuard original position = withChainPosition (const True) original position (const ())
""",
}

ENDPOINTS_SOURCE = HASKELL / "src/DatraCore/Atlases/Core/Consolidation/Endpoints.hs"
ENDPOINTS_GUARDS = {
    "consolidation endpoint transport requires equal positions": """
{-@ proofGuard :: OrderedConsolidation a b -> Chain a -> Chain b -> OrderedConsolidation a b @-}
proofGuard :: OrderedConsolidation a b -> Chain a -> Chain b -> OrderedConsolidation a b
proofGuard mapping source target =
  withConsolidationEndpoints (const True) (const True) mapping source target (const ()) (const ())
""",
}

MERGE_ACTION_SOURCE = HASKELL / "src/DatraCore/Atlases/Derived/AtlasConfederations/AtlasMerge/Action.hs"
MERGE_ACTION_GUARDS = {
    "public Atlas predicate construction requires action laws": """
{-@ proofGuard :: pages:Pagination.Pagination scope origin final
      -> accepts:(forall object. PageElement scope object -> cellData object -> Bool)
      -> action:{AtlasDataAction scope cellData |
           atlasActionDomain action == pageElementDomain (Pagination.paginationPageElements pages)
           && atlasActionMembership action == atlasMembership accepts}
      -> (forall atlasScope. Atlas atlasScope scope cellData origin final -> result)
      -> result @-}
proofGuard :: Pagination.Pagination scope origin final
  -> (forall object. PageElement scope object -> cellData object -> Bool)
  -> AtlasDataAction scope cellData
  -> (forall atlasScope. Atlas atlasScope scope cellData origin final -> result) -> result
proofGuard pages accepts action useAtlas = atlasForPredicate pages accepts action
  (\\_ _ -> ()) (\\_ _ _ _ -> ()) (\\_ _ _ _ -> ()) (\\_ _ _ _ _ _ _ -> ()) useAtlas
""",
    "merge action composition requires aligned endpoints": """
{-@ proofGuard :: left:Atlas la ls ld lo lf -> right:Atlas ra rs rd ro rf
      -> category:{PageElements ms () (MergeFinalCell left right) | pageElementsFolio category == atlasMergeFolio left right}
      -> second:{PageElementArrow ms middle target | pageElementTraceValid category (arrowSource second)
           && pageElementTraceValid category (arrowTarget second)}
      -> first:{PageElementArrow ms source middle | pageElementTraceValid category (arrowSource first)
           && pageElementTraceValid category (arrowTarget first)}
      -> datum:{AtlasMergeDatum source | mergeCellContains left right (normalizePageElement category (arrowSource first)) datum}
      -> () @-}
proofGuard :: Atlas la ls ld lo lf -> Atlas ra rs rd ro rf
  -> PageElements ms () AtlasMergePageCell -> PageElementArrow ms middle target
  -> PageElementArrow ms source middle -> AtlasMergeDatum source -> ()
proofGuard left right category second first datum =
  mergeActionComposition left right category second first () datum
""",
    "merge action identity requires accepted source data": """
{-@ proofGuard :: left:Atlas la ls ld lo lf -> right:Atlas ra rs rd ro rf
      -> category:{PageElements ms () (MergeFinalCell left right) | pageElementsFolio category == atlasMergeFolio left right}
      -> occurrence:{PageElement ms object | pageElementTraceValid category occurrence}
      -> AtlasMergeDatum object -> () @-}
proofGuard :: Atlas la ls ld lo lf -> Atlas ra rs rd ro rf
  -> PageElements ms () AtlasMergePageCell -> PageElement ms object -> AtlasMergeDatum object -> ()
proofGuard = mergeActionIdentity
""",
    "merge action package requires the actual owning folio": """
{-@ proofGuard :: left:Atlas la ls ld lo lf -> right:Atlas ra rs rd ro rf
      -> PageElements ms () (MergeFinalCell left right) -> AtlasDataAction ms AtlasMergeDatum @-}
proofGuard :: Atlas la ls ld lo lf -> Atlas ra rs rd ro rf
  -> PageElements ms () AtlasMergePageCell -> AtlasDataAction ms AtlasMergeDatum
proofGuard = mergeDataAction
""",
    "merge data insertion requires both owning traces": """
{-@ proofGuard :: left:Atlas la ls ld lo lf -> right:Atlas ra rs rd ro rf
      -> arrow:PageElementArrow ms s t
      -> DomanialInsertion
           ({datum:AtlasMergeDatum s | mergeCellContains left right (arrowSource arrow) datum})
           ({datum:AtlasMergeDatum t | mergeCellContains left right (arrowTarget arrow) datum}) @-}
proofGuard :: Atlas la ls ld lo lf -> Atlas ra rs rd ro rf -> PageElementArrow ms s t
  -> DomanialInsertion (AtlasMergeDatum s) (AtlasMergeDatum t)
proofGuard = mergeDataMap
""",
}

MERGE_TRANSPORT_SOURCE = HASKELL / "src/DatraCore/Atlases/Derived/AtlasConfederations/AtlasMerge/Transport.hs"
MERGE_TRANSPORT_GUARDS = {
    "merge raw membership preservation requires target ownership": """
{-@ proofGuard :: left:Atlas la ls ld lo lf -> right:Atlas ra rs rd ro rf
      -> arrow:{PageElementArrow ms s t | mergeOccurrenceTraceValid left right (arrowSource arrow)}
      -> datum:{AtlasMergeDatum s | mergeCellContains left right (arrowSource arrow) datum} -> () @-}
proofGuard :: Atlas la ls ld lo lf -> Atlas ra rs rd ro rf -> PageElementArrow ms s t -> AtlasMergeDatum s -> ()
proofGuard = mergeCellContainsPreserved
""",
    "merge raw membership preservation requires an accepted source datum": """
{-@ proofGuard :: left:Atlas la ls ld lo lf -> right:Atlas ra rs rd ro rf
      -> arrow:{PageElementArrow ms s t | mergeOccurrenceTraceValid left right (arrowSource arrow)
           && mergeOccurrenceTraceValid left right (arrowTarget arrow)}
      -> AtlasMergeDatum s -> () @-}
proofGuard :: Atlas la ls ld lo lf -> Atlas ra rs rd ro rf -> PageElementArrow ms s t -> AtlasMergeDatum s -> ()
proofGuard = mergeCellContainsPreserved
""",
    "merge native witnesses require a successful owning lookup": """
{-@ proofGuard :: left:Atlas la ls ld lo lf -> right:Atlas ra rs rd ro rf
      -> page:{Natural | page > 0} -> position:Ordinal -> [Ordinal] -> Maybe AtlasMergePageCell @-}
proofGuard :: Atlas la ls ld lo lf -> Atlas ra rs rd ro rf -> Natural -> Ordinal -> [Ordinal]
  -> Maybe AtlasMergePageCell
proofGuard = mergeLookupNative
""",
    "merge resolver totality requires the owning trace": """
{-@ proofGuard :: left:Atlas la ls ld lo lf -> right:Atlas ra rs rd ro rf
      -> occurrence:PageElement ms object -> {mergePositionResolvable left right occurrence} @-}
proofGuard :: Atlas la ls ld lo lf -> Atlas ra rs rd ro rf -> PageElement ms object -> ()
proofGuard = mergeOccurrenceResolvable
""",
    "merge full lookup requires an accepted native cell": """
{-@ proofGuard :: Atlas la ls ld lo lf -> Atlas ra rs rd ro rf
      -> page:{Natural | page > 0} -> AtlasMergePageCell -> () @-}
proofGuard :: Atlas la ls ld lo lf -> Atlas ra rs rd ro rf -> Natural -> AtlasMergePageCell -> ()
proofGuard = mergeFullCellLookup
""",
    "merge padded positions require both component bounds": """
{-@ proofGuard :: left:Atlas la ls ld lo lf -> right:Atlas ra rs rd ro rf
      -> page:{Natural | page >= folioLength (atlasFolio left)}
      -> cell:{AtlasMergePageCell | mergePageContains (atlasFolio left) (atlasFolio right) page cell}
      -> () @-}
proofGuard :: Atlas la ls ld lo lf -> Atlas ra rs rd ro rf -> Natural -> AtlasMergePageCell -> ()
proofGuard = mergePaddedPreviousPosition
""",
    "merge resolved transport requires target resolver coordinates": """
{-@ proofGuard :: left:Atlas la ls ld lo lf -> right:Atlas ra rs rd ro rf
      -> arrow:{PageElementArrow ms s t |
           mergeOccurrenceTraceValid left right (arrowSource arrow)
           && mergeOccurrenceTraceValid left right (arrowTarget arrow)}
      -> source:{AtlasMergeSource ls rs | mergeSourceValid left right source
           && mergeResolvedAt left (arrowSource arrow) source}
      -> target:{AtlasMergeSource ls rs | mergeSourceValid left right target}
      -> () @-}
proofGuard :: Atlas la ls ld lo lf -> Atlas ra rs rd ro rf -> PageElementArrow ms s t
  -> AtlasMergeSource ls rs -> AtlasMergeSource ls rs -> ()
proofGuard = mergeResolvedTransport
""",
    "merge prefix transport requires the suffix arrow": """
{-@ proofGuard :: left:Atlas la ls ld lo lf -> right:Atlas ra rs rd ro rf
      -> sourcePage:Natural -> targetPage:{Natural | targetPage <= sourcePage}
      -> source:{AtlasMergePageCell | mergePageContains (atlasFolio left) (atlasFolio right) sourcePage source}
      -> target:{AtlasMergePageCell | mergePageContains (atlasFolio left) (atlasFolio right) targetPage target}
      -> () @-}
proofGuard :: Atlas la ls ld lo lf -> Atlas ra rs rd ro rf -> Natural -> Natural
  -> AtlasMergePageCell -> AtlasMergePageCell -> ()
proofGuard = mergePrefixNativeTransport
""",
    "merge raw transport requires the target owning trace": """
{-@ proofGuard :: left:Atlas la ls ld lo lf -> right:Atlas ra rs rd ro rf
      -> arrow:{PageElementArrow ms s t | mergeOccurrenceTraceValid left right (arrowSource arrow)
           && pageElementPage (arrowTarget arrow) > 0}
      -> source:{AtlasMergePageCell |
           mergePageContains (atlasFolio left) (atlasFolio right) (pageElementPage (arrowSource arrow) - 1) source
           && mergePagePosition (folioPageOrderType (atlasFolio left) (pageElementPage (arrowSource arrow) - 1)) source
                == pageElementPosition (arrowSource arrow)}
      -> target:{AtlasMergePageCell |
           mergePageContains (atlasFolio left) (atlasFolio right) (pageElementPage (arrowTarget arrow) - 1) target
           && mergePagePosition (folioPageOrderType (atlasFolio left) (pageElementPage (arrowTarget arrow) - 1)) target
                == pageElementPosition (arrowTarget arrow)}
      -> () @-}
proofGuard :: Atlas la ls ld lo lf -> Atlas ra rs rd ro rf -> PageElementArrow ms s t
  -> AtlasMergePageCell -> AtlasMergePageCell -> ()
proofGuard = mergeArrowNativeTransport
""",
    "merge raw transport requires the target encoded position": """
{-@ proofGuard :: left:Atlas la ls ld lo lf -> right:Atlas ra rs rd ro rf
      -> arrow:{PageElementArrow ms s t |
           mergeOccurrenceTraceValid left right (arrowSource arrow)
           && mergeOccurrenceTraceValid left right (arrowTarget arrow)
           && pageElementPage (arrowTarget arrow) > 0}
      -> source:{AtlasMergePageCell |
           mergePageContains (atlasFolio left) (atlasFolio right) (pageElementPage (arrowSource arrow) - 1) source
           && mergePagePosition (folioPageOrderType (atlasFolio left) (pageElementPage (arrowSource arrow) - 1)) source
                == pageElementPosition (arrowSource arrow)}
      -> target:{AtlasMergePageCell |
           mergePageContains (atlasFolio left) (atlasFolio right) (pageElementPage (arrowTarget arrow) - 1) target}
      -> () @-}
proofGuard :: Atlas la ls ld lo lf -> Atlas ra rs rd ro rf -> PageElementArrow ms s t
  -> AtlasMergePageCell -> AtlasMergePageCell -> ()
proofGuard = mergeArrowNativeTransport
""",
}

MERGE_ASSEMBLY_SOURCE = HASKELL / "src/DatraCore/Atlases/Derived/AtlasConfederations/AtlasMerge/Assembly.hs"
MERGE_ASSEMBLY_GUARDS = {
    "merge initial trace requires an accepted first-page cell": """
{-@ proofGuard :: Atlas la ls ld lo lf -> Atlas ra rs rd ro rf -> AtlasMergePageCell -> () @-}
proofGuard :: Atlas la ls ld lo lf -> Atlas ra rs rd ro rf -> AtlasMergePageCell -> ()
proofGuard = atlasMergePrefixOriginTrace
""",
    "merge initial trace cannot replace its position": """
{-@ proofGuard :: left:Atlas la ls ld lo lf -> right:Atlas ra rs rd ro rf
      -> cell:{AtlasMergePageCell | mergePageContains (atlasFolio left) (atlasFolio right) 0 cell}
      -> position:Ordinal
      -> {genuinePageElementTrace (atlasMergePrefix left right 1) cell == firstPageTrace position} @-}
proofGuard :: Atlas la ls ld lo lf -> Atlas ra rs rd ro rf -> AtlasMergePageCell -> Ordinal -> ()
proofGuard left right cell _ = atlasMergePrefixOriginTrace left right cell
""",
    "merge prefix trace cannot replace its head": """
{-@ proofGuard :: left:Atlas la ls ld lo lf -> right:Atlas ra rs rd ro rf
      -> depth:{Natural | depth > 0}
      -> cell:{AtlasMergePageCell | mergePageContains (atlasFolio left) (atlasFolio right) depth cell}
      -> position:Ordinal
      -> {genuinePageElementTrace (atlasMergePrefix left right (depth + 1)) cell
           == prependCopies 1 position
                (genuinePageElementTrace (atlasMergePrefix left right depth) (previousMergeCell left right depth cell))} @-}
proofGuard :: Atlas la ls ld lo lf -> Atlas ra rs rd ro rf -> Natural -> AtlasMergePageCell -> Ordinal -> ()
proofGuard left right depth cell _ = atlasMergePrefixTrace left right depth cell
""",
    "merge prefix trace requires an accepted next-page cell": """
{-@ proofGuard :: Atlas la ls ld lo lf -> Atlas ra rs rd ro rf
      -> depth:{Natural | depth > 0} -> AtlasMergePageCell -> () @-}
proofGuard :: Atlas la ls ld lo lf -> Atlas ra rs rd ro rf -> Natural -> AtlasMergePageCell -> ()
proofGuard = atlasMergePrefixTrace
""",
    "merge genuine cell lookup requires an accepted native cell": """
{-@ proofGuard :: left:Atlas la ls ld lo lf -> right:Atlas ra rs rd ro rf
      -> page:{Natural | page > 0 && page < atlasMergeLength left right} -> AtlasMergePageCell -> () @-}
proofGuard :: Atlas la ls ld lo lf -> Atlas ra rs rd ro rf -> Natural -> AtlasMergePageCell -> ()
proofGuard = atlasMergeCellLookup
""",
    "merge genuine lookup rejects a padded page": """
proofGuard :: Atlas la ls ld lo lf -> Atlas ra rs rd ro rf -> Ordinal -> ()
proofGuard left right position = atlasMergePageLookup left right (atlasMergeLength left right) position
""",
    "merge intermediate lookup rejects a longer prefix": """
{-@ proofGuard :: Atlas la ls ld lo lf -> Atlas ra rs rd ro rf -> depth:{Natural | depth > 0} -> Ordinal -> () @-}
proofGuard :: Atlas la ls ld lo lf -> Atlas ra rs rd ro rf -> Natural -> Ordinal -> ()
proofGuard left right depth position = atlasMergePrefixLookup left right (depth + 1) depth 0 position
""",

    "merge extension preserves only existing prefix lookups": """
{-@ proofGuard :: left:Atlas la ls ld lo lf -> right:Atlas ra rs rd ro rf
      -> page:{Natural | page > 0} -> depth:{Natural | page < depth}
      -> pages:{Folio () {cell:AtlasMergePageCell | mergePageContains (atlasFolio left) (atlasFolio right) (page - 1) cell} |
           folioLengthData pages == page + 1
           && chainPosition (lastPageData pages) == mergePagePosition (folioPageOrderType (atlasFolio left) (page - 1))}
      -> position:Ordinal -> () @-}
proofGuard :: Atlas la ls ld lo lf -> Atlas ra rs rd ro rf -> Natural -> Natural
  -> Folio () AtlasMergePageCell -> Ordinal -> ()
proofGuard left right page depth pages position =
  appendRemainingLookup left right page depth pages (folioLengthData pages) position
""",

    "merge assembly requires the prefix length": """
{-@ proofGuard :: left:Atlas la ls ld lo lf -> right:Atlas ra rs rd ro rf
      -> page:{Natural | page > 0} -> depth:{Natural | page <= depth}
      -> pages:{Folio () {cell:AtlasMergePageCell | mergePageContains (atlasFolio left) (atlasFolio right) (page - 1) cell} |
           folioLengthData pages == page
           && chainPosition (lastPageData pages) == mergePagePosition (folioPageOrderType (atlasFolio left) (page - 1))}
      -> () @-}
proofGuard :: Atlas la ls ld lo lf -> Atlas ra rs rd ro rf -> Natural -> Natural
  -> Folio () AtlasMergePageCell -> ()
proofGuard left right page depth pages = appendRemainingPages left right page depth pages `seq` ()
""",
    "merge assembly requires the prefix endpoint": """
{-@ proofGuard :: left:Atlas la ls ld lo lf -> right:Atlas ra rs rd ro rf
      -> page:{Natural | page > 0} -> depth:{Natural | page <= depth}
      -> pages:{Folio () {cell:AtlasMergePageCell | mergePageContains (atlasFolio left) (atlasFolio right) (page - 1) cell} |
           folioLengthData pages == page + 1}
      -> () @-}
proofGuard :: Atlas la ls ld lo lf -> Atlas ra rs rd ro rf -> Natural -> Natural
  -> Folio () AtlasMergePageCell -> ()
proofGuard left right page depth pages = appendRemainingPages left right page depth pages `seq` ()
""",
    "merge origin collapse requires a canonical chosen cell": """
{-@ proofGuard :: contains:(AtlasMergePageCell -> Bool)
      -> Chain {cell:AtlasMergePageCell | contains cell} -> Chain () -> AtlasMergePageCell -> () @-}
proofGuard :: (AtlasMergePageCell -> Bool) -> Chain AtlasMergePageCell -> Chain () -> AtlasMergePageCell -> ()
proofGuard contains source target chosen = collapseToOrigin contains source target chosen `seq` ()
""",
}

SEQUENCE_MEMBER_SOURCE = HASKELL / "src/DatraCore/Atlases/Derived/AtlasConfederations/AtlasSequence/Member.hs"
SEQUENCE_MEMBER_GUARDS = {
    "sequence member predecessors require canonical traces": """
{-@ proofGuard :: member:AtlasSequenceMember -> page:Natural -> positions:[Ordinal]
      -> {memberPageContains member page (previousTrace positions)} @-}
proofGuard :: AtlasSequenceMember -> Natural -> [Ordinal] -> ()
proofGuard = memberPagePrevious
""",
    "sequence member preimages belong to their owning member": """
{-@ proofGuard :: first:AtlasSequenceMember -> second:AtlasSequenceMember -> page:Natural
      -> positions:{[Ordinal] | memberPageContains first page positions}
      -> {result:[Ordinal] | memberPageContains second (page + 1) result} @-}
proofGuard :: AtlasSequenceMember -> AtlasSequenceMember -> Natural -> [Ordinal] -> [Ordinal]
proofGuard first _ page positions = memberPageNext first page positions
""",
    "sequence member transitions require the actual page positions": """
{-@ proofGuard :: member:AtlasSequenceMember -> page:Natural
      -> Chain {positions:[Ordinal] | memberPageContains member (page + 1) positions}
      -> Chain {positions:[Ordinal] | memberPageContains member page positions} -> () @-}
proofGuard :: AtlasSequenceMember -> Natural -> Chain [Ordinal] -> Chain [Ordinal] -> ()
proofGuard member page source target = memberPageTransition member page source target `seq` ()
""",
}

SEQUENCE_PAGE_SOURCE = HASKELL / "src/DatraCore/Atlases/Derived/AtlasConfederations/AtlasSequence/Page.hs"
SEQUENCE_PAGE_GUARDS = {
    "sequence native selection cannot switch its member": """
{-@ proofGuard :: members:[AtlasSequenceMember] -> page:Natural
      -> cell:{AtlasSequencePageCell | sequencePageContains members page cell}
      -> {member:AtlasSequenceMember | memberAt members (sequenceCellIndex cell) /= Just member} @-}
proofGuard :: [AtlasSequenceMember] -> Natural -> AtlasSequencePageCell -> AtlasSequenceMember
proofGuard = sequenceCellMember
""",
    "sequence stored predecessor cannot be replaced by identity": """
{-@ proofGuard :: members:[AtlasSequenceMember] -> page:{Natural | page > 0}
      -> target:{Chain {cell:AtlasSequencePageCell | sequencePageContains members (page - 1) cell} |
           chainPosition target == sequencePagePosition members (page - 1)}
      -> cell:{AtlasSequencePageCell | sequencePageContains members page cell}
      -> {result:AtlasSequencePageCell | result == cell} @-}
proofGuard :: [AtlasSequenceMember] -> Natural -> Chain AtlasSequencePageCell
  -> AtlasSequencePageCell -> AtlasSequencePageCell
proofGuard members page target cell = orderedApply (sequencePageTransition members page target) cell
""",
    "sequence stored preimage cannot be replaced by identity": """
{-@ proofGuard :: members:[AtlasSequenceMember] -> page:{Natural | page > 0}
      -> target:{Chain {cell:AtlasSequencePageCell | sequencePageContains members (page - 1) cell} |
           chainPosition target == sequencePagePosition members (page - 1)}
      -> cell:{AtlasSequencePageCell | sequencePageContains members (page - 1) cell}
      -> {result:AtlasSequencePageCell | result == cell} @-}
proofGuard :: [AtlasSequenceMember] -> Natural -> Chain AtlasSequencePageCell
  -> AtlasSequencePageCell -> AtlasSequencePageCell
proofGuard members page target cell = orderedPreimage (sequencePageTransition members page target) cell
""",
    "sequence transitions cannot widen their canonical carriers": """
{-@ proofGuard :: members:[AtlasSequenceMember] -> page:{Natural | page > 0}
      -> target:{Chain {cell:AtlasSequencePageCell | sequencePageContains members (page - 1) cell} |
           chainPosition target == sequencePagePosition members (page - 1)}
      -> OrderedConsolidation AtlasSequencePageCell AtlasSequencePageCell @-}
proofGuard :: [AtlasSequenceMember] -> Natural -> Chain AtlasSequencePageCell
  -> OrderedConsolidation AtlasSequencePageCell AtlasSequencePageCell
proofGuard = sequencePageTransition
""",
    "sequence transitions require the actual preceding page positions": """
{-@ proofGuard :: members:[AtlasSequenceMember] -> page:{Natural | page > 0}
      -> Chain {cell:AtlasSequencePageCell | sequencePageContains members (page - 1) cell} -> () @-}
proofGuard :: [AtlasSequenceMember] -> Natural -> Chain AtlasSequencePageCell -> ()
proofGuard members page target = sequencePageTransition members page target `seq` ()
""",
    "sequence transitions reject page zero": """
{-@ proofGuard :: [AtlasSequenceMember] -> () @-}
proofGuard :: [AtlasSequenceMember] -> ()
proofGuard members = sequencePageTransition members 0 (atlasSequencePageChain members 0) `seq` ()
""",
    "sequence page chains reject arbitrary raw cells": """
{-@ proofGuard :: [AtlasSequenceMember] -> Natural -> AtlasSequencePageCell -> Ordinal @-}
proofGuard :: [AtlasSequenceMember] -> Natural -> AtlasSequencePageCell -> Ordinal
proofGuard members page cell = chainPosition (atlasSequencePageChain members page) cell
""",
    "sequence cell encodings preserve their accepted carriers": """
{-@ proofGuard :: first:([Ordinal] -> Bool) -> rest:(AtlasSequencePageCell -> Bool)
      -> Either [Ordinal] AtlasSequencePageCell
      -> {cell:AtlasSequencePageCell | consContains first rest cell} @-}
proofGuard :: ([Ordinal] -> Bool) -> (AtlasSequencePageCell -> Bool)
  -> Either [Ordinal] AtlasSequencePageCell -> AtlasSequencePageCell
proofGuard = consCell
""",
}

SEQUENCE_ASSEMBLY_SOURCE = HASKELL / "src/DatraCore/Atlases/Derived/AtlasConfederations/AtlasSequence/Assembly.hs"
SEQUENCE_ASSEMBLY_GUARDS = {
    "sequence initial trace requires an accepted first-page cell": """
{-@ proofGuard :: NonEmpty AtlasSequenceMember -> AtlasSequencePageCell -> () @-}
proofGuard :: NonEmpty AtlasSequenceMember -> AtlasSequencePageCell -> ()
proofGuard = atlasSequencePrefixOriginTrace
""",
    "sequence initial trace cannot replace its position": """
{-@ proofGuard :: members:NonEmpty AtlasSequenceMember
      -> cell:{AtlasSequencePageCell | sequencePageContains (memberList members) 0 cell}
      -> position:Ordinal
      -> {genuinePageElementTrace (atlasSequencePrefix members 1) cell == firstPageTrace position} @-}
proofGuard :: NonEmpty AtlasSequenceMember -> AtlasSequencePageCell -> Ordinal -> ()
proofGuard members cell _ = atlasSequencePrefixOriginTrace members cell
""",
    "sequence prefix trace cannot replace its head": """
{-@ proofGuard :: members:NonEmpty AtlasSequenceMember -> depth:{Natural | depth > 0}
      -> cell:{AtlasSequencePageCell | sequencePageContains (memberList members) depth cell}
      -> position:Ordinal
      -> {genuinePageElementTrace (atlasSequencePrefix members (depth + 1)) cell
           == prependCopies 1 position
                (genuinePageElementTrace (atlasSequencePrefix members depth)
                  (previousSequenceCell (memberList members) depth cell))} @-}
proofGuard :: NonEmpty AtlasSequenceMember -> Natural -> AtlasSequencePageCell -> Ordinal -> ()
proofGuard members depth cell _ = atlasSequencePrefixTrace members depth cell
""",
    "sequence prefix trace requires an accepted next-page cell": """
{-@ proofGuard :: NonEmpty AtlasSequenceMember -> depth:{Natural | depth > 0} -> AtlasSequencePageCell -> () @-}
proofGuard :: NonEmpty AtlasSequenceMember -> Natural -> AtlasSequencePageCell -> ()
proofGuard = atlasSequencePrefixTrace
""",
    "sequence genuine cell lookup requires an accepted native cell": """
{-@ proofGuard :: members:NonEmpty AtlasSequenceMember
      -> page:{Natural | page > 0 && page < atlasSequenceLength members} -> AtlasSequencePageCell -> () @-}
proofGuard :: NonEmpty AtlasSequenceMember -> Natural -> AtlasSequencePageCell -> ()
proofGuard = atlasSequenceCellLookup
""",
    "sequence genuine lookup rejects a padded page": """
proofGuard :: NonEmpty AtlasSequenceMember -> Ordinal -> ()
proofGuard members position = atlasSequencePageLookup members (atlasSequenceLength members) position
""",
    "sequence intermediate lookup rejects a longer prefix": """
{-@ proofGuard :: NonEmpty AtlasSequenceMember -> depth:{Natural | depth > 0} -> Ordinal -> () @-}
proofGuard :: NonEmpty AtlasSequenceMember -> Natural -> Ordinal -> ()
proofGuard members depth position = atlasSequencePrefixLookup members (depth + 1) depth 0 position
""",

    "sequence extension preserves only existing prefix lookups": """
{-@ proofGuard :: members:[AtlasSequenceMember] -> page:{Natural | page > 0} -> depth:{Natural | page < depth}
      -> pages:{Folio () {cell:AtlasSequencePageCell | sequencePageContains members (page - 1) cell} |
           folioLengthData pages == page + 1
           && chainPosition (lastPageData pages) == sequencePagePosition members (page - 1)}
      -> position:Ordinal -> () @-}
proofGuard :: [AtlasSequenceMember] -> Natural -> Natural -> Folio () AtlasSequencePageCell -> Ordinal -> ()
proofGuard members page depth pages position =
  appendRemainingLookup members page depth pages (folioLengthData pages) position
""",

    "sequence assembly requires the prefix length": """
{-@ proofGuard :: members:[AtlasSequenceMember] -> page:{Natural | page > 0} -> depth:{Natural | page <= depth}
      -> pages:{Folio () {cell:AtlasSequencePageCell | sequencePageContains members (page - 1) cell} |
           folioLengthData pages == page
           && chainPosition (lastPageData pages) == sequencePagePosition members (page - 1)} -> () @-}
proofGuard :: [AtlasSequenceMember] -> Natural -> Natural -> Folio () AtlasSequencePageCell -> ()
proofGuard members page depth pages = appendRemainingPages members page depth pages `seq` ()
""",
    "sequence assembly requires the prefix endpoint": """
{-@ proofGuard :: members:[AtlasSequenceMember] -> page:{Natural | page > 0} -> depth:{Natural | page <= depth}
      -> pages:{Folio () {cell:AtlasSequencePageCell | sequencePageContains members (page - 1) cell} |
           folioLengthData pages == page + 1} -> () @-}
proofGuard :: [AtlasSequenceMember] -> Natural -> Natural -> Folio () AtlasSequencePageCell -> ()
proofGuard members page depth pages = appendRemainingPages members page depth pages `seq` ()
""",
    "sequence assembly requires an inhabited first member": """
{-@ proofGuard :: () -> AtlasSequencePageCell @-}
proofGuard :: () -> AtlasSequencePageCell
proofGuard () = firstCellFromList []
""",
}

REINDEX_CONSOLIDATION_SOURCE = HASKELL / "src/DatraCore/Atlases/Core/Consolidation/Reindex.hs"
REINDEX_CONSOLIDATION_GUARDS = {
    "consolidation reindexing requires the source inverse": """
{-@ proofGuard :: OrderedConsolidation Int Int -> OrderedConsolidation Int Int @-}
proofGuard :: OrderedConsolidation Int Int -> OrderedConsolidation Int Int
proofGuard mapping = reindexConsolidation (const True) (const True) mapping
  (const 0) id (const ()) (const ()) id id (const ()) (const ())
""",
    "consolidation reindexing requires the target inverse": """
{-@ proofGuard :: OrderedConsolidation Int Int -> OrderedConsolidation Int Int @-}
proofGuard :: OrderedConsolidation Int Int -> OrderedConsolidation Int Int
proofGuard mapping = reindexConsolidation (const True) (const True) mapping
  id id (const ()) (const ()) (const 0) id (const ()) (const ())
""",
}

SUM_CONSOLIDATION_SOURCE = HASKELL / "src/DatraCore/Atlases/Core/Consolidation/Sum.hs"
SUM_CONSOLIDATION_GUARDS = {
    "sum consolidations require matching endpoint positions": """
{-@ proofGuard :: OrderedConsolidation a b -> OrderedConsolidation c d
      -> Chain (Either a c) -> Chain (Either b d)
      -> OrderedConsolidation (Either a c) (Either b d) @-}
proofGuard :: OrderedConsolidation a b -> OrderedConsolidation c d
  -> Chain (Either a c) -> Chain (Either b d)
  -> OrderedConsolidation (Either a c) (Either b d)
proofGuard = sumConsolidationsBetween
""",
    "sum consolidation monotonicity requires the source order": """
{-@ proofGuard :: left:OrderedConsolidation a b -> right:OrderedConsolidation c d
      -> first:Either a c -> second:Either a c
      -> {result:Either b d | sumPrecedes (orderedTarget left) (orderedTarget right)
            (sumApply left right first) result} @-}
proofGuard :: OrderedConsolidation a b -> OrderedConsolidation c d
  -> Either a c -> Either a c -> Either b d
proofGuard left right first second =
  sumApplyMonotone left right first (sumApply left right first) second
""",
    "sum consolidation cannot exchange summand tags": """
{-@ proofGuard :: left:OrderedConsolidation a b -> right:OrderedConsolidation a b
      -> value:a -> {result:Either b b | result == Left (orderedApply left value)} @-}
proofGuard :: OrderedConsolidation a b -> OrderedConsolidation a b -> a -> Either b b
{-@ ple proofGuard @-}
proofGuard left right value = sumApply left right (Right value)
""",
}

PAGE_TRACE_SOURCE = HASKELL / "src/DatraCore/Atlases/Core/PageElements/TraceChain.hs"
PAGE_TRACE_GUARDS = {
    "padded trace lookup requires a padded page": """
{-@ proofGuard :: pages:Folio origin final -> page:Natural -> position:Ordinal
      -> previous:{[Ordinal] | folioTraceLookup pages (page - 1) position == Just previous}
      -> () @-}
proofGuard :: Folio origin final -> Natural -> Ordinal -> [Ordinal] -> ()
proofGuard = folioLookupPaddedStep
""",
    "trace consolidations require the actual position functions": """
{-@ proofGuard :: pages:Folio origin final -> page:Natural
      -> Chain {positions:[Ordinal] | pageTraceContains pages (page + 1) positions}
      -> Chain {positions:[Ordinal] | pageTraceContains pages page positions}
      -> OrderedConsolidation
           {positions:[Ordinal] | pageTraceContains pages (page + 1) positions}
           {positions:[Ordinal] | pageTraceContains pages page positions} @-}
proofGuard :: Folio origin final -> Natural -> Chain [Ordinal] -> Chain [Ordinal]
  -> OrderedConsolidation [Ordinal] [Ordinal]
proofGuard pages page source target = pageTraceTransition pages page source target
""",
    "trace consolidations reject an unowned input trace": """
{-@ proofGuard :: pages:Folio origin final -> page:Natural
      -> OrderedConsolidation
           {positions:[Ordinal] | pageTraceContains pages (page + 1) positions}
           {positions:[Ordinal] | pageTraceContains pages page positions}
      -> [Ordinal] -> [Ordinal] @-}
proofGuard :: Folio origin final -> Natural -> OrderedConsolidation [Ordinal] [Ordinal]
  -> [Ordinal] -> [Ordinal]
proofGuard _ _ mapping positions = orderedApply mapping positions
""",
    "trace monotonicity requires an ordered source pair": """
{-@ proofGuard :: pages:Folio origin final -> page:Natural
      -> first:{[Ordinal] | pageTraceContains pages (page + 1) first}
      -> second:{[Ordinal] | pageTraceContains pages (page + 1) second}
      -> {tracePrecedes (previousTrace first) (previousTrace second)} @-}
proofGuard :: Folio origin final -> Natural -> [Ordinal] -> [Ordinal] -> ()
proofGuard pages page first second = pageTracePreviousMonotone pages page first second
""",
    "trace monotonicity requires the owning page": """
{-@ proofGuard :: pages:Folio origin final -> page:Natural
      -> first:[Ordinal] -> second:{[Ordinal] | tracePrecedes first second}
      -> {tracePrecedes (previousTrace first) (previousTrace second)} @-}
proofGuard :: Folio origin final -> Natural -> [Ordinal] -> [Ordinal] -> ()
proofGuard pages page first second = pageTracePreviousMonotone pages page first second
""",
    "trace preimages require membership in the source page": """
{-@ proofGuard :: pages:Folio origin final -> page:Natural -> positions:[Ordinal]
      -> {result:[Ordinal] | pageTraceContains pages (page + 1) result} @-}
proofGuard :: Folio origin final -> Natural -> [Ordinal] -> [Ordinal]
proofGuard = pageTraceNext
""",
    "trace predecessors require membership in the source page": """
{-@ proofGuard :: pages:Folio origin final -> page:Natural -> positions:[Ordinal]
      -> {pageTraceContains pages page (previousTrace positions)} @-}
proofGuard :: Folio origin final -> Natural -> [Ordinal] -> ()
proofGuard = pageTracePrevious
""",
    "native trace chains cannot widen their accepted carrier": """
{-@ proofGuard :: Folio origin final -> Natural -> Chain [Ordinal] @-}
proofGuard :: Folio origin final -> Natural -> Chain [Ordinal]
proofGuard = pageTraceChain
""",
}

MERGE_PAGE_SOURCE = HASKELL / "src/DatraCore/Atlases/Derived/AtlasConfederations/AtlasMerge/Page.hs"
MERGE_PAGE_GUARDS = {
    "merge stored forward map cannot change components": """
{-@ proofGuard :: left:Atlas la ls ld lo lf -> right:Atlas ra rs rd ro rf
      -> page:{Natural | page > 0}
      -> positions:{[Ordinal] | pageTraceContains (atlasFolio left) page positions}
      -> {result:AtlasMergePageCell | result == AtlasMergeRightCell (previousTrace positions)} @-}
proofGuard :: Atlas la ls ld lo lf -> Atlas ra rs rd ro rf -> Natural -> [Ordinal] -> AtlasMergePageCell
proofGuard left right page positions =
  orderedApply (mergePageTransition left right page (atlasMergePageChain left right (page - 1)))
    (AtlasMergeLeftCell positions)
""",
    "merge stored preimage cannot choose the other component": """
{-@ proofGuard :: left:Atlas la ls ld lo lf -> right:Atlas ra rs rd ro rf
      -> page:{Natural | page > 0}
      -> positions:{[Ordinal] | pageTraceContains (atlasFolio left) (page - 1) positions}
      -> {result:AtlasMergePageCell |
           result == AtlasMergeRightCell (pageTraceNext (atlasFolio left) (page - 1) positions)} @-}
proofGuard :: Atlas la ls ld lo lf -> Atlas ra rs rd ro rf -> Natural -> [Ordinal] -> AtlasMergePageCell
proofGuard left right page positions =
  orderedPreimage (mergePageTransition left right page (atlasMergePageChain left right (page - 1)))
    (AtlasMergeLeftCell positions)
""",

    "merge transitions cannot widen their canonical carriers": """
{-@ proofGuard :: left:Atlas la ls ld lo lf -> right:Atlas ra rs rd ro rf
      -> page:{Natural | page > 0}
      -> target:{Chain {cell:AtlasMergePageCell | mergePageContains (atlasFolio left) (atlasFolio right) (page - 1) cell} |
           chainPosition target == mergePagePosition (folioPageOrderType (atlasFolio left) (page - 1))}
      -> OrderedConsolidation AtlasMergePageCell AtlasMergePageCell @-}
proofGuard :: Atlas la ls ld lo lf -> Atlas ra rs rd ro rf -> Natural -> Chain AtlasMergePageCell
  -> OrderedConsolidation AtlasMergePageCell AtlasMergePageCell
proofGuard = mergePageTransition
""",
    "merge transitions require the actual preceding page positions": """
{-@ proofGuard :: left:Atlas la ls ld lo lf -> right:Atlas ra rs rd ro rf
      -> page:{Natural | page > 0}
      -> Chain {cell:AtlasMergePageCell | mergePageContains (atlasFolio left) (atlasFolio right) (page - 1) cell}
      -> () @-}
proofGuard :: Atlas la ls ld lo lf -> Atlas ra rs rd ro rf -> Natural -> Chain AtlasMergePageCell -> ()
proofGuard left right page target = mergePageTransition left right page target `seq` ()
""",
    "merge transitions reject page zero": """
{-@ proofGuard :: Atlas la ls ld lo lf -> Atlas ra rs rd ro rf -> () @-}
proofGuard :: Atlas la ls ld lo lf -> Atlas ra rs rd ro rf -> ()
proofGuard left right = mergePageTransition left right 0 (atlasMergePageChain left right 0) `seq` ()
""",
    "merge preimages cannot use the other component as their inverse": """
{-@ proofGuard :: left:Atlas la ls ld lo lf -> right:Atlas ra rs rd ro rf
      -> page:{Natural | page > 0}
      -> positions:{[Ordinal] | pageTraceContains (atlasFolio left) (page - 1) positions}
      -> {cell:AtlasMergePageCell |
           previousMergeCell left right page cell == AtlasMergeLeftCell positions} @-}
proofGuard :: Atlas la ls ld lo lf -> Atlas ra rs rd ro rf -> Natural -> [Ordinal] -> AtlasMergePageCell
proofGuard left _ page positions =
  AtlasMergeRightCell (pageTraceNext (atlasFolio left) (page - 1) positions)
""",
    "merge predecessors reject page zero": """
{-@ proofGuard :: left:Atlas la ls ld lo lf -> right:Atlas ra rs rd ro rf
      -> cell:{AtlasMergePageCell | mergePageContains (atlasFolio left) (atlasFolio right) 0 cell}
      -> AtlasMergePageCell @-}
proofGuard :: Atlas la ls ld lo lf -> Atlas ra rs rd ro rf -> AtlasMergePageCell -> AtlasMergePageCell
proofGuard left right cell = previousMergeCell left right 0 cell
""",
    "merge predecessors cannot switch the owning component": """
{-@ proofGuard :: left:Atlas la ls ld lo lf -> right:Atlas ra rs rd ro rf
      -> page:{Natural | page > 0}
      -> positions:{[Ordinal] | pageTraceContains (atlasFolio left) page positions}
      -> {cell:AtlasMergePageCell | mergePageContains (atlasFolio left) (atlasFolio right) (page - 1) cell} @-}
proofGuard :: Atlas la ls ld lo lf -> Atlas ra rs rd ro rf -> Natural -> [Ordinal] -> AtlasMergePageCell
proofGuard left _ page positions =
  previousPageTrace (atlasFolio left) (page - 1) positions `seq`
    AtlasMergeRightCell (previousTrace positions)
""",
    "merge page chains cannot accept arbitrary component traces": """
{-@ proofGuard :: Atlas la ls ld lo lf -> Atlas ra rs rd ro rf -> Natural -> Chain AtlasMergePageCell @-}
proofGuard :: Atlas la ls ld lo lf -> Atlas ra rs rd ro rf -> Natural -> Chain AtlasMergePageCell
proofGuard = atlasMergePageChain
""",
}


STABLE_SOURCE = HASKELL / "src/DatraCore/Atlases/Derived/AtlasTransposals/StableAtlasTransversal/Internal.hs"
STABLE_GUARDS = {
    "stored stable mapped images retain target validity": """
{-@ proofGuard :: action:StableTransversalAction sa ss sd so sf ta ts td to tf mo mf
      -> value:{CoalitionData sa ss sd | StableCoalitionValid (stableActionSource action) value}
      -> {image:CoalitionData ta ts td |
           not (coalitionElementValid (stableActionMappedTarget action) image)} @-}
proofGuard :: StableTransversalAction sa ss sd so sf ta ts td to tf mo mf
  -> CoalitionData sa ss sd -> CoalitionData ta ts td
proofGuard action value =
  stableActionForwardValid action value `seq` applyInsertion (stableActionInsertion action) value
""",
    "stored stable mapped images retain the canonical target origin": """
{-@ proofGuard :: action:StableTransversalAction sa ss sd so sf ta ts td to tf mo mf
      -> value:{CoalitionData sa ss sd | StableCoalitionValid (stableActionSource action) value}
      -> {image:CoalitionData ta ts td |
           coalitionElementSource image /= originPageElement (atlasPageElements (stableActionMappedTarget action))} @-}
proofGuard :: StableTransversalAction sa ss sd so sf ta ts td to tf mo mf
  -> CoalitionData sa ss sd -> CoalitionData ta ts td
proofGuard action value =
  stableActionForwardValid action value `seq` applyInsertion (stableActionInsertion action) value
""",
    "composed inverse packages retain source validity on arbitrary raw targets": """
{-@ proofGuard :: first:CoalitionInverseData a s d o f ma ms md
      -> (CoalitionData ta ts td -> Maybe (CoalitionData ma ms md))
      -> CoalitionData ta ts td
      -> Maybe ({source:CoalitionData a s d |
           not (coalitionElementValid (coalitionInverseOwner first) source)}) @-}
proofGuard :: CoalitionInverseData a s d o f ma ms md
  -> (CoalitionData ta ts td -> Maybe (CoalitionData ma ms md))
  -> CoalitionData ta ts td -> Maybe (CoalitionData a s d)
proofGuard first second target =
  coalitionInverseFunction (composeCoalitionInverseData first second) target
""",
    "stored stable insertions require canonical source inputs": """
proofGuard :: StableTransversalAction sa ss sd so sf ta ts td to tf mo mf
  -> CoalitionData sa ss sd -> CoalitionData ta ts td
proofGuard action value = applyInsertion (stableActionInsertion action) value
""",
    "stored stable insertions retain the actual forward action": """
{-@ proofGuard :: source:Atlas sa ss sd so sf -> target:Atlas ta ts td to tf
      -> arrow:AtlasTransversal (AtlasObject sa ss sd) (AtlasObject ta ts td)
      -> {proof:() | stableOriginPreserved source target arrow}
      -> mapped:Atlas ta ts td mo mf
      -> insertion:DomanialInsertion ({value:CoalitionData sa ss sd | StableCoalitionValid source value})
           (CoalitionData ta ts td)
      -> (value:{CoalitionData sa ss sd | StableCoalitionValid source value}
           -> {StableCoalitionValid mapped (applyInsertion insertion value)})
      -> StableTransversalAction sa ss sd so sf ta ts td to tf mo mf @-}
proofGuard :: Atlas sa ss sd so sf -> Atlas ta ts td to tf
  -> AtlasTransversal (AtlasObject sa ss sd) (AtlasObject ta ts td) -> ()
  -> Atlas ta ts td mo mf
  -> DomanialInsertion (CoalitionData sa ss sd) (CoalitionData ta ts td)
  -> (CoalitionData sa ss sd -> ())
  -> StableTransversalAction sa ss sd so sf ta ts td to tf mo mf
proofGuard = StableTransversalAction
""",
    "stable inverses must retain source validity outside the forward image": """
{-@ proofGuard :: source:Atlas sa ss sd so sf -> target:Atlas ta ts td to tf
      -> arrow:AtlasTransversal (AtlasObject sa ss sd) (AtlasObject ta ts td)
      -> {proof:() | stableOriginPreserved source target arrow}
      -> backward:(CoalitionData ta ts td -> Maybe (CoalitionData sa ss sd))
      -> (value:{CoalitionData sa ss sd | StableCoalitionValid source value}
            -> {backward (mapCoalitionElement source arrow value) == Just value})
      -> StableAtlasTransversal (AtlasObject sa ss sd) (AtlasObject ta ts td) @-}
proofGuard :: Atlas sa ss sd so sf -> Atlas ta ts td to tf
  -> AtlasTransversal (AtlasObject sa ss sd) (AtlasObject ta ts td) -> ()
  -> (CoalitionData ta ts td -> Maybe (CoalitionData sa ss sd))
  -> (CoalitionData sa ss sd -> ())
  -> StableAtlasTransversal (AtlasObject sa ss sd) (AtlasObject ta ts td)
proofGuard = stableAtlasTransversal
""",
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


DOMINC_DATA_SOURCE = HASKELL / "src/DatraCore/Atlases/Derived/Coalitions/DomanialInclusion/Data.hs"
DOMINC_PRESENTATION_SOURCE = HASKELL / "src/DatraCore/Atlases/Derived/Coalitions/DomanialInclusion/Presentation.hs"
DOMINC_PRESENTATION_GUARDS = {
    "Dominion owner storage requires constant membership": """
{-@ proofGuard :: presentation:{AtlasPresentation (DominionPaginationScope a) (DominionCellData a) () () |
      folioLength (pageElementsFolio (paginationPageElements (atlasPresentationPagination presentation))) == 1
      && atlasActionMap (atlasPresentationAction presentation) == constantDataMap}
      -> value:{Atlas owner (DominionPaginationScope a) (DominionCellData a) () () |
        atlasDescription value == presentation && atlasPagination value == atlasPresentationPagination presentation}
      -> DominionAtlas owner a @-}
proofGuard :: AtlasPresentation (DominionPaginationScope a) (DominionCellData a) () ()
  -> Atlas owner (DominionPaginationScope a) (DominionCellData a) () ()
  -> DominionAtlas owner a
proofGuard presentation value = retainDominionAtlas presentation value
""",
    "Dominion owner storage requires identity insertion": """
{-@ proofGuard :: presentation:{AtlasPresentation (DominionPaginationScope a) (DominionCellData a) () () |
      folioLength (pageElementsFolio (paginationPageElements (atlasPresentationPagination presentation))) == 1
      && atlasActionMembership (atlasPresentationAction presentation) == atlasMembership acceptsConstantDatum}
      -> value:{Atlas owner (DominionPaginationScope a) (DominionCellData a) () () |
        atlasDescription value == presentation && atlasPagination value == atlasPresentationPagination presentation}
      -> DominionAtlas owner a @-}
proofGuard :: AtlasPresentation (DominionPaginationScope a) (DominionCellData a) () ()
  -> Atlas owner (DominionPaginationScope a) (DominionCellData a) () ()
  -> DominionAtlas owner a
proofGuard presentation value = retainDominionAtlas presentation value
""",
    "Dominion owner accepts every constant datum": """
{-@ proofGuard :: owner:DominionAtlas ownerScope a
      -> occurrence:PageElement (DominionPaginationScope a) object
      -> datum:DominionCellData a object
      -> {not (atlasAcceptsDatum (dominionAtlas owner) occurrence datum)} @-}
proofGuard :: DominionAtlas owner a
  -> PageElement (DominionPaginationScope a) object -> DominionCellData a object -> ()
proofGuard = dominionAcceptsDatum
""",
    "Dominion owner storage requires a one-page Atlas": """
{-@ proofGuard :: presentation:{AtlasPresentation (DominionPaginationScope a) (DominionCellData a) () () |
      atlasActionMembership (atlasPresentationAction presentation) == atlasMembership acceptsConstantDatum
      && atlasActionMap (atlasPresentationAction presentation) == constantDataMap}
      -> value:{Atlas owner (DominionPaginationScope a) (DominionCellData a) () () |
        atlasDescription value == presentation && atlasPagination value == atlasPresentationPagination presentation}
      -> DominionAtlas owner a @-}
proofGuard :: AtlasPresentation (DominionPaginationScope a) (DominionCellData a) () ()
  -> Atlas owner (DominionPaginationScope a) (DominionCellData a) () ()
  -> DominionAtlas owner a
proofGuard presentation value = retainDominionAtlas presentation value
""",
    "Dominion owner observation retains its one-page certificate": """
{-@ proofGuard :: DominionAtlas owner a
      -> {value:Atlas owner (DominionPaginationScope a) (DominionCellData a) () () |
           folioLength (atlasFolio value) /= 1} @-}
proofGuard :: DominionAtlas owner a
  -> Atlas owner (DominionPaginationScope a) (DominionCellData a) () ()
proofGuard = dominionAtlas
""",
    "canonical Dominion allocation retains its one-page certificate": """
{-@ proofGuard :: CanonicalDominion a => Proxy a
      -> {value:Atlas (CanonicalDominionAtlasScope a) (DominionPaginationScope a) (DominionCellData a) () () |
           folioLength (atlasFolio value) /= 1} @-}
proofGuard :: forall a. CanonicalDominion a => Proxy a
  -> Atlas (CanonicalDominionAtlasScope a) (DominionPaginationScope a) (DominionCellData a) () ()
proofGuard _ = dominionAtlas (canonicalDominionAtlas @a)
""",
    "Dominion pagination recipe retains its one-page contract": """
{-@ proofGuard :: Proxy (DominionPaginationRecipe a)
      -> {pages:Folio () () | folioLength pages /= 1} @-}
proofGuard :: Proxy (DominionPaginationRecipe a) -> Folio () ()
proofGuard = pageElementsRecipe
""",
    "Dominion presentation retains its one-page recipe": """
{-@ proofGuard :: Dominion a
      -> {presentation:AtlasPresentation (DominionPaginationScope a) (DominionCellData a) () () |
           folioLength (pageElementsFolio (paginationPageElements (atlasPresentationPagination presentation))) > 1} @-}
proofGuard :: Dominion a -> AtlasPresentation (DominionPaginationScope a) (DominionCellData a) () ()
proofGuard = dominionPresentation
""",
    "constant Atlas presentation requires a one-page folio": """
{-@ proofGuard :: Pagination scope origin final -> Dominion a
      -> AtlasPresentation scope (DominionCellData a) origin final @-}
proofGuard :: Pagination scope origin final -> Dominion a
  -> AtlasPresentation scope (DominionCellData a) origin final
proofGuard = constantPresentation
""",
    "same-page position requires valid owning traces": """
{-@ proofGuard :: category:PageElements scope origin final
      -> arrow:{PageElementArrow scope source target |
           pageElementPage (arrowSource arrow) == pageElementPage (arrowTarget arrow)}
      -> {pageElementPosition (arrowSource arrow) == pageElementPosition (arrowTarget arrow)} @-}
proofGuard :: PageElements scope origin final -> PageElementArrow scope source target -> ()
proofGuard = samePagePosition
""",
    "same-page position requires equal page numbers": """
{-@ proofGuard :: category:PageElements scope origin final
      -> arrow:{PageElementArrow scope source target |
           pageElementTraceValid category (arrowSource arrow)
           && pageElementTraceValid category (arrowTarget arrow)}
      -> {pageElementPosition (arrowSource arrow) == pageElementPosition (arrowTarget arrow)} @-}
proofGuard :: PageElements scope origin final -> PageElementArrow scope source target -> ()
proofGuard = samePagePosition
""",
}


DOMINC_TRANSPORT_PUBLIC_SOURCE = r"""
{-# LANGUAGE CPP #-}
#include "LiquidPlugin.h"
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--higherorder" @-}
module DominionTransportPublicGuard where
import Atlas (Atlas, atlasPageElements, atlasDescription, atlasPresentationAction,
  atlasActionMap, normalizeAtlasArrow, mapAtlasData, atlasDescriptionMap)
import DomanialInclusion.Presentation
  (DominionAtlas, DominionPaginationScope, dominionAtlas, dominionMapDataIdentity)
import DomanialInclusion.Data (DominionCellData, identityCellMap, identityCellPreimage)
import DomanialInsertion.Core (DomanialInsertion (..))
import PageElements (pageElementTraceValid)
import PageElements.Structure (PageElementArrow, arrowSource, arrowTarget)

{-@ observedDescriptionMap :: owner:Atlas a s d o f
      -> arrow:{PageElementArrow s source target |
           pageElementTraceValid (atlasPageElements owner) (arrowSource arrow)
           && pageElementTraceValid (atlasPageElements owner) (arrowTarget arrow)}
      -> {mapAtlasData owner arrow ==
           atlasActionMap (atlasPresentationAction (atlasDescription owner))
             (normalizeAtlasArrow owner arrow)} @-}
observedDescriptionMap :: Atlas a s d o f -> PageElementArrow s source target -> ()
observedDescriptionMap = atlasDescriptionMap

{-@ observedTransport :: owner:DominionAtlas ownerScope a
      -> arrow:{PageElementArrow (DominionPaginationScope a) source target |
           pageElementTraceValid (atlasPageElements (dominionAtlas owner)) (arrowSource arrow)
           && pageElementTraceValid (atlasPageElements (dominionAtlas owner)) (arrowTarget arrow)}
      -> {applyInsertion (mapAtlasData (dominionAtlas owner) arrow) == identityCellMap
           && preimage (mapAtlasData (dominionAtlas owner) arrow) == identityCellPreimage} @-}
observedTransport :: DominionAtlas owner a
  -> PageElementArrow (DominionPaginationScope a) source target -> ()
observedTransport = dominionMapDataIdentity
"""
DOMINC_TRANSPORT_PUBLIC_GUARDS = {
    "Dominion transport retains the entire identity forward map": r"""
{-@ proofGuard :: owner:DominionAtlas ownerScope a
      -> arrow:{PageElementArrow (DominionPaginationScope a) source target |
           pageElementTraceValid (atlasPageElements (dominionAtlas owner)) (arrowSource arrow)
           && pageElementTraceValid (atlasPageElements (dominionAtlas owner)) (arrowTarget arrow)}
      -> {applyInsertion (mapAtlasData (dominionAtlas owner) arrow) /= identityCellMap} @-}
proofGuard :: DominionAtlas owner a
  -> PageElementArrow (DominionPaginationScope a) source target -> ()
proofGuard = observedTransport
""",
    "Dominion transport retains the entire identity decoder": r"""
{-@ proofGuard :: owner:DominionAtlas ownerScope a
      -> arrow:{PageElementArrow (DominionPaginationScope a) source target |
           pageElementTraceValid (atlasPageElements (dominionAtlas owner)) (arrowSource arrow)
           && pageElementTraceValid (atlasPageElements (dominionAtlas owner)) (arrowTarget arrow)}
      -> {preimage (mapAtlasData (dominionAtlas owner) arrow) /= identityCellPreimage} @-}
proofGuard :: DominionAtlas owner a
  -> PageElementArrow (DominionPaginationScope a) source target -> ()
proofGuard = observedTransport
""",
    "Dominion transport requires valid owning traces": r"""
{-@ proofGuard :: owner:DominionAtlas ownerScope a
      -> arrow:PageElementArrow (DominionPaginationScope a) source target
      -> {applyInsertion (mapAtlasData (dominionAtlas owner) arrow) == identityCellMap
           && preimage (mapAtlasData (dominionAtlas owner) arrow) == identityCellPreimage} @-}
proofGuard :: DominionAtlas owner a
  -> PageElementArrow (DominionPaginationScope a) source target -> ()
proofGuard = observedTransport
""",
    "Atlas transport retains the exact normalized presentation insertion": r"""
{-@ proofGuard :: owner:Atlas a s d o f
      -> arrow:{PageElementArrow s source target |
           pageElementTraceValid (atlasPageElements owner) (arrowSource arrow)
           && pageElementTraceValid (atlasPageElements owner) (arrowTarget arrow)}
      -> {mapAtlasData owner arrow /=
           atlasActionMap (atlasPresentationAction (atlasDescription owner))
             (normalizeAtlasArrow owner arrow)} @-}
proofGuard :: Atlas a s d o f -> PageElementArrow s source target -> ()
proofGuard = observedDescriptionMap
""",
}


DOMINC_ACTION_PUBLIC_SOURCE = r"""
{-# LANGUAGE CPP #-}
{-# LANGUAGE TypeFamilies #-}
#include "LiquidPlugin.h"
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--higherorder" @-}
module DominionActionPublicGuard where
import Atlas (Atlas, AtlasMappedObject, AtlasObjectMap, atlasPageElements, mapPrimitiveElement)
import DomanialInclusion.Action (OriginObjectMap, constantObject, constantObjectPreservesArrow)
import PageElements (PageElement, pageElementTraceValid)
import PageElements.Structure
  ( SomePageElement, pageElementPage, pageElementPosition, pageElementTrace, pageElementCell
  , somePageElementPrecedes, somePageElementTransported )

{-@ observedConstantObject :: owner:Atlas a ts d o f
      -> target:{PageElement ts targetObject | pageElementTraceValid (atlasPageElements owner) target}
      -> PageElement ss sourceObject
      -> {result:PageElement ts (AtlasMappedObject (OriginObjectMap targetObject) sourceObject) |
           pageElementTraceValid (atlasPageElements owner) result
           && pageElementPage result == pageElementPage target
           && pageElementPosition result == pageElementPosition target
           && pageElementTrace result == pageElementTrace target
           && pageElementCell result == pageElementCell target} @-}
observedConstantObject :: Atlas a ts d o f -> PageElement ts targetObject
  -> PageElement ss sourceObject -> PageElement ts (AtlasMappedObject (OriginObjectMap targetObject) sourceObject)
observedConstantObject = constantObject

{-@ observedConstantPageLaw :: witness:AtlasObjectMap (OriginObjectMap targetObject)
      -> sourceAtlas:Atlas sa ss sd so sf -> targetAtlas:Atlas ta ts td to tf
      -> targetOccurrence:{PageElement ts targetObject |
           pageElementTraceValid (atlasPageElements targetAtlas) targetOccurrence}
      -> source:SomePageElement ss -> destination:SomePageElement ss
      -> {result:Bool | result} @-}
observedConstantPageLaw :: AtlasObjectMap (OriginObjectMap targetObject)
  -> Atlas sa ss sd so sf -> Atlas ta ts td to tf -> PageElement ts targetObject
  -> SomePageElement ss -> SomePageElement ss -> Bool
observedConstantPageLaw witness sourceAtlas targetAtlas targetOccurrence source destination =
  constantObjectPreservesArrow witness sourceAtlas targetAtlas targetOccurrence source destination `seq`
    (somePageElementPrecedes
       (mapPrimitiveElement witness sourceAtlas targetAtlas (constantObject targetAtlas targetOccurrence) source)
       (mapPrimitiveElement witness sourceAtlas targetAtlas (constantObject targetAtlas targetOccurrence) destination)
     && somePageElementTransported
       (mapPrimitiveElement witness sourceAtlas targetAtlas (constantObject targetAtlas targetOccurrence) source)
       (mapPrimitiveElement witness sourceAtlas targetAtlas (constantObject targetAtlas targetOccurrence) destination))
"""
DOMINC_ACTION_PUBLIC_GUARDS = {
    "constant inclusion objects retain every target field": r"""
{-@ proofGuard :: owner:Atlas a ts d o f
      -> target:{PageElement ts targetObject | pageElementTraceValid (atlasPageElements owner) target}
      -> PageElement ss sourceObject
      -> {result:PageElement ts (AtlasMappedObject (OriginObjectMap targetObject) sourceObject) |
           pageElementPage result /= pageElementPage target
           || pageElementPosition result /= pageElementPosition target
           || pageElementTrace result /= pageElementTrace target
           || pageElementCell result /= pageElementCell target} @-}
proofGuard :: Atlas a ts d o f -> PageElement ts targetObject
  -> PageElement ss sourceObject -> PageElement ts (AtlasMappedObject (OriginObjectMap targetObject) sourceObject)
proofGuard = observedConstantObject
""",
    "constant inclusion objects require a valid owning target": r"""
{-@ proofGuard :: owner:Atlas a ts d o f
      -> target:PageElement ts targetObject -> PageElement ss sourceObject
      -> {result:PageElement ts (AtlasMappedObject (OriginObjectMap targetObject) sourceObject) |
           pageElementTraceValid (atlasPageElements owner) result} @-}
proofGuard :: Atlas a ts d o f -> PageElement ts targetObject
  -> PageElement ss sourceObject -> PageElement ts (AtlasMappedObject (OriginObjectMap targetObject) sourceObject)
proofGuard = observedConstantObject
""",
    "constant inclusion objects cannot switch the target owner": r"""
{-@ proofGuard :: owner:Atlas a ts d o f -> other:Atlas a ts d o f
      -> target:{PageElement ts targetObject | pageElementTraceValid (atlasPageElements owner) target}
      -> PageElement ss sourceObject
      -> {result:PageElement ts (AtlasMappedObject (OriginObjectMap targetObject) sourceObject) |
           pageElementTraceValid (atlasPageElements other) result} @-}
proofGuard :: Atlas a ts d o f -> Atlas a ts d o f -> PageElement ts targetObject
  -> PageElement ss sourceObject -> PageElement ts (AtlasMappedObject (OriginObjectMap targetObject) sourceObject)
proofGuard owner _ = observedConstantObject owner
""",
    "constant inclusion page law retains normalized order and transport": r"""
{-@ proofGuard :: witness:AtlasObjectMap (OriginObjectMap targetObject)
      -> sourceAtlas:Atlas sa ss sd so sf -> targetAtlas:Atlas ta ts td to tf
      -> targetOccurrence:{PageElement ts targetObject |
           pageElementTraceValid (atlasPageElements targetAtlas) targetOccurrence}
      -> source:SomePageElement ss -> destination:SomePageElement ss
      -> {result:Bool | not result} @-}
proofGuard :: AtlasObjectMap (OriginObjectMap targetObject)
  -> Atlas sa ss sd so sf -> Atlas ta ts td to tf -> PageElement ts targetObject
  -> SomePageElement ss -> SomePageElement ss -> Bool
proofGuard = observedConstantPageLaw
""",
}


DOMINC_MAPPED_COMPONENT_PUBLIC_SOURCE = r"""
{-# LANGUAGE CPP #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeFamilies #-}
#include "LiquidPlugin.h"
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--higherorder" @-}
{-@ LIQUID "--fast" @-}
module DominionMappedComponentPublicGuard where
import Atlas (Atlas, AtlasObjectMap, AtlasMappedObject, atlasPageElements, atlasAcceptsDatum)
import Coalition.Element (CoalitionData, coalitionElementAt, coalitionElementValid, coalitionElementSource, coalitionElementReaches)
import DomanialInsertion.Core (DomanialInsertion (..), composePartialInverses)
import DomanialInclusion.Action (constantComponentInsertion)
import DomanialInclusion.Component (coalitionComponentMap, acceptedDominionPreimage)
import DomanialInclusion.Data (DominionCellData, dominionCellProjectionPreimage, domIncHomFromValue)
import DomanialInclusion.Presentation (DominionAtlas, DominionPaginationScope, dominionAtlas)
import PageElements (PageElement, pageElementTraceValid, originPageElement)
import PageElements.Structure (SomePageElement (..))
{-@ observedMappedComponent :: witness:AtlasObjectMap objectMap
      -> sourceOwner:DominionAtlas owner a
      -> targetAtlas:Atlas atlasScope scope cellData origin final
      -> target:{PageElement scope targetObject | pageElementTraceValid (atlasPageElements targetAtlas) target}
      -> mapObject:(forall object. PageElement (DominionPaginationScope a) object
           -> {occurrence:PageElement scope (AtlasMappedObject objectMap object) |
                pageElementTraceValid (atlasPageElements targetAtlas) occurrence
                && SomePageElement occurrence == SomePageElement target})
      -> forward:(a -> {element:CoalitionData atlasScope scope cellData |
           coalitionElementValid targetAtlas element
           && coalitionElementSource element == originPageElement (atlasPageElements targetAtlas)
           && coalitionElementReaches element target})
      -> backward:(forall object. PageElement scope object -> cellData object -> Maybe a)
      -> leftInverse:(forall object. occurrence:{PageElement scope object |
           pageElementTraceValid (atlasPageElements targetAtlas) occurrence
           && SomePageElement occurrence == SomePageElement target}
           -> value:a -> {backward occurrence (coalitionElementAt targetAtlas occurrence (forward value)) == Just value})
      -> source:PageElement (DominionPaginationScope a) sourceObject
      -> {result:DomanialInsertion
           ({datum:DominionCellData a sourceObject | atlasAcceptsDatum (dominionAtlas sourceOwner) source datum})
           ({datum:cellData (AtlasMappedObject objectMap sourceObject) |
             atlasAcceptsDatum targetAtlas (mapObject source) datum}) |
           applyInsertion result == domIncHomFromValue
             (coalitionComponentMap targetAtlas (mapObject source) forward)
           && preimage result == acceptedDominionPreimage sourceOwner source
             (composePartialInverses dominionCellProjectionPreimage (backward (mapObject source)))} @-}
observedMappedComponent :: AtlasObjectMap objectMap
  -> DominionAtlas owner a
  -> Atlas atlasScope scope cellData origin final
  -> PageElement scope targetObject
  -> (forall object. PageElement (DominionPaginationScope a) object -> PageElement scope (AtlasMappedObject objectMap object))
  -> (a -> CoalitionData atlasScope scope cellData)
  -> (forall object. PageElement scope object -> cellData object -> Maybe a)
  -> (forall object. PageElement scope object -> a -> ())
  -> PageElement (DominionPaginationScope a) sourceObject
  -> DomanialInsertion (DominionCellData a sourceObject)
       (cellData (AtlasMappedObject objectMap sourceObject))
observedMappedComponent = constantComponentInsertion

{-@ observedAcceptedPreimage :: owner:DominionAtlas ownerScope a
      -> source:PageElement (DominionPaginationScope a) object
      -> backward:(b -> Maybe (DominionCellData a object)) -> value:b
      -> {result:Maybe ({datum:DominionCellData a object | atlasAcceptsDatum (dominionAtlas owner) source datum}) |
           result == backward value} @-}
observedAcceptedPreimage :: DominionAtlas owner a -> PageElement (DominionPaginationScope a) object
  -> (b -> Maybe (DominionCellData a object)) -> b -> Maybe (DominionCellData a object)
observedAcceptedPreimage = acceptedDominionPreimage
"""

def mapped_component_guard(old, new):
    contract = DOMINC_MAPPED_COMPONENT_PUBLIC_SOURCE.split("{-@ observedMappedComponent", 1)[1]
    contract = "{-@ observedMappedComponent" + contract.split("{-@ observedAcceptedPreimage", 1)[0]
    assert old in contract
    return contract.replace(old, new, 1).replace("observedMappedComponent", "proofGuard").replace(
        "proofGuard = constantComponentInsertion", "proofGuard = observedMappedComponent")

DOMINC_MAPPED_COMPONENT_PUBLIC_GUARDS = {
    "mapped inclusion source acceptance preserves every decoder result": r"""
{-@ proofGuard :: owner:DominionAtlas ownerScope a
      -> source:PageElement (DominionPaginationScope a) object
      -> backward:(b -> Maybe (DominionCellData a object)) -> value:b
      -> {result:Maybe (DominionCellData a object) | result /= backward value} @-}
proofGuard :: DominionAtlas owner a -> PageElement (DominionPaginationScope a) object
  -> (b -> Maybe (DominionCellData a object)) -> b -> Maybe (DominionCellData a object)
proofGuard = observedAcceptedPreimage
""",
    "mapped inclusion components require a constant target occurrence": mapped_component_guard(
        "&& SomePageElement occurrence == SomePageElement target", ""),
    "mapped inclusion components require coalition reachability": mapped_component_guard(
        "&& coalitionElementReaches element target", ""),
    "mapped inclusion components require inverse evidence": mapped_component_guard(
        "{backward occurrence (coalitionElementAt targetAtlas occurrence (forward value)) == Just value}", "()"),
    "mapped inclusion components retain their forward callback": mapped_component_guard(
        "applyInsertion result == domIncHomFromValue", "applyInsertion result /= domIncHomFromValue"),
    "mapped inclusion components retain their raw decoder": mapped_component_guard(
        "preimage result == acceptedDominionPreimage", "preimage result /= acceptedDominionPreimage"),
}

# Changing an allocation while retaining its nominal scope must not change the
# owner whose membership the mapped component certifies.
_mapped_wrong_owner = mapped_component_guard(
    "atlasAcceptsDatum targetAtlas (mapObject source) datum",
    "atlasAcceptsDatum otherAtlas (mapObject source) datum")
_mapped_wrong_owner = _mapped_wrong_owner.replace(
    "      -> targetAtlas:Atlas atlasScope scope cellData origin final",
    "      -> otherAtlas:Atlas atlasScope scope cellData origin final\n"
    "      -> targetAtlas:Atlas atlasScope scope cellData origin final", 1).replace(
    "  -> Atlas atlasScope scope cellData origin final\n",
    "  -> Atlas atlasScope scope cellData origin final\n"
    "  -> Atlas atlasScope scope cellData origin final\n", 1).replace(
    "proofGuard = observedMappedComponent",
    "proofGuard witness sourceOwner _ = observedMappedComponent witness sourceOwner")
DOMINC_MAPPED_COMPONENT_PUBLIC_GUARDS[
    "mapped inclusion components retain the actual target owner"] = _mapped_wrong_owner


ATLAS_WITNESS_PUBLIC_SOURCE = r"""
{-# LANGUAGE CPP #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeFamilies #-}
#include "LiquidPlugin.h"
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--higherorder" @-}
module AtlasWitnessPublicGuard where
import Atlas (Atlas, atlasPageElements, normalizeAtlasElement)
import qualified Atlas as PublicAtlas (atlasWitness, withAtlasWitness)
import Atlas.Witness
import PageElements (PageElement, pageElementTraceValid)

{-@ observedOwnerAgreement :: witness:AtlasWitnessData object a s d
      -> owner:{Atlas a s d o f | atlasOwner owner == atlasWitnessOwner witness}
      -> source:PageElement s cell
      -> {(atlasWitnessElementValid witness source <=> pageElementTraceValid (atlasPageElements owner) source)
           && normalizeAtlasWitnessElement witness source == normalizeAtlasElement owner source} @-}
observedOwnerAgreement :: AtlasWitnessData object a s d -> Atlas a s d o f -> PageElement s cell -> ()
observedOwnerAgreement = atlasWitnessOwnerAgrees

{-@ observedOwner :: witness:AtlasWitness object
      -> {owner:AtlasOwner | owner == atlasWitnessOwner witness} @-}
observedOwner :: AtlasWitness object -> AtlasOwner
observedOwner witness = withAtlasWitness witness (\AtlasObjectEquality owner -> atlasOwner owner)

{-@ observedWitness :: owner:Atlas a s d o f
      -> {witness:AtlasWitnessData (AtlasObject a s d) a s d | atlasWitnessOwner witness == atlasOwner owner} @-}
observedWitness :: Atlas a s d o f -> AtlasWitnessData (AtlasObject a s d) a s d
observedWitness owner = atlasWitnessData owner

{-@ observedIndexedWitness :: owner:Atlas a s d o f
      -> {witness:AtlasWitness (AtlasObject a s d) | atlasWitnessOwner witness == atlasOwner owner} @-}
observedIndexedWitness :: Atlas a s d o f -> AtlasWitness (AtlasObject a s d)
observedIndexedWitness owner = PublicAtlas.atlasWitness owner

{-@ observedIndexedOwner :: owner:Atlas a s d o f
      -> {result:AtlasOwner | result == atlasOwner owner} @-}
observedIndexedOwner :: Atlas a s d o f -> AtlasOwner
observedIndexedOwner owner =
  PublicAtlas.withAtlasWitness (observedIndexedWitness owner) (\_ recovered -> atlasOwner recovered)

{-@ observedNormalized :: witness:AtlasWitness object
      -> source:{PageElement (AtlasObjectPaginationScope object) cell | atlasWitnessElementValid witness source}
      -> {result:PageElement (AtlasObjectPaginationScope object) cell |
           result == normalizeAtlasWitnessElement witness source
           && atlasWitnessElementValid witness result
           && normalizeAtlasWitnessElement witness result == result} @-}
observedNormalized :: AtlasWitness object -> PageElement (AtlasObjectPaginationScope object) cell
  -> PageElement (AtlasObjectPaginationScope object) cell
observedNormalized witness source =
  atlasWitnessNormalizeValid witness source `seq` normalizeAtlasWitnessElement witness source
"""
ATLAS_WITNESS_PUBLIC_GUARDS = {
    "atlas witness indexed construction does not substitute owners": r"""
{-@ proofGuard :: first:Atlas a s d o f -> second:Atlas a s d o f
      -> {witness:AtlasWitness (AtlasObject a s d) | atlasWitnessOwner witness == atlasOwner first} @-}
proofGuard :: Atlas a s d o f -> Atlas a s d o f -> AtlasWitness (AtlasObject a s d)
proofGuard _ second = observedIndexedWitness second
""",

    "atlas witness indexed elimination retains its owner": r"""
{-@ proofGuard :: owner:Atlas a s d o f
      -> {result:AtlasOwner | result /= atlasOwner owner} @-}
proofGuard :: Atlas a s d o f -> AtlasOwner
proofGuard = observedIndexedOwner
""",
    "atlas witness indexed construction cannot prove false": r"""
{-@ proofGuard :: owner:Atlas a s d o f -> {proof:() | False} @-}
proofGuard :: Atlas a s d o f -> ()
proofGuard owner = observedIndexedWitness owner `seq` ()
""",

    "atlas witness indexed construction retains its owner": r"""
{-@ proofGuard :: owner:Atlas a s d o f
      -> {witness:AtlasWitness (AtlasObject a s d) | atlasWitnessOwner witness /= atlasOwner owner} @-}
proofGuard :: Atlas a s d o f -> AtlasWitness (AtlasObject a s d)
proofGuard = observedIndexedWitness
""",

    "atlas witness agreement requires the same complete owner": r"""
{-@ proofGuard :: witness:AtlasWitnessData object a s d -> owner:Atlas a s d o f -> source:PageElement s cell
      -> {(atlasWitnessElementValid witness source <=> pageElementTraceValid (atlasPageElements owner) source)
           && normalizeAtlasWitnessElement witness source == normalizeAtlasElement owner source} @-}
proofGuard :: AtlasWitnessData object a s d -> Atlas a s d o f -> PageElement s cell -> ()
proofGuard = observedOwnerAgreement
""",
    "atlas witness agreement retains normalization": r"""
{-@ proofGuard :: witness:AtlasWitnessData object a s d
      -> owner:{Atlas a s d o f | atlasOwner owner == atlasWitnessOwner witness}
      -> source:PageElement s cell
      -> {normalizeAtlasWitnessElement witness source /= normalizeAtlasElement owner source} @-}
proofGuard :: AtlasWitnessData object a s d -> Atlas a s d o f -> PageElement s cell -> ()
proofGuard = observedOwnerAgreement
""",
    "atlas witness agreement retains the source domain": r"""
{-@ proofGuard :: witness:AtlasWitnessData object a s d
      -> owner:{Atlas a s d o f | atlasOwner owner == atlasWitnessOwner witness}
      -> source:PageElement s cell
      -> {atlasWitnessElementValid witness source /= pageElementTraceValid (atlasPageElements owner) source} @-}
proofGuard :: AtlasWitnessData object a s d -> Atlas a s d o f -> PageElement s cell -> ()
proofGuard = observedOwnerAgreement
""",
    "atlas witness elimination retains the entire owner": r"""
{-@ proofGuard :: witness:AtlasWitness object -> {owner:AtlasOwner | owner /= atlasWitnessOwner witness} @-}
proofGuard :: AtlasWitness object -> AtlasOwner
proofGuard = observedOwner
""",
    "atlas witness same object index does not substitute owners": r"""
{-@ proofGuard :: first:AtlasWitness object -> second:AtlasWitness object
      -> {owner:AtlasOwner | owner == atlasWitnessOwner first} @-}
proofGuard :: AtlasWitness object -> AtlasWitness object -> AtlasOwner
proofGuard _ second = observedOwner second
""",
    "atlas witness construction retains its owner": r"""
{-@ proofGuard :: owner:Atlas a s d o f
      -> {witness:AtlasWitnessData (AtlasObject a s d) a s d | atlasWitnessOwner witness /= atlasOwner owner} @-}
proofGuard :: Atlas a s d o f -> AtlasWitnessData (AtlasObject a s d) a s d
proofGuard = observedWitness
""",
    "atlas witness normalization requires owning validity": r"""
{-@ proofGuard :: witness:AtlasWitness object
      -> source:PageElement (AtlasObjectPaginationScope object) cell
      -> {result:PageElement (AtlasObjectPaginationScope object) cell | atlasWitnessElementValid witness result} @-}
proofGuard :: AtlasWitness object -> PageElement (AtlasObjectPaginationScope object) cell
  -> PageElement (AtlasObjectPaginationScope object) cell
proofGuard = observedNormalized
""",
    "atlas witness normalization retains the exact occurrence": r"""
{-@ proofGuard :: witness:AtlasWitness object
      -> source:{PageElement (AtlasObjectPaginationScope object) cell | atlasWitnessElementValid witness source}
      -> {result:PageElement (AtlasObjectPaginationScope object) cell |
           result /= normalizeAtlasWitnessElement witness source} @-}
proofGuard :: AtlasWitness object -> PageElement (AtlasObjectPaginationScope object) cell
  -> PageElement (AtlasObjectPaginationScope object) cell
proofGuard = observedNormalized
""",
}

ORDERED_TRANSPOSAL_PUBLIC_SOURCE = r"""
{-# LANGUAGE CPP #-}
{-# LANGUAGE TypeFamilies #-}
#include "LiquidPlugin.h"
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}
{-@ LIQUID "--higherorder" @-}
module OrderedTransposalPublicGuard where
import Atlas (AtlasWitness)
import AtlasTransposal
import OrderedAtlasTransposal

{-@ observedOrder :: ordered:OrderedAtlasTransposal source target
      -> left:{AtlasTransposalElement source | atlasTransposalPathValid (orderedAtlasTransposalTransposal ordered) left}
      -> right:{AtlasTransposalElement source | atlasTransposalPathValid (orderedAtlasTransposalTransposal ordered) right
           && atlasTransposalElementLT left right}
      -> {atlasTransposalElementLT (mapOrderedAtlasTransposalObject ordered left) (mapOrderedAtlasTransposalObject ordered right)} @-}
observedOrder :: OrderedAtlasTransposal source target -> AtlasTransposalElement source -> AtlasTransposalElement source -> ()
observedOrder = orderedAtlasTransposalPreservesOrder

{-@ observedOwnedOrder :: witness:AtlasWitness source
      -> ordered:{OrderedAtlasTransposal source target | TransposalOwnedBy witness (orderedAtlasTransposalTransposal ordered)}
      -> left:{AtlasTransposalElement source | atlasTransposalElementValid witness left}
      -> right:{AtlasTransposalElement source | atlasTransposalElementValid witness right && atlasTransposalElementLT left right}
      -> {atlasTransposalElementLT (mapOrderedAtlasTransposalObject ordered left) (mapOrderedAtlasTransposalObject ordered right)} @-}
observedOwnedOrder :: AtlasWitness source -> OrderedAtlasTransposal source target
  -> AtlasTransposalElement source -> AtlasTransposalElement source -> ()
observedOwnedOrder = orderedAtlasTransposalOwnedOrder

{-@ observedOrderConstructor :: witness:AtlasWitness source
      -> transposal:{AtlasTransposal source target | TransposalOwnedBy witness transposal}
      -> (left:{AtlasTransposalElement source | atlasTransposalSourceValid transposal left}
           -> right:{AtlasTransposalElement source | atlasTransposalSourceValid transposal right && atlasTransposalElementLT left right}
           -> {atlasTransposalElementLT (mapAtlasTransposalObject transposal left) (mapAtlasTransposalObject transposal right)})
      -> {result:OrderedAtlasTransposal source target | orderedAtlasTransposalTransposal result == transposal
           && TransposalOwnedBy witness (orderedAtlasTransposalTransposal result)} @-}
observedOrderConstructor :: AtlasWitness source -> AtlasTransposal source target
  -> (AtlasTransposalElement source -> AtlasTransposalElement source -> ()) -> OrderedAtlasTransposal source target
observedOrderConstructor _ = orderedAtlasTransposal

{-@ observedOrderInverse :: ordered:OrderedAtlasTransposal source target
      -> source:{AtlasTransposalElement source | atlasTransposalPathValid (orderedAtlasTransposalTransposal ordered) source}
      -> {orderedAtlasTransposalPreimage ordered (mapOrderedAtlasTransposalObject ordered source) == Just source} @-}
observedOrderInverse :: OrderedAtlasTransposal source target -> AtlasTransposalElement source -> ()
observedOrderInverse = orderedAtlasTransposalLeftInverse
"""


def ordered_transposal_guard(observed, original, replacement="True"):
    declaration = ORDERED_TRANSPOSAL_PUBLIC_SOURCE.split("{-@ " + observed + " ::", 1)[1].split(
        "\n" + observed + " =", 1)[0]
    assert original in declaration
    return ("{-@ " + observed + " ::" + declaration).replace(observed, "proofGuard").replace(
        original, replacement, 1) + "\nproofGuard = " + observed + "\n"


ORDERED_TRANSPOSAL_PUBLIC_GUARDS = {
    "ordered transposal proof requires the left path domain": ordered_transposal_guard(
        "observedOrder", "atlasTransposalPathValid (orderedAtlasTransposalTransposal ordered) left"),
    "ordered transposal proof requires the right path domain": ordered_transposal_guard(
        "observedOrder", "atlasTransposalPathValid (orderedAtlasTransposalTransposal ordered) right"),
    "ordered transposal proof requires the source order": ordered_transposal_guard(
        "observedOrder", "atlasTransposalElementLT left right"),
    "ordered transposal owning proof requires complete owner evidence": ordered_transposal_guard(
        "observedOwnedOrder", "TransposalOwnedBy witness (orderedAtlasTransposalTransposal ordered)"),
    "ordered transposal owning proof requires left membership": ordered_transposal_guard(
        "observedOwnedOrder", "atlasTransposalElementValid witness left"),
    "ordered transposal owning proof requires right membership": ordered_transposal_guard(
        "observedOwnedOrder", "atlasTransposalElementValid witness right"),
    "ordered transposal owning proof requires source order": ordered_transposal_guard(
        "observedOwnedOrder", "atlasTransposalElementLT left right"),
    "ordered transposal inverse requires path acceptance": ordered_transposal_guard(
        "observedOrderInverse", "atlasTransposalPathValid (orderedAtlasTransposalTransposal ordered) source"),
    "ordered transposal owning proof cannot prove false": ordered_transposal_guard(
        "observedOwnedOrder", "atlasTransposalElementLT (mapOrderedAtlasTransposalObject ordered left) (mapOrderedAtlasTransposalObject ordered right)", "False"),
}


TRANSPOSAL_NATIVE_PUBLIC_SOURCE = r"""
{-# LANGUAGE CPP #-}
{-# LANGUAGE TypeFamilies #-}
#include "LiquidPlugin.h"
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}
{-@ LIQUID "--higherorder" @-}
module TransposalNativePublicGuard where
import Atlas (AtlasWitness, AtlasHom)
import Atlas.Witness (AtlasObjectPaginationScope, atlasWitnessOwner, atlasWitnessElementValid, normalizeAtlasWitnessElement)
import AtlasTransposal
import AtlasTransposal.Element (transposalElementSource)
import DomanialInsertion.Core (composePartialInverses)
import OrderedAtlasTransposal (OrderedAtlasTransposal, orderedAtlasTransposal)
import PageElements.Structure (PageElement, SomePageElement (..))

{-@ observedNativeElement :: witness:AtlasWitness object
      -> source:{PageElement (AtlasObjectPaginationScope object) cell | atlasWitnessElementValid witness source}
      -> {result:AtlasTransposalElement object | atlasTransposalElementValid witness result
           && transposalElementSource result == SomePageElement (normalizeAtlasWitnessElement witness source)} @-}
observedNativeElement :: AtlasWitness object -> PageElement (AtlasObjectPaginationScope object) cell
  -> AtlasTransposalElement object
observedNativeElement = atlasTransposalElement

{-@ observedNative :: witness:AtlasWitness source
      -> hom:{AtlasHom source target | atlasHomSourceOwner witness hom == atlasWitnessOwner witness}
      -> backward:(targetElement:AtlasTransposalElement target
           -> Maybe ({sourceElement:AtlasTransposalElement source |
                atlasHomTargetValid witness hom targetElement => atlasHomSourceValid witness hom sourceElement}))
      -> (sourceElement:{AtlasTransposalElement source | atlasHomSourceValid witness hom sourceElement}
           -> {backward (mapAtlasHomObject witness hom sourceElement) == Just sourceElement})
      -> {result:AtlasTransposal source target |
           TransposalOwnedBy witness result
           && atlasTransposalSourceOwner result == Just (atlasWitnessOwner witness)
           && atlasTransposalTargetOwner result == Just (atlasHomTargetOwner witness hom)
           && atlasTransposalSourceValid result == atlasHomSourceValid witness hom
           && atlasTransposalPathValid result == atlasHomSourceValid witness hom
           && mapAtlasTransposalObject result == mapAtlasHomObject witness hom
           && atlasTransposalPreimage result == backward} @-}
observedNative :: AtlasWitness source -> AtlasHom source target
  -> (AtlasTransposalElement target -> Maybe (AtlasTransposalElement source))
  -> (AtlasTransposalElement source -> ()) -> AtlasTransposal source target
observedNative = atlasTransposal

{-@ observedWitnessedMap :: witness:AtlasWitness source
      -> hom:{AtlasHom source target | atlasHomSourceOwner witness hom == atlasWitnessOwner witness}
      -> sourceElement:{AtlasTransposalElement source | atlasTransposalElementValid witness sourceElement}
      -> {targetElement:AtlasTransposalElement target | atlasHomTargetValid witness hom targetElement} @-}
observedWitnessedMap :: AtlasWitness source -> AtlasHom source target -> AtlasTransposalElement source
  -> AtlasTransposalElement target
observedWitnessedMap witness hom source =
  atlasHomSourceAgrees witness hom source `seq` mapAtlasHomObject witness hom source

{-@ observedOwnedComposite :: sourceWitness:AtlasWitness source
      -> firstHom:{AtlasHom source middle | atlasHomSourceOwner sourceWitness firstHom == atlasWitnessOwner sourceWitness}
      -> secondHom:{AtlasHom middle target |
           atlasHomSourceOwner (atlasHomTargetWitness sourceWitness firstHom) secondHom == atlasHomTargetOwner sourceWitness firstHom}
      -> first:{AtlasTransposal source middle |
           atlasTransposalPathValid first == atlasHomSourceValid sourceWitness firstHom
           && mapAtlasTransposalObject first == mapAtlasHomObject sourceWitness firstHom}
      -> second:{AtlasTransposal middle target |
           atlasTransposalPathValid second == atlasHomSourceValid (atlasHomTargetWitness sourceWitness firstHom) secondHom}
      -> sourceElement:{AtlasTransposalElement source | atlasTransposalElementValid sourceWitness sourceElement}
      -> {atlasTransposalPreimage (composeAtlasTransposals second first)
           (mapAtlasTransposalObject (composeAtlasTransposals second first) sourceElement) == Just sourceElement} @-}
observedOwnedComposite :: AtlasWitness source -> AtlasHom source middle -> AtlasHom middle target
  -> AtlasTransposal source middle -> AtlasTransposal middle target -> AtlasTransposalElement source -> ()
observedOwnedComposite sourceWitness firstHom secondHom first second source =
  atlasHomSourceAgrees sourceWitness firstHom source `seq`
  atlasHomNextSourceValid sourceWitness firstHom secondHom source `seq`
  observedNativeComposite second first source

{-@ observedOwnedIdentity :: witness:AtlasWitness object
      -> {result:AtlasTransposal object object | TransposalOwnedBy witness result} @-}
observedOwnedIdentity :: AtlasWitness object -> AtlasTransposal object object
observedOwnedIdentity _ = identityAtlasTransposal

{-@ observedOwnerInverse :: witness:AtlasWitness source
      -> arrow:{AtlasTransposal source target | TransposalOwnedBy witness arrow}
      -> source:{AtlasTransposalElement source | atlasTransposalElementValid witness source}
      -> {atlasTransposalPreimage arrow (mapAtlasTransposalObject arrow source) == Just source} @-}
observedOwnerInverse :: AtlasWitness source -> AtlasTransposal source target -> AtlasTransposalElement source -> ()
observedOwnerInverse witness arrow source =
  atlasTransposalOwnedPath witness arrow source `seq` atlasTransposalLeftInverse arrow source

{-@ observedOwnerComposite :: witness:AtlasWitness source
      -> first:{AtlasTransposal source middle | TransposalOwnedBy witness first}
      -> second:{AtlasTransposal middle target | TransposalOwnedBy (atlasTransposalTargetWitness witness first) second}
      -> {result:AtlasTransposal source target | TransposalOwnedBy witness result
           && result == composeAtlasTransposals second first} @-}
observedOwnerComposite :: AtlasWitness source -> AtlasTransposal source middle -> AtlasTransposal middle target
  -> AtlasTransposal source target
observedOwnerComposite witness first second =
  atlasTransposalComposeOwned witness first second `seq` composeAtlasTransposals second first

{-@ observedOwnerCompositeInverse :: witness:AtlasWitness source
      -> first:{AtlasTransposal source middle | TransposalOwnedBy witness first}
      -> second:{AtlasTransposal middle target | TransposalOwnedBy (atlasTransposalTargetWitness witness first) second}
      -> source:{AtlasTransposalElement source | atlasTransposalElementValid witness source}
      -> {atlasTransposalPreimage (composeAtlasTransposals second first)
           (mapAtlasTransposalObject (composeAtlasTransposals second first) source) == Just source} @-}
observedOwnerCompositeInverse :: AtlasWitness source -> AtlasTransposal source middle -> AtlasTransposal middle target
  -> AtlasTransposalElement source -> ()
observedOwnerCompositeInverse witness first second source =
  observedOwnerInverse witness (observedOwnerComposite witness first second) source

{-@ observedNativeTargetWitness :: witness:AtlasWitness source -> arrow:AtlasTransposal source target
      -> {result:AtlasWitness target |
           atlasTransposalTargetOwner arrow == Just (atlasWitnessOwner result)
           || (atlasTransposalTargetOwner arrow == Nothing
                && atlasWitnessOwner result == atlasWitnessOwner witness)} @-}
observedNativeTargetWitness :: AtlasWitness source -> AtlasTransposal source target -> AtlasWitness target
observedNativeTargetWitness = atlasTransposalTargetWitness

{-@ observedNativeTargetMap :: witness:AtlasWitness source -> arrow:AtlasTransposal source target
      -> element:{AtlasTransposalElement source |
           atlasTransposalElementValid witness element && atlasTransposalPathValid arrow element}
      -> {result:AtlasTransposalElement target |
           atlasTransposalElementValid (atlasTransposalTargetWitness witness arrow) result} @-}
observedNativeTargetMap :: AtlasWitness source -> AtlasTransposal source target
  -> AtlasTransposalElement source -> AtlasTransposalElement target
observedNativeTargetMap witness arrow source =
  atlasTransposalMapValid witness arrow source `seq` mapAtlasTransposalObject arrow source

{-@ observedTreeComposite :: witness:AtlasWitness source -> first:AtlasTransposal source middle
      -> secondHom:{AtlasHom middle target |
           atlasHomSourceOwner (atlasTransposalTargetWitness witness first) secondHom
             == atlasWitnessOwner (atlasTransposalTargetWitness witness first)}
      -> second:{AtlasTransposal middle target |
           atlasTransposalPathValid second == atlasHomSourceValid (atlasTransposalTargetWitness witness first) secondHom}
      -> source:{AtlasTransposalElement source |
           atlasTransposalElementValid witness source && atlasTransposalPathValid first source}
      -> {atlasTransposalPreimage (composeAtlasTransposals second first)
           (mapAtlasTransposalObject (composeAtlasTransposals second first) source) == Just source} @-}
observedTreeComposite :: AtlasWitness source -> AtlasTransposal source middle -> AtlasHom middle target
  -> AtlasTransposal middle target -> AtlasTransposalElement source -> ()
observedTreeComposite witness first secondHom second source =
  atlasTransposalMapValid witness first source `seq`
  atlasHomSourceAgrees (atlasTransposalTargetWitness witness first) secondHom
    (mapAtlasTransposalObject first source) `seq`
  observedNativeComposite second first source

{-@ observedHomTargetWitness :: sourceWitness:AtlasWitness source -> hom:AtlasHom source target
      -> {witness:AtlasWitness target | atlasWitnessOwner witness == atlasHomTargetOwner sourceWitness hom} @-}
observedHomTargetWitness :: AtlasWitness source -> AtlasHom source target -> AtlasWitness target
observedHomTargetWitness = atlasHomTargetWitness

{-@ observedTargetMap :: sourceWitness:AtlasWitness source
      -> hom:{AtlasHom source target | atlasHomSourceOwner sourceWitness hom == atlasWitnessOwner sourceWitness}
      -> sourceElement:{AtlasTransposalElement source | atlasTransposalElementValid sourceWitness sourceElement}
      -> {targetElement:AtlasTransposalElement target |
           atlasTransposalElementValid (atlasHomTargetWitness sourceWitness hom) targetElement} @-}
observedTargetMap :: AtlasWitness source -> AtlasHom source target -> AtlasTransposalElement source -> AtlasTransposalElement target
observedTargetMap sourceWitness hom source =
  atlasHomSourceAgrees sourceWitness hom source `seq`
  let target = mapAtlasHomObject sourceWitness hom source
  in atlasHomTargetAgrees sourceWitness hom (atlasHomTargetWitness sourceWitness hom) target `seq` target

{-@ observedOrdered :: transposal:AtlasTransposal source target
      -> (left:{AtlasTransposalElement source | atlasTransposalSourceValid transposal left}
           -> right:{AtlasTransposalElement source |
                atlasTransposalSourceValid transposal right && atlasTransposalElementLT left right}
           -> {atlasTransposalElementLT
                (mapAtlasTransposalObject transposal left)
                (mapAtlasTransposalObject transposal right)})
      -> OrderedAtlasTransposal source target @-}
observedOrdered :: AtlasTransposal source target
  -> (AtlasTransposalElement source -> AtlasTransposalElement source -> ())
  -> OrderedAtlasTransposal source target
observedOrdered = orderedAtlasTransposal

{-@ observedNativeRoundTrip :: transposal:AtlasTransposal source target
      -> sourceElement:{AtlasTransposalElement source | atlasTransposalPathValid transposal sourceElement}
      -> {atlasTransposalPreimage transposal (mapAtlasTransposalObject transposal sourceElement)
            == Just sourceElement} @-}
observedNativeRoundTrip :: AtlasTransposal source target -> AtlasTransposalElement source -> ()
observedNativeRoundTrip = atlasTransposalLeftInverse

{-@ observedNativeIdentity
      :: identity:{AtlasTransposal object object | identity == identityAtlasTransposal}
      -> source:AtlasTransposalElement object
      -> {mapAtlasTransposalObject identity source == source
           && atlasTransposalPreimage identity source == Just source
           && atlasTransposalPathValid identity source} @-}
observedNativeIdentity :: AtlasTransposal object object -> AtlasTransposalElement object -> ()
observedNativeIdentity = identityAtlasTransposalRetains

{-@ observedNativeComposite :: second:AtlasTransposal middle target
      -> first:AtlasTransposal source middle
      -> sourceElement:{AtlasTransposalElement source |
           atlasTransposalPathValid first sourceElement
           && atlasTransposalPathValid second (mapAtlasTransposalObject first sourceElement)}
      -> {atlasTransposalPreimage (composeAtlasTransposals second first)
           (mapAtlasTransposalObject (composeAtlasTransposals second first) sourceElement)
             == Just sourceElement} @-}
observedNativeComposite :: AtlasTransposal middle target -> AtlasTransposal source middle
  -> AtlasTransposalElement source -> ()
observedNativeComposite second first source =
  composeAtlasTransposalsRetains second first source
    (mapAtlasTransposalObject second (mapAtlasTransposalObject first source)) `seq`
  atlasTransposalLeftInverse (composeAtlasTransposals second first) source

{-@ observedNativeLookup :: second:AtlasTransposal middle target -> first:AtlasTransposal source middle
      -> sourceElement:AtlasTransposalElement source -> targetElement:AtlasTransposalElement target
      -> {result:Maybe (AtlasTransposalElement source) |
           result == composePartialInverses (atlasTransposalPreimage first) (atlasTransposalPreimage second) targetElement} @-}
observedNativeLookup :: AtlasTransposal middle target -> AtlasTransposal source middle
  -> AtlasTransposalElement source -> AtlasTransposalElement target -> Maybe (AtlasTransposalElement source)
observedNativeLookup second first source target =
  composeAtlasTransposalsRetains second first source target `seq`
    atlasTransposalPreimage (composeAtlasTransposals second first) target

{-@ observedNativeMap :: second:AtlasTransposal middle target -> first:AtlasTransposal source middle
      -> sourceElement:AtlasTransposalElement source
      -> {result:AtlasTransposalElement target |
           result == mapAtlasTransposalObject second (mapAtlasTransposalObject first sourceElement)} @-}
observedNativeMap :: AtlasTransposal middle target -> AtlasTransposal source middle
  -> AtlasTransposalElement source -> AtlasTransposalElement target
observedNativeMap second first source =
  composeAtlasTransposalsRetains second first source
    (mapAtlasTransposalObject second (mapAtlasTransposalObject first source)) `seq`
    mapAtlasTransposalObject (composeAtlasTransposals second first) source

{-@ observedNativeLeftIdentity :: identity:{AtlasTransposal target target | identity == identityAtlasTransposal}
      -> arrow:AtlasTransposal source target
      -> sourceElement:AtlasTransposalElement source -> targetElement:AtlasTransposalElement target
      -> {mapAtlasTransposalObject (composeAtlasTransposals identity arrow) sourceElement == mapAtlasTransposalObject arrow sourceElement
           && atlasTransposalPreimage (composeAtlasTransposals identity arrow) targetElement == atlasTransposalPreimage arrow targetElement
           && (atlasTransposalPathValid (composeAtlasTransposals identity arrow) sourceElement <=> atlasTransposalPathValid arrow sourceElement)
           && atlasTransposalSourceOwner (composeAtlasTransposals identity arrow) == atlasTransposalSourceOwner arrow
           && atlasTransposalTargetOwner (composeAtlasTransposals identity arrow) == atlasTransposalTargetOwner arrow} @-}
observedNativeLeftIdentity :: AtlasTransposal target target -> AtlasTransposal source target
  -> AtlasTransposalElement source -> AtlasTransposalElement target -> ()
observedNativeLeftIdentity = atlasTransposalLeftIdentity

{-@ observedNativeRightIdentity :: identity:{AtlasTransposal source source | identity == identityAtlasTransposal}
      -> arrow:AtlasTransposal source target
      -> sourceElement:AtlasTransposalElement source -> targetElement:AtlasTransposalElement target
      -> {mapAtlasTransposalObject (composeAtlasTransposals arrow identity) sourceElement == mapAtlasTransposalObject arrow sourceElement
           && atlasTransposalPreimage (composeAtlasTransposals arrow identity) targetElement == atlasTransposalPreimage arrow targetElement
           && (atlasTransposalPathValid (composeAtlasTransposals arrow identity) sourceElement <=> atlasTransposalPathValid arrow sourceElement)
           && atlasTransposalSourceOwner (composeAtlasTransposals arrow identity) == atlasTransposalSourceOwner arrow
           && atlasTransposalTargetOwner (composeAtlasTransposals arrow identity) == atlasTransposalTargetOwner arrow} @-}
observedNativeRightIdentity :: AtlasTransposal source source -> AtlasTransposal source target
  -> AtlasTransposalElement source -> AtlasTransposalElement target -> ()
observedNativeRightIdentity = atlasTransposalRightIdentity

{-@ observedNativeAssociativity :: third:AtlasTransposal next target
      -> second:AtlasTransposal middle next -> first:AtlasTransposal source middle
      -> sourceElement:AtlasTransposalElement source -> targetElement:AtlasTransposalElement target
      -> {mapAtlasTransposalObject (composeAtlasTransposals third (composeAtlasTransposals second first)) sourceElement == mapAtlasTransposalObject (composeAtlasTransposals (composeAtlasTransposals third second) first) sourceElement
           && atlasTransposalPreimage (composeAtlasTransposals third (composeAtlasTransposals second first)) targetElement == atlasTransposalPreimage (composeAtlasTransposals (composeAtlasTransposals third second) first) targetElement
           && (atlasTransposalSourceValid (composeAtlasTransposals third (composeAtlasTransposals second first)) sourceElement <=> atlasTransposalSourceValid (composeAtlasTransposals (composeAtlasTransposals third second) first) sourceElement)
           && (atlasTransposalPathValid (composeAtlasTransposals third (composeAtlasTransposals second first)) sourceElement <=> atlasTransposalPathValid (composeAtlasTransposals (composeAtlasTransposals third second) first) sourceElement)
           && atlasTransposalSourceOwner (composeAtlasTransposals third (composeAtlasTransposals second first)) == atlasTransposalSourceOwner (composeAtlasTransposals (composeAtlasTransposals third second) first)
           && atlasTransposalTargetOwner (composeAtlasTransposals third (composeAtlasTransposals second first)) == atlasTransposalTargetOwner (composeAtlasTransposals (composeAtlasTransposals third second) first)} @-}
observedNativeAssociativity :: AtlasTransposal next target -> AtlasTransposal middle next
  -> AtlasTransposal source middle -> AtlasTransposalElement source -> AtlasTransposalElement target -> ()
observedNativeAssociativity = atlasTransposalAssociativity

"""
def native_transposal_guard(original, replacement):
    signature = TRANSPOSAL_NATIVE_PUBLIC_SOURCE.split("{-@ observedNative ::", 1)[1].split(
        "\nobservedNative = atlasTransposal", 1)[0]
    return ("{-@ observedNative ::" + signature).replace("observedNative", "proofGuard").replace(
        original, replacement, 1) + "\nproofGuard = observedNative\n"


def native_owned_composition_guard(original):
    signature = TRANSPOSAL_NATIVE_PUBLIC_SOURCE.split("{-@ observedOwnedComposite ::", 1)[1].split(
        "\nobservedOwnedComposite sourceWitness", 1)[0]
    return ("{-@ observedOwnedComposite ::" + signature).replace("observedOwnedComposite", "proofGuard").replace(
        original, "True", 1) + "\nproofGuard = observedOwnedComposite\n"


def native_law_guard(observed, original, replacement):
    signature = TRANSPOSAL_NATIVE_PUBLIC_SOURCE.split("{-@ " + observed + " ::", 1)[1].split(
        "\n" + observed + " =", 1)[0]
    return ("{-@ " + observed + " ::" + signature).replace(observed, "proofGuard").replace(
        original, replacement, 1) + "\nproofGuard = " + observed + "\n"


TRANSPOSAL_NATIVE_PUBLIC_GUARDS = {
    "native transposal owner proof requires compatibility at every join": r"""
{-@ proofGuard :: witness:AtlasWitness source
      -> arrow:{AtlasTransposal source target | atlasTransposalSourceOwner arrow == Nothing
           || atlasTransposalSourceOwner arrow == Just (atlasWitnessOwner witness)}
      -> source:{AtlasTransposalElement source | atlasTransposalElementValid witness source}
      -> {atlasTransposalPreimage arrow (mapAtlasTransposalObject arrow source) == Just source} @-}
proofGuard :: AtlasWitness source -> AtlasTransposal source target -> AtlasTransposalElement source -> ()
proofGuard = observedOwnerInverse
""",
    "native transposal owner proof requires its actual source owner": r"""
{-@ proofGuard :: witness:AtlasWitness source
      -> arrow:{AtlasTransposal source target | TransposalCompatible arrow}
      -> source:{AtlasTransposalElement source | atlasTransposalElementValid witness source}
      -> {atlasTransposalPreimage arrow (mapAtlasTransposalObject arrow source) == Just source} @-}
proofGuard :: AtlasWitness source -> AtlasTransposal source target -> AtlasTransposalElement source -> ()
proofGuard = observedOwnerInverse
""",
    "native transposal owner proof requires witnessed membership": r"""
{-@ proofGuard :: witness:AtlasWitness source
      -> arrow:{AtlasTransposal source target | TransposalOwnedBy witness arrow}
      -> source:AtlasTransposalElement source
      -> {atlasTransposalPreimage arrow (mapAtlasTransposalObject arrow source) == Just source} @-}
proofGuard :: AtlasWitness source -> AtlasTransposal source target -> AtlasTransposalElement source -> ()
proofGuard = observedOwnerInverse
""",
    "native transposal owner composition requires the first subtree certificate": r"""
{-@ proofGuard :: witness:AtlasWitness source -> first:AtlasTransposal source middle
      -> second:{AtlasTransposal middle target | TransposalOwnedBy (atlasTransposalTargetWitness witness first) second}
      -> {result:AtlasTransposal source target | TransposalOwnedBy witness result} @-}
proofGuard :: AtlasWitness source -> AtlasTransposal source middle -> AtlasTransposal middle target
  -> AtlasTransposal source target
proofGuard = observedOwnerComposite
""",
    "native transposal owner composition requires the second subtree certificate": r"""
{-@ proofGuard :: witness:AtlasWitness source
      -> first:{AtlasTransposal source middle | TransposalOwnedBy witness first}
      -> second:{AtlasTransposal middle target | atlasTransposalSourceOwner second == Nothing
           || atlasTransposalSourceOwner second == Just (atlasWitnessOwner (atlasTransposalTargetWitness witness first))}
      -> {result:AtlasTransposal source target | TransposalOwnedBy witness result} @-}
proofGuard :: AtlasWitness source -> AtlasTransposal source middle -> AtlasTransposal middle target
  -> AtlasTransposal source target
proofGuard = observedOwnerComposite
""",
    "native transposal owner composition requires the complete middle owner": r"""
{-@ proofGuard :: witness:AtlasWitness source
      -> first:{AtlasTransposal source middle | TransposalOwnedBy witness first}
      -> second:{AtlasTransposal middle target | TransposalCompatible second}
      -> {result:AtlasTransposal source target | TransposalOwnedBy witness result} @-}
proofGuard :: AtlasWitness source -> AtlasTransposal source middle -> AtlasTransposal middle target
  -> AtlasTransposal source target
proofGuard = observedOwnerComposite
""",
    "native transposal owner proof cannot prove false": r"""
{-@ proofGuard :: witness:AtlasWitness source
      -> arrow:{AtlasTransposal source target | TransposalOwnedBy witness arrow}
      -> source:{AtlasTransposalElement source | atlasTransposalElementValid witness source}
      -> {proof:() | False} @-}
proofGuard :: AtlasWitness source -> AtlasTransposal source target -> AtlasTransposalElement source -> ()
proofGuard = observedOwnerInverse
""",
    "native transposal tree target membership requires source membership": r"""
{-@ proofGuard :: witness:AtlasWitness source -> arrow:AtlasTransposal source target
      -> element:{AtlasTransposalElement source | atlasTransposalPathValid arrow element}
      -> {result:AtlasTransposalElement target |
           atlasTransposalElementValid (atlasTransposalTargetWitness witness arrow) result} @-}
proofGuard :: AtlasWitness source -> AtlasTransposal source target
  -> AtlasTransposalElement source -> AtlasTransposalElement target
proofGuard = observedNativeTargetMap
""",
    "native transposal tree target membership requires path acceptance": r"""
{-@ proofGuard :: witness:AtlasWitness source -> arrow:AtlasTransposal source target
      -> element:{AtlasTransposalElement source | atlasTransposalElementValid witness element}
      -> {result:AtlasTransposalElement target |
           atlasTransposalElementValid (atlasTransposalTargetWitness witness arrow) result} @-}
proofGuard :: AtlasWitness source -> AtlasTransposal source target
  -> AtlasTransposalElement source -> AtlasTransposalElement target
proofGuard = observedNativeTargetMap
""",
    "native transposal tree target witness retains the stored owner": r"""
{-@ proofGuard :: witness:AtlasWitness source
      -> arrow:{AtlasTransposal source target | atlasTransposalTargetOwner arrow /= Nothing}
      -> {result:AtlasWitness target | atlasTransposalTargetOwner arrow /= Just (atlasWitnessOwner result)} @-}
proofGuard :: AtlasWitness source -> AtlasTransposal source target -> AtlasWitness target
proofGuard = observedNativeTargetWitness
""",
    "native transposal tree target witness preserves identity-only owners": r"""
{-@ proofGuard :: witness:AtlasWitness source
      -> arrow:{AtlasTransposal source target | atlasTransposalTargetOwner arrow == Nothing}
      -> {result:AtlasWitness target | atlasWitnessOwner result /= atlasWitnessOwner witness} @-}
proofGuard :: AtlasWitness source -> AtlasTransposal source target -> AtlasWitness target
proofGuard = observedNativeTargetWitness
""",
    "native transposal tree target witness cannot substitute its input owner": r"""
{-@ proofGuard :: first:AtlasWitness source -> second:AtlasWitness source
      -> arrow:{AtlasTransposal source target | atlasTransposalTargetOwner arrow == Nothing}
      -> {result:AtlasWitness target | atlasWitnessOwner result == atlasWitnessOwner first} @-}
proofGuard :: AtlasWitness source -> AtlasWitness source -> AtlasTransposal source target -> AtlasWitness target
proofGuard _ second = observedNativeTargetWitness second
""",
    "native transposal tree target validity cannot prove false": r"""
{-@ proofGuard :: witness:AtlasWitness source -> arrow:AtlasTransposal source target
      -> element:{AtlasTransposalElement source |
           atlasTransposalElementValid witness element && atlasTransposalPathValid arrow element}
      -> {proof:() | False} @-}
proofGuard :: AtlasWitness source -> AtlasTransposal source target -> AtlasTransposalElement source -> ()
proofGuard witness arrow source = observedNativeTargetMap witness arrow source `seq` ()
""",
    "native transposal target witness membership requires its source owner": r"""
{-@ proofGuard :: sourceWitness:AtlasWitness source -> hom:AtlasHom source target
      -> sourceElement:{AtlasTransposalElement source | atlasTransposalElementValid sourceWitness sourceElement}
      -> {targetElement:AtlasTransposalElement target |
           atlasTransposalElementValid (atlasHomTargetWitness sourceWitness hom) targetElement} @-}
proofGuard :: AtlasWitness source -> AtlasHom source target -> AtlasTransposalElement source -> AtlasTransposalElement target
proofGuard = observedTargetMap
""",
    "native transposal target witness membership requires source membership": r"""
{-@ proofGuard :: sourceWitness:AtlasWitness source
      -> hom:{AtlasHom source target | atlasHomSourceOwner sourceWitness hom == atlasWitnessOwner sourceWitness}
      -> sourceElement:AtlasTransposalElement source
      -> {targetElement:AtlasTransposalElement target |
           atlasTransposalElementValid (atlasHomTargetWitness sourceWitness hom) targetElement} @-}
proofGuard :: AtlasWitness source -> AtlasHom source target -> AtlasTransposalElement source -> AtlasTransposalElement target
proofGuard = observedTargetMap
""",

    "native transposal target witness retains the materialized owner": r"""
{-@ proofGuard :: sourceWitness:AtlasWitness source -> hom:AtlasHom source target
      -> {witness:AtlasWitness target | atlasWitnessOwner witness /= atlasHomTargetOwner sourceWitness hom} @-}
proofGuard :: AtlasWitness source -> AtlasHom source target -> AtlasWitness target
proofGuard = observedHomTargetWitness
""",
    "native transposal target witness does not substitute owners": r"""
{-@ proofGuard :: sourceWitness:AtlasWitness source -> first:AtlasHom source target -> second:AtlasHom source target
      -> {witness:AtlasWitness target | atlasWitnessOwner witness == atlasHomTargetOwner sourceWitness first} @-}
proofGuard :: AtlasWitness source -> AtlasHom source target -> AtlasHom source target -> AtlasWitness target
proofGuard sourceWitness _ second = observedHomTargetWitness sourceWitness second
""",
    "native transposal target witness cannot prove false": r"""
{-@ proofGuard :: sourceWitness:AtlasWitness source -> hom:AtlasHom source target -> {proof:() | False} @-}
proofGuard :: AtlasWitness source -> AtlasHom source target -> ()
proofGuard sourceWitness hom = observedHomTargetWitness sourceWitness hom `seq` ()
""",

    "native transposal associativity retains raw map": native_law_guard(
        "observedNativeAssociativity", "mapAtlasTransposalObject (composeAtlasTransposals third (composeAtlasTransposals second first)) sourceElement ==", "mapAtlasTransposalObject (composeAtlasTransposals third (composeAtlasTransposals second first)) sourceElement /="),
    "native transposal associativity retains every inverse lookup": native_law_guard(
        "observedNativeAssociativity", "atlasTransposalPreimage (composeAtlasTransposals third (composeAtlasTransposals second first)) targetElement ==", "atlasTransposalPreimage (composeAtlasTransposals third (composeAtlasTransposals second first)) targetElement /="),
    "native transposal associativity retains source domain": native_law_guard(
        "observedNativeAssociativity", "(atlasTransposalSourceValid (composeAtlasTransposals third (composeAtlasTransposals second first)) sourceElement <=> atlasTransposalSourceValid (composeAtlasTransposals (composeAtlasTransposals third second) first) sourceElement)", "not (atlasTransposalSourceValid (composeAtlasTransposals third (composeAtlasTransposals second first)) sourceElement <=> atlasTransposalSourceValid (composeAtlasTransposals (composeAtlasTransposals third second) first) sourceElement)"),
    "native transposal associativity retains path acceptance": native_law_guard(
        "observedNativeAssociativity", "(atlasTransposalPathValid (composeAtlasTransposals third (composeAtlasTransposals second first)) sourceElement <=> atlasTransposalPathValid (composeAtlasTransposals (composeAtlasTransposals third second) first) sourceElement)", "not (atlasTransposalPathValid (composeAtlasTransposals third (composeAtlasTransposals second first)) sourceElement <=> atlasTransposalPathValid (composeAtlasTransposals (composeAtlasTransposals third second) first) sourceElement)"),
    "native transposal associativity retains source owner": native_law_guard(
        "observedNativeAssociativity", "atlasTransposalSourceOwner (composeAtlasTransposals third (composeAtlasTransposals second first)) ==", "atlasTransposalSourceOwner (composeAtlasTransposals third (composeAtlasTransposals second first)) /="),
    "native transposal associativity retains target owner": native_law_guard(
        "observedNativeAssociativity", "atlasTransposalTargetOwner (composeAtlasTransposals third (composeAtlasTransposals second first)) ==", "atlasTransposalTargetOwner (composeAtlasTransposals third (composeAtlasTransposals second first)) /="),
    "native transposal left identity requires identity evidence": native_law_guard(
        "observedNativeLeftIdentity", "identity == identityAtlasTransposal", "True"),
    "native transposal left identity retains the raw map": native_law_guard(
        "observedNativeLeftIdentity", "mapAtlasTransposalObject (composeAtlasTransposals identity arrow) sourceElement ==", "mapAtlasTransposalObject (composeAtlasTransposals identity arrow) sourceElement /="),
    "native transposal left identity retains every inverse lookup": native_law_guard(
        "observedNativeLeftIdentity", "atlasTransposalPreimage (composeAtlasTransposals identity arrow) targetElement ==", "atlasTransposalPreimage (composeAtlasTransposals identity arrow) targetElement /="),
    "native transposal left identity retains path acceptance": native_law_guard(
        "observedNativeLeftIdentity", "(atlasTransposalPathValid (composeAtlasTransposals identity arrow) sourceElement <=> atlasTransposalPathValid arrow sourceElement)", "not (atlasTransposalPathValid (composeAtlasTransposals identity arrow) sourceElement <=> atlasTransposalPathValid arrow sourceElement)"),
    "native transposal left identity retains the source owner": native_law_guard(
        "observedNativeLeftIdentity", "atlasTransposalSourceOwner (composeAtlasTransposals identity arrow) ==", "atlasTransposalSourceOwner (composeAtlasTransposals identity arrow) /="),
    "native transposal left identity retains the target owner": native_law_guard(
        "observedNativeLeftIdentity", "atlasTransposalTargetOwner (composeAtlasTransposals identity arrow) ==", "atlasTransposalTargetOwner (composeAtlasTransposals identity arrow) /="),
    "native transposal right identity requires identity evidence": native_law_guard(
        "observedNativeRightIdentity", "identity == identityAtlasTransposal", "True"),
    "native transposal right identity retains the raw map": native_law_guard(
        "observedNativeRightIdentity", "mapAtlasTransposalObject (composeAtlasTransposals arrow identity) sourceElement ==", "mapAtlasTransposalObject (composeAtlasTransposals arrow identity) sourceElement /="),
    "native transposal right identity retains every inverse lookup": native_law_guard(
        "observedNativeRightIdentity", "atlasTransposalPreimage (composeAtlasTransposals arrow identity) targetElement ==", "atlasTransposalPreimage (composeAtlasTransposals arrow identity) targetElement /="),
    "native transposal right identity retains path acceptance": native_law_guard(
        "observedNativeRightIdentity", "(atlasTransposalPathValid (composeAtlasTransposals arrow identity) sourceElement <=> atlasTransposalPathValid arrow sourceElement)", "not (atlasTransposalPathValid (composeAtlasTransposals arrow identity) sourceElement <=> atlasTransposalPathValid arrow sourceElement)"),
    "native transposal right identity retains the source owner": native_law_guard(
        "observedNativeRightIdentity", "atlasTransposalSourceOwner (composeAtlasTransposals arrow identity) ==", "atlasTransposalSourceOwner (composeAtlasTransposals arrow identity) /="),
    "native transposal right identity retains the target owner": native_law_guard(
        "observedNativeRightIdentity", "atlasTransposalTargetOwner (composeAtlasTransposals arrow identity) ==", "atlasTransposalTargetOwner (composeAtlasTransposals arrow identity) /="),
    "native transposal retains its path domain": native_transposal_guard(
        "atlasTransposalPathValid result == atlasHomSourceValid witness hom",
        "atlasTransposalPathValid result /= atlasHomSourceValid witness hom"),
    "native transposal owned composition requires the first source owner": native_owned_composition_guard(
        "atlasHomSourceOwner sourceWitness firstHom == atlasWitnessOwner sourceWitness"),
    "native transposal owned composition requires the second source owner": native_owned_composition_guard(
        "atlasHomSourceOwner (atlasHomTargetWitness sourceWitness firstHom) secondHom == atlasHomTargetOwner sourceWitness firstHom"),
    "native transposal owned composition requires source membership": native_owned_composition_guard(
        "atlasTransposalElementValid sourceWitness sourceElement"),
    "native transposal owned composition requires the first path domain": native_owned_composition_guard(
        "atlasTransposalPathValid first == atlasHomSourceValid sourceWitness firstHom"),
    "native transposal owned composition requires the second path domain": native_owned_composition_guard(
        "atlasTransposalPathValid second == atlasHomSourceValid (atlasHomTargetWitness sourceWitness firstHom) secondHom"),
    "native transposal owned composition requires the retained first map": native_owned_composition_guard(
        "mapAtlasTransposalObject first == mapAtlasHomObject sourceWitness firstHom"),

    "native transposal witnessed map requires owner agreement": r"""
{-@ proofGuard :: witness:AtlasWitness source -> hom:AtlasHom source target
      -> sourceElement:{AtlasTransposalElement source | atlasTransposalElementValid witness sourceElement}
      -> {targetElement:AtlasTransposalElement target | atlasHomTargetValid witness hom targetElement} @-}
proofGuard :: AtlasWitness source -> AtlasHom source target -> AtlasTransposalElement source
  -> AtlasTransposalElement target
proofGuard = observedWitnessedMap
""",
    "native transposal witnessed map requires source membership": r"""
{-@ proofGuard :: witness:AtlasWitness source
      -> hom:{AtlasHom source target | atlasHomSourceOwner witness hom == atlasWitnessOwner witness}
      -> sourceElement:AtlasTransposalElement source
      -> {targetElement:AtlasTransposalElement target | atlasHomTargetValid witness hom targetElement} @-}
proofGuard :: AtlasWitness source -> AtlasHom source target -> AtlasTransposalElement source
  -> AtlasTransposalElement target
proofGuard = observedWitnessedMap
""",
    "native transposal retains its materialized source domain": native_transposal_guard(
        "atlasTransposalSourceValid result == atlasHomSourceValid witness hom",
        "atlasTransposalSourceValid result /= atlasHomSourceValid witness hom"),
    "native transposal retains its materialized map": native_transposal_guard(
        "mapAtlasTransposalObject result == mapAtlasHomObject witness hom",
        "mapAtlasTransposalObject result /= mapAtlasHomObject witness hom"),
    "native transposal retains its supplied inverse": native_transposal_guard(
        "atlasTransposalPreimage result == backward", "atlasTransposalPreimage result /= backward"),
    "native transposal requires the witnessed source owner": native_transposal_guard(
        "atlasHomSourceOwner witness hom == atlasWitnessOwner witness", "True"),
    "native transposal retains the witnessed source owner": native_transposal_guard(
        "atlasTransposalSourceOwner result == Just (atlasWitnessOwner witness)",
        "atlasTransposalSourceOwner result /= Just (atlasWitnessOwner witness)"),
    "native transposal retains the materialized target owner": native_transposal_guard(
        "atlasTransposalTargetOwner result == Just (atlasHomTargetOwner witness hom)",
        "atlasTransposalTargetOwner result /= Just (atlasHomTargetOwner witness hom)"),
    "native transposal element requires witnessed source validity": r"""
{-@ proofGuard :: witness:AtlasWitness object
      -> source:PageElement (AtlasObjectPaginationScope object) cell
      -> {result:AtlasTransposalElement object | atlasTransposalElementValid witness result} @-}
proofGuard :: AtlasWitness object -> PageElement (AtlasObjectPaginationScope object) cell
  -> AtlasTransposalElement object
proofGuard = atlasTransposalElement
""",
    "native transposal element retains the witnessed occurrence": r"""
{-@ proofGuard :: witness:AtlasWitness object
      -> source:{PageElement (AtlasObjectPaginationScope object) cell | atlasWitnessElementValid witness source}
      -> {result:AtlasTransposalElement object |
           transposalElementSource result /= SomePageElement (normalizeAtlasWitnessElement witness source)} @-}
proofGuard :: AtlasWitness object -> PageElement (AtlasObjectPaginationScope object) cell
  -> AtlasTransposalElement object
proofGuard = observedNativeElement
""",
    "native transposal element cannot substitute a witness": r"""
{-@ proofGuard :: first:AtlasWitness object -> second:AtlasWitness object
      -> source:{PageElement (AtlasObjectPaginationScope object) cell | atlasWitnessElementValid second source}
      -> {result:AtlasTransposalElement object | atlasTransposalElementValid first result} @-}
proofGuard :: AtlasWitness object -> AtlasWitness object -> PageElement (AtlasObjectPaginationScope object) cell
  -> AtlasTransposalElement object
proofGuard _ second source = observedNativeElement second source
""",
    "native transposal rejects unchecked order preservation": r"""
proofGuard :: AtlasTransposal source target -> OrderedAtlasTransposal source target
proofGuard transposal = orderedAtlasTransposal transposal (\_ _ -> ())
""",
    "native transposal rejects an unchecked inverse": r"""
{-@ proofGuard :: witness:AtlasWitness source
      -> hom:{AtlasHom source target | atlasHomSourceOwner witness hom == atlasWitnessOwner witness}
      -> backward:(targetElement:AtlasTransposalElement target
           -> Maybe ({sourceElement:AtlasTransposalElement source |
                atlasHomTargetValid witness hom targetElement => atlasHomSourceValid witness hom sourceElement}))
      -> AtlasTransposal source target @-}
proofGuard :: AtlasWitness source -> AtlasHom source target
  -> (AtlasTransposalElement target -> Maybe (AtlasTransposalElement source)) -> AtlasTransposal source target
proofGuard witness hom backward = observedNative witness hom backward (const ())
""",
    "native transposal source validity cannot prove false": r"""
{-@ proofGuard :: witness:AtlasWitness source -> hom:AtlasHom source target
      -> sourceElement:{AtlasTransposalElement source | atlasHomSourceValid witness hom sourceElement}
      -> {proof:() | False} @-}
proofGuard :: AtlasWitness source -> AtlasHom source target -> AtlasTransposalElement source -> ()
proofGuard _ _ _ = ()
""",
    "native transposal inverse requires path validity": r"""
{-@ proofGuard :: transposal:AtlasTransposal source target
      -> sourceElement:AtlasTransposalElement source
      -> {atlasTransposalPreimage transposal (mapAtlasTransposalObject transposal sourceElement)
            == Just sourceElement} @-}
proofGuard :: AtlasTransposal source target -> AtlasTransposalElement source -> ()
proofGuard = atlasTransposalLeftInverse
""",
    "native transposal source domain does not replace path validity": r"""
{-@ proofGuard :: transposal:AtlasTransposal source target
      -> sourceElement:{AtlasTransposalElement source | atlasTransposalSourceValid transposal sourceElement}
      -> {atlasTransposalPreimage transposal (mapAtlasTransposalObject transposal sourceElement)
            == Just sourceElement} @-}
proofGuard :: AtlasTransposal source target -> AtlasTransposalElement source -> ()
proofGuard = atlasTransposalLeftInverse
""",
    "native transposal path validity cannot prove false": r"""
{-@ proofGuard :: transposal:AtlasTransposal source target
      -> sourceElement:{AtlasTransposalElement source | atlasTransposalPathValid transposal sourceElement}
      -> {proof:() | False} @-}
proofGuard :: AtlasTransposal source target -> AtlasTransposalElement source -> ()
proofGuard _ _ = ()
""",
    "native transposal composition requires the second domain": r"""
{-@ proofGuard :: second:AtlasTransposal middle target
      -> first:AtlasTransposal source middle
      -> sourceElement:{AtlasTransposalElement source | atlasTransposalPathValid first sourceElement}
      -> {atlasTransposalPreimage (composeAtlasTransposals second first)
           (mapAtlasTransposalObject (composeAtlasTransposals second first) sourceElement)
             == Just sourceElement} @-}
proofGuard :: AtlasTransposal middle target -> AtlasTransposal source middle
  -> AtlasTransposalElement source -> ()
proofGuard second first source = atlasTransposalLeftInverse (composeAtlasTransposals second first) source
""",
    "native transposal composition requires the first domain": r"""
{-@ proofGuard :: second:AtlasTransposal middle target
      -> first:AtlasTransposal source middle
      -> sourceElement:{AtlasTransposalElement source |
           atlasTransposalPathValid second (mapAtlasTransposalObject first sourceElement)}
      -> {atlasTransposalPreimage (composeAtlasTransposals second first)
           (mapAtlasTransposalObject (composeAtlasTransposals second first) sourceElement)
             == Just sourceElement} @-}
proofGuard :: AtlasTransposal middle target -> AtlasTransposal source middle
  -> AtlasTransposalElement source -> ()
proofGuard second first source = atlasTransposalLeftInverse (composeAtlasTransposals second first) source
""",
    "native transposal composition preserves every raw inverse result": r"""
{-@ proofGuard :: second:AtlasTransposal middle target -> first:AtlasTransposal source middle
      -> sourceElement:AtlasTransposalElement source -> targetElement:AtlasTransposalElement target
      -> {result:Maybe (AtlasTransposalElement source) |
           result /= composePartialInverses (atlasTransposalPreimage first) (atlasTransposalPreimage second) targetElement} @-}
proofGuard :: AtlasTransposal middle target -> AtlasTransposal source middle
  -> AtlasTransposalElement source -> AtlasTransposalElement target -> Maybe (AtlasTransposalElement source)
proofGuard = observedNativeLookup
""",
    "native transposal composition preserves the raw map": r"""
{-@ proofGuard :: second:AtlasTransposal middle target -> first:AtlasTransposal source middle
      -> sourceElement:AtlasTransposalElement source
      -> {result:AtlasTransposalElement target |
           result /= mapAtlasTransposalObject second (mapAtlasTransposalObject first sourceElement)} @-}
proofGuard :: AtlasTransposal middle target -> AtlasTransposal source middle
  -> AtlasTransposalElement source -> AtlasTransposalElement target
proofGuard = observedNativeMap
""",
    "native transposal identity preserves raw inverse results": r"""
{-@ proofGuard :: identity:{AtlasTransposal object object | identity == identityAtlasTransposal}
      -> sourceElement:AtlasTransposalElement object
      -> {atlasTransposalPreimage identity sourceElement == Nothing} @-}
proofGuard :: AtlasTransposal object object -> AtlasTransposalElement object -> ()
proofGuard = observedNativeIdentity
""",
}

TRANSPOSAL_OBJECTS_PUBLIC_SOURCE = r"""
{-# LANGUAGE CPP #-}
{-# LANGUAGE RankNTypes #-}
#include "LiquidPlugin.h"
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--higherorder" @-}
module TransposalObjectsPublicGuard where
import Atlas (AtlasMorphismAction, atlasMorphismSource, atlasMorphismTarget)
import Atlas.Witness (AtlasOwner, atlasOwner, AtlasObjectEquality, AtlasWitnessData, atlasWitnessOwner)
import AtlasTransposal.Objects
import AtlasTransposal.Element (TransposalElementData, transposalElementValid)

{-@ observedObjects :: action:AtlasMorphismAction m sa ta ss ts sd td so sf to tf
      -> {objects:TransposalObjects sa ss sd ta ts td |
           transposalObjectsSourceOwner objects == atlasOwner (atlasMorphismSource action)
           && transposalObjectsTargetOwner objects == atlasOwner (atlasMorphismTarget action)} @-}
observedObjects :: AtlasMorphismAction m sa ta ss ts sd td so sf to tf
  -> TransposalObjects sa ss sd ta ts td
observedObjects = transposalObjects

{-@ observedSourceOwner :: objects:TransposalObjects sa ss sd ta ts td
      -> {owner:AtlasOwner | owner == transposalObjectsSourceOwner objects} @-}
observedSourceOwner :: TransposalObjects sa ss sd ta ts td -> AtlasOwner
observedSourceOwner objects = withTransposalObjects objects (\source _ _ -> atlasOwner source)

{-@ observedTargetOwner :: objects:TransposalObjects sa ss sd ta ts td
      -> {owner:AtlasOwner | owner == transposalObjectsTargetOwner objects} @-}
observedTargetOwner :: TransposalObjects sa ss sd ta ts td -> AtlasOwner
observedTargetOwner objects = withTransposalObjects objects (\_ target _ -> atlasOwner target)

{-@ observedTargetWitness :: AtlasObjectEquality target ta ts td -> objects:TransposalObjects sa ss sd ta ts td
      -> {witness:AtlasWitnessData target ta ts td | atlasWitnessOwner witness == transposalObjectsTargetOwner objects} @-}
observedTargetWitness :: AtlasObjectEquality target ta ts td -> TransposalObjects sa ss sd ta ts td
  -> AtlasWitnessData target ta ts td
observedTargetWitness = transposalObjectsTargetWitness

{-@ observedObjectsMap :: objects:TransposalObjects sa ss sd ta ts td
      -> source:TransposalElementData sa ss sd
      -> {target:TransposalElementData ta ts td |
           (transposalObjectsSource objects source => transposalObjectsTarget objects target)
           && target == transposalObjectsMap objects source} @-}
observedObjectsMap :: TransposalObjects sa ss sd ta ts td
  -> TransposalElementData sa ss sd -> TransposalElementData ta ts td
observedObjectsMap objects source = withTransposalObjects objects (\_ _ forward -> forward source)
"""
TRANSPOSAL_OBJECTS_PUBLIC_GUARDS = {
    "transposal materialization target witness retains its owner": r"""
{-@ proofGuard :: AtlasObjectEquality target ta ts td -> objects:TransposalObjects sa ss sd ta ts td
      -> {witness:AtlasWitnessData target ta ts td | atlasWitnessOwner witness /= transposalObjectsTargetOwner objects} @-}
proofGuard :: AtlasObjectEquality target ta ts td -> TransposalObjects sa ss sd ta ts td -> AtlasWitnessData target ta ts td
proofGuard = observedTargetWitness
""",
    "transposal materialization target witness does not substitute owners": r"""
{-@ proofGuard :: AtlasObjectEquality target ta ts td -> first:TransposalObjects sa ss sd ta ts td
      -> second:TransposalObjects sa ss sd ta ts td
      -> {witness:AtlasWitnessData target ta ts td | atlasWitnessOwner witness == transposalObjectsTargetOwner first} @-}
proofGuard :: AtlasObjectEquality target ta ts td -> TransposalObjects sa ss sd ta ts td
  -> TransposalObjects sa ss sd ta ts td -> AtlasWitnessData target ta ts td
proofGuard equality _ second = observedTargetWitness equality second
""",

    "transposal materialization construction retains its source owner": r"""
{-@ proofGuard :: action:AtlasMorphismAction m sa ta ss ts sd td so sf to tf
      -> {objects:TransposalObjects sa ss sd ta ts td |
           transposalObjectsSourceOwner objects /= atlasOwner (atlasMorphismSource action)} @-}
proofGuard :: AtlasMorphismAction m sa ta ss ts sd td so sf to tf
  -> TransposalObjects sa ss sd ta ts td
proofGuard = observedObjects
""",
    "transposal materialization construction retains its target owner": r"""
{-@ proofGuard :: action:AtlasMorphismAction m sa ta ss ts sd td so sf to tf
      -> {objects:TransposalObjects sa ss sd ta ts td |
           transposalObjectsTargetOwner objects /= atlasOwner (atlasMorphismTarget action)} @-}
proofGuard :: AtlasMorphismAction m sa ta ss ts sd td so sf to tf
  -> TransposalObjects sa ss sd ta ts td
proofGuard = observedObjects
""",
    "transposal materialization elimination retains its source owner": r"""
{-@ proofGuard :: objects:TransposalObjects sa ss sd ta ts td
      -> {owner:AtlasOwner | owner /= transposalObjectsSourceOwner objects} @-}
proofGuard :: TransposalObjects sa ss sd ta ts td -> AtlasOwner
proofGuard = observedSourceOwner
""",
    "transposal materialization elimination retains its target owner": r"""
{-@ proofGuard :: objects:TransposalObjects sa ss sd ta ts td
      -> {owner:AtlasOwner | owner /= transposalObjectsTargetOwner objects} @-}
proofGuard :: TransposalObjects sa ss sd ta ts td -> AtlasOwner
proofGuard = observedTargetOwner
""",
    "transposal materialization retains its exact object map": r"""
{-@ proofGuard :: objects:TransposalObjects sa ss sd ta ts td
      -> source:TransposalElementData sa ss sd
      -> {target:TransposalElementData ta ts td | target /= transposalObjectsMap objects source} @-}
proofGuard :: TransposalObjects sa ss sd ta ts td
  -> TransposalElementData sa ss sd -> TransposalElementData ta ts td
proofGuard = observedObjectsMap
""",
    "transposal materialization requires the source domain for target validity": r"""
{-@ proofGuard :: objects:TransposalObjects sa ss sd ta ts td
      -> source:TransposalElementData sa ss sd
      -> {target:TransposalElementData ta ts td | transposalObjectsTarget objects target} @-}
proofGuard :: TransposalObjects sa ss sd ta ts td
  -> TransposalElementData sa ss sd -> TransposalElementData ta ts td
proofGuard = observedObjectsMap
""",
}

TRANSPOSAL_ACTION_PUBLIC_SOURCE = r"""
{-# LANGUAGE CPP #-}
#include "LiquidPlugin.h"
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}
{-@ LIQUID "--higherorder" @-}
module TransposalActionPublicGuard where
import Atlas (Atlas)
import Atlas.Witness (AtlasWitnessData, atlasOwner, withAtlasWitnessData)
import AtlasTransposal.Element (TransposalElementData, transposalElementValid)
import AtlasTransposal.Action
import DomanialInsertion.Core (DomanialInsertion (..), composePartialInverses)

{-@ observedWitnessedComposition :: witness:AtlasWitnessData object a s d -> source:TransposalElementData a s d
      -> {result:TransposalElementData a s d | result == source} @-}
observedWitnessedComposition :: AtlasWitnessData object a s d -> TransposalElementData a s d -> TransposalElementData a s d
observedWitnessedComposition witness source =
  withAtlasWitnessData witness $ \_ firstOwner ->
    withAtlasWitnessData witness $ \_ secondOwner ->
      let first = identityTransposalAction firstOwner
          second = identityTransposalAction secondOwner
      in identityTransposalActionRetains firstOwner source `seq`
        identityTransposalActionRetains secondOwner source `seq`
        composeTransposalActionsMap second first source `seq`
        mapTransposalAction (composeTransposalActions second first) source

{-@ observedAction :: sourceOwner:Atlas sa ss sd so sf -> targetOwner:Atlas ta ts td to tf
      -> forward:(source:TransposalElementData sa ss sd
           -> {target:TransposalElementData ta ts td | transposalElementValid sourceOwner source => transposalElementValid targetOwner target})
      -> backward:(target:TransposalElementData ta ts td
           -> Maybe ({source:TransposalElementData sa ss sd | transposalElementValid targetOwner target => transposalElementValid sourceOwner source}))
      -> (source:{TransposalElementData sa ss sd | transposalElementValid sourceOwner source}
           -> {backward (forward source) == Just source})
      -> {action:TransposalAction sa ss sd so sf ta ts td to tf |
           transposalActionSource action == sourceOwner && transposalActionTarget action == targetOwner
           && mapTransposalAction action == forward && transposalActionPreimage action == backward} @-}
observedAction :: Atlas sa ss sd so sf -> Atlas ta ts td to tf
  -> (TransposalElementData sa ss sd -> TransposalElementData ta ts td)
  -> (TransposalElementData ta ts td -> Maybe (TransposalElementData sa ss sd))
  -> (TransposalElementData sa ss sd -> ()) -> TransposalAction sa ss sd so sf ta ts td to tf
observedAction = transposalAction

{-@ observedInsertion :: action:TransposalAction sa ss sd so sf ta ts td to tf
      -> {insertion:DomanialInsertion
           ({source:TransposalElementData sa ss sd | transposalElementValid (transposalActionSource action) source})
           ({target:TransposalElementData ta ts td | transposalElementValid (transposalActionTarget action) target}) |
           applyInsertion insertion == mapTransposalAction action && preimage insertion == transposalActionPreimage action} @-}
observedInsertion :: TransposalAction sa ss sd so sf ta ts td to tf
  -> DomanialInsertion (TransposalElementData sa ss sd) (TransposalElementData ta ts td)
observedInsertion = transposalActionInsertion

{-@ observedForward :: action:TransposalAction sa ss sd so sf ta ts td to tf
      -> source:{TransposalElementData sa ss sd | transposalElementValid (transposalActionSource action) source}
      -> {target:TransposalElementData ta ts td | transposalElementValid (transposalActionTarget action) target} @-}
observedForward :: TransposalAction sa ss sd so sf ta ts td to tf
  -> TransposalElementData sa ss sd -> TransposalElementData ta ts td
observedForward action source = mapTransposalAction action source

{-@ observedPreimage :: action:TransposalAction sa ss sd so sf ta ts td to tf
      -> target:{TransposalElementData ta ts td | transposalElementValid (transposalActionTarget action) target}
      -> Maybe ({source:TransposalElementData sa ss sd | transposalElementValid (transposalActionSource action) source}) @-}
observedPreimage :: TransposalAction sa ss sd so sf ta ts td to tf
  -> TransposalElementData ta ts td -> Maybe (TransposalElementData sa ss sd)
observedPreimage action target = transposalActionPreimage action target

{-@ observedComposition :: second:TransposalAction ma ms md mo mf ta ts td to tf
      -> first:{TransposalAction sa ss sd so sf ma ms md mo1 mf1 |
           atlasOwner (transposalActionTarget first) == atlasOwner (transposalActionSource second)}
      -> {action:TransposalAction sa ss sd so sf ta ts td to tf |
           transposalActionSource action == transposalActionSource first
           && transposalActionTarget action == transposalActionTarget second} @-}
observedComposition :: TransposalAction ma ms md mo mf ta ts td to tf
  -> TransposalAction sa ss sd so sf ma ms md mo1 mf1 -> TransposalAction sa ss sd so sf ta ts td to tf
observedComposition = composeTransposalActions

{-@ observedCompositePreimage :: second:TransposalAction ma ms md mo mf ta ts td to tf
      -> first:{TransposalAction sa ss sd so sf ma ms md mo1 mf1 |
           atlasOwner (transposalActionTarget first) == atlasOwner (transposalActionSource second)}
      -> target:TransposalElementData ta ts td
      -> {result:Maybe (TransposalElementData sa ss sd) |
           result == composePartialInverses (transposalActionPreimage first) (transposalActionPreimage second) target} @-}
observedCompositePreimage :: TransposalAction ma ms md mo mf ta ts td to tf
  -> TransposalAction sa ss sd so sf ma ms md mo1 mf1 -> TransposalElementData ta ts td
  -> Maybe (TransposalElementData sa ss sd)
observedCompositePreimage second first target = composeTransposalActionsPreimage second first target `seq`
  transposalActionPreimage (composeTransposalActions second first) target

{-@ observedCompositeMap :: second:TransposalAction ma ms md mo mf ta ts td to tf
      -> first:{TransposalAction sa ss sd so sf ma ms md mo1 mf1 |
           atlasOwner (transposalActionTarget first) == atlasOwner (transposalActionSource second)}
      -> source:TransposalElementData sa ss sd
      -> {target:TransposalElementData ta ts td |
           target == mapTransposalAction second (mapTransposalAction first source)} @-}
observedCompositeMap :: TransposalAction ma ms md mo mf ta ts td to tf
  -> TransposalAction sa ss sd so sf ma ms md mo1 mf1 -> TransposalElementData sa ss sd
  -> TransposalElementData ta ts td
observedCompositeMap second first source = composeTransposalActionsMap second first source `seq`
  mapTransposalAction (composeTransposalActions second first) source

{-@ observedIdentity :: owner:Atlas a s d o f -> source:TransposalElementData a s d
      -> {target:TransposalElementData a s d | target == source} @-}
observedIdentity :: Atlas a s d o f -> TransposalElementData a s d -> TransposalElementData a s d
observedIdentity owner source = identityTransposalActionRetains owner source `seq`
  mapTransposalAction (identityTransposalAction owner) source
"""


def transposal_action_guard(old, new):
    contract = "{-@ observedAction" + TRANSPOSAL_ACTION_PUBLIC_SOURCE.split("{-@ observedAction", 1)[1].split("\n\n{-@ observedInsertion", 1)[0]
    assert old in contract
    return contract.replace(old, new, 1).replace("observedAction", "proofGuard").replace("proofGuard = transposalAction", "proofGuard = observedAction")


TRANSPOSAL_ACTION_PUBLIC_GUARDS = {
    "owned transposal action composes independently eliminated owners": r"""
{-@ proofGuard :: witness:AtlasWitnessData object a s d -> source:TransposalElementData a s d
      -> {result:TransposalElementData a s d | result /= source} @-}
proofGuard :: AtlasWitnessData object a s d -> TransposalElementData a s d -> TransposalElementData a s d
proofGuard = observedWitnessedComposition
""",
    "owned transposal action requires forward validity": transposal_action_guard(
        "transposalElementValid sourceOwner source => transposalElementValid targetOwner target", "True"),
    "owned transposal action requires inverse result validity": transposal_action_guard(
        "transposalElementValid targetOwner target => transposalElementValid sourceOwner source", "True"),
    "owned transposal action requires its left inverse": transposal_action_guard(
        "{backward (forward source) == Just source}", "()"),
    "owned transposal action retains its source owner": transposal_action_guard(
        "transposalActionSource action == sourceOwner", "transposalActionSource action /= sourceOwner"),
    "owned transposal action retains its target owner": transposal_action_guard(
        "transposalActionTarget action == targetOwner", "transposalActionTarget action /= targetOwner"),
    "owned transposal action retains its raw map": transposal_action_guard(
        "mapTransposalAction action == forward", "mapTransposalAction action /= forward"),
    "owned transposal action retains its raw inverse": transposal_action_guard(
        "transposalActionPreimage action == backward", "transposalActionPreimage action /= backward"),
    "owned transposal action requires the actual middle owner": r"""
proofGuard :: TransposalAction ma ms md mo mf ta ts td to tf
  -> TransposalAction sa ss sd so sf ma ms md mo1 mf1 -> TransposalAction sa ss sd so sf ta ts td to tf
proofGuard = observedComposition
""",
    "owned transposal action restricts the inverse law to its source domain": r"""
proofGuard :: TransposalAction sa ss sd so sf ta ts td to tf -> TransposalElementData sa ss sd -> ()
proofGuard = transposalActionLeftInverse
""",
    "owned transposal action retains the inverse law": r"""
{-@ proofGuard :: action:TransposalAction sa ss sd so sf ta ts td to tf
      -> source:{TransposalElementData sa ss sd | transposalElementValid (transposalActionSource action) source}
      -> {transposalActionPreimage action (mapTransposalAction action source) /= Just source} @-}
proofGuard :: TransposalAction sa ss sd so sf ta ts td to tf -> TransposalElementData sa ss sd -> ()
proofGuard = transposalActionLeftInverse
""",
    "owned transposal action retains every composed raw lookup": r"""
{-@ proofGuard :: second:TransposalAction ma ms md mo mf ta ts td to tf
      -> first:{TransposalAction sa ss sd so sf ma ms md mo1 mf1 |
           atlasOwner (transposalActionTarget first) == atlasOwner (transposalActionSource second)}
      -> target:TransposalElementData ta ts td
      -> {result:Maybe (TransposalElementData sa ss sd) |
           result /= composePartialInverses (transposalActionPreimage first) (transposalActionPreimage second) target} @-}
proofGuard :: TransposalAction ma ms md mo mf ta ts td to tf
  -> TransposalAction sa ss sd so sf ma ms md mo1 mf1 -> TransposalElementData ta ts td
  -> Maybe (TransposalElementData sa ss sd)
proofGuard = observedCompositePreimage
""",
    "owned transposal action retains its composed raw map": r"""
{-@ proofGuard :: second:TransposalAction ma ms md mo mf ta ts td to tf
      -> first:{TransposalAction sa ss sd so sf ma ms md mo1 mf1 |
           atlasOwner (transposalActionTarget first) == atlasOwner (transposalActionSource second)}
      -> source:TransposalElementData sa ss sd
      -> {target:TransposalElementData ta ts td |
           target /= mapTransposalAction second (mapTransposalAction first source)} @-}
proofGuard :: TransposalAction ma ms md mo mf ta ts td to tf
  -> TransposalAction sa ss sd so sf ma ms md mo1 mf1 -> TransposalElementData sa ss sd
  -> TransposalElementData ta ts td
proofGuard = observedCompositeMap
""",
    "owned transposal action retains raw identity": r"""
{-@ proofGuard :: owner:Atlas a s d o f -> source:TransposalElementData a s d
      -> {target:TransposalElementData a s d | target /= source} @-}
proofGuard :: Atlas a s d o f -> TransposalElementData a s d -> TransposalElementData a s d
proofGuard = observedIdentity
""",
}


TRANSPOSAL_ELEMENT_PUBLIC_SOURCE = r"""
{-# LANGUAGE CPP #-}
{-# LANGUAGE RankNTypes #-}
#include "LiquidPlugin.h"
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}
{-@ LIQUID "--higherorder" @-}
module TransposalElementPublicGuard where
import Atlas (Atlas, atlasPageElements, normalizeAtlasElement)
import Atlas.Witness (atlasOwner)
import AtlasTransposal.Element
import PageElements (pageElementTraceValid)
import PageElements.Structure (PageElement, SomePageElement (..))

{-@ observedOwnerTransfer :: first:Atlas a s d o f
      -> second:{Atlas a s d o2 f2 | atlasOwner second == atlasOwner first}
      -> element:{TransposalElementData a s d | transposalElementValid first element}
      -> {result:TransposalElementData a s d | result == element && transposalElementValid second result} @-}
observedOwnerTransfer :: Atlas a s d o f -> Atlas a s d o2 f2
  -> TransposalElementData a s d -> TransposalElementData a s d
observedOwnerTransfer first second element = transposalOwnersAgree first second element `seq` element

{-@ observedElement :: owner:Atlas a s d o f
      -> source:{PageElement s object | pageElementTraceValid (atlasPageElements owner) source}
      -> {element:TransposalElementData a s d | transposalElementValid owner element
           && transposalElementSource element == SomePageElement (normalizeAtlasElement owner source)} @-}
observedElement :: Atlas a s d o f -> PageElement s object -> TransposalElementData a s d
observedElement = transposalElementAt

{-@ observedSource :: owner:Atlas a s d o f
      -> element:{TransposalElementData a s d | transposalElementValid owner element}
      -> {source:SomePageElement s | source == transposalElementSource element} @-}
observedSource :: Atlas a s d o f -> TransposalElementData a s d -> SomePageElement s
observedSource owner element = withTransposalElementOf owner element SomePageElement

{-@ observedNormalized :: owner:Atlas a s d o f
      -> element:{TransposalElementData a s d | transposalElementValid owner element}
      -> {answer:Bool | answer} @-}
observedNormalized :: Atlas a s d o f -> TransposalElementData a s d -> Bool
observedNormalized owner element = withTransposalElementOf owner element
  (\source -> normalizeAtlasElement owner source == source)

{-@ observedValid :: owner:Atlas a s d o f
      -> element:{TransposalElementData a s d | transposalElementValid owner element}
      -> {answer:Bool | answer} @-}
observedValid :: Atlas a s d o f -> TransposalElementData a s d -> Bool
observedValid owner element = withTransposalElementOf owner element
  (pageElementTraceValid (atlasPageElements owner))
"""
TRANSPOSAL_ELEMENT_PUBLIC_GUARDS = {
    "transposal owner transfer requires complete owner equality": r"""
{-@ proofGuard :: first:Atlas a s d o f -> second:Atlas a s d o2 f2
      -> element:{TransposalElementData a s d | transposalElementValid first element}
      -> {result:TransposalElementData a s d | result == element && transposalElementValid second result} @-}
proofGuard :: Atlas a s d o f -> Atlas a s d o2 f2
  -> TransposalElementData a s d -> TransposalElementData a s d
proofGuard = observedOwnerTransfer
""",
    "transposal owner transfer requires source membership": r"""
{-@ proofGuard :: first:Atlas a s d o f
      -> second:{Atlas a s d o2 f2 | atlasOwner second == atlasOwner first}
      -> element:TransposalElementData a s d
      -> {result:TransposalElementData a s d | result == element && transposalElementValid second result} @-}
proofGuard :: Atlas a s d o f -> Atlas a s d o2 f2
  -> TransposalElementData a s d -> TransposalElementData a s d
proofGuard = observedOwnerTransfer
""",
    "transposal elements require an owning valid source": r"""
proofGuard :: Atlas a s d o f -> PageElement s object -> TransposalElementData a s d
proofGuard = observedElement
""",
    "transposal elements retain the actual owner": r"""
{-@ proofGuard :: owner:Atlas a s d o f -> other:Atlas a s d o f
      -> source:{PageElement s object | pageElementTraceValid (atlasPageElements owner) source}
      -> {element:TransposalElementData a s d | transposalElementValid other element} @-}
proofGuard :: Atlas a s d o f -> Atlas a s d o f -> PageElement s object -> TransposalElementData a s d
proofGuard owner _ = observedElement owner
""",
    "transposal elements retain the normalized source": r"""
{-@ proofGuard :: owner:Atlas a s d o f
      -> source:{PageElement s object | pageElementTraceValid (atlasPageElements owner) source}
      -> {element:TransposalElementData a s d |
           transposalElementSource element /= SomePageElement (normalizeAtlasElement owner source)} @-}
proofGuard :: Atlas a s d o f -> PageElement s object -> TransposalElementData a s d
proofGuard = observedElement
""",
    "transposal elements require validity for elimination": r"""
proofGuard :: Atlas a s d o f -> TransposalElementData a s d -> SomePageElement s
proofGuard = observedSource
""",
    "transposal elements expose the exact stored occurrence": r"""
{-@ proofGuard :: owner:Atlas a s d o f
      -> element:{TransposalElementData a s d | transposalElementValid owner element}
      -> {source:SomePageElement s | source /= transposalElementSource element} @-}
proofGuard :: Atlas a s d o f -> TransposalElementData a s d -> SomePageElement s
proofGuard = observedSource
""",
    "transposal elements expose normalization evidence": r"""
{-@ proofGuard :: owner:Atlas a s d o f
      -> element:{TransposalElementData a s d | transposalElementValid owner element}
      -> {answer:Bool | not answer} @-}
proofGuard :: Atlas a s d o f -> TransposalElementData a s d -> Bool
proofGuard = observedNormalized
""",
    "transposal elements expose owning validity evidence": r"""
{-@ proofGuard :: owner:Atlas a s d o f
      -> element:{TransposalElementData a s d | transposalElementValid owner element}
      -> {answer:Bool | not answer} @-}
proofGuard :: Atlas a s d o f -> TransposalElementData a s d -> Bool
proofGuard = observedValid
""",
}


DOMINC_MORPHISM_PUBLIC_SOURCE = r"""
{-# LANGUAGE CPP #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeFamilies #-}
#include "LiquidPlugin.h"
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--higherorder" @-}
module InclusionMorphismPublicGuard where
import Atlas
  ( Atlas, AtlasMorphismAction, AtlasObjectMap, AtlasMappedObject
  , atlasMorphismSource, atlasMorphismTarget, atlasMorphismObjectMapWitness
  , mapAtlasMorphismActionObject, mapAtlasMorphismActionComponent, atlasPageElements, mapPrimitiveElement )
import Coalition.Element
  ( CoalitionData, coalitionElementAt, coalitionElementReaches, coalitionElementValid, coalitionElementSource )
import DomanialInclusion.Action (constantComponentInsertion)
import DomanialInclusion.Morphism (coalitionMorphismAction)
import DomanialInclusion.Data (DominionCellData)
import DomanialInclusion.Presentation (DominionAtlas, DominionPaginationScope, dominionAtlas)
import PageElements (PageElement, pageElementTraceValid, originPageElement)
import PageElements.Structure (SomePageElement (..), somePageElementPrecedes, somePageElementTransported)
{-@ observedMorphism :: witness:AtlasObjectMap objectMap
      -> sourceOwner:DominionAtlas owner a
      -> targetAtlas:Atlas atlasScope scope cellData origin final
      -> target:{PageElement scope targetObject | pageElementTraceValid (atlasPageElements targetAtlas) target}
      -> mapObject:(forall object. PageElement (DominionPaginationScope a) object
           -> {occurrence:PageElement scope (AtlasMappedObject objectMap object) |
                pageElementTraceValid (atlasPageElements targetAtlas) occurrence
                && SomePageElement occurrence == SomePageElement target})
      -> forward:(a -> {element:CoalitionData atlasScope scope cellData |
           coalitionElementValid targetAtlas element
           && coalitionElementSource element == originPageElement (atlasPageElements targetAtlas)
           && coalitionElementReaches element target})
      -> backward:(forall object. PageElement scope object -> cellData object -> Maybe a)
      -> leftInverse:(forall object. occurrence:{PageElement scope object |
           pageElementTraceValid (atlasPageElements targetAtlas) occurrence
           && SomePageElement occurrence == SomePageElement target}
           -> value:a -> {backward occurrence (coalitionElementAt targetAtlas occurrence (forward value)) == Just value})
      -> pageLaw:(sourceValue:SomePageElement (DominionPaginationScope a)
           -> targetValue:{SomePageElement (DominionPaginationScope a) |
                somePageElementPrecedes sourceValue targetValue
                && somePageElementTransported sourceValue targetValue}
           -> {somePageElementPrecedes
                 (mapPrimitiveElement witness (dominionAtlas sourceOwner) targetAtlas mapObject sourceValue)
                 (mapPrimitiveElement witness (dominionAtlas sourceOwner) targetAtlas mapObject targetValue)
               && somePageElementTransported
                 (mapPrimitiveElement witness (dominionAtlas sourceOwner) targetAtlas mapObject sourceValue)
                 (mapPrimitiveElement witness (dominionAtlas sourceOwner) targetAtlas mapObject targetValue)})
      -> {action:AtlasMorphismAction objectMap owner atlasScope (DominionPaginationScope a) scope
           (DominionCellData a) cellData () () origin final |
           atlasMorphismSource action == dominionAtlas sourceOwner
           && atlasMorphismTarget action == targetAtlas
           && atlasMorphismObjectMapWitness action == witness
           && mapAtlasMorphismActionObject action == mapObject
           && mapAtlasMorphismActionComponent action
                == constantComponentInsertion witness sourceOwner targetAtlas target mapObject forward backward leftInverse} @-}
observedMorphism :: AtlasObjectMap objectMap
  -> DominionAtlas owner a
  -> Atlas atlasScope scope cellData origin final
  -> PageElement scope targetObject
  -> (forall object. PageElement (DominionPaginationScope a) object -> PageElement scope (AtlasMappedObject objectMap object))
  -> (a -> CoalitionData atlasScope scope cellData)
  -> (forall object. PageElement scope object -> cellData object -> Maybe a)
  -> (forall object. PageElement scope object -> a -> ())
  -> (SomePageElement (DominionPaginationScope a) -> SomePageElement (DominionPaginationScope a) -> ())
  -> AtlasMorphismAction objectMap owner atlasScope (DominionPaginationScope a) scope
       (DominionCellData a) cellData () () origin final
observedMorphism = coalitionMorphismAction
"""

def inclusion_morphism_guard(old, new):
    contract = "{-@ observedMorphism" + DOMINC_MORPHISM_PUBLIC_SOURCE.split("{-@ observedMorphism", 1)[1]
    assert old in contract
    return contract.replace(old, new, 1).replace("observedMorphism", "proofGuard").replace(
        "proofGuard = coalitionMorphismAction", "proofGuard = observedMorphism")


DOMINC_MORPHISM_PUBLIC_GUARDS = {
    "inclusion morphism assembly requires checked inverse evidence": inclusion_morphism_guard(
        "{backward occurrence (coalitionElementAt targetAtlas occurrence (forward value)) == Just value}", "()"),
    "inclusion morphism assembly requires a valid owning target": inclusion_morphism_guard(
        "{PageElement scope targetObject | pageElementTraceValid (atlasPageElements targetAtlas) target}",
        "PageElement scope targetObject"),
    "inclusion morphism assembly requires a constant object action": inclusion_morphism_guard(
        "&& SomePageElement occurrence == SomePageElement target", ""),
    "inclusion morphism assembly retains its source owner": inclusion_morphism_guard(
        "atlasMorphismSource action == dominionAtlas sourceOwner", "atlasMorphismSource action /= dominionAtlas sourceOwner"),
    "inclusion morphism assembly retains its target owner": inclusion_morphism_guard(
        "atlasMorphismTarget action == targetAtlas", "atlasMorphismTarget action /= targetAtlas"),
    "inclusion morphism assembly retains its object callback": inclusion_morphism_guard(
        "mapAtlasMorphismActionObject action == mapObject", "mapAtlasMorphismActionObject action /= mapObject"),
    "inclusion morphism assembly retains its entire component callback": inclusion_morphism_guard(
        "== constantComponentInsertion witness", "/= constantComponentInsertion witness"),
}
_page_law_start = DOMINC_MORPHISM_PUBLIC_SOURCE.index("      -> pageLaw:")
_page_law_end = DOMINC_MORPHISM_PUBLIC_SOURCE.index("      -> {action:", _page_law_start)
DOMINC_MORPHISM_PUBLIC_GUARDS[
    "inclusion morphism assembly requires a checked page law"] = inclusion_morphism_guard(
        DOMINC_MORPHISM_PUBLIC_SOURCE[_page_law_start:_page_law_end],
        "      -> pageLaw:(SomePageElement (DominionPaginationScope a) -> SomePageElement (DominionPaginationScope a) -> ())\n")

DOMINC_DATA_GUARDS = {
    "constant Dominion preserves the supplied forward rank": """
{-@ proofGuard :: owner:Dominion a -> value:a
      -> {result:Natural | result /= rank owner value} @-}
proofGuard :: Dominion a -> a -> Natural
proofGuard owner value = rank (constantDominion owner) (dominionCellData value)
""",
    "constant Dominion preserves successful decoding outside its rank image too": """
{-@ proofGuard :: owner:Dominion a -> index:{Natural | unrank owner index /= Nothing}
      -> {result:Maybe (DominionCellData a object) | result == Nothing} @-}
proofGuard :: Dominion a -> Natural -> Maybe (DominionCellData a object)
proofGuard owner index = unrank (constantDominion owner) index
""",
    "constant cell insertion cannot change a datum": """
{-@ proofGuard :: datum:DominionCellData a object
      -> {result:DominionCellData a object | result /= datum} @-}
proofGuard :: DominionCellData a object -> DominionCellData a object
proofGuard datum = applyInsertion identityDominionCellInsertion datum
""",
    "constant cell insertion cannot discard its inverse": """
{-@ proofGuard :: datum:DominionCellData a object
      -> {result:Maybe (DominionCellData a object) | result == Nothing} @-}
proofGuard :: DominionCellData a object -> Maybe (DominionCellData a object)
proofGuard datum = preimage identityDominionCellInsertion datum
""",
}

DOMINC_SOURCE = HASKELL / "src/DatraCore/Atlases/Derived/Coalitions/DomanialInclusion/LiquidInternal.hs"
DOMINC_GUARDS = {
    "Dominion coalition counit requires its owning validity": """
{-@ proofGuard :: DominionAtlas owner a
      -> CoalitionData owner (DominionPaginationScope a) (DominionCellData a) -> a @-}
proofGuard :: DominionAtlas owner a
  -> CoalitionData owner (DominionPaginationScope a) (DominionCellData a) -> a
proofGuard owner = applyInsertion (dominionCoalitionCounit owner)
""",
    "Dominion coalition isomorphism requires its owning validity": """
{-@ proofGuard :: DominionAtlas owner a
      -> CoalitionData owner (DominionPaginationScope a) (DominionCellData a) -> () @-}
proofGuard :: DominionAtlas owner a
  -> CoalitionData owner (DominionPaginationScope a) (DominionCellData a) -> ()
proofGuard = coaDomIncIsoLeftInverse
""",
    "Dominion coalition counit requires the canonical origin": """
{-@ proofGuard :: owner:DominionAtlas ownerScope a
      -> {element:CoalitionData ownerScope (DominionPaginationScope a) (DominionCellData a) |
           coalitionElementValid (dominionAtlas owner) element} -> a @-}
proofGuard :: DominionAtlas owner a
  -> CoalitionData owner (DominionPaginationScope a) (DominionCellData a) -> a
proofGuard owner = applyInsertion (dominionCoalitionCounit owner)
""",
    "Dominion coalition counit cannot discard its inverse": """
{-@ proofGuard :: owner:DominionAtlas ownerScope a
      -> element:{CoalitionData ownerScope (DominionPaginationScope a) (DominionCellData a) |
           DominionCoalitionValid owner element}
      -> {result:Maybe (CoalitionData ownerScope (DominionPaginationScope a) (DominionCellData a)) |
           result == Nothing} @-}
proofGuard :: DominionAtlas owner a
  -> CoalitionData owner (DominionPaginationScope a) (DominionCellData a)
  -> Maybe (CoalitionData owner (DominionPaginationScope a) (DominionCellData a))
proofGuard owner element = dominionCoalitionReconstruct owner element `seq`
  preimage (dominionCoalitionCounit owner) (applyInsertion (dominionCoalitionCounit owner) element)
""",
    "Dominion coalition construction retains the original value": """
{-@ proofGuard :: DominionAtlas owner a -> value:a -> {result:a | result /= value} @-}
proofGuard :: DominionAtlas owner a -> a -> a
proofGuard owner value = coalitionValue (dominionCoalitionElement owner value)
""",
    "Dominion coalition unit cannot discard its inverse": """
{-@ proofGuard :: DominionAtlas owner a -> a -> {result:Maybe a | result == Nothing} @-}
proofGuard :: DominionAtlas owner a -> a -> Maybe a
proofGuard owner value = dominionCoalitionRoundTrip owner value `seq`
  preimage (dominionCoalitionUnit owner) (applyInsertion (dominionCoalitionUnit owner) value)
""",
    "one-page coverage requires a one-page owner": """
{-@ proofGuard :: owner:Atlas a s d o f
      -> source:{PageElement s object | cellTraceValid owner source}
      -> datum:{d object | atlasAcceptsDatum owner source datum}
      -> CoverageWitness a s d @-}
proofGuard :: Atlas a s d o f -> PageElement s object -> d object -> CoverageWitness a s d
proofGuard = onePageCoverage
""",
    "one-page coverage requires an owning trace": """
{-@ proofGuard :: owner:{Atlas a s d o f | folioLength (atlasFolio owner) == 1}
      -> source:PageElement s object
      -> datum:{d object | atlasAcceptsDatum owner source datum}
      -> CoverageWitness a s d @-}
proofGuard :: Atlas a s d o f -> PageElement s object -> d object -> CoverageWitness a s d
proofGuard = onePageCoverage
""",
    "one-page coverage requires an accepted datum": """
{-@ proofGuard :: owner:{Atlas a s d o f | folioLength (atlasFolio owner) == 1}
      -> source:{PageElement s object | cellTraceValid owner source}
      -> d object -> CoverageWitness a s d @-}
proofGuard :: Atlas a s d o f -> PageElement s object -> d object -> CoverageWitness a s d
proofGuard = onePageCoverage
""",

}


DOMINC_COMPONENT_PUBLIC_SOURCE = r"""
{-# LANGUAGE CPP #-}
#include "LiquidPlugin.h"
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--higherorder" @-}
module DominionComponentPublicGuard where
import Atlas (Atlas, atlasPageElements, atlasAcceptsDatum)
import AtlasExtent (cellTraceValid)
import Coalition.Element
  ( CoalitionData, coalitionElementAt, coalitionElementValid, coalitionElementSource, coalitionElementReaches )
import DomanialInclusion.Component (coalitionComponentInsertion, coalitionComponentMap)
import DomanialInclusion.Data
  ( DominionCellData, domIncHomFromValue, dominionCellProjectionPreimage )
import DomanialInsertion.Core (DomanialInsertion (..), composePartialInverses)
import PageElements (PageElement, originPageElement)

{-@ opaque-reflect coalitionComponentInsertion @-}

{-@ observedComponentRoundTrip :: owner:Atlas a s d o f
      -> target:{PageElement s object | cellTraceValid owner target}
      -> forward:(value -> {element:CoalitionData a s d |
           coalitionElementValid owner element
           && coalitionElementSource element == originPageElement (atlasPageElements owner)
           && coalitionElementReaches element target})
      -> backward:(d object -> Maybe value)
      -> law:(value:value -> {backward (coalitionElementAt owner target (forward value)) == Just value})
      -> datum:DominionCellData value sourceObject
      -> {preimage (coalitionComponentInsertion owner target forward backward law)
           (applyInsertion (coalitionComponentInsertion owner target forward backward law) datum) == Just datum} @-}
observedComponentRoundTrip :: Atlas a s d o f -> PageElement s object
  -> (value -> CoalitionData a s d) -> (d object -> Maybe value) -> (value -> ())
  -> DominionCellData value sourceObject -> ()
observedComponentRoundTrip owner target forward backward law datum =
  insertionLeftInverse (coalitionComponentInsertion owner target forward backward law) datum

{-@ observedComponentFunctions :: owner:Atlas a s d o f
      -> target:{PageElement s object | cellTraceValid owner target}
      -> forward:(value -> {element:CoalitionData a s d |
           coalitionElementValid owner element
           && coalitionElementSource element == originPageElement (atlasPageElements owner)
           && coalitionElementReaches element target})
      -> backward:(d object -> Maybe value)
      -> law:(value:value -> {backward (coalitionElementAt owner target (forward value)) == Just value})
      -> {result:DomanialInsertion (DominionCellData value sourceObject)
           ({datum:d object | atlasAcceptsDatum owner target datum}) |
           applyInsertion result == domIncHomFromValue (coalitionComponentMap owner target forward)
           && preimage result == composePartialInverses dominionCellProjectionPreimage backward} @-}
observedComponentFunctions :: Atlas a s d o f -> PageElement s object
  -> (value -> CoalitionData a s d) -> (d object -> Maybe value) -> (value -> ())
  -> DomanialInsertion (DominionCellData value sourceObject) (d object)
observedComponentFunctions = coalitionComponentInsertion
"""
DOMINC_COMPONENT_PUBLIC_GUARDS = {
    "coalition components retain the exact forward callback": r"""
{-@ proofGuard :: owner:Atlas a s d o f
      -> target:{PageElement s object | cellTraceValid owner target}
      -> forward:(value -> {element:CoalitionData a s d |
           coalitionElementValid owner element
           && coalitionElementSource element == originPageElement (atlasPageElements owner)
           && coalitionElementReaches element target})
      -> backward:(d object -> Maybe value)
      -> law:(value:value -> {backward (coalitionElementAt owner target (forward value)) == Just value})
      -> {result:DomanialInsertion (DominionCellData value sourceObject)
           ({datum:d object | atlasAcceptsDatum owner target datum}) |
           applyInsertion result /= domIncHomFromValue (coalitionComponentMap owner target forward)} @-}
proofGuard :: Atlas a s d o f -> PageElement s object
  -> (value -> CoalitionData a s d) -> (d object -> Maybe value) -> (value -> ())
  -> DomanialInsertion (DominionCellData value sourceObject) (d object)
proofGuard = observedComponentFunctions
""",
    "coalition components retain the complete partial inverse": r"""
{-@ proofGuard :: owner:Atlas a s d o f
      -> target:{PageElement s object | cellTraceValid owner target}
      -> forward:(value -> {element:CoalitionData a s d |
           coalitionElementValid owner element
           && coalitionElementSource element == originPageElement (atlasPageElements owner)
           && coalitionElementReaches element target})
      -> backward:(d object -> Maybe value)
      -> law:(value:value -> {backward (coalitionElementAt owner target (forward value)) == Just value})
      -> {result:DomanialInsertion (DominionCellData value sourceObject)
           ({datum:d object | atlasAcceptsDatum owner target datum}) |
           preimage result /= composePartialInverses dominionCellProjectionPreimage backward} @-}
proofGuard :: Atlas a s d o f -> PageElement s object
  -> (value -> CoalitionData a s d) -> (d object -> Maybe value) -> (value -> ())
  -> DomanialInsertion (DominionCellData value sourceObject) (d object)
proofGuard = observedComponentFunctions
""",
    "coalition components reject an inverse that drops every image": """
{-@ proofGuard :: targetAtlas:Atlas atlasScope scope cellData origin final
      -> targetOccurrence:{PageElement scope object | cellTraceValid targetAtlas targetOccurrence}
      -> (a -> {element:CoalitionData atlasScope scope cellData |
           coalitionElementValid targetAtlas element
           && coalitionElementSource element == originPageElement (atlasPageElements targetAtlas)
           && coalitionElementReaches element targetOccurrence})
      -> DomanialInsertion (DominionCellData a sourceObject) (cellData object) @-}
proofGuard
  :: Atlas atlasScope scope cellData origin final
  -> PageElement scope object
  -> (a -> CoalitionData atlasScope scope cellData)
  -> DomanialInsertion (DominionCellData a sourceObject) (cellData object)
proofGuard targetAtlas targetOccurrence forward =
  coalitionComponentInsertion targetAtlas targetOccurrence forward
    (const Nothing) (const ())
""",
}

COALITION_ELEMENT_SOURCE = HASKELL / "src/DatraCore/Atlases/Derived/Coalitions/Coalition/Element/Data.hs"
COALITION_PUBLIC_SOURCE = """
{-# LANGUAGE CPP #-}
#include "LiquidPlugin.h"
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}
{-@ LIQUID "--higherorder" @-}
module PublicCoalitionGuard where
import Coalition.Element
import Atlas (Atlas, atlasPageElements)
import AtlasCoveredPageElement
  ( CoveredPageElement, coveredPageElementValid, coverageWitnessOriginRank
  , atlasCoveredPageElementWitness )
import PageElements (originPageElement)
{-@ predicate PublicCoalitionValid A E = coalitionElementValid A E
      && coalitionElementSource E == originPageElement (atlasPageElements A) @-}
"""

COALITION_CANONICAL_GUARDS = {
    "coalition canonicalization rank equality requires equal ranks": """
{-@ proofGuard :: owner:Atlas a s d o f
      -> left:{CoalitionData a s d | PublicCoalitionValid owner left}
      -> right:{CoalitionData a s d | PublicCoalitionValid owner right}
      -> {left == right} @-}
proofGuard :: Atlas a s d o f -> CoalitionData a s d -> CoalitionData a s d -> ()
proofGuard = coalitionElementRankExtensionality
""",
    "coalition canonicalization round trip preserves the exact record": """
{-@ proofGuard :: owner:Atlas a s d o f
      -> element:{CoalitionData a s d | PublicCoalitionValid owner element}
      -> {coalitionFromCovered owner (coalitionCoveredElement owner element) /= element} @-}
proofGuard :: Atlas a s d o f -> CoalitionData a s d -> ()
proofGuard = coalitionFromCoveredRoundTrip
""",
    "coalition canonicalization requires covered owning validity": """
{-@ proofGuard :: Atlas a s d o f -> CoveredPageElement a s d -> CoalitionData a s d @-}
proofGuard :: Atlas a s d o f -> CoveredPageElement a s d -> CoalitionData a s d
proofGuard = coalitionFromCovered
""",
    "coalition canonicalization retains the witness origin rank": """
{-@ proofGuard :: owner:Atlas a s d o f
      -> covered:{CoveredPageElement a s d | coveredPageElementValid owner covered}
      -> {element:CoalitionData a s d |
           coalitionElementRank element /= coverageWitnessOriginRank (atlasCoveredPageElementWitness covered)} @-}
proofGuard :: Atlas a s d o f -> CoveredPageElement a s d -> CoalitionData a s d
proofGuard = coalitionFromCovered
""",
    "coalition canonicalization retains the canonical origin": """
{-@ proofGuard :: owner:Atlas a s d o f
      -> {covered:CoveredPageElement a s d | coveredPageElementValid owner covered}
      -> {element:CoalitionData a s d |
           coalitionElementSource element /= originPageElement (atlasPageElements owner)} @-}
proofGuard :: Atlas a s d o f -> CoveredPageElement a s d -> CoalitionData a s d
proofGuard = coalitionFromCovered
""",
    "coalition covered conversion requires owning validity": """
{-@ proofGuard :: Atlas a s d o f -> CoalitionData a s d -> CoveredPageElement a s d @-}
proofGuard :: Atlas a s d o f -> CoalitionData a s d -> CoveredPageElement a s d
proofGuard = coalitionCoveredElement
""",
}

COALITION_TRANSPORT_PUBLIC_SOURCE = r"""
{-# LANGUAGE CPP #-}
#include "LiquidPlugin.h"
{-@ LIQUID "--reflection" @-}
module CoalitionTransportPublicGuard where
import Atlas (Atlas, atlasPageElements, mapAtlasData, normalizeAtlasElement)
import AtlasExtent (cellTraceValid)
import Coalition.Element
  ( CoalitionData, coalitionElementAt, coalitionElementReaches, coalitionElementValid
  , coalitionElementSource, coalitionElementAlongArrow, coalitionElementAtNormalized )
import DomanialInsertion.Core (DomanialInsertion (..))
import PageElements (PageElement, originPageElement)
import PageElements.Structure (PageElementArrow, arrowSource, arrowTarget)

{-@ observedTransport :: owner:Atlas a s d o f
      -> arrow:{PageElementArrow s source target |
           cellTraceValid owner (arrowSource arrow) && cellTraceValid owner (arrowTarget arrow)}
      -> element:{CoalitionData a s d | coalitionElementValid owner element
           && coalitionElementSource element == originPageElement (atlasPageElements owner)
           && coalitionElementReaches element (arrowSource arrow)}
      -> {coalitionElementReaches element (arrowTarget arrow)
           && coalitionElementAt owner (arrowTarget arrow) element
             == applyInsertion (mapAtlasData owner arrow)
                  (coalitionElementAt owner (arrowSource arrow) element)} @-}
observedTransport :: Atlas a s d o f -> PageElementArrow s source target -> CoalitionData a s d -> ()
observedTransport = coalitionElementAlongArrow

{-@ observedNormalization :: owner:Atlas a s d o f
      -> target:{PageElement s object | cellTraceValid owner target}
      -> element:{CoalitionData a s d | coalitionElementValid owner element
           && coalitionElementSource element == originPageElement (atlasPageElements owner)
           && coalitionElementReaches element target}
      -> {coalitionElementReaches element (normalizeAtlasElement owner target)
           && coalitionElementAt owner (normalizeAtlasElement owner target) element
                == coalitionElementAt owner target element} @-}
observedNormalization :: Atlas a s d o f -> PageElement s object -> CoalitionData a s d -> ()
observedNormalization = coalitionElementAtNormalized
"""


def coalition_transport_guard(name, old, new):
    contract = "{-@ " + name + COALITION_TRANSPORT_PUBLIC_SOURCE.split("{-@ " + name, 1)[1]
    contract = contract.split("\n{-@ observed", 1)[0]
    assert old in contract
    return contract.replace(old, new, 1).replace(name, "proofGuard").replace(
        "proofGuard = coalitionElementAlongArrow", "proofGuard = observedTransport").replace(
        "proofGuard = coalitionElementAtNormalized", "proofGuard = observedNormalization")


COALITION_TRANSPORT_PUBLIC_GUARDS = {
    "coalition transport retains the Atlas action equation": coalition_transport_guard(
        "observedTransport", "== applyInsertion", "/= applyInsertion"),
    "coalition transport requires valid owning arrow endpoints": coalition_transport_guard(
        "observedTransport",
        "{PageElementArrow s source target |\n"
        "           cellTraceValid owner (arrowSource arrow) && cellTraceValid owner (arrowTarget arrow)}",
        "PageElementArrow s source target"),
    "coalition transport requires reachability of the arrow source": coalition_transport_guard(
        "observedTransport", "&& coalitionElementReaches element (arrowSource arrow)", ""),
    "coalition transport requires an owning valid coalition": coalition_transport_guard(
        "observedTransport", "coalitionElementValid owner element\n           && ", ""),
    "coalition normalization retains the transported datum": coalition_transport_guard(
        "observedNormalization", "== coalitionElementAt owner target element", "/= coalitionElementAt owner target element"),
    "coalition normalization requires a valid owning target": coalition_transport_guard(
        "observedNormalization", "{PageElement s object | cellTraceValid owner target}", "PageElement s object"),
}

COALITION_ACTION_PUBLIC_SOURCE = r"""
{-# LANGUAGE CPP #-}
#include "LiquidPlugin.h"
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}
{-@ LIQUID "--higherorder" @-}
module PublicCoalitionActionGuard where
import Atlas (Atlas, AtlasObject, atlasPageElements)
import AtlasTransversal (AtlasTransversal)
import Coalition.Element
import AtlasCoveredPageElement (CoveredPageElement)
import DomanialInsertion.Core (DomanialInsertion, applyInsertion, preimage)
import PageElements (SomePageElement, originPageElement)
{-@ predicate PublicCoalitionValid A E = coalitionElementValid A E
      && coalitionElementSource E == originPageElement (atlasPageElements A) @-}
discardMappedCoalition :: Atlas a s d o f -> CoalitionData a s d -> ()
discardMappedCoalition _ _ = ()

{-@ observedCoalitionOperation :: owner:Atlas sa ss sd so sf
      -> AtlasTransversal (AtlasObject sa ss sd) (AtlasObject ta ts td)
      -> first:{CoalitionData sa ss sd | PublicCoalitionValid owner first}
      -> second:{CoalitionData sa ss sd | PublicCoalitionValid owner second}
      -> {result:Bool | result} @-}
observedCoalitionOperation :: Atlas sa ss sd so sf
  -> AtlasTransversal (AtlasObject sa ss sd) (AtlasObject ta ts td)
  -> CoalitionData sa ss sd -> CoalitionData sa ss sd -> Bool
observedCoalitionOperation owner arrow first second =
  withMappedCoalitionAction owner arrow (coalitionPairValid owner first second)

{-@ coalitionPairValid :: sourceOwner:Atlas sa ss sd so sf
      -> first:{CoalitionData sa ss sd | PublicCoalitionValid sourceOwner first}
      -> second:{CoalitionData sa ss sd | PublicCoalitionValid sourceOwner second}
      -> targetOwner:Atlas ta ts td to tf
      -> ({source:CoalitionData sa ss sd | PublicCoalitionValid sourceOwner source}
           -> {target:CoalitionData ta ts td | PublicCoalitionValid targetOwner target})
      -> {result:Bool | result} @-}
coalitionPairValid :: Atlas sa ss sd so sf -> CoalitionData sa ss sd -> CoalitionData sa ss sd
  -> Atlas ta ts td to tf -> (CoalitionData sa ss sd -> CoalitionData ta ts td) -> Bool
coalitionPairValid _ first second target forward =
  canonicalOperationSource target (forward first) `seq`
    canonicalOperationSource target (forward second) `seq`
      (coalitionElementValid target (forward first) && coalitionElementValid target (forward second))

{-@ canonicalOperationSource :: owner:Atlas a s d o f
      -> element:{CoalitionData a s d | PublicCoalitionValid owner element}
      -> {source:SomePageElement s | source == originPageElement (atlasPageElements owner)} @-}
canonicalOperationSource :: Atlas a s d o f -> CoalitionData a s d -> SomePageElement s
canonicalOperationSource _ element = coalitionElementSource element

{-@ observedExactCoalitionImage :: owner:Atlas sa ss sd so sf
      -> arrow:AtlasTransversal (AtlasObject sa ss sd) (AtlasObject ta ts td)
      -> source:{CoalitionData sa ss sd | PublicCoalitionValid owner source}
      -> {image:CoalitionData ta ts td | image == mapCoalitionElement owner arrow source} @-}
observedExactCoalitionImage :: Atlas sa ss sd so sf
  -> AtlasTransversal (AtlasObject sa ss sd) (AtlasObject ta ts td)
  -> CoalitionData sa ss sd -> CoalitionData ta ts td
observedExactCoalitionImage owner arrow source =
  withMappedCoalitionElement owner arrow source (\_ image -> image)

{-@ observedExactCoalitionOperation :: owner:Atlas sa ss sd so sf
      -> arrow:AtlasTransversal (AtlasObject sa ss sd) (AtlasObject ta ts td)
      -> source:{CoalitionData sa ss sd | PublicCoalitionValid owner source}
      -> {image:CoalitionData ta ts td | image == mapCoalitionElement owner arrow source} @-}
observedExactCoalitionOperation :: Atlas sa ss sd so sf
  -> AtlasTransversal (AtlasObject sa ss sd) (AtlasObject ta ts td)
  -> CoalitionData sa ss sd -> CoalitionData ta ts td
observedExactCoalitionOperation owner arrow source =
  withMappedCoalitionAction owner arrow (readCoalitionOperation owner arrow source)

{-@ readCoalitionOperation :: owner:Atlas sa ss sd so sf
      -> arrow:AtlasTransversal (AtlasObject sa ss sd) (AtlasObject ta ts td)
      -> source:{CoalitionData sa ss sd | PublicCoalitionValid owner source}
      -> target:Atlas ta ts td to tf
      -> ({value:CoalitionData sa ss sd | PublicCoalitionValid owner value}
           -> {image:CoalitionData ta ts td | PublicCoalitionValid target image
                && image == mapCoalitionElement owner arrow value})
      -> {image:CoalitionData ta ts td | image == mapCoalitionElement owner arrow source} @-}
readCoalitionOperation :: Atlas sa ss sd so sf
  -> AtlasTransversal (AtlasObject sa ss sd) (AtlasObject ta ts td)
  -> CoalitionData sa ss sd -> Atlas ta ts td to tf
  -> (CoalitionData sa ss sd -> CoalitionData ta ts td) -> CoalitionData ta ts td
readCoalitionOperation _ _ source _ forward = forward source

{-@ observedOwnedInsertion :: owner:Atlas sa ss sd so sf
      -> arrow:AtlasTransversal (AtlasObject sa ss sd) (AtlasObject ta ts td)
      -> backward:(CoalitionData ta ts td -> Maybe ({value:CoalitionData sa ss sd | PublicCoalitionValid owner value}))
      -> (value:{CoalitionData sa ss sd | PublicCoalitionValid owner value}
           -> {backward (mapCoalitionElement owner arrow value) == Just value})
      -> {insertion:DomanialInsertion ({value:CoalitionData sa ss sd | PublicCoalitionValid owner value}) (CoalitionData ta ts td) |
           preimage insertion == backward} @-}
observedOwnedInsertion :: Atlas sa ss sd so sf
  -> AtlasTransversal (AtlasObject sa ss sd) (AtlasObject ta ts td)
  -> (CoalitionData ta ts td -> Maybe (CoalitionData sa ss sd))
  -> (CoalitionData sa ss sd -> ())
  -> DomanialInsertion (CoalitionData sa ss sd) (CoalitionData ta ts td)
observedOwnedInsertion owner arrow backward leftInverse =
  withMappedCoalitionAction owner arrow (assembleOwnedInsertion owner arrow backward leftInverse)

{-@ assembleOwnedInsertion :: owner:Atlas sa ss sd so sf
      -> arrow:AtlasTransversal (AtlasObject sa ss sd) (AtlasObject ta ts td)
      -> backward:(CoalitionData ta ts td -> Maybe ({value:CoalitionData sa ss sd | PublicCoalitionValid owner value}))
      -> (value:{CoalitionData sa ss sd | PublicCoalitionValid owner value}
           -> {backward (mapCoalitionElement owner arrow value) == Just value})
      -> target:Atlas ta ts td to tf
      -> forward:({value:CoalitionData sa ss sd | PublicCoalitionValid owner value}
           -> {image:CoalitionData ta ts td | PublicCoalitionValid target image
                && image == mapCoalitionElement owner arrow value})
      -> {insertion:DomanialInsertion ({value:CoalitionData sa ss sd | PublicCoalitionValid owner value}) (CoalitionData ta ts td) |
           preimage insertion == backward} @-}
assembleOwnedInsertion :: Atlas sa ss sd so sf
  -> AtlasTransversal (AtlasObject sa ss sd) (AtlasObject ta ts td)
  -> (CoalitionData ta ts td -> Maybe (CoalitionData sa ss sd)) -> (CoalitionData sa ss sd -> ())
  -> Atlas ta ts td to tf -> (CoalitionData sa ss sd -> CoalitionData ta ts td)
  -> DomanialInsertion (CoalitionData sa ss sd) (CoalitionData ta ts td)
assembleOwnedInsertion owner _ backward leftInverse _ forward =
  coalitionCounitInsertion (coalitionElementValid owner) coalitionElementSource
    (originPageElement (atlasPageElements owner)) forward backward
    (\source -> forward source `seq` leftInverse source)
"""

COALITION_ACTION_PUBLIC_GUARDS = {
    "owned coalition image retains the raw mapper result": r"""
{-@ proofGuard :: owner:Atlas sa ss sd so sf
      -> arrow:AtlasTransversal (AtlasObject sa ss sd) (AtlasObject ta ts td)
      -> source:{CoalitionData sa ss sd | PublicCoalitionValid owner source}
      -> {image:CoalitionData ta ts td | image /= mapCoalitionElement owner arrow source} @-}
proofGuard :: Atlas sa ss sd so sf
  -> AtlasTransversal (AtlasObject sa ss sd) (AtlasObject ta ts td)
  -> CoalitionData sa ss sd -> CoalitionData ta ts td
proofGuard = observedExactCoalitionImage
""",
    "owned coalition operation retains the raw mapper result": r"""
{-@ proofGuard :: owner:Atlas sa ss sd so sf
      -> arrow:AtlasTransversal (AtlasObject sa ss sd) (AtlasObject ta ts td)
      -> source:{CoalitionData sa ss sd | PublicCoalitionValid owner source}
      -> {image:CoalitionData ta ts td | image /= mapCoalitionElement owner arrow source} @-}
proofGuard :: Atlas sa ss sd so sf
  -> AtlasTransversal (AtlasObject sa ss sd) (AtlasObject ta ts td)
  -> CoalitionData sa ss sd -> CoalitionData ta ts td
proofGuard = observedExactCoalitionOperation
""",
    "owned coalition insertion retains the supplied partial inverse": r"""
{-@ proofGuard :: owner:Atlas sa ss sd so sf
      -> arrow:AtlasTransversal (AtlasObject sa ss sd) (AtlasObject ta ts td)
      -> backward:(CoalitionData ta ts td -> Maybe ({value:CoalitionData sa ss sd | PublicCoalitionValid owner value}))
      -> (value:{CoalitionData sa ss sd | PublicCoalitionValid owner value}
           -> {backward (mapCoalitionElement owner arrow value) == Just value})
      -> {insertion:DomanialInsertion ({value:CoalitionData sa ss sd | PublicCoalitionValid owner value}) (CoalitionData ta ts td) |
           preimage insertion /= backward} @-}
proofGuard :: Atlas sa ss sd so sf
  -> AtlasTransversal (AtlasObject sa ss sd) (AtlasObject ta ts td)
  -> (CoalitionData ta ts td -> Maybe (CoalitionData sa ss sd)) -> (CoalitionData sa ss sd -> ())
  -> DomanialInsertion (CoalitionData sa ss sd) (CoalitionData ta ts td)
proofGuard = observedOwnedInsertion
""",
    "owned coalition operation certifies all canonical outputs for one owner": r"""
{-@ proofGuard :: owner:Atlas sa ss sd so sf
      -> AtlasTransversal (AtlasObject sa ss sd) (AtlasObject ta ts td)
      -> first:{CoalitionData sa ss sd | PublicCoalitionValid owner first}
      -> second:{CoalitionData sa ss sd | PublicCoalitionValid owner second}
      -> {result:Bool | not result} @-}
proofGuard :: Atlas sa ss sd so sf
  -> AtlasTransversal (AtlasObject sa ss sd) (AtlasObject ta ts td)
  -> CoalitionData sa ss sd -> CoalitionData sa ss sd -> Bool
proofGuard = observedCoalitionOperation
""",
    "owned coalition operation requires the canonical source domain": r"""
{-@ proofGuard :: owner:Atlas sa ss sd so sf
      -> AtlasTransversal (AtlasObject sa ss sd) (AtlasObject ta ts td)
      -> source:{CoalitionData sa ss sd | coalitionElementValid owner source}
      -> CoalitionData ta ts td @-}
proofGuard :: Atlas sa ss sd so sf
  -> AtlasTransversal (AtlasObject sa ss sd) (AtlasObject ta ts td)
  -> CoalitionData sa ss sd -> CoalitionData ta ts td
proofGuard owner arrow source =
  withMappedCoalitionAction owner arrow (\_ forward -> forward source)
""",
    "raw coalition mapping requires source owning validity": """
proofGuard :: Atlas sa ss sd so sf
  -> AtlasTransversal (AtlasObject sa ss sd) (AtlasObject ta ts td)
  -> CoalitionData sa ss sd -> CoalitionData ta ts td
proofGuard = mapCoalitionElement
""",
    "raw coalition mapping requires the canonical source origin": """
{-@ proofGuard :: owner:Atlas sa ss sd so sf
      -> AtlasTransversal (AtlasObject sa ss sd) (AtlasObject ta ts td)
      -> source:{CoalitionData sa ss sd | coalitionElementValid owner source}
      -> CoalitionData ta ts td @-}
proofGuard :: Atlas sa ss sd so sf
  -> AtlasTransversal (AtlasObject sa ss sd) (AtlasObject ta ts td)
  -> CoalitionData sa ss sd -> CoalitionData ta ts td
proofGuard = mapCoalitionElement
""",
    "owned coalition mapping requires source owning validity": """
proofGuard :: Atlas sa ss sd so sf
  -> AtlasTransversal (AtlasObject sa ss sd) (AtlasObject ta ts td)
  -> CoalitionData sa ss sd -> ()
proofGuard owner arrow source =
  withMappedCoalitionElement owner arrow source discardMappedCoalition
""",
    "owned coalition mapping requires the canonical source origin": """
{-@ proofGuard :: owner:Atlas sa ss sd so sf
      -> AtlasTransversal (AtlasObject sa ss sd) (AtlasObject ta ts td)
      -> source:{CoalitionData sa ss sd | coalitionElementValid owner source} -> () @-}
proofGuard :: Atlas sa ss sd so sf
  -> AtlasTransversal (AtlasObject sa ss sd) (AtlasObject ta ts td)
  -> CoalitionData sa ss sd -> ()
proofGuard owner arrow source =
  withMappedCoalitionElement owner arrow source discardMappedCoalition
""",
    "owned coalition mapping cannot substitute the retained target": """
{-@ proofGuard :: owner:Atlas sa ss sd so sf -> other:Atlas ta ts td to tf
      -> AtlasTransversal (AtlasObject sa ss sd) (AtlasObject ta ts td)
      -> source:{CoalitionData sa ss sd | PublicCoalitionValid owner source}
      -> CoveredPageElement ta ts td @-}
proofGuard :: Atlas sa ss sd so sf -> Atlas ta ts td to tf
  -> AtlasTransversal (AtlasObject sa ss sd) (AtlasObject ta ts td)
  -> CoalitionData sa ss sd -> CoveredPageElement ta ts td
proofGuard owner other arrow source =
  withMappedCoalitionElement owner arrow source (wrongCoalitionOwner other)

{-@ wrongCoalitionOwner :: other:Atlas a s d oo ofinal -> actual:Atlas a s d o f
      -> {element:CoalitionData a s d | PublicCoalitionValid actual element}
      -> CoveredPageElement a s d @-}
wrongCoalitionOwner :: Atlas a s d oo ofinal -> Atlas a s d o f
  -> CoalitionData a s d -> CoveredPageElement a s d
wrongCoalitionOwner other _ element = coalitionCoveredElement other element
""",
}

COALITION_ELEMENT_GUARDS = {
    "coalition transport requires an owning target": """
{-@ proofGuard :: owner:Atlas a s d o f -> target:PageElement s object
      -> element:{CoalitionData a s d | CoalitionValid owner element
           && coalitionElementReaches element target} -> d object @-}
proofGuard :: Atlas a s d o f -> PageElement s object -> CoalitionData a s d -> d object
proofGuard = coalitionElementAt
""",
    "coalition transport requires an actual arrow": """
{-@ proofGuard :: owner:Atlas a s d o f
      -> target:{PageElement s object | cellTraceValid owner target}
      -> {element:CoalitionData a s d | CoalitionValid owner element} -> d object @-}
proofGuard :: Atlas a s d o f -> PageElement s object -> CoalitionData a s d -> d object
proofGuard = coalitionElementAt
""",
    "coalition transport preserves the stored origin rank": """
{-@ proofGuard :: owner:Atlas a s d o f
      -> target:{PageElement s object | cellTraceValid owner target}
      -> element:{CoalitionData a s d | CoalitionValid owner element
           && coalitionElementReaches element target}
      -> {datum:d object | atlasOriginImageRank owner target datum /= coalitionElementRank element} @-}
proofGuard :: Atlas a s d o f -> PageElement s object -> CoalitionData a s d -> d object
proofGuard = coalitionElementAt
""",
    "coalition transport retains coverage of its exact datum": """
{-@ proofGuard :: owner:Atlas a s d o f
      -> target:{PageElement s object | cellTraceValid owner target}
      -> element:{CoalitionData a s d | CoalitionValid owner element
           && coalitionElementReaches element target}
      -> {witness:CoverageWitness a s d |
           not (coverageWitnessCovers owner target (coalitionElementAt owner target element) witness)} @-}
proofGuard :: Atlas a s d o f -> PageElement s object -> CoalitionData a s d -> CoverageWitness a s d
proofGuard = coalitionElementCoverageAt
""",
    "coalition dominion requires its owning validity": """
{-@ proofGuard :: Atlas a s d o f -> CoalitionData a s d -> Natural @-}
proofGuard :: Atlas a s d o f -> CoalitionData a s d -> Natural
proofGuard owner = rank (coalition owner)
""",
    "coalition dominion requires its canonical origin": """
{-@ proofGuard :: owner:Atlas a s d o f
      -> {element:CoalitionData a s d | coalitionElementValid owner element} -> Natural @-}
proofGuard :: Atlas a s d o f -> CoalitionData a s d -> Natural
proofGuard owner = rank (coalition owner)
""",
    "coalition dominion recovers the exact stored record": """
{-@ proofGuard :: owner:Atlas a s d o f
      -> element:{CoalitionData a s d | CoalitionValid owner element}
      -> {result:Maybe (CoalitionData a s d) | result /= Just element} @-}
proofGuard :: Atlas a s d o f -> CoalitionData a s d -> Maybe (CoalitionData a s d)
proofGuard owner element = coalitionRankRoundTrip owner element `seq`
  unrank (coalition owner) (rank (coalition owner) element)
""",
    "coalition finite decoding retains its owning validity": """
{-@ proofGuard :: owner:Atlas a s d o f -> Natural
      -> Maybe ({element:CoalitionData a s d | not (coalitionElementValid owner element)}) @-}
proofGuard :: Atlas a s d o f -> Natural -> Maybe (CoalitionData a s d)
proofGuard = coalitionUnrank
""",
    "coalition finite decoding retains its canonical origin": """
{-@ proofGuard :: owner:Atlas a s d o f -> Natural
      -> Maybe ({element:CoalitionData a s d |
           coalitionElementSource element /= originPageElement (atlasPageElements owner)}) @-}
proofGuard :: Atlas a s d o f -> Natural -> Maybe (CoalitionData a s d)
proofGuard = coalitionUnrank
""",
    "coalition finite decoding can reject a candidate": """
{-@ proofGuard :: Atlas a s d o f -> Natural
      -> {result:Maybe (CoalitionData a s d) | result /= Nothing} @-}
proofGuard :: Atlas a s d o f -> Natural -> Maybe (CoalitionData a s d)
proofGuard = coalitionUnrank
""",
    "coalition extensionality requires equal dependent views": """
{-@ proofGuard :: owner:Atlas a s d o f
      -> left:{CoalitionData a s d | CoalitionValid owner left}
      -> right:{CoalitionData a s d | CoalitionValid owner right}
      -> {left == right} @-}
proofGuard :: Atlas a s d o f -> CoalitionData a s d -> CoalitionData a s d -> ()
proofGuard = coalitionElementExtensionality
""",
    "coalition constructor view preserves its dependent payload": """
{-@ proofGuard :: owner:Atlas a s d o f
      -> source:{PageElement s object | cellTraceValid owner source
           && SomePageElement source == originPageElement (atlasPageElements owner)}
      -> datum:{d object | atlasAcceptsDatum owner source datum}
      -> witness:{CoverageWitness a s d | coverageWitnessCovers owner source datum witness}
      -> {viewCoalitionElement (coalitionElement owner source datum witness) /= CoalitionView source datum} @-}
proofGuard :: Atlas a s d o f -> PageElement s object -> d object -> CoverageWitness a s d -> ()
proofGuard = coalitionElementView
""",
    "canonical coalition reconstruction preserves the stored carrier": """
{-@ proofGuard :: owner:Atlas a s d o f
      -> element:{CoalitionData a s d | CoalitionValid owner element}
      -> {result:CoalitionData a s d | result /= element} @-}
proofGuard :: Atlas a s d o f -> CoalitionData a s d -> CoalitionData a s d
proofGuard owner element =
  withCoalitionElementOf owner element (\\source datum witness -> coalitionElement owner source datum witness)
""",
    "canonical coalition construction is independent of its witness": """
{-@ proofGuard :: owner:Atlas a s d o f
      -> source:{PageElement s object | cellTraceValid owner source
           && SomePageElement source == originPageElement (atlasPageElements owner)}
      -> datum:{d object | atlasAcceptsDatum owner source datum}
      -> first:{CoverageWitness a s d | coverageWitnessCovers owner source datum first}
      -> second:{CoverageWitness a s d | coverageWitnessCovers owner source datum second}
      -> {coalitionElement owner source datum first /= coalitionElement owner source datum second} @-}
proofGuard :: Atlas a s d o f -> PageElement s object -> d object
  -> CoverageWitness a s d -> CoverageWitness a s d -> ()
proofGuard = coalitionElementWitnessIndependent
""",
    "certified coalition elimination requires its owning validity": """
proofGuard :: Atlas a s d o f -> CoalitionData a s d -> Bool
proofGuard owner element =
  withCoalitionElementOf owner element (\\_ _ _ -> True)
""",
    "certified coalition elimination retains the cached rank": """
{-@ proofGuard :: owner:Atlas a s d o f
      -> element:{CoalitionData a s d | CoalitionValid owner element}
      -> {result:Bool | not result} @-}
proofGuard :: Atlas a s d o f -> CoalitionData a s d -> Bool
proofGuard owner element =
  withCoalitionElementOf owner element
    (\\_ _ witness -> coverageWitnessOriginRank witness == coalitionElementRank element)
""",
    "certified coalition elimination retains the canonical origin": """
{-@ proofGuard :: owner:Atlas a s d o f
      -> element:{CoalitionData a s d | CoalitionValid owner element}
      -> {source:SomePageElement s | source /= originPageElement (atlasPageElements owner)} @-}
proofGuard :: Atlas a s d o f -> CoalitionData a s d -> SomePageElement s
proofGuard owner element =
  withCoalitionElementOf owner element (\\source _ _ -> SomePageElement source)
""",
    "public coalition elimination preserves its constructor payload": """
{-@ proofGuard :: owner:Atlas a s d o f
      -> source:{PageElement s object | cellTraceValid owner source
           && SomePageElement source == originPageElement (atlasPageElements owner)}
      -> datum:{d object | atlasAcceptsDatum owner source datum}
      -> witness:{CoverageWitness a s d | coverageWitnessCovers owner source datum witness}
      -> useElement:(forall other. PageElement s other -> d other -> result)
      -> {withCoalitionElement (coalitionElement owner source datum witness) useElement
           /= useElement source datum} @-}
proofGuard :: Atlas a s d o f -> PageElement s object -> d object -> CoverageWitness a s d
  -> (forall other. PageElement s other -> d other -> result) -> ()
proofGuard = coalitionElementEliminate
""",
    "public coalitions require coverage of the exact origin datum": """
{-@ proofGuard :: owner:Atlas a s d o f
      -> origin:{PageElement s object | cellTraceValid owner origin
           && SomePageElement origin == originPageElement (atlasPageElements owner)}
      -> datum:{d object | atlasAcceptsDatum owner origin datum}
      -> CoverageWitness a s d
      -> CoalitionData a s d @-}
proofGuard :: Atlas a s d o f -> PageElement s object -> d object
  -> CoverageWitness a s d -> CoalitionData a s d
proofGuard = coalitionElement
""",
    "public coalitions reject a covered cell without origin evidence": """
{-@ proofGuard :: owner:Atlas a s d o f
      -> source:{PageElement s object | cellTraceValid owner source}
      -> datum:{d object | atlasAcceptsDatum owner source datum}
      -> witness:{CoverageWitness a s d |
           coverageWitnessCovers owner source datum witness}
      -> CoalitionData a s d @-}
proofGuard :: Atlas a s d o f -> PageElement s object -> d object
  -> CoverageWitness a s d -> CoalitionData a s d
proofGuard = coalitionElement
""",
}


TRANSVERSAL_SOURCE = HASKELL / "src/DatraCore/Atlases/Derived/AtlasTransposals/AtlasTransversal/Internal.hs"
TRANSVERSAL_GUARDS = {
    "stored transversal operations require coverage for their retained owner": """
proofGuard :: Atlas a s d o f -> (source -> CoveredPageElement a s d) -> CoveredActionData source a s d o f
proofGuard = CoveredActionData
""",
    "primitive transversal mapping cannot substitute its target owner": """
{-@ proofGuard :: action:TransversalAction sa ss sd so sf ta ts td to tf
      -> other:Atlas ta ts td to tf -> covered:CoveredPageElement sa ss sd
      -> {result:CoveredPageElement ta ts td | coveredPageElementValid other result} @-}
proofGuard :: TransversalAction sa ss sd so sf ta ts td to tf
  -> Atlas ta ts td to tf -> CoveredPageElement sa ss sd -> CoveredPageElement ta ts td
proofGuard action _ covered = mapTransversalAction action covered
""",
    "primitive transversal mapping cannot substitute its coverage witness": """
{-@ proofGuard :: action:TransversalAction sa ss sd so sf ta ts td to tf
      -> other:CoverageWitness ta ts td -> covered:CoveredPageElement sa ss sd
      -> {result:CoveredPageElement ta ts td | atlasCoveredPageElementWitness result == other} @-}
proofGuard :: TransversalAction sa ss sd so sf ta ts td to tf
  -> CoverageWitness ta ts td -> CoveredPageElement sa ss sd -> CoveredPageElement ta ts td
proofGuard action _ covered = mapTransversalAction action covered
""",
    "stored transversal actions reject coverage evidence for the wrong image": """
{-@ proofGuard
      :: sourceAtlas:Atlas sa ss sd so sf -> targetAtlas:Atlas ta ts td to tf
      -> ordered:OrderedAtlasTransposal (AtlasObject sa ss sd) (AtlasObject ta ts td)
      -> badCoverage:(covered:CoveredPageElement sa ss sd
           -> {w:CoverageWitness ta ts td |
                not (transversalImageCovered sourceAtlas targetAtlas ordered covered w)})
      -> TransversalAction sa ss sd so sf ta ts td to tf @-}
proofGuard :: Atlas sa ss sd so sf -> Atlas ta ts td to tf
  -> OrderedAtlasTransposal (AtlasObject sa ss sd) (AtlasObject ta ts td)
  -> (CoveredPageElement sa ss sd -> CoverageWitness ta ts td)
  -> TransversalAction sa ss sd so sf ta ts td to tf
proofGuard = TransversalAction
""",
    "transversals reject coverage evidence for the wrong image": """
{-@
proofGuard
  :: sourceAtlas:Atlas sa ss sd so sf
  -> targetAtlas:Atlas ta ts td to tf
  -> ordered:OrderedAtlasTransposal (AtlasObject sa ss sd) (AtlasObject ta ts td)
  -> badCoverage:(covered:CoveredPageElement sa ss sd
       -> {w:CoverageWitness ta ts td |
         not (transversalImageCovered sourceAtlas targetAtlas ordered covered w)})
  -> AtlasTransversal (AtlasObject sa ss sd) (AtlasObject ta ts td)
@-}
proofGuard
  :: Atlas sa ss sd so sf
  -> Atlas ta ts td to tf
  -> OrderedAtlasTransposal (AtlasObject sa ss sd) (AtlasObject ta ts td)
  -> (CoveredPageElement sa ss sd
       -> CoverageWitness ta ts td)
  -> AtlasTransversal (AtlasObject sa ss sd) (AtlasObject ta ts td)
proofGuard sourceAtlas targetAtlas ordered badCoverage =
  atlasTransversal sourceAtlas targetAtlas ordered badCoverage
""",
}

TRANSVERSAL_PUBLIC_SOURCE = r"""
{-# LANGUAGE CPP #-}
#include "LiquidPlugin.h"
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}
{-@ LIQUID "--higherorder" @-}
module PublicTransversalGuard where
import Atlas (Atlas, AtlasObject)
import AtlasTransversal (AtlasTransversal, withAtlasTransversalCoveredImage, withAtlasTransversalCoveredAction)
import AtlasCoveredPageElement (CoveredPageElement, coveredPageElementValid)
import Coalition.Element (CoalitionData, coalitionFromCovered)

{-@ observedCoveredOperation :: owner:Atlas sa ss sd so sf
      -> AtlasTransversal (AtlasObject sa ss sd) (AtlasObject ta ts td)
      -> first:{CoveredPageElement sa ss sd | coveredPageElementValid owner first}
      -> second:{CoveredPageElement sa ss sd | coveredPageElementValid owner second}
      -> {result:Bool | result} @-}
observedCoveredOperation :: Atlas sa ss sd so sf
  -> AtlasTransversal (AtlasObject sa ss sd) (AtlasObject ta ts td)
  -> CoveredPageElement sa ss sd -> CoveredPageElement sa ss sd -> Bool
observedCoveredOperation owner arrow first second =
  withAtlasTransversalCoveredAction owner arrow (coveredPairValid owner first second)

{-@ coveredPairValid :: sourceOwner:Atlas sa ss sd so sf
      -> first:{CoveredPageElement sa ss sd | coveredPageElementValid sourceOwner first}
      -> second:{CoveredPageElement sa ss sd | coveredPageElementValid sourceOwner second}
      -> targetOwner:Atlas ta ts td to tf
      -> ({source:CoveredPageElement sa ss sd | coveredPageElementValid sourceOwner source}
           -> {target:CoveredPageElement ta ts td | coveredPageElementValid targetOwner target})
      -> {result:Bool | result} @-}
coveredPairValid :: Atlas sa ss sd so sf -> CoveredPageElement sa ss sd -> CoveredPageElement sa ss sd
  -> Atlas ta ts td to tf -> (CoveredPageElement sa ss sd -> CoveredPageElement ta ts td) -> Bool
coveredPairValid _ first second target forward =
  coveredPageElementValid target (forward first) && coveredPageElementValid target (forward second)
"""

TRANSVERSAL_PUBLIC_GUARDS = {
    "owned transversal operation certifies all outputs for one owner": r"""
{-@ proofGuard :: owner:Atlas sa ss sd so sf
      -> AtlasTransversal (AtlasObject sa ss sd) (AtlasObject ta ts td)
      -> first:{CoveredPageElement sa ss sd | coveredPageElementValid owner first}
      -> second:{CoveredPageElement sa ss sd | coveredPageElementValid owner second}
      -> {result:Bool | not result} @-}
proofGuard :: Atlas sa ss sd so sf
  -> AtlasTransversal (AtlasObject sa ss sd) (AtlasObject ta ts td)
  -> CoveredPageElement sa ss sd -> CoveredPageElement sa ss sd -> Bool
proofGuard = observedCoveredOperation
""",
    "owned transversal operation requires accepted inputs": r"""
proofGuard :: Atlas sa ss sd so sf
  -> AtlasTransversal (AtlasObject sa ss sd) (AtlasObject ta ts td)
  -> CoveredPageElement sa ss sd -> CoveredPageElement ta ts td
proofGuard owner arrow source =
  withAtlasTransversalCoveredAction owner arrow (\_ forward -> forward source)
""",
    "owned transversal elimination requires source owning validity": """
proofGuard :: Atlas sa ss sd so sf
  -> AtlasTransversal (AtlasObject sa ss sd) (AtlasObject ta ts td)
  -> CoveredPageElement sa ss sd -> CoalitionData ta ts td
proofGuard owner arrow source =
  withAtlasTransversalCoveredImage owner arrow source coalitionFromCovered
""",
    "owned transversal elimination cannot replace the certified target": """
{-@ proofGuard :: owner:Atlas sa ss sd so sf -> other:Atlas ta ts td to tf
      -> AtlasTransversal (AtlasObject sa ss sd) (AtlasObject ta ts td)
      -> source:{CoveredPageElement sa ss sd | coveredPageElementValid owner source}
      -> CoalitionData ta ts td @-}
proofGuard :: Atlas sa ss sd so sf -> Atlas ta ts td to tf
  -> AtlasTransversal (AtlasObject sa ss sd) (AtlasObject ta ts td)
  -> CoveredPageElement sa ss sd -> CoalitionData ta ts td
proofGuard owner other arrow source =
  withAtlasTransversalCoveredImage owner arrow source (wrongOwnerCanonical other)

{-@ wrongOwnerCanonical :: other:Atlas a s d oo ofinal -> actual:Atlas a s d o f
      -> {image:CoveredPageElement a s d | coveredPageElementValid actual image}
      -> CoalitionData a s d @-}
wrongOwnerCanonical :: Atlas a s d oo ofinal -> Atlas a s d o f
  -> CoveredPageElement a s d -> CoalitionData a s d
wrongOwnerCanonical other _ image = coalitionFromCovered other image
""",
}

COVERAGE_PUBLIC_SOURCE = HASKELL / "src/DatraCore/Atlases/Derived/AtlasDerived/AtlasCoveredPageElement/AtlasCoveredPageElement.hs"
COVERAGE_PUBLIC_GUARDS = {
    "public coverage transport requires valid cells and an accepted datum": """
{-@ proofGuard :: owner:Atlas a s d o f -> PageElementArrow s source target -> d source -> Natural -> () @-}
proofGuard :: Atlas a s d o f -> PageElementArrow s source target -> d source -> Natural -> ()
proofGuard = coverageRankAlongArrow
""",
    "public coverage transport cannot shift the preserved code": """
{-@ proofGuard :: owner:Atlas a s d o f
      -> arrow:{PageElementArrow s source target |
           cellTraceValid owner (arrowSource arrow) && cellTraceValid owner (arrowTarget arrow)}
      -> datum:{d source | atlasAcceptsDatum owner (arrowSource arrow) datum}
      -> candidate:Natural
      -> {coverageRankCandidate owner (arrowSource arrow) datum candidate
           == coverageRankCandidate owner (arrowTarget arrow) (applyInsertion (mapAtlasData owner arrow) datum) (candidate + 1)} @-}
proofGuard :: Atlas a s d o f -> PageElementArrow s source target -> d source -> Natural -> ()
proofGuard = coverageRankAlongArrow
""",
}

COVERAGE_REPRESENTATION_SOURCE = HASKELL / "src/DatraCore/Atlases/Derived/AtlasDerived/AtlasCoveredPageElement/Internal.hs"
COVERAGE_REPRESENTATION_GUARDS = {
    "coverage code transport requires equal origin images": """
{-@ proofGuard :: owner:Atlas a s d o f
      -> source:{PageElement s sourceObject | cellTraceValid owner source}
      -> datum:{d sourceObject | atlasAcceptsDatum owner source datum}
      -> target:{PageElement s targetObject | cellTraceValid owner target}
      -> targetDatum:{d targetObject | atlasAcceptsDatum owner target targetDatum}
      -> candidate:Natural
      -> {coverageRankCanonical owner source datum candidate == coverageRankCanonical owner target targetDatum candidate} @-}
proofGuard :: Atlas a s d o f -> PageElement s sourceObject -> d sourceObject
  -> PageElement s targetObject -> d targetObject -> Natural -> ()
proofGuard = coverageRankCanonicalSameOrigin
""",

    "rank witness recovery requires a certified successful index": """
{-@ proofGuard :: owner:Atlas a s d o f
      -> source:{PageElement s object | cellTraceValid owner source}
      -> datum:{d object | atlasAcceptsDatum owner source datum} -> Natural
      -> {result:Maybe (CoverageWitness a s d) | result /= Nothing} @-}
proofGuard :: Atlas a s d o f -> PageElement s object -> d object -> Natural -> Maybe (CoverageWitness a s d)
proofGuard = coverageRankWitness
""",

    "coverage witness bounds require coverage of the requested datum": """
{-@ proofGuard :: owner:Atlas a s d o f
      -> source:{PageElement s object | cellTraceValid owner source}
      -> datum:{d object | atlasAcceptsDatum owner source datum}
      -> witness:{CoverageWitness a s d | coverageWitnessValid owner witness}
      -> {candidate:Natural | coverageRankCandidate owner source datum candidate} @-}
proofGuard :: Atlas a s d o f -> PageElement s object -> d object -> CoverageWitness a s d -> Natural
proofGuard = coverageWitnessBound
""",
    "witness-bounded ranking requires coverage of the requested datum": """
{-@ proofGuard :: owner:Atlas a s d o f
      -> source:{PageElement s object | cellTraceValid owner source}
      -> datum:{d object | atlasAcceptsDatum owner source datum}
      -> CoverageWitness a s d -> Natural @-}
proofGuard :: Atlas a s d o f -> PageElement s object -> d object -> CoverageWitness a s d -> Natural
proofGuard = atlasCoverageRank
""",

    "region decoding requires the exact source origin image": """
{-@ proofGuard :: owner:Atlas a s d o f
      -> source:{PageElement s object | cellTraceValid owner source}
      -> datum:{d object | atlasAcceptsDatum owner source datum}
      -> region:{PageElement s other | cellTraceValid owner region
           && coveragePage region == coverageFinalPage owner}
      -> regionDatum:{d other | atlasAcceptsDatum owner region regionDatum}
      -> {coverageDecodedDatum
           (coverageAtRegion owner source (rank (atlasDataAt owner region) regionDatum) region) == Just datum} @-}
proofGuard :: Atlas a s d o f -> PageElement s object -> d object
  -> PageElement s other -> d other -> ()
proofGuard = coverageAtRegionInverse
""",
    "region decoding rejects shifting the encoded datum rank": """
{-@ proofGuard :: owner:Atlas a s d o f
      -> source:{PageElement s object | cellTraceValid owner source}
      -> datum:{d object | atlasAcceptsDatum owner source datum}
      -> region:{PageElement s other | cellTraceValid owner region
           && coveragePage region == coverageFinalPage owner}
      -> regionDatum:{d other | atlasAcceptsDatum owner region regionDatum
           && atlasOriginImageRank owner region regionDatum == atlasOriginImageRank owner source datum}
      -> {coverageDecodedDatum
           (coverageAtRegion owner source (rank (atlasDataAt owner region) regionDatum + 1) region) == Just datum} @-}
proofGuard :: Atlas a s d o f -> PageElement s object -> d object
  -> PageElement s other -> d other -> ()
proofGuard = coverageAtRegionInverse
""",
    "bounded coverage ranking rejects a result beyond its limit": """
{-@ proofGuard :: owner:Atlas a s d o f
      -> source:{PageElement s object | cellTraceValid owner source}
      -> datum:{d object | atlasAcceptsDatum owner source datum} -> limit:Natural
      -> Maybe ({found:Natural | found > limit}) @-}
proofGuard :: Atlas a s d o f -> PageElement s object -> d object -> Natural -> Maybe Natural
proofGuard = atlasCoverageRankWithin
""",
    "bounded coverage minimality requires a successful selected rank": """
{-@ proofGuard :: owner:Atlas a s d o f
      -> source:{PageElement s object | cellTraceValid owner source}
      -> datum:{d object | atlasAcceptsDatum owner source datum} -> limit:Natural
      -> found:Natural -> earlier:{Natural | earlier < found}
      -> {not (coverageRankCandidate owner source datum earlier)} @-}
proofGuard :: Atlas a s d o f -> PageElement s object -> d object
  -> Natural -> Natural -> Natural -> ()
proofGuard = atlasCoverageRankLeast
""",
    "coverage witnesses reject matching caches on a nonfinal region": """
{-@ proofGuard :: owner:Atlas a s d o f
      -> source:{PageElement s object | cellTraceValid owner source}
      -> datum:{d object | atlasAcceptsDatum owner source datum}
      -> region:{PageElement s other | cellTraceValid owner region
           && coveragePage region /= coverageFinalPage owner}
      -> regionDatum:{d other | atlasAcceptsDatum owner region regionDatum}
      -> {w:CoverageWitness a s d |
           coverageWitnessCovers owner source datum w} @-}
proofGuard :: Atlas a s d o f -> PageElement s object -> d object
  -> PageElement s other -> d other -> CoverageWitness a s d
proofGuard owner source datum region regionDatum =
  AtlasCoverageWitness (CoverageRegionData region regionDatum
    (coverageFinalPage owner) (atlasOriginImageRank owner source datum))
""",
}

COVERED_API_SOURCE = HASKELL / "src/DatraCore/Atlases/Derived/AtlasDerived/AtlasCoveredPageElement/AtlasCoveredPageElement.hs"
COVERED_API_GUARDS = {
    "certified covered elimination retains the exact witness": """
{-@ proofGuard :: owner:Atlas a s d o f
      -> element:{CoveredPageElement a s d | coveredPageElementValid owner element}
      -> {witness:CoverageWitness a s d | witness /= atlasCoveredPageElementWitness element} @-}
proofGuard :: Atlas a s d o f -> CoveredPageElement a s d -> CoverageWitness a s d
proofGuard owner element =
  withAtlasCoveredPageElementOf owner element (\\_ _ witness -> witness)
""",
    "certified covered elimination requires its owning validity": """
proofGuard :: Atlas a s d o f -> CoveredPageElement a s d -> Bool
proofGuard owner element =
  withAtlasCoveredPageElementOf owner element (\\_ _ _ -> True)
""",
    "covered decoding retains the owning payload validity": """
{-@ proofGuard :: owner:Atlas a s d o f
      -> source:{PageElement s object | cellTraceValid owner source} -> Natural
      -> Maybe ({element:CoveredPageElement a s d | not (coveredPageElementValid owner element)}) @-}
proofGuard :: Atlas a s d o f -> PageElement s object -> Natural
  -> Maybe (CoveredPageElement a s d)
proofGuard = atlasCoveredAt
""",
    "coverage elimination rejects an invalid retained region": """
{-@ proofGuard :: owner:Atlas a s d o f
      -> witness:{CoverageWitness a s d | not (coverageWitnessValid owner witness)}
      -> () @-}
proofGuard :: Atlas a s d o f -> CoverageWitness a s d -> ()
proofGuard owner witness = withAtlasCoverageWitness owner witness (\\_ _ -> ())
""",
    "coverage decoding rejects attaching its witness to another source": """
{-@ proofGuard :: owner:Atlas a s d o f
      -> source:{PageElement s object | cellTraceValid owner source}
      -> other:PageElement s object -> Natural
      -> Maybe (AtlasCoveredPageElement (AtlasObject a s d)) @-}
proofGuard :: Atlas a s d o f -> PageElement s object -> PageElement s object -> Natural
  -> Maybe (AtlasCoveredPageElement (AtlasObject a s d))
proofGuard owner source other candidate =
  case atlasCoverageAt owner source candidate of
    Nothing -> Nothing
    Just (datum, witness) -> Just (atlasCoveredByWitness owner other datum witness)
""",
    "covered-element packaging rejects unrelated coverage evidence": """
{-@ proofGuard :: owner:Atlas a s d o f -> source:PageElement s object -> datum:d object
      -> witness:{CoverageWitness a s d |
           not (coverageWitnessCovers owner source datum witness)}
      -> AtlasCoveredPageElement (AtlasObject a s d) @-}
proofGuard :: Atlas a s d o f -> PageElement s object -> d object
  -> CoverageWitness a s d -> AtlasCoveredPageElement (AtlasObject a s d)
proofGuard = atlasCoveredByWitness
""",
}


ATLAS_MAP_SOURCE = HASKELL / "src/DatraCore/Atlases/Derived/Cartography/AtlasMap/Internal.hs"
ATLAS_MAP_API_SOURCE = HASKELL / "src/DatraCore/Atlases/Derived/Cartography/AtlasMap/AtlasMap.hs"
ATLAS_MAP_API_GUARDS = {
    "public Atlas map construction rejects unrelated coverage": """
{-@ proofGuard :: owner:Atlas a s d o f -> CoverageWitness a s d -> AtlasMap (AtlasObject a s d) @-}
proofGuard :: Atlas a s d o f -> CoverageWitness a s d -> AtlasMap (AtlasObject a s d)
proofGuard owner witness = atlasMap owner (\\_ _ -> witness)
""",
}

ATLAS_MAP_GUARDS = {
    "stored Atlas maps reject coverage for a different extent datum": """
{-@ proofGuard :: owner:Atlas a s d o f
      -> source:{PageElement s extent | cellTraceValid owner source
           && SomePageElement source == originPageElement (atlasPageElements owner)}
      -> wrong:(datum:{d extent | atlasAcceptsDatum owner source datum}
           -> {w:CoverageWitness a s d |
                not (coverageWitnessCovers owner source datum w)})
      -> AtlasMapData a s d o f extent @-}
proofGuard :: Atlas a s d o f -> PageElement s extent
  -> (d extent -> CoverageWitness a s d) -> AtlasMapData a s d o f extent
proofGuard = AtlasMapData
""",
    "stored Atlas maps reject a nonorigin extent": """
{-@ proofGuard :: owner:Atlas a s d o f
      -> source:{PageElement s extent | cellTraceValid owner source
           && SomePageElement source /= originPageElement (atlasPageElements owner)}
      -> covers:(datum:{d extent | atlasAcceptsDatum owner source datum}
           -> {w:CoverageWitness a s d |
                coverageWitnessCovers owner source datum w})
      -> AtlasMapData a s d o f extent @-}
proofGuard :: Atlas a s d o f -> PageElement s extent
  -> (d extent -> CoverageWitness a s d) -> AtlasMapData a s d o f extent
proofGuard = AtlasMapData
""",
    "Atlas map coverage rejects data outside the source carrier": """
{-@ proofGuard :: value:AtlasMap (AtlasObject a s d)
      -> source:{PageElement s cell | atlasMapCellValid value source}
      -> datum:{d cell | not (atlasMapAcceptsDatum value source datum)}
      -> CoverageWitness a s d @-}
proofGuard :: AtlasMap (AtlasObject a s d) -> PageElement s cell -> d cell
  -> CoverageWitness a s d
proofGuard = atlasMapCoversDatum
""",
}


CHARTER_PRESENTATION_SOURCE = HASKELL / "src/DatraCore/Atlases/Derived/Cartography/Charter/LiquidInternal.hs"
CHARTER_PRESENTATION_GUARDS = {
    "Charter presentation construction rejects dummy normalized laws": """
{-@ proofGuard :: owner:Atlas a s d o f -> AtlasPresentation s (ChartedDatum a s d) o f @-}
proofGuard :: Atlas a s d o f -> AtlasPresentation s (ChartedDatum a s d) o f
proofGuard owner =
  atlasPresentationForPredicate (atlasPagination owner) (chartedDatumValid owner) (chartedAction owner)
    (\\_ _ -> ()) (\\_ _ _ _ -> ()) (\\_ _ _ _ -> ()) (\\_ _ _ _ _ _ _ -> ())
""",
    "Charter presentation retains the owning pagination": """
{-@ proofGuard :: owner:Atlas a s d o f
      -> other:{AtlasPresentation s (ChartedDatum a s d) o f |
           atlasPresentationPagination other /= atlasPagination owner}
      -> {result:AtlasPresentation s (ChartedDatum a s d) o f |
           atlasPresentationPagination result == atlasPresentationPagination other} @-}
proofGuard :: Atlas a s d o f -> AtlasPresentation s (ChartedDatum a s d) o f
  -> AtlasPresentation s (ChartedDatum a s d) o f
proofGuard owner _ = chartedPresentation owner
""",
    "Charter presentation retains the certified cached action": """
{-@ proofGuard :: owner:Atlas a s d o f
      -> other:{AtlasPresentation s (ChartedDatum a s d) o f |
           atlasPresentationAction other /= chartedAction owner}
      -> {result:AtlasPresentation s (ChartedDatum a s d) o f |
           atlasPresentationAction result == atlasPresentationAction other} @-}
proofGuard :: Atlas a s d o f -> AtlasPresentation s (ChartedDatum a s d) o f
  -> AtlasPresentation s (ChartedDatum a s d) o f
proofGuard owner _ = chartedPresentation owner
""",
}

CHARTER_SOURCE = HASKELL / "src/DatraCore/Atlases/Derived/Cartography/Charter/Data.hs"
CHARTER_GUARDS = {
    "charted action lookup rejects a noncanonical carrier": """
{-@ proofGuard :: owner:Atlas a s d o f
      -> source:{PageElement s object | cellTraceValid owner source}
      -> value:{ChartedDatum a s d object | not (chartedDatumValid owner source value)} -> Natural @-}
proofGuard :: Atlas a s d o f -> PageElement s object -> ChartedDatum a s d object -> Natural
proofGuard owner source value = rank (atlasActionDataAt (chartedAction owner) source) value
""",
    "normalized charter composition requires matching intermediate cells": """
{-@ proofGuard :: owner:Atlas a s d o f
      -> second:{PageElementArrow s middle target |
           cellTraceValid owner (arrowSource second) && cellTraceValid owner (arrowTarget second)}
      -> first:{PageElementArrow s source middle |
           cellTraceValid owner (arrowSource first) && cellTraceValid owner (arrowTarget first)
           && arrowTarget first /= arrowSource second}
      -> value:{ChartedDatum a s d source |
           chartedDatumValid owner (Elements.normalizePageElement (atlasPageElements owner) (arrowSource first)) value}
      -> () @-}
proofGuard :: Atlas a s d o f -> PageElementArrow s middle target -> PageElementArrow s source middle
  -> ChartedDatum a s d source -> ()
proofGuard owner second first value = chartedNormalizedCompositionLaw owner second first () value
""",

    "charted normalization cannot admit an invalid cached datum": """
{-@ proofGuard :: owner:Atlas a s d o f
      -> source:{PageElement s object | cellTraceValid owner source}
      -> value:{ChartedDatum a s d object | not (chartedDatumValid owner source value)}
      -> {chartedDatumValid owner (normalizeAtlasElement owner source) value} @-}
proofGuard :: Atlas a s d o f -> PageElement s object -> ChartedDatum a s d object -> ()
proofGuard = chartedDatumValidNormalized
""",

    "charted identity rejects a noncanonical carrier": """
{-@ proofGuard :: owner:Atlas a s d o f
      -> occurrence:{PageElement s object | cellTraceValid owner occurrence}
      -> value:{ChartedDatum a s d object |
           atlasAcceptsDatum owner occurrence (chartedCellDataValue value)
           && not (coverageRankCanonical owner occurrence (chartedCellDataValue value) (chartedCellDataRank value))}
      -> {chartedDataMap owner (identityPageElementArrow occurrence) value == value} @-}
proofGuard :: Atlas a s d o f -> PageElement s object -> ChartedDatum a s d object -> ()
proofGuard = chartedIdentityLaw
""",
    "charted composition requires matching intermediate cells": """
{-@ proofGuard :: owner:Atlas a s d o f
      -> second:{PageElementArrow s middle target |
           cellTraceValid owner (arrowSource second) && cellTraceValid owner (arrowTarget second)}
      -> first:{PageElementArrow s source middle |
           cellTraceValid owner (arrowSource first) && cellTraceValid owner (arrowTarget first)
           && arrowTarget first /= arrowSource second}
      -> value:{ChartedDatum a s d source | chartedDatumValid owner (arrowSource first) value}
      -> () @-}
proofGuard :: Atlas a s d o f -> PageElementArrow s middle target -> PageElementArrow s source middle
  -> ChartedDatum a s d source -> ()
proofGuard = chartedCompositionLaw
""",

    "charted inverse soundness requires a returned candidate": """
{-@ proofGuard :: owner:Atlas a s d o f
      -> arrow:{PageElementArrow s source target |
           cellTraceValid owner (arrowSource arrow) && cellTraceValid owner (arrowTarget arrow)}
      -> value:{ChartedDatum a s d target | chartedDatumValid owner (arrowTarget arrow) value}
      -> candidate:{ChartedDatum a s d source | chartedDatumValid owner (arrowSource arrow) candidate}
      -> {chartedDataMap owner arrow candidate == value} @-}
proofGuard :: Atlas a s d o f -> PageElementArrow s source target
  -> ChartedDatum a s d target -> ChartedDatum a s d source -> ()
proofGuard = chartedDataPreimageSound
""",
    "charted data inverse rejects a noncanonical target": """
{-@ proofGuard :: owner:Atlas a s d o f
      -> arrow:{PageElementArrow s source target |
           cellTraceValid owner (arrowSource arrow) && cellTraceValid owner (arrowTarget arrow)}
      -> value:{ChartedDatum a s d target |
           atlasAcceptsDatum owner (arrowTarget arrow) (chartedCellDataValue value)
           && not (coverageRankCanonical owner (arrowTarget arrow) (chartedCellDataValue value) (chartedCellDataRank value))}
      -> Maybe (ChartedDatum a s d source) @-}
proofGuard :: Atlas a s d o f -> PageElementArrow s source target
  -> ChartedDatum a s d target -> Maybe (ChartedDatum a s d source)
proofGuard = chartedDataPreimage
""",
    "opaque reflection still checks function bodies": """
{-@ opaque-reflect proofGuard @-}
{-@ proofGuard :: value:Natural -> {result:Natural | result == value} @-}
proofGuard :: Natural -> Natural
proofGuard value = value + 1
""",
    "charted rank round trip rejects a noncanonical cache": """
{-@ proofGuard :: owner:Atlas a s d o f
      -> occurrence:{PageElement s object | cellTraceValid owner occurrence}
      -> value:{ChartedDatum a s d object |
           atlasAcceptsDatum owner occurrence (chartedCellDataValue value)
           && not (coverageRankCanonical owner occurrence (chartedCellDataValue value) (chartedCellDataRank value))}
      -> {chartedUnrank owner occurrence (chartedCellDataRank value) == Just value} @-}
proofGuard :: Atlas a s d o f -> PageElement s object -> ChartedDatum a s d object -> ()
proofGuard = chartedRankRoundTrip
""",
    "charted unranking cannot fabricate a result for a failed code": """
{-@ proofGuard :: owner:Atlas a s d o f
      -> occurrence:{PageElement s object | cellTraceValid owner occurrence}
      -> code:{Natural | atlasCoverageAt owner occurrence code == Nothing}
      -> {result:Maybe (ChartedDatum a s d object) | result /= Nothing} @-}
proofGuard :: Atlas a s d o f -> PageElement s object -> Natural -> Maybe (ChartedDatum a s d object)
proofGuard = chartedUnrank
""",
    "charted data transport cannot shift its certified code": """
{-@ proofGuard :: owner:Atlas a s d o f
      -> arrow:{PageElementArrow s source target |
           cellTraceValid owner (arrowSource arrow) && cellTraceValid owner (arrowTarget arrow)}
      -> value:{ChartedDatum a s d source | chartedDatumValid owner (arrowSource arrow) value}
      -> {result:ChartedDatum a s d target |
           chartedCellDataRank result == chartedCellDataRank value + 1} @-}
proofGuard :: Atlas a s d o f -> PageElementArrow s source target
  -> ChartedDatum a s d source -> ChartedDatum a s d target
proofGuard = chartedDataMap
""",
    "charted coverage rejects an unsuccessful cached code": """
{-@ proofGuard :: owner:Atlas a s d o f
      -> occurrence:{PageElement s object | cellTraceValid owner occurrence}
      -> value:{ChartedDatum a s d object |
           atlasAcceptsDatum owner occurrence (chartedCellDataValue value)
           && not (coverageRankCandidate owner occurrence (chartedCellDataValue value) (chartedCellDataRank value))}
      -> CoverageWitness a s d @-}
proofGuard :: Atlas a s d o f -> PageElement s object -> ChartedDatum a s d object -> CoverageWitness a s d
proofGuard = chartedCellCoverage
""",
    "charted equality rejects a noncanonical cached code": """
{-@ proofGuard :: owner:Atlas a s d o f
      -> occurrence:{PageElement s object | cellTraceValid owner occurrence}
      -> left:{ChartedDatum a s d object |
           atlasAcceptsDatum owner occurrence (chartedCellDataValue left)
           && coverageRankCanonical owner occurrence (chartedCellDataValue left) (chartedCellDataRank left)}
      -> right:{ChartedDatum a s d object |
           chartedCellDataValue right == chartedCellDataValue left
           && not (coverageRankCanonical owner occurrence (chartedCellDataValue right) (chartedCellDataRank right))}
      -> {left == right} @-}
proofGuard :: Atlas a s d o f -> PageElement s object -> ChartedDatum a s d object -> ChartedDatum a s d object -> ()
proofGuard = chartedCellDataEqual
""",
    "charted components reject a source inverse that drops every covered value": """
{-@ proofGuard
      :: sourceAtlas:Atlas sa ss sd so sf
      -> source:{PageElement ss sourceObject | cellTraceValid sourceAtlas source}
      -> targetAtlas:Atlas ta ts td to tf
      -> target:{PageElement ts targetObject | cellTraceValid targetAtlas target}
      -> original:DomanialInsertion
           ({datum:sd sourceObject | atlasAcceptsDatum sourceAtlas source datum})
           ({datum:td targetObject | atlasAcceptsDatum targetAtlas target datum})
      -> forward:(value:{ChartedDatum sa ss sd sourceObject | chartedDatumValid sourceAtlas source value} ->
           {result:ChartedDatum ta ts td targetObject | chartedDatumValid targetAtlas target result
             && chartedCellDataValue result == applyInsertion original (chartedCellDataValue value)})
      -> DomanialInsertion
           ({value:ChartedDatum sa ss sd sourceObject | chartedDatumValid sourceAtlas source value})
           ({value:ChartedDatum ta ts td targetObject | chartedDatumValid targetAtlas target value}) @-}
proofGuard
  :: Atlas sa ss sd so sf -> PageElement ss sourceObject
  -> Atlas ta ts td to tf -> PageElement ts targetObject
  -> DomanialInsertion (sd sourceObject) (td targetObject)
  -> (ChartedDatum sa ss sd sourceObject -> ChartedDatum ta ts td targetObject)
  -> DomanialInsertion (ChartedDatum sa ss sd sourceObject) (ChartedDatum ta ts td targetObject)
proofGuard sourceAtlas source targetAtlas target original forward =
  chartMapInsertion sourceAtlas source targetAtlas target original forward (const Nothing) (const ())
""",
    "chart counits reject an inverse that drops every covered value": """
{-@ proofGuard :: owner:Atlas a s d o f
      -> occurrence:{PageElement s object | cellTraceValid owner occurrence}
      -> DomanialInsertion
           ({value:ChartedDatum a s d object | chartedDatumValid owner occurrence value})
           ({datum:d object | atlasAcceptsDatum owner occurrence datum}) @-}
proofGuard :: Atlas a s d o f -> PageElement s object
  -> DomanialInsertion (ChartedDatum a s d object) (d object)
proofGuard owner occurrence = chartCounitInsertion owner occurrence (const Nothing) (const ())
""",
    "charted membership rejects a noncanonical cached code": """
{-@ proofGuard :: owner:Atlas a s d o f
      -> occurrence:{PageElement s object | cellTraceValid owner occurrence}
      -> datum:{d object | atlasAcceptsDatum owner occurrence datum}
      -> code:{Natural | not (coverageRankCanonical owner occurrence datum code)}
      -> {result:ChartedDatum a s d object | chartedDatumValid owner occurrence result} @-}
proofGuard :: Atlas a s d o f -> PageElement s object -> d object -> Natural -> ChartedDatum a s d object
proofGuard _ _ datum code = chartedCellData datum code
""",
    "charted data rejects a witness that does not cover the datum": """
{-@
proofGuard
  :: valueAtlas:Atlas atlasScope scope cellData origin final
  -> occurrence:PageElement scope object
  -> datum:cellData object
  -> witness:{w:CoverageWitness atlasScope scope cellData |
       not (coverageWitnessCovers valueAtlas occurrence datum w)}
  -> ChartedDatum atlasScope scope cellData object
@-}
proofGuard
  :: Atlas atlasScope scope cellData origin final
  -> PageElement scope object
  -> cellData object
  -> CoverageWitness atlasScope scope cellData
  -> ChartedDatum atlasScope scope cellData object
proofGuard valueAtlas occurrence datum witness =
  chartCellData valueAtlas occurrence datum witness ()
""",
}


RANK_IMAGE_SOURCE = HASKELL / "src/DatraCore/Atlases/Core/DomanialInsertion/Core.hs"
STABLE_PREIMAGE_PUBLIC_SOURCE = """
{-# LANGUAGE CPP #-}
{-# LANGUAGE RankNTypes #-}
#include "LiquidPlugin.h"
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--higherorder" @-}
module PublicStablePreimageGuard where
import Atlas (Atlas, AtlasObject, atlasPageElements)
import Coalition.Element (CoalitionData, coalitionElementValid, coalitionElementSource)
import PageElements (originPageElement)
import StableAtlasTransversal (StableAtlasTransversal, withStableAtlasTransversalCoalitionPreimage)
{-@ predicate PublicCanonical A E = coalitionElementValid A E
      && coalitionElementSource E == originPageElement (atlasPageElements A) @-}
"""
STABLE_PREIMAGE_PUBLIC_GUARDS = {
    "owned stable inverse cannot substitute another source owner": """
{-@ chosenOwnerCallback :: chosen:Atlas a s d co cf -> Atlas a s d o f
      -> {value:CoalitionData a s d | PublicCanonical chosen value} -> Bool @-}
chosenOwnerCallback :: Atlas a s d co cf -> Atlas a s d o f -> CoalitionData a s d -> Bool
chosenOwnerCallback _ _ _ = True
{-@ proofGuard :: Atlas sa ss sd co cf -> owner:Atlas ta ts td to tf
      -> StableAtlasTransversal (AtlasObject sa ss sd) (AtlasObject ta ts td)
      -> {value:CoalitionData ta ts td | PublicCanonical owner value} -> Maybe Bool @-}
proofGuard :: Atlas sa ss sd co cf -> Atlas ta ts td to tf
  -> StableAtlasTransversal (AtlasObject sa ss sd) (AtlasObject ta ts td)
  -> CoalitionData ta ts td -> Maybe Bool
proofGuard chosen owner arrow value =
  withStableAtlasTransversalCoalitionPreimage owner arrow value (chosenOwnerCallback chosen)
""",
    "owned stable inverse requires target owning validity": """
{-@ proofGuard :: owner:Atlas ta ts td to tf
      -> StableAtlasTransversal (AtlasObject sa ss sd) (AtlasObject ta ts td)
      -> CoalitionData ta ts td -> Maybe Bool @-}
proofGuard :: Atlas ta ts td to tf
  -> StableAtlasTransversal (AtlasObject sa ss sd) (AtlasObject ta ts td)
  -> CoalitionData ta ts td -> Maybe Bool
proofGuard owner arrow value = withStableAtlasTransversalCoalitionPreimage owner arrow value (\\_ _ -> True)
""",
    "owned stable inverse requires the canonical target origin": """
{-@ proofGuard :: owner:Atlas ta ts td to tf
      -> StableAtlasTransversal (AtlasObject sa ss sd) (AtlasObject ta ts td)
      -> {value:CoalitionData ta ts td | coalitionElementValid owner value} -> Maybe Bool @-}
proofGuard :: Atlas ta ts td to tf
  -> StableAtlasTransversal (AtlasObject sa ss sd) (AtlasObject ta ts td)
  -> CoalitionData ta ts td -> Maybe Bool
proofGuard owner arrow value = withStableAtlasTransversalCoalitionPreimage owner arrow value (\\_ _ -> True)
""",
    "owned stable inverse cannot supply an invalid source to its callback": """
{-@ invalidSource :: owner:Atlas a s d o f
      -> {value:CoalitionData a s d | not (coalitionElementValid owner value)} -> Bool @-}
invalidSource :: Atlas a s d o f -> CoalitionData a s d -> Bool
invalidSource _ _ = True
{-@ proofGuard :: owner:Atlas ta ts td to tf
      -> StableAtlasTransversal (AtlasObject sa ss sd) (AtlasObject ta ts td)
      -> {value:CoalitionData ta ts td | PublicCanonical owner value} -> Maybe Bool @-}
proofGuard :: Atlas ta ts td to tf
  -> StableAtlasTransversal (AtlasObject sa ss sd) (AtlasObject ta ts td)
  -> CoalitionData ta ts td -> Maybe Bool
proofGuard owner arrow value = withStableAtlasTransversalCoalitionPreimage owner arrow value invalidSource
""",
    "owned stable inverse cannot change the recovered source origin": """
{-@ changedOrigin :: owner:Atlas a s d o f
      -> {value:CoalitionData a s d | coalitionElementSource value /= originPageElement (atlasPageElements owner)}
      -> Bool @-}
changedOrigin :: Atlas a s d o f -> CoalitionData a s d -> Bool
changedOrigin _ _ = True
{-@ proofGuard :: owner:Atlas ta ts td to tf
      -> StableAtlasTransversal (AtlasObject sa ss sd) (AtlasObject ta ts td)
      -> {value:CoalitionData ta ts td | PublicCanonical owner value} -> Maybe Bool @-}
proofGuard :: Atlas ta ts td to tf
  -> StableAtlasTransversal (AtlasObject sa ss sd) (AtlasObject ta ts td)
  -> CoalitionData ta ts td -> Maybe Bool
proofGuard owner arrow value = withStableAtlasTransversalCoalitionPreimage owner arrow value changedOrigin
""",
}

INSERTION_COMPOSITION_PUBLIC_SOURCE = """
{-# LANGUAGE CPP #-}
#include "LiquidPlugin.h"
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--higherorder" @-}
module PublicInsertionCompositionGuard where
import DomanialInsertion.Core
{-@ qualif Positive(v:Int) { v > 0 } @-}
"""
INSERTION_COMPOSITION_PUBLIC_GUARDS = {
    "insertion composition cannot discard the second forward action": """
{-@ proofGuard :: second:DomanialInsertion Int Int
      -> first:DomanialInsertion Int Int -> value:Int
      -> {applyInsertion (composeInsertions second first) value == applyInsertion first value} @-}
proofGuard :: DomanialInsertion Int Int -> DomanialInsertion Int Int -> Int -> ()
proofGuard = composeInsertionsApply
""",
    "insertion composition retains a failed second inverse": """
{-@ proofGuard :: second:DomanialInsertion b c -> first:DomanialInsertion a b
      -> value:{c | preimage second value == Nothing}
      -> {preimage (composeInsertions second first) value /= Nothing} @-}
proofGuard :: DomanialInsertion b c -> DomanialInsertion a b -> c -> ()
proofGuard = composeInsertionsPreimageNothing
""",
    "insertion composition requires the actual inverse intermediate": """
{-@ proofGuard :: second:DomanialInsertion b c -> first:DomanialInsertion a b
      -> value:c -> middle:b
      -> {preimage (composeInsertions second first) value == preimage first middle} @-}
proofGuard :: DomanialInsertion b c -> DomanialInsertion a b -> c -> b -> ()
proofGuard = composeInsertionsPreimageJust
""",
    "insertion composition retains its restricted source domain": """
{-@ proofGuard :: DomanialInsertion Int Int
      -> DomanialInsertion {value:Int | value > 0} Int -> Int -> Int @-}
proofGuard :: DomanialInsertion Int Int -> DomanialInsertion Int Int -> Int -> Int
proofGuard second first value = applyInsertion (composeInsertions second first) value
""",
}

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


MERGE_SOURCE = HASKELL / "src/DatraCore/Atlases/Derived/AtlasConfederations/AtlasMerge/Data.hs"
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

SEQUENCE_SOURCE = HASKELL / "src/DatraCore/Atlases/Derived/AtlasConfederations/AtlasSequence/Data.hs"
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
    "explicit Atlas lookup cannot discard its trace result": """
{-@ proofGuard :: owner:Atlas a s d o f -> page:Natural
      -> positions:{[Ordinal] | pageTraceContains (Elements.pageElementsFolio (atlasPageElements owner)) page positions}
      -> {resolved:Maybe (SomePageElement s) | cellLookupTrace resolved == Nothing} @-}
proofGuard :: Atlas a s d o f -> Natural -> [Ordinal] -> Maybe (SomePageElement s)
proofGuard owner page positions = atlasCellAt owner page (traceHead positions)
""",
    "explicit Atlas lookup cannot shift its returned page": """
{-@ proofGuard :: owner:Atlas a s d o f -> page:Natural -> Ordinal
      -> Maybe ({source:SomePageElement s | Trace.somePageElementPage source == page + 1}) @-}
proofGuard :: Atlas a s d o f -> Natural -> Ordinal -> Maybe (SomePageElement s)
proofGuard = atlasCellAt
""",
    "native Atlas trace lookup requires an accepted trace": """
proofGuard :: Atlas atlasScope scope cellData origin final -> Natural -> [Ordinal] -> Maybe ()
proofGuard valueAtlas page positions = withAtlasCellTrace valueAtlas page positions (\\_ -> ())
""",
    "native Atlas trace lookup cannot substitute another trace": """
{-@ proofGuard :: valueAtlas:Atlas atlasScope scope cellData origin final
      -> page:Natural
      -> positions:{[Ordinal] | pageTraceContains (Elements.pageElementsFolio (atlasPageElements valueAtlas)) page positions}
      -> [Ordinal] -> Natural -> Maybe Bool @-}
proofGuard :: Atlas atlasScope scope cellData origin final -> Natural -> [Ordinal] -> [Ordinal] -> Natural -> Maybe Bool
proofGuard valueAtlas page positions other rankValue =
  withAtlasCellTrace valueAtlas page positions (\\source -> cellContainsRank valueAtlas (source {pageElementTrace = other}) rankValue)
""",
    "cell lookup cannot claim another Atlas transport trace": """
{-@ proofGuard :: Atlas a s d o f -> Atlas a s d o f -> Natural -> Ordinal
      -> Maybe ({answer:Bool | answer}) @-}
proofGuard :: Atlas a s d o f -> Atlas a s d o f -> Natural -> Ordinal -> Maybe Bool
proofGuard owner other page position =
  withAtlasCellAt owner page position (\\source -> cellTraceValid other source)
""",
    "cell membership disjointness requires distinct positions": """
{-@ proofGuard :: valueAtlas:Atlas a s d o f
      -> cell:{PageElement s object | cellHasOrigin valueAtlas cell && cellTraceValid valueAtlas cell}
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


FOLIO_SOURCE = HASKELL / "src/DatraCore/Atlases/Core/Folio/Presentation.hs"
FOLIO_GUARDS = {
    "opaque folio accessors cannot equate different endpoints": """
{-@ proofGuard :: step:FolioStep origin page page
      -> {stepSource step == orderedTarget (stepTransition step)} @-}
proofGuard :: FolioStep origin page page -> ()
proofGuard step = stepSource step `seq` ()
""",
    "folio steps require the actual preceding chain": """
{-@ proofGuard :: pages:FolioData origin previous
      -> OrderedConsolidation next previous -> FolioData origin next @-}
proofGuard :: FolioData origin previous -> OrderedConsolidation next previous -> FolioData origin next
proofGuard pages transition = SnocPage (FolioStep (folioLengthData pages + 1) pages transition)
""",
    "folio origins reject a zero cached length": """
proofGuard :: Chain origin -> SingletonOrigin origin -> FolioData origin origin
proofGuard = OriginFolio 0
""",
    "folio origins reject a cached length greater than one": """
proofGuard :: Chain origin -> SingletonOrigin origin -> FolioData origin origin
proofGuard = OriginFolio 2
""",
    "folio append rejects an unchanged cached length": """
proofGuard :: FolioStep origin previous next -> FolioData origin next
proofGuard (FolioStep _ pages transition) =
  SnocPage (FolioStep (folioLengthData pages) pages transition)
""",
}

FOLIO_API_SOURCE = HASKELL / "src/DatraCore/Atlases/Core/Folio/Internal.hs"
FOLIO_API_GUARDS = {
    "folio append requires page-order evidence": """
{-@ proofGuard :: Folio origin previous -> Chain next
      -> Coconsolidation previous next -> Folio origin next @-}
proofGuard :: Folio origin previous -> Chain next -> Coconsolidation previous next -> Folio origin next
proofGuard pages next transition = appendPage pages next transition
""",
}

PAGE_ARROW_SOURCE = HASKELL / "src/DatraCore/Atlases/Core/PageElements/Structure.hs"
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

TERRITORY_SOURCE = HASKELL / "src/DatraCore/Atlases/Derived/AtlasDerived/AtlasTerritory/AtlasTerritory.hs"
TERRITORY_GUARDS = {
    "territory reconstruction cannot drop a valid final occurrence": """
{-@ proofGuard :: owner:Atlas a s d o f
      -> source:{PageElement s object | cellTraceValid owner source
           && pageElementPage source == folioLength (atlasFolio owner) - 1}
      -> {result:Maybe () | not (Elements.traceLookupPresent result)} @-}
proofGuard :: Atlas a s d o f -> PageElement s object -> Maybe ()
proofGuard owner source = withAtlasTerritoryOf owner source (const (const ()))
""",
    "territory reconstruction preserves the selected position": r"""
{-@ proofGuard :: owner:Atlas a s d o f
      -> source:{PageElement s object | cellTraceValid owner source
           && pageElementPage source == folioLength (atlasFolio owner) - 1}
      -> Maybe {different:Bool | different} @-}
proofGuard :: Atlas a s d o f -> PageElement s object -> Maybe Bool
proofGuard owner source = withAtlasTerritoryOf owner source $ \_index arrow ->
  pageElementPosition (arrowTarget arrow) /= pageElementPosition source
""",
}

PAGE_API_SOURCE = HASKELL / "src/DatraCore/Atlases/Core/PageElements/PageElements.hs"
PAGE_API_GUARDS = {
    "public page allocation retains the supplied folio": """
{-@ proofGuard :: pages:Folio origin final
      -> {result:Folio origin final | result /= pages} @-}
proofGuard :: Folio origin final -> Folio origin final
proofGuard pages = pageElements pages pageElementsFolio
""",
    "public normalization retains the final-page bound": """
{-@ proofGuard :: category:PageElements scope origin final
      -> occurrence:PageElement scope object
      -> {result:PageElement scope object |
           pageElementPage result > folioLength (pageElementsFolio category) - 1} @-}
proofGuard :: PageElements scope origin final -> PageElement scope object -> PageElement scope object
proofGuard = normalizePageElement
""",
    "final region indexing requires a final-page occurrence": """
{-@ proofGuard :: category:PageElements scope origin final
      -> occurrence:{PageElement scope object | pageElementTraceValid category occurrence}
      -> Maybe (ChainIndex final) @-}
proofGuard :: PageElements scope origin final -> PageElement scope object -> Maybe (ChainIndex final)
proofGuard = finalPageElementIndex
""",
    "public final page lookup retains the requested chain position": """
{-@ proofGuard :: category:PageElements scope origin final
      -> index:{ChainIndex final |
           chainPosition (lastChain (pageElementsFolio category)) (chainObjectAt index)
             == chainIndexPosition index}
      -> {result:SomePageElement scope |
           Trace.somePageElementPosition result /= chainIndexPosition index} @-}
proofGuard :: PageElements scope origin final -> ChainIndex final -> SomePageElement scope
proofGuard = lastPageElement
""",
}

DOMINION_LOOKUP_SOURCE = HASKELL / "src/DatraCore/Atlases/Core/Dominion/Dominion.hs"
DOMINION_LOOKUP_GUARDS = {
    "Dominion rank lookup rejects a candidate with a different forward rank": """
{-@ proofGuard :: owner:Dominion a -> index:Natural -> Maybe {value:a | rank owner value /= index} @-}
proofGuard :: Dominion a -> Natural -> Maybe a
proofGuard = lookupRank
""",
    "Dominion rank lookup retains the round trip": """
{-@ proofGuard :: owner:Dominion a -> value:a -> {lookupRank owner (rank owner value) /= Just value} @-}
proofGuard :: Dominion a -> a -> ()
proofGuard = lookupRankRoundTrip
""",
}
RANKED_DOMINION_SOURCE = HASKELL / "src/DatraCore/Atlases/Derived/Cartography/RankedDominionAtlas.hs"

PAGE_CONSTRUCTION_SOURCE = HASKELL / "src/DatraCore/Atlases/Core/PageElements/Construction.hs"
PAGE_CONSTRUCTION_GUARDS = {
    "fixed page construction retains its recipe folio": """
{-@ proofGuard :: PageElementsConstruction recipe origin final
      => recipe:Proxy recipe
      -> {result:Folio origin final | result /= pageElementsRecipe recipe} @-}
proofGuard :: PageElementsConstruction recipe origin final
  => Proxy recipe -> Folio origin final
proofGuard recipe = pageElementsFolio (constructPageElements recipe)
""",
}
PAGINATION_API_SOURCE = HASKELL / "src/DatraCore/Atlases/Core/Pagination/Pagination.hs"
PAGINATION_API_GUARDS = {
    "pagination assembly retains the supplied occurrence category": """
{-@ proofGuard :: elements:PageElements scope origin final
      -> {value:Pagination scope origin final | paginationPageElements value /= elements} @-}
proofGuard :: PageElements scope origin final -> Pagination scope origin final
proofGuard = paginationFromPageElements
""",
}

PAGE_INDEX_SOURCE = HASKELL / "src/DatraCore/Atlases/Core/PageElements/Internal.hs"
PAGE_INDEX_GUARDS = {
    "final page lookup retains the requested chain position": """
{-@ proofGuard :: category:PageElements scope origin final
      -> index:{ChainIndex final |
           chainPosition (lastChain (pageElementsFolio category)) (chainObjectAt index)
             == chainIndexPosition index}
      -> {result:SomePageElement scope |
           Trace.somePageElementPosition result /= chainIndexPosition index} @-}
proofGuard :: PageElements scope origin final -> ChainIndex final -> SomePageElement scope
proofGuard = lastPageElement
""",
    "final cell lookup cannot substitute another trace": """
{-@ proofGuard :: pages:{Folio origin current | folioLength pages > 1} -> value:current -> other:current
      -> {folioTraceLookup pages (folioLength pages - 1) (chainPosition (lastChain pages) value)
           == Just (genuinePageElementTrace pages other)} @-}
proofGuard :: Folio origin current -> current -> current -> ()
proofGuard pages value _ = finalPageTraceLookup pages value
""",

    "appended lookup cannot treat the new page as an earlier page": """
{-@ proofGuard :: previous:Folio origin earlier -> pageChain:Chain current
      -> transition:{OrderedConsolidation current earlier |
           orderedSource transition == pageChain && orderedTarget transition == lastPageData previous}
      -> position:Ordinal -> () @-}
proofGuard :: Folio origin earlier -> Chain current -> OrderedConsolidation current earlier -> Ordinal -> ()
proofGuard previous pageChain transition position =
  appendedEarlierLookup previous pageChain transition (folioLength previous) position
""",
    "appended lookup cannot drop the new trace head": """
{-@ proofGuard :: previous:Folio origin earlier -> pageChain:Chain current
      -> transition:{OrderedConsolidation current earlier |
           orderedSource transition == pageChain && orderedTarget transition == lastPageData previous}
      -> value:current
      -> {folioTraceLookup (appendPageData previous pageChain transition) (folioLength previous)
           (chainPosition pageChain value) == Just (genuinePageElementTrace previous (orderedApply transition value))} @-}
proofGuard :: Folio origin earlier -> Chain current -> OrderedConsolidation current earlier -> current -> ()
proofGuard previous pageChain transition value = appendedFinalLookup previous pageChain transition value
""",

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


ATLAS_CONSTRUCTION_SOURCE = HASKELL / "src/DatraCore/Atlases/Core/Atlas/Construction.hs"
ATLAS_CONSTRUCTION_GUARDS = {
    "fixed Atlas construction retains its complete presentation": """
{-@ proofGuard :: AtlasConstruction recipe scope cellData origin final
      => recipe:Proxy recipe
      -> {value:Atlas (FixedAtlasScope recipe scope cellData origin final) scope cellData origin final |
           atlasDescription value /= atlasConstructionPresentation recipe} @-}
proofGuard :: AtlasConstruction recipe scope cellData origin final
  => Proxy recipe
  -> Atlas (FixedAtlasScope recipe scope cellData origin final) scope cellData origin final
proofGuard = constructAtlas
""",
    "fixed Atlas construction retains its recipe pagination": """
{-@ proofGuard :: AtlasConstruction recipe scope cellData origin final
      => recipe:Proxy recipe
      -> {value:Atlas (FixedAtlasScope recipe scope cellData origin final) scope cellData origin final |
           atlasPagination value /= atlasPresentationPagination (atlasConstructionPresentation recipe)} @-}
proofGuard :: AtlasConstruction recipe scope cellData origin final
  => Proxy recipe
  -> Atlas (FixedAtlasScope recipe scope cellData origin final) scope cellData origin final
proofGuard = constructAtlas
""",
    "construction instances must satisfy their declared method contracts": """
data ProofGuardConstruction a s (d :: Type -> Type) object

{-@ class ProofGuardClass construction where
      proofGuardMethod :: forall a s d object.
        Maybe (construction a s d object) -> {proof:() | False}
  @-}
class ProofGuardClass (construction :: Type -> Type -> (Type -> Type) -> Type -> Type) where
  proofGuardMethod :: forall a s d object. Maybe (construction a s d object) -> ()

instance ProofGuardClass ProofGuardConstruction where
  proofGuardMethod _ = ()
""",
    "stable construction retains the original pagination": """
{-@ proofGuard :: AtlasDataConstruction construction => owner:Atlas a s d o f
      -> other:{Atlas a s d o f | atlasPagination other /= atlasPagination owner}
      -> {value:Atlas (ConstructedAtlasScope construction a s d) s (construction a s d) o f |
           atlasPagination value == atlasPagination other} @-}
proofGuard :: AtlasDataConstruction construction => Atlas a s d o f -> Atlas a s d o f
  -> Atlas (ConstructedAtlasScope construction a s d) s (construction a s d) o f
proofGuard owner _ = constructAtlasData owner
""",
}

ATLAS_PRESENTATION_SOURCE = HASKELL / "src/DatraCore/Atlases/Core/Atlas/Atlas.hs"
ATLAS_PRESENTATION_GUARDS = {
    "public Atlas allocation retains its complete presentation": """
-- Check the rank-polymorphic callback from its explicit contracts.
{-@ LIQUID "--fast" @-}
{-@ proofGuard :: presentation:AtlasPresentation scope cellData origin final
      -> {result:AtlasPresentation scope cellData origin final | result /= presentation} @-}
proofGuard :: AtlasPresentation scope cellData origin final
  -> AtlasPresentation scope cellData origin final
proofGuard presentation = withAtlasPresentation presentation (\\value -> atlasDescription value)
""",
    "Atlas presentation construction requires normalized action laws": """
{-@ proofGuard :: pages:Pagination scope origin final
      -> accepts:(forall object. PageElement scope object -> cellData object -> Bool)
      -> action:{AtlasDataAction scope cellData |
           atlasActionDomain action == Elements.pageElementDomain (paginationPageElements pages)
           && atlasActionMembership action == atlasMembership accepts}
      -> AtlasPresentation scope cellData origin final @-}
proofGuard :: Pagination scope origin final
  -> (forall object. PageElement scope object -> cellData object -> Bool)
  -> AtlasDataAction scope cellData -> AtlasPresentation scope cellData origin final
proofGuard pages accepts action = atlasPresentationForPredicate pages accepts action
  (\\_ _ -> ()) (\\_ _ _ _ -> ()) (\\_ _ _ _ -> ()) (\\_ _ _ _ _ _ _ -> ())
""",
    "Atlas presentation allocation cannot change its pagination": """
{-@ proofGuard :: presentation:AtlasPresentation s d o f
      -> other:{Pagination s o f | other /= atlasPresentationPagination presentation}
      -> {result:Pagination s o f | result == other} @-}
proofGuard :: AtlasPresentation s d o f -> Pagination s o f -> Pagination s o f
proofGuard presentation _ = withAtlasPresentation presentation atlasPagination
""",
}

ATLAS_SOURCE = HASKELL / "src/DatraCore/Atlases/Core/Atlas/Internal.hs"
ATLAS_GUARDS = {
    "Atlas normalization arrow requires the owning trace": """
{-@ proofGuard :: owner:Atlas a s d o f
      -> source:{PageElement s object | not (Elements.pageElementTraceValid (atlasPageElements owner) source)}
      -> PageElementArrow s object object @-}
proofGuard :: Atlas a s d o f -> PageElement s object -> PageElementArrow s object object
proofGuard = atlasNormalizationArrow
""",
    "Atlas normalized insertion cannot change owners": """
{-@ proofGuard :: owner:Atlas a s d o f -> other:Atlas a s d o f
      -> arrow:{PageElementArrow s source target |
           Elements.pageElementTraceValid (atlasPageElements owner) (arrowSource arrow)
           && Elements.pageElementTraceValid (atlasPageElements owner) (arrowTarget arrow)
           && Elements.pageElementTraceValid (atlasPageElements other) (arrowSource arrow)
           && Elements.pageElementTraceValid (atlasPageElements other) (arrowTarget arrow)}
      -> {mapAtlasData owner (normalizeAtlasArrow owner arrow) == mapAtlasData other arrow} @-}
proofGuard :: Atlas a s d o f -> Atlas a s d o f -> PageElementArrow s source target -> ()
proofGuard owner _ arrow = mapAtlasDataNormalized owner arrow
""",

    "Atlas predicate packaging requires membership-preserving callbacks": """
{-@ proofGuard :: category:PageElements scope origin final
      -> accepts:(forall object. PageElement scope object -> cellData object -> Bool)
      -> dataAt:(forall object. occurrence:{PageElement scope object | Elements.pageElementTraceValid category occurrence}
           -> Dominion ({datum:cellData object | accepts occurrence datum}))
      -> mapData:(forall source target. arrow:{PageElementArrow scope source target |
           Elements.pageElementTraceValid category (arrowSource arrow)
           && Elements.pageElementTraceValid category (arrowTarget arrow)}
           -> DomanialInsertion (cellData source) (cellData target))
      -> AtlasDataAction scope cellData @-}
proofGuard :: PageElements scope origin final
  -> (forall object. PageElement scope object -> cellData object -> Bool)
  -> (forall object. PageElement scope object -> Dominion (cellData object))
  -> (forall source target. PageElementArrow scope source target
        -> DomanialInsertion (cellData source) (cellData target))
  -> AtlasDataAction scope cellData
proofGuard = atlasPredicateDataAction
""",
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
    "Atlas disjointness witnesses require distinct cells on one page": """
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
    "merge cell disjointness requires distinct positions": """
{-@ proofGuard :: left:Atlas la ls ld lo lf -> right:Atlas ra rs rd ro rf
      -> cell:{PageElement ms a | pageElementPage cell > 0}
      -> datum:{AtlasMergeDatum c | mergeCellContains left right cell datum}
      -> {not (mergeCellContains left right cell datum)} @-}
proofGuard :: Atlas la ls ld lo lf -> Atlas ra rs rd ro rf
  -> PageElement ms a -> AtlasMergeDatum c -> ()
proofGuard left right cell datum = mergeCellContainsDisjoint left right cell cell datum
""",
    "merge cell disjointness requires one page": """
{-@ proofGuard :: left:Atlas la ls ld lo lf -> right:Atlas ra rs rd ro rf
      -> first:{PageElement ms a | pageElementPage first > 0}
      -> second:{PageElement ms b | pageElementPosition second /= pageElementPosition first}
      -> datum:{AtlasMergeDatum c | mergeCellContains left right first datum}
      -> {not (mergeCellContains left right second datum)} @-}
proofGuard :: Atlas la ls ld lo lf -> Atlas ra rs rd ro rf
  -> PageElement ms a -> PageElement ms b -> AtlasMergeDatum c -> ()
proofGuard = mergeCellContainsDisjoint
""",
    "merge cell disjointness requires a positive raw page": """
{-@ proofGuard :: left:Atlas la ls ld lo lf -> right:Atlas ra rs rd ro rf
      -> first:PageElement ms a
      -> second:{PageElement ms b | pageElementPage second == pageElementPage first
           && pageElementPosition second /= pageElementPosition first}
      -> datum:{AtlasMergeDatum c | mergeCellContains left right first datum}
      -> {not (mergeCellContains left right second datum)} @-}
proofGuard :: Atlas la ls ld lo lf -> Atlas ra rs rd ro rf
  -> PageElement ms a -> PageElement ms b -> AtlasMergeDatum c -> ()
proofGuard = mergeCellContainsDisjoint
""",
    "native merge resolution requires an accepted cell": """
proofGuard :: Atlas la ls ld lo lf -> Atlas ra rs rd ro rf -> Natural -> AtlasMergePageCell -> Maybe ()
proofGuard left right page cell = withMergeNativeCell left right page cell (\\_ -> ()) (\\_ -> ())
""",
    "native merge resolution cannot shift the component page": """
{-@ proofGuard :: left:Atlas la ls ld lo lf -> right:Atlas ra rs rd ro rf
      -> page:Natural -> cell:{AtlasMergePageCell | mergePageContains (atlasFolio left) (atlasFolio right) page cell}
      -> Natural -> Maybe Bool @-}
proofGuard :: Atlas la ls ld lo lf -> Atlas ra rs rd ro rf -> Natural -> AtlasMergePageCell -> Natural -> Maybe Bool
proofGuard left right page cell rankValue = withMergeNativeCell left right page cell
  (\\source -> Extent.cellContainsRank left (source {pageElementPage = page + 1}) rankValue)
  (\\source -> Extent.cellContainsRank right (source {pageElementPage = page + 1}) rankValue)
""",
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

MERGE_CELL_SOURCE = HASKELL / "src/DatraCore/Atlases/Derived/AtlasConfederations/AtlasMerge/Source.hs"
MERGE_CELL_GUARDS = {
    "resolved merge membership requires component transport": """
{-@ proofGuard :: left:Atlas la ls ld lo lf -> right:Atlas ra rs rd ro rf
      -> source:{AtlasMergeSource ls rs | mergeSourceValid left right source}
      -> target:{AtlasMergeSource ls rs | mergeSourceValid left right target}
      -> datum:{AtlasMergeDatum object | mergeSourceContains left right source datum} -> () @-}
proofGuard :: Atlas la ls ld lo lf -> Atlas ra rs rd ro rf
  -> AtlasMergeSource ls rs -> AtlasMergeSource ls rs -> AtlasMergeDatum object -> ()
proofGuard = mergeSourceContainsPreserved
""",
    "resolved merge membership cannot cross components": """
{-@ proofGuard :: left:Atlas la ls ld lo lf -> right:Atlas ra rs rd ro rf
      -> source:{PageElement ls a | Extent.cellHasOrigin left source && Extent.cellTraceValid left source}
      -> target:{PageElement rs b | Extent.cellHasOrigin right target && Extent.cellTraceValid right target}
      -> datum:{AtlasMergeDatum object | mergeSourceContains left right (leftMergeSource left right source) datum} -> () @-}
proofGuard :: Atlas la ls ld lo lf -> Atlas ra rs rd ro rf
  -> PageElement ls a -> PageElement rs b -> AtlasMergeDatum object -> ()
proofGuard left right source target datum = mergeSourceContainsPreserved left right
  (leftMergeSource left right source) (rightMergeSource left right target) datum
""",
}

SEQUENCE_RESOLUTION_SOURCE = HASKELL / "src/DatraCore/Atlases/Derived/AtlasConfederations/AtlasSequence/Resolution.hs"
SEQUENCE_RESOLUTION_GUARDS = {
    "native sequence resolution requires an accepted cell": """
proofGuard :: [AtlasSequenceMember] -> Natural -> AtlasSequencePageCell -> Maybe ()
proofGuard members page cell = withSequenceNativeCell members page cell (\\_ _ _ -> ())
""",
    "native sequence resolution cannot shift the component page": """
{-@ proofGuard :: members:[AtlasSequenceMember] -> page:Natural
      -> cell:{AtlasSequencePageCell | sequencePageContains members page cell} -> Maybe Bool @-}
proofGuard :: [AtlasSequenceMember] -> Natural -> AtlasSequencePageCell -> Maybe Bool
proofGuard members page cell = withSequenceNativeCell members page cell
  (\\_ owner source -> Extent.cellContainsRank owner (source {pageElementPage = page + 1}) 0)
""",
    "sequence member resolution cannot return an out-of-range index": """
{-@ proofGuard :: members:[AtlasSequenceMember] -> page:Natural
      -> cell:{AtlasSequencePageCell | sequencePageContains members page cell}
      -> Maybe ({index:Natural | index >= len members}) @-}
proofGuard :: [AtlasSequenceMember] -> Natural -> AtlasSequencePageCell -> Maybe Natural
proofGuard members page cell =
  withSequenceNativeCell members page cell (\\index _ _ -> index)
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


PRIMITIVE_MORPHISM_SOURCE = HASKELL / "src/DatraCore/Atlases/Core/Atlas/Morphism/LiquidInternal.hs"
PRIMITIVE_MORPHISM_PUBLIC_SOURCE = r"""
{-# LANGUAGE CPP #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeFamilies #-}
#include "LiquidPlugin.h"
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}
{-@ LIQUID "--higherorder" @-}
module PrimitiveMorphismPublicGuard where
import Atlas
import qualified PageElements as Elements (pageElementTraceValid)
import DomanialInsertion.Core (DomanialInsertion, applyInsertion, preimage)
import PageElements.Structure
  ( PageElement (..), PageElementArrow, SomePageElement (..), arrowSource, arrowTarget
  , pageElementArrow, somePageElementPrecedes, somePageElementTransported )

{-@ observedNaturality :: action:AtlasMorphismAction objectMap sa ta ss ts sd td so sf to tf
      -> sourceArrow:{PageElementArrow ss source target |
           Elements.pageElementTraceValid (atlasPageElements (atlasMorphismSource action)) (arrowSource sourceArrow)
           && Elements.pageElementTraceValid (atlasPageElements (atlasMorphismSource action)) (arrowTarget sourceArrow)}
      -> datum:{sd source | atlasAcceptsDatum (atlasMorphismSource action) (arrowSource sourceArrow) datum}
      -> {applyInsertion
          ((mapAtlasMorphismActionComponent action) (normalizeAtlasElement (atlasMorphismSource action) (arrowTarget sourceArrow)))
          (applyInsertion (mapAtlasData (atlasMorphismSource action) sourceArrow) datum)
        == applyInsertion
          (mapAtlasData (atlasMorphismTarget action)
            (pageElementArrow
              (normalizeAtlasElement (atlasMorphismTarget action)
                ((mapAtlasMorphismActionObject action) (normalizeAtlasElement (atlasMorphismSource action) (arrowSource sourceArrow))))
              (normalizeAtlasElement (atlasMorphismTarget action)
                ((mapAtlasMorphismActionObject action) (normalizeAtlasElement (atlasMorphismSource action) (arrowTarget sourceArrow))))))
          (applyInsertion
            ((mapAtlasMorphismActionComponent action) (normalizeAtlasElement (atlasMorphismSource action) (arrowSource sourceArrow))) datum)} @-}
observedNaturality :: AtlasMorphismAction m sa ta ss ts sd td so sf to tf
  -> PageElementArrow ss source target -> sd source -> ()
observedNaturality = atlasMorphismActionNaturality

{-@ observedRelated :: action:AtlasMorphismAction m sa ta ss ts sd td so sf to tf
      -> source:SomePageElement ss
      -> target:{SomePageElement ss | somePageElementPrecedes source target
           && somePageElementTransported source target}
      -> {result:Bool | result} @-}
observedRelated :: AtlasMorphismAction m sa ta ss ts sd td so sf to tf
  -> SomePageElement ss -> SomePageElement ss -> Bool
observedRelated action source target =
  atlasMorphismActionPreservesArrow action source target `seq`
    (somePageElementPrecedes (mapAtlasMorphismActionElement action source)
       (mapAtlasMorphismActionElement action target)
      && somePageElementTransported (mapAtlasMorphismActionElement action source)
         (mapAtlasMorphismActionElement action target))

{-@ opaque-reflect rebuildAction @-}
{-@ rebuildAction :: action:AtlasMorphismAction m sa ta ss ts sd td so sf to tf
      -> {result:AtlasMorphismAction m sa ta ss ts sd td so sf to tf |
           atlasMorphismSource result == atlasMorphismSource action
           && atlasMorphismTarget result == atlasMorphismTarget action
           && atlasMorphismObjectMapWitness result == atlasMorphismObjectMapWitness action
           && mapAtlasMorphismActionObject result == mapAtlasMorphismActionObject action
           && mapAtlasMorphismActionComponent result == mapAtlasMorphismActionComponent action} @-}
rebuildAction :: AtlasMorphismAction m sa ta ss ts sd td so sf to tf
  -> AtlasMorphismAction m sa ta ss ts sd td so sf to tf
rebuildAction action = atlasMorphismAction
  (atlasMorphismObjectMapWitness action) (atlasMorphismSource action) (atlasMorphismTarget action)
  (mapAtlasMorphismActionObject action) (mapAtlasMorphismActionComponent action)
  (atlasMorphismActionPreservesArrow action) (atlasMorphismActionNaturality action)

{-@ observedNormalizedAction :: action:AtlasMorphismAction m sa ta ss ts sd td so sf to tf
      -> {result:AtlasMorphismAction m sa ta ss ts sd td so sf to tf |
           atlasMorphismSource result == atlasMorphismSource action
           && atlasMorphismTarget result == atlasMorphismTarget action} @-}
observedNormalizedAction :: AtlasMorphismAction m sa ta ss ts sd td so sf to tf
  -> AtlasMorphismAction m sa ta ss ts sd td so sf to tf
observedNormalizedAction = normalizeAtlasMorphismAction

{-@ observedNormalizedObject :: action:AtlasMorphismAction m sa ta ss ts sd td so sf to tf
      -> source:PageElement ss object
      -> {target:PageElement ts (AtlasMappedObject m object) |
           target == normalizeAtlasElement (atlasMorphismTarget action)
             (mapAtlasMorphismActionObject action
               (normalizeAtlasElement (atlasMorphismSource action) source))} @-}
observedNormalizedObject :: AtlasMorphismAction m sa ta ss ts sd td so sf to tf
  -> PageElement ss object -> PageElement ts (AtlasMappedObject m object)
observedNormalizedObject action source =
  normalizeAtlasMorphismActionRetains action source `seq`
    mapAtlasMorphismActionObject (normalizeAtlasMorphismAction action) source

{-@ opaque-reflect observedNormalizedComponent @-}
{-@ observedNormalizedComponent :: action:AtlasMorphismAction m sa ta ss ts sd td so sf to tf
      -> source:PageElement ss object
      -> {insertion:DomanialInsertion
           ({datum:sd object | atlasAcceptsDatum (atlasMorphismSource action) source datum})
           ({datum:td (AtlasMappedObject m object) |
                atlasAcceptsDatum (atlasMorphismTarget action)
                  (mapAtlasMorphismActionObject (normalizeAtlasMorphismAction action) source) datum}) |
           insertion == mapAtlasMorphismActionComponent action
             (normalizeAtlasElement (atlasMorphismSource action) source)} @-}
observedNormalizedComponent :: AtlasMorphismAction m sa ta ss ts sd td so sf to tf
  -> PageElement ss object -> DomanialInsertion (sd object) (td (AtlasMappedObject m object))
observedNormalizedComponent action source =
  normalizeAtlasMorphismActionRetains action source `seq`
    mapAtlasMorphismActionComponent (normalizeAtlasMorphismAction action) source


{-@ observedAcceptedForward :: action:AtlasMorphismAction m sa ta ss ts sd td so sf to tf
      -> source:PageElement ss object
      -> datum:{sd object | atlasAcceptsDatum (atlasMorphismSource action) source datum}
      -> {result:td (AtlasMappedObject m object) |
           atlasAcceptsDatum (atlasMorphismTarget action) (mapAtlasMorphismActionObject action source) result} @-}
observedAcceptedForward :: AtlasMorphismAction m sa ta ss ts sd td so sf to tf
  -> PageElement ss object -> sd object -> td (AtlasMappedObject m object)
observedAcceptedForward action source datum =
  applyInsertion (mapAtlasMorphismActionComponent action source) datum

{-@ observedAcceptedInverse :: action:AtlasMorphismAction m sa ta ss ts sd td so sf to tf
      -> source:PageElement ss object
      -> datum:{td (AtlasMappedObject m object) |
           atlasAcceptsDatum (atlasMorphismTarget action) (mapAtlasMorphismActionObject action source) datum}
      -> Maybe ({result:sd object | atlasAcceptsDatum (atlasMorphismSource action) source result}) @-}
observedAcceptedInverse :: AtlasMorphismAction m sa ta ss ts sd td so sf to tf
  -> PageElement ss object -> td (AtlasMappedObject m object) -> Maybe (sd object)
observedAcceptedInverse action source datum =
  preimage (mapAtlasMorphismActionComponent action source) datum


{-@ observedNormalizationIdempotent :: owner:Atlas a s d o f
      -> source:PageElement s object
      -> {normalizeAtlasElement owner (normalizeAtlasElement owner source)
           == normalizeAtlasElement owner source} @-}
observedNormalizationIdempotent :: Atlas a s d o f -> PageElement s object -> ()
observedNormalizationIdempotent = atlasCoherenceIdempotent


{-@ observedValidObject :: action:AtlasMorphismAction m sa ta ss ts sd td so sf to tf
      -> source:{PageElement ss object |
           Elements.pageElementTraceValid (atlasPageElements (atlasMorphismSource action)) source}
      -> {target:PageElement ts (AtlasMappedObject m object) |
           Elements.pageElementTraceValid (atlasPageElements (atlasMorphismTarget action)) target} @-}
observedValidObject :: AtlasMorphismAction m sa ta ss ts sd td so sf to tf
  -> PageElement ss object -> PageElement ts (AtlasMappedObject m object)
observedValidObject action source = mapAtlasMorphismActionObject action source

{-@ observedValidNormalizedObject :: action:AtlasMorphismAction m sa ta ss ts sd td so sf to tf
      -> source:{PageElement ss object |
           Elements.pageElementTraceValid (atlasPageElements (atlasMorphismSource action)) source}
      -> {target:PageElement ts (AtlasMappedObject m object) |
           Elements.pageElementTraceValid (atlasPageElements (atlasMorphismTarget action)) target} @-}
observedValidNormalizedObject :: AtlasMorphismAction m sa ta ss ts sd td so sf to tf
  -> PageElement ss object -> PageElement ts (AtlasMappedObject m object)
observedValidNormalizedObject action source =
  mapAtlasMorphismActionObject (normalizeAtlasMorphismAction action) source


{-@ observedIdentityObject :: owner:Atlas a s d o f -> source:PageElement s object
      -> {target:PageElement s (AtlasMappedObject IdentityAtlasObjectMap object) |
           pageElementPage target == pageElementPage source
           && pageElementPosition target == pageElementPosition source
           && pageElementTrace target == pageElementTrace source
           && pageElementCell target == pageElementCell source} @-}
observedIdentityObject :: Atlas a s d o f -> PageElement s object
  -> PageElement s (AtlasMappedObject IdentityAtlasObjectMap object)
observedIdentityObject = identityAtlasMorphismObject

{-@ reflect observedIdentityElement @-}
observedIdentityElement :: Atlas a s d o f -> SomePageElement s -> SomePageElement s
observedIdentityElement owner =
  mapPrimitiveElement identityAtlasObjectMap owner owner (identityAtlasMorphismObject owner)

{-@ observedIdentityRelated :: owner:Atlas a s d o f -> source:SomePageElement s
      -> target:{SomePageElement s | somePageElementPrecedes source target
           && somePageElementTransported source target}
      -> {result:Bool | result} @-}
observedIdentityRelated :: Atlas a s d o f -> SomePageElement s -> SomePageElement s -> Bool
observedIdentityRelated owner source target =
  identityAtlasMorphismPreservesArrow identityAtlasObjectMap owner source target `seq`
    (somePageElementPrecedes (observedIdentityElement owner source)
       (observedIdentityElement owner target)
      && somePageElementTransported (observedIdentityElement owner source)
         (observedIdentityElement owner target))

"""
PRIMITIVE_MORPHISM_PUBLIC_GUARDS = {
    'primitive identity preserves every occurrence field': r"""
{-@ proofGuard :: owner:Atlas a s d o f -> source:PageElement s object
      -> {target:PageElement s (AtlasMappedObject IdentityAtlasObjectMap object) |
           pageElementPage target /= pageElementPage source
           || pageElementPosition target /= pageElementPosition source
           || pageElementTrace target /= pageElementTrace source
           || pageElementCell target /= pageElementCell source} @-}
proofGuard :: Atlas a s d o f -> PageElement s object
  -> PageElement s (AtlasMappedObject IdentityAtlasObjectMap object)
proofGuard = observedIdentityObject
""",
    'primitive identity preserves normalized page arrows': r"""
{-@ proofGuard :: owner:Atlas a s d o f -> source:SomePageElement s
      -> target:{SomePageElement s | somePageElementPrecedes source target
           && somePageElementTransported source target}
      -> {result:Bool | not result} @-}
proofGuard :: Atlas a s d o f -> SomePageElement s -> SomePageElement s -> Bool
proofGuard = observedIdentityRelated
""",
    'primitive morphism observation retains stored naturality': r"""
{-@ proofGuard :: action:AtlasMorphismAction objectMap sa ta ss ts sd td so sf to tf
      -> sourceArrow:{PageElementArrow ss source target |
           Elements.pageElementTraceValid (atlasPageElements (atlasMorphismSource action)) (arrowSource sourceArrow)
           && Elements.pageElementTraceValid (atlasPageElements (atlasMorphismSource action)) (arrowTarget sourceArrow)}
      -> datum:{sd source | atlasAcceptsDatum (atlasMorphismSource action) (arrowSource sourceArrow) datum}
      -> {applyInsertion
          ((mapAtlasMorphismActionComponent action) (normalizeAtlasElement (atlasMorphismSource action) (arrowTarget sourceArrow)))
          (applyInsertion (mapAtlasData (atlasMorphismSource action) sourceArrow) datum)
        /= applyInsertion
          (mapAtlasData (atlasMorphismTarget action)
            (pageElementArrow
              (normalizeAtlasElement (atlasMorphismTarget action)
                ((mapAtlasMorphismActionObject action) (normalizeAtlasElement (atlasMorphismSource action) (arrowSource sourceArrow))))
              (normalizeAtlasElement (atlasMorphismTarget action)
                ((mapAtlasMorphismActionObject action) (normalizeAtlasElement (atlasMorphismSource action) (arrowTarget sourceArrow))))))
          (applyInsertion
            ((mapAtlasMorphismActionComponent action) (normalizeAtlasElement (atlasMorphismSource action) (arrowSource sourceArrow))) datum)} @-}
proofGuard :: AtlasMorphismAction m sa ta ss ts sd td so sf to tf
  -> PageElementArrow ss source target -> sd source -> ()
proofGuard = observedNaturality
""",
    'primitive morphism observation retains the normalized page law': r"""
{-@ proofGuard :: action:AtlasMorphismAction m sa ta ss ts sd td so sf to tf
      -> source:SomePageElement ss
      -> target:{SomePageElement ss | somePageElementPrecedes source target
           && somePageElementTransported source target}
      -> {result:Bool | result} @-}
proofGuard :: AtlasMorphismAction m sa ta ss ts sd td so sf to tf
  -> SomePageElement ss -> SomePageElement ss -> Bool
proofGuard action source target = not (observedRelated action source target)
""",
    'primitive morphism assembly retains its source owner': r"""
{-@ proofGuard :: action:AtlasMorphismAction m sa ta ss ts sd td so sf to tf
      -> {owner:Atlas sa ss sd so sf | owner /= atlasMorphismSource action} @-}
proofGuard :: AtlasMorphismAction m sa ta ss ts sd td so sf to tf
  -> Atlas sa ss sd so sf
proofGuard action = atlasMorphismSource (rebuildAction action)
""",
    'primitive morphism assembly retains its target owner': r"""
{-@ proofGuard :: action:AtlasMorphismAction m sa ta ss ts sd td so sf to tf
      -> {owner:Atlas ta ts td to tf | owner /= atlasMorphismTarget action} @-}
proofGuard :: AtlasMorphismAction m sa ta ss ts sd td so sf to tf
  -> Atlas ta ts td to tf
proofGuard action = atlasMorphismTarget (rebuildAction action)
""",
    'primitive morphism assembly retains its object callback': r"""
{-@ proofGuard :: action:AtlasMorphismAction m sa ta ss ts sd td so sf to tf
      -> source:PageElement ss object
      -> {target:PageElement ts (AtlasMappedObject m object) |
           target /= mapAtlasMorphismActionObject action source} @-}
proofGuard :: AtlasMorphismAction m sa ta ss ts sd td so sf to tf
  -> PageElement ss object -> PageElement ts (AtlasMappedObject m object)
proofGuard action source = mapAtlasMorphismActionObject (rebuildAction action) source
""",
    'primitive morphism assembly retains its forward component': r"""
{-@ proofGuard :: action:AtlasMorphismAction m sa ta ss ts sd td so sf to tf
      -> source:PageElement ss object
      -> {applyInsertion (mapAtlasMorphismActionComponent (rebuildAction action) source) /= applyInsertion (mapAtlasMorphismActionComponent action source)} @-}
proofGuard :: AtlasMorphismAction m sa ta ss ts sd td so sf to tf
  -> PageElement ss object -> ()
proofGuard action source = mapAtlasMorphismActionComponent (rebuildAction action) source `seq` ()
""",
    'primitive morphism assembly retains its entire partial inverse': r"""
{-@ proofGuard :: action:AtlasMorphismAction m sa ta ss ts sd td so sf to tf
      -> source:PageElement ss object
      -> {preimage (mapAtlasMorphismActionComponent (rebuildAction action) source) /= preimage (mapAtlasMorphismActionComponent action source)} @-}
proofGuard :: AtlasMorphismAction m sa ta ss ts sd td so sf to tf
  -> PageElement ss object -> ()
proofGuard action source = mapAtlasMorphismActionComponent (rebuildAction action) source `seq` ()
""",
    'primitive morphism normalization retains its source owner': r"""
{-@ proofGuard :: action:AtlasMorphismAction m sa ta ss ts sd td so sf to tf
      -> {owner:Atlas sa ss sd so sf | owner /= atlasMorphismSource action} @-}
proofGuard :: AtlasMorphismAction m sa ta ss ts sd td so sf to tf
  -> Atlas sa ss sd so sf
proofGuard action = atlasMorphismSource (observedNormalizedAction action)
""",
    'primitive morphism normalization retains its target owner': r"""
{-@ proofGuard :: action:AtlasMorphismAction m sa ta ss ts sd td so sf to tf
      -> {owner:Atlas ta ts td to tf | owner /= atlasMorphismTarget action} @-}
proofGuard :: AtlasMorphismAction m sa ta ss ts sd td so sf to tf
  -> Atlas ta ts td to tf
proofGuard action = atlasMorphismTarget (observedNormalizedAction action)
""",
    'primitive morphism normalization retains its object callback': r"""
{-@ proofGuard :: action:AtlasMorphismAction m sa ta ss ts sd td so sf to tf
      -> source:PageElement ss object
      -> {target:PageElement ts (AtlasMappedObject m object) |
           target /= normalizeAtlasElement (atlasMorphismTarget action)
             (mapAtlasMorphismActionObject action
               (normalizeAtlasElement (atlasMorphismSource action) source))} @-}
proofGuard :: AtlasMorphismAction m sa ta ss ts sd td so sf to tf
  -> PageElement ss object -> PageElement ts (AtlasMappedObject m object)
proofGuard = observedNormalizedObject
""",
    'primitive morphism normalization retains its forward component': r"""
{-@ proofGuard :: action:AtlasMorphismAction m sa ta ss ts sd td so sf to tf
      -> source:PageElement ss object
      -> {applyInsertion (observedNormalizedComponent action source) /= applyInsertion (mapAtlasMorphismActionComponent action (normalizeAtlasElement (atlasMorphismSource action) source))} @-}
proofGuard :: AtlasMorphismAction m sa ta ss ts sd td so sf to tf
  -> PageElement ss object -> ()
proofGuard action source = observedNormalizedComponent action source `seq` ()
""",
    'primitive morphism normalization retains its entire partial inverse': r"""
{-@ proofGuard :: action:AtlasMorphismAction m sa ta ss ts sd td so sf to tf
      -> source:PageElement ss object
      -> {preimage (observedNormalizedComponent action source) /= preimage (mapAtlasMorphismActionComponent action (normalizeAtlasElement (atlasMorphismSource action) source))} @-}
proofGuard :: AtlasMorphismAction m sa ta ss ts sd td so sf to tf
  -> PageElement ss object -> ()
proofGuard action source = observedNormalizedComponent action source `seq` ()
""",

    'primitive morphism normalization uses idempotent Atlas coherence': r"""
{-@ proofGuard :: owner:Atlas a s d o f -> source:PageElement s object
      -> {normalizeAtlasElement owner (normalizeAtlasElement owner source)
           /= normalizeAtlasElement owner source} @-}
proofGuard :: Atlas a s d o f -> PageElement s object -> ()
proofGuard = observedNormalizationIdempotent
""",

    'primitive morphism validity retains its target owner': r"""
{-@ proofGuard :: action:AtlasMorphismAction m sa ta ss ts sd td so sf to tf
      -> source:{PageElement ss object |
           Elements.pageElementTraceValid (atlasPageElements (atlasMorphismSource action)) source}
      -> {target:PageElement ts (AtlasMappedObject m object) |
           not (Elements.pageElementTraceValid (atlasPageElements (atlasMorphismTarget action)) target)} @-}
proofGuard :: AtlasMorphismAction m sa ta ss ts sd td so sf to tf
  -> PageElement ss object -> PageElement ts (AtlasMappedObject m object)
proofGuard = observedValidObject
""",
    'primitive morphism validity survives normalization': r"""
{-@ proofGuard :: action:AtlasMorphismAction m sa ta ss ts sd td so sf to tf
      -> source:{PageElement ss object |
           Elements.pageElementTraceValid (atlasPageElements (atlasMorphismSource action)) source}
      -> {target:PageElement ts (AtlasMappedObject m object) |
           not (Elements.pageElementTraceValid (atlasPageElements (atlasMorphismTarget action)) target)} @-}
proofGuard :: AtlasMorphismAction m sa ta ss ts sd td so sf to tf
  -> PageElement ss object -> PageElement ts (AtlasMappedObject m object)
proofGuard = observedValidNormalizedObject
""",

    'primitive morphism validity requires an accepted source': r"""
{-@ proofGuard :: action:AtlasMorphismAction m sa ta ss ts sd td so sf to tf
      -> source:PageElement ss object
      -> {target:PageElement ts (AtlasMappedObject m object) |
           Elements.pageElementTraceValid (atlasPageElements (atlasMorphismTarget action)) target} @-}
proofGuard :: AtlasMorphismAction m sa ta ss ts sd td so sf to tf
  -> PageElement ss object -> PageElement ts (AtlasMappedObject m object)
proofGuard = observedValidObject
""",
    'primitive morphism validity rejects an unrelated target owner': r"""
{-@ proofGuard :: action:AtlasMorphismAction m sa ta ss ts sd td so sf to tf
      -> otherOwner:Atlas ta ts td to tf
      -> source:{PageElement ss object |
           Elements.pageElementTraceValid (atlasPageElements (atlasMorphismSource action)) source}
      -> {target:PageElement ts (AtlasMappedObject m object) |
           Elements.pageElementTraceValid (atlasPageElements otherOwner) target} @-}
proofGuard :: AtlasMorphismAction m sa ta ss ts sd td so sf to tf
  -> Atlas ta ts td to tf -> PageElement ss object -> PageElement ts (AtlasMappedObject m object)
proofGuard action _ source = observedValidObject action source
""",

    'primitive morphism components reject unaccepted source data': r"""
{-@ proofGuard :: action:AtlasMorphismAction m sa ta ss ts sd td so sf to tf
      -> source:PageElement ss object -> datum:sd object
      -> {result:td (AtlasMappedObject m object) |
           atlasAcceptsDatum (atlasMorphismTarget action) (mapAtlasMorphismActionObject action source) result} @-}
proofGuard :: AtlasMorphismAction m sa ta ss ts sd td so sf to tf
  -> PageElement ss object -> sd object -> td (AtlasMappedObject m object)
proofGuard = observedAcceptedForward
""",
    'primitive morphism components retain target membership': r"""
{-@ proofGuard :: action:AtlasMorphismAction m sa ta ss ts sd td so sf to tf
      -> source:PageElement ss object
      -> datum:{sd object | atlasAcceptsDatum (atlasMorphismSource action) source datum}
      -> {result:td (AtlasMappedObject m object) |
           not (atlasAcceptsDatum (atlasMorphismTarget action) (mapAtlasMorphismActionObject action source) result)} @-}
proofGuard :: AtlasMorphismAction m sa ta ss ts sd td so sf to tf
  -> PageElement ss object -> sd object -> td (AtlasMappedObject m object)
proofGuard = observedAcceptedForward
""",
    'primitive morphism inverse requires target membership': r"""
{-@ proofGuard :: action:AtlasMorphismAction m sa ta ss ts sd td so sf to tf
      -> source:PageElement ss object -> datum:td (AtlasMappedObject m object)
      -> Maybe ({result:sd object | atlasAcceptsDatum (atlasMorphismSource action) source result}) @-}
proofGuard :: AtlasMorphismAction m sa ta ss ts sd td so sf to tf
  -> PageElement ss object -> td (AtlasMappedObject m object) -> Maybe (sd object)
proofGuard = observedAcceptedInverse
""",
    'primitive morphism inverse retains source membership': r"""
{-@ proofGuard :: action:AtlasMorphismAction m sa ta ss ts sd td so sf to tf
      -> source:PageElement ss object
      -> datum:{td (AtlasMappedObject m object) |
           atlasAcceptsDatum (atlasMorphismTarget action) (mapAtlasMorphismActionObject action source) datum}
      -> {result:Bool | result} @-}
proofGuard :: AtlasMorphismAction m sa ta ss ts sd td so sf to tf
  -> PageElement ss object -> td (AtlasMappedObject m object) -> Bool
proofGuard action source datum = case observedAcceptedInverse action source datum of
  Nothing -> True
  Just result -> not (atlasAcceptsDatum (atlasMorphismSource action) source result)
""",
    'primitive morphism components cannot use an unrelated target owner': r"""
{-@ proofGuard :: action:AtlasMorphismAction m sa ta ss ts sd td so sf to tf
      -> other:Atlas ta ts td to tf -> source:PageElement ss object
      -> datum:{sd object | atlasAcceptsDatum (atlasMorphismSource action) source datum}
      -> {result:td (AtlasMappedObject m object) |
           atlasAcceptsDatum other (mapAtlasMorphismActionObject action source) result} @-}
proofGuard :: AtlasMorphismAction m sa ta ss ts sd td so sf to tf
  -> Atlas ta ts td to tf -> PageElement ss object -> sd object -> td (AtlasMappedObject m object)
proofGuard action _ = observedAcceptedForward action
""",

}
def primitive_naturality_domain_guard(drop_validity=False):
    """Keep the naturality conclusion; remove exactly one owning-domain premise."""
    source = PRIMITIVE_MORPHISM_PUBLIC_SOURCE
    start = source.index("{-@ observedNaturality ::")
    end = source.index("\n\n{-@ observedRelated", start)
    guard = source[start:end].replace("observedNaturality", "proofGuard")
    guard = guard.replace("proofGuard = atlasMorphismActionNaturality", "proofGuard = observedNaturality")
    if drop_validity:
        guard = re.sub(r"sourceArrow:\{PageElementArrow ss source target \|.*?\}",
                       "sourceArrow:PageElementArrow ss source target", guard, count=1, flags=re.S)
    else:
        guard = guard.replace(
            "datum:{sd source | atlasAcceptsDatum (atlasMorphismSource action) (arrowSource sourceArrow) datum}",
            "datum:sd source")
    return guard

PRIMITIVE_MORPHISM_PUBLIC_GUARDS.update({
    "primitive morphism naturality requires valid owning arrows": primitive_naturality_domain_guard(True),
    "primitive morphism naturality requires accepted source data": primitive_naturality_domain_guard(),
})

PRIMITIVE_MORPHISM_STORAGE_GUARDS = {
    'primitive morphism storage rejects an uncertified replacement component': r"""
proofGuard :: AtlasMorphismAction m sa ta ss ts sd td so sf to tf
  -> (forall object. PageElement ss object -> DomanialInsertion (sd object) (td (AtlasMappedObject m object)))
  -> AtlasMorphismAction m sa ta ss ts sd td so sf to tf
proofGuard action component = action { actionComponent = component }
""",
    'primitive morphism storage rejects an uncertified replacement object map': r"""
proofGuard :: AtlasMorphismAction m sa ta ss ts sd td so sf to tf
  -> (forall object. PageElement ss object -> PageElement ts (AtlasMappedObject m object))
  -> AtlasMorphismAction m sa ta ss ts sd td so sf to tf
proofGuard action mapObject = action { actionObject = mapObject }
""",
}

def primitive_morphism_without_validity_guard():
    """Drop only owning validity; retain every other constructor certificate."""
    source = PRIMITIVE_MORPHISM_SOURCE.read_text()
    match = re.search(r"\{-@\natlasMorphismAction\b.*?@-\}", source, re.S)
    if match is None:
        raise ValueError("Primitive morphism constructor contract is missing")
    annotation = match.group()
    target_contract = (
        "{target:PageElement targetScope (AtlasMappedObject objectMap sourceObject) |\n"
        "            MorphismCellValid sourceAtlas source => MorphismCellValid targetAtlas target}"
    )
    if annotation.count(target_contract) != 1:
        raise ValueError("Primitive object-validity contract changed; update its rejection check")
    annotation = annotation.replace(target_contract,
        "PageElement targetScope (AtlasMappedObject objectMap sourceObject)")
    annotation = annotation.replace("atlasMorphismAction", "proofGuard", 1)
    signature_start = source.index("\natlasMorphismAction\n  ::", match.end())
    signature_end = source.index("\natlasMorphismAction\n  objectMapWitness", signature_start)
    signature = source[signature_start:signature_end].replace("atlasMorphismAction", "proofGuard", 1)
    return annotation + signature + "\nproofGuard = atlasMorphismAction\n"

PRIMITIVE_MORPHISM_STORAGE_GUARDS[
    'primitive morphism validity is required at construction'
] = primitive_morphism_without_validity_guard()


def primitive_morphism_without_component_membership_guard(drop_source=False):
    """Keep both morphism laws; omit one component carrier's membership."""
    source = PRIMITIVE_MORPHISM_SOURCE.read_text()
    match = re.search(r"\{-@\natlasMorphismAction\b.*?@-\}", source, re.S)
    if match is None:
        raise ValueError("Primitive morphism constructor contract is missing")
    annotation = match.group()
    if drop_source:
        before = "({datum:sourceCellData sourceObject | atlasAcceptsDatum sourceAtlas source datum})"
        after = "(sourceCellData sourceObject)"
    else:
        before = ("({datum:targetCellData (AtlasMappedObject objectMap sourceObject) |\n"
                  "                 atlasAcceptsDatum targetAtlas (mapObject source) datum})")
        after = "(targetCellData (AtlasMappedObject objectMap sourceObject))"
    if annotation.count(before) != 1:
        raise ValueError("Primitive component membership changed; update its rejection check")
    annotation = annotation.replace(before, after).replace("atlasMorphismAction", "proofGuard", 1)
    start = source.index("\natlasMorphismAction\n  ::", match.end())
    end = source.index("\natlasMorphismAction\n  objectMapWitness", start)
    signature = source[start:end].replace("atlasMorphismAction", "proofGuard", 1)
    return annotation + signature + "\nproofGuard = atlasMorphismAction\n"

PRIMITIVE_MORPHISM_STORAGE_GUARDS.update({
    "primitive morphism construction requires component target membership":
        primitive_morphism_without_component_membership_guard(),
    "primitive morphism construction requires inverse source membership":
        primitive_morphism_without_component_membership_guard(True),
})


TOTAL_MAP_PUBLIC_SOURCE = r"""
{-# LANGUAGE CPP #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeFamilies #-}
#include "LiquidPlugin.h"
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--higherorder" @-}
module TotalMapPublicGuard where
import Atlas (AtlasObject)
import AtlasMap (AtlasMap, atlasMapRegionValid, atlasMapAcceptsDatum)
import PageElements.Structure (PageElement)
import TotalAtlasMap

{-@ selectedAt :: owner:AtlasMap (AtlasObject a s d)
      -> (forall cell. region:{PageElement s cell | atlasMapRegionValid owner region}
            -> SingletonDominion ({datum:d cell | atlasMapAcceptsDatum owner region datum}))
      -> PageElement s object -> {result:Bool | result} @-}
selectedAt :: AtlasMap (AtlasObject a s d)
  -> (forall cell. PageElement s cell -> SingletonDominion (d cell))
  -> PageElement s object -> Bool
selectedAt owner singleton region =
  if atlasMapRegionValid owner region
    then atlasMapAcceptsDatum owner region (singletonDominionValue (singleton region))
    else True

{-@ selectedAccepted :: TotalAtlasMap (AtlasObject a s d) -> PageElement s object
      -> {result:Bool | result} @-}
selectedAccepted :: TotalAtlasMap (AtlasObject a s d) -> PageElement s object -> Bool
selectedAccepted value = withTotalAtlasMap value selectedAt

{-@ uniqueAt :: owner:AtlasMap (AtlasObject a s d)
      -> (forall cell. region:{PageElement s cell | atlasMapRegionValid owner region}
            -> SingletonDominion ({datum:d cell | atlasMapAcceptsDatum owner region datum}))
      -> PageElement s object -> d object -> () @-}
uniqueAt :: AtlasMap (AtlasObject a s d)
  -> (forall cell. PageElement s cell -> SingletonDominion (d cell))
  -> PageElement s object -> d object -> ()
uniqueAt owner singleton region candidate =
  if atlasMapRegionValid owner region && atlasMapAcceptsDatum owner region candidate
    then singletonDominionUnique (singleton region) candidate else ()

acceptedUnique :: TotalAtlasMap (AtlasObject a s d) -> PageElement s object -> d object -> ()
acceptedUnique value = withTotalAtlasMap value uniqueAt

{-@ exactSingleton :: selected:value
      -> (candidate:value -> {candidate == selected})
      -> {result:SingletonDominion value | singletonDominionValue result == selected} @-}
exactSingleton :: value -> (value -> ()) -> SingletonDominion value
exactSingleton = singletonDominion

{-@ restrictedSingleton :: SingletonDominion {value:Int | value == 7} @-}
restrictedSingleton :: SingletonDominion Int
restrictedSingleton = singletonDominion 7 (\_ -> ())

rebuildTotal :: TotalAtlasMap (AtlasObject a s d) -> TotalAtlasMap (AtlasObject a s d)
rebuildTotal value = withTotalAtlasMap value totalAtlasMap
"""
TOTAL_MAP_PUBLIC_GUARDS = {
    "total map singleton construction rejects a dummy uniqueness proof": r"""
proofGuard :: Int -> SingletonDominion Int
proofGuard selected = singletonDominion selected (\_ -> ())
""",
    "total map singleton construction retains its selected value": r"""
{-@ proofGuard :: selected:value
      -> (candidate:value -> {candidate == selected})
      -> {result:SingletonDominion value | singletonDominionValue result /= selected} @-}
proofGuard :: value -> (value -> ()) -> SingletonDominion value
proofGuard = singletonDominion
""",
    "total map singleton lookup requires an owning final region": r"""
proofGuard :: TotalAtlasMap (AtlasObject a s d) -> PageElement s object -> d object
proofGuard value region = withTotalAtlasMap value $ \_ singleton ->
  singletonDominionValue (singleton region)
""",
    "total map singleton lookup cannot substitute another owner": r"""
proofGuard :: TotalAtlasMap (AtlasObject a s d) -> AtlasMap (AtlasObject a s d)
  -> PageElement s object -> Maybe (d object)
proofGuard value other region = withTotalAtlasMap value $ \_ singleton ->
  if atlasMapRegionValid other region
    then Just (singletonDominionValue (singleton region)) else Nothing
""",
    "total map singleton lookup cannot return rejected data": r"""
{-@ proofGuard :: TotalAtlasMap (AtlasObject a s d) -> PageElement s object
      -> {result:Bool | result} @-}
proofGuard :: TotalAtlasMap (AtlasObject a s d) -> PageElement s object -> Bool
proofGuard value region = withTotalAtlasMap value $ \owner singleton ->
  if atlasMapRegionValid owner region
    then not (atlasMapAcceptsDatum owner region (singletonDominionValue (singleton region)))
    else True
""",
    "total map singleton uniqueness requires an accepted candidate": r"""
proofGuard :: TotalAtlasMap (AtlasObject a s d) -> PageElement s object -> d object -> ()
proofGuard value region candidate = withTotalAtlasMap value $ \owner singleton ->
  if atlasMapRegionValid owner region
    then singletonDominionUnique (singleton region) candidate else ()
""",
    "total map construction requires accepted singleton witnesses": r"""
proofGuard :: AtlasMap (AtlasObject a s d)
  -> (forall object. PageElement s object -> SingletonDominion (d object))
  -> TotalAtlasMap (AtlasObject a s d)
proofGuard = totalAtlasMap
""",
}


RANKED_DATA_PUBLIC_SOURCE = r"""
{-# LANGUAGE CPP #-}
#include "LiquidPlugin.h"
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}
{-@ LIQUID "--higherorder" @-}
module RankedDataPublicGuard where
import RankedDominionAtlas.Data
import Dominion (Dominion, dominionCoherence, unrank)
import Numeric.Natural (Natural)

{-@ observedRegionRoundTrip :: owner:Dominion value -> selected:Natural
      -> datum:{RankedDominionCellData value object | regionAccepts owner selected datum}
      -> {regionUnrank owner selected (regionRank datum) == Just datum} @-}
observedRegionRoundTrip :: Dominion value -> Natural -> RankedDominionCellData value object -> ()
observedRegionRoundTrip owner selected datum =
  dominionCoherence (regionDominion owner selected) datum

{-@ observedExtentRoundTrip :: owner:Dominion value
      -> datum:{RankedDominionCellData value object | extentAccepts datum}
      -> {extentUnrank owner (extentRank owner datum) == Just datum} @-}
observedExtentRoundTrip :: Dominion value -> RankedDominionCellData value object -> ()
observedExtentRoundTrip owner datum = dominionCoherence (extentDominion owner) datum

{-@ regionDecoder :: owner:Dominion value -> selected:Natural -> index:Natural
      -> {result:Maybe (RankedDominionCellData value object) | result == regionUnrank owner selected index} @-}
regionDecoder :: Dominion value -> Natural -> Natural -> Maybe (RankedDominionCellData value object)
regionDecoder owner selected index = unrank (regionDominion owner selected) index

{-@ extentDecoder :: owner:Dominion value -> index:Natural
      -> {result:Maybe (RankedDominionCellData value object) | result == extentUnrank owner index} @-}
extentDecoder :: Dominion value -> Natural -> Maybe (RankedDominionCellData value object)
extentDecoder owner index = unrank (extentDominion owner) index

{-@ decodedAccepted :: owner:Dominion value -> selected:Natural -> Natural -> {result:Bool | result} @-}
decodedAccepted :: Dominion value -> Natural -> Natural -> Bool
decodedAccepted owner selected index =
  case unrank (regionDominion owner selected) index of
    Nothing -> True
    Just datum -> regionAccepts owner selected datum
"""
RANKED_DATA_PUBLIC_GUARDS = {
    "ranked region Dominion rejects extent-tagged data": r"""
proofGuard :: Dominion value -> Natural -> value -> ()
proofGuard owner selected value =
  observedRegionRoundTrip owner selected (RankedDominionExtentDatum value)
""",
    "ranked region Dominion requires the selected rank": r"""
proofGuard :: Dominion value -> Natural -> value -> ()
proofGuard owner selected value =
  observedRegionRoundTrip owner selected (RankedDominionRegionDatum value)
""",
    "ranked extent Dominion rejects region-tagged data": r"""
proofGuard :: Dominion value -> value -> ()
proofGuard owner value = observedExtentRoundTrip owner (RankedDominionRegionDatum value)
""",
    "ranked region decoding cannot return rejected data": r"""
{-@ proofGuard :: owner:Dominion value -> selected:Natural -> Natural -> {result:Bool | result} @-}
proofGuard :: Dominion value -> Natural -> Natural -> Bool
proofGuard owner selected index =
  case unrank (regionDominion owner selected) index of
    Nothing -> True
    Just datum -> not (regionAccepts owner selected datum)
""",
    "ranked region Dominion preserves its exact decoder": r"""
{-@ proofGuard :: owner:Dominion value -> selected:Natural -> index:Natural
      -> {result:Maybe (RankedDominionCellData value object) | result /= regionUnrank owner selected index} @-}
proofGuard :: Dominion value -> Natural -> Natural -> Maybe (RankedDominionCellData value object)
proofGuard owner selected index = regionDecoder owner selected index
""",
    "ranked extent Dominion preserves its raw off-image decoder": r"""
{-@ proofGuard :: owner:Dominion value -> index:Natural
      -> {result:Maybe (RankedDominionCellData value object) | result /= extentUnrank owner index} @-}
proofGuard :: Dominion value -> Natural -> Maybe (RankedDominionCellData value object)
proofGuard owner index = extentDecoder owner index
""",
}


CHAINED_DATA_PUBLIC_SOURCE = r"""
{-# LANGUAGE CPP #-}
#include "LiquidPlugin.h"
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--higherorder" @-}
module ChainedDataPublicGuard where
import Chain (Chain)
import ChainedDominionAtlas.Data
import Dominion (Dominion, dominionCoherence, unrank)
import Numeric.Natural (Natural)

{-@ observedRegionRoundTrip :: owner:Chain value -> selected:value
      -> datum:{ChainedDominionCellData value object | regionAccepts owner selected datum} -> () @-}
observedRegionRoundTrip :: Chain value -> value -> ChainedDominionCellData value object -> ()
observedRegionRoundTrip owner selected datum =
  dominionCoherence (regionDominion owner selected) datum

{-@ observedExtentRoundTrip :: owner:Dominion value
      -> datum:{ChainedDominionCellData value object | extentAccepts datum} -> () @-}
observedExtentRoundTrip :: Dominion value -> ChainedDominionCellData value object -> ()
observedExtentRoundTrip owner datum = dominionCoherence (extentDominion owner) datum

{-@ regionDecoder :: owner:Chain value -> selected:value -> index:Natural
      -> {result:Maybe (ChainedDominionCellData value object) | result == regionUnrank owner selected index} @-}
regionDecoder :: Chain value -> value -> Natural -> Maybe (ChainedDominionCellData value object)
regionDecoder owner selected index = unrank (regionDominion owner selected) index

{-@ extentDecoder :: owner:Dominion value -> index:Natural
      -> {result:Maybe (ChainedDominionCellData value object) | result == extentUnrank owner index} @-}
extentDecoder :: Dominion value -> Natural -> Maybe (ChainedDominionCellData value object)
extentDecoder owner index = unrank (extentDominion owner) index

{-@ decodedAccepted :: owner:Chain value -> selected:value -> Natural -> {result:Bool | result} @-}
decodedAccepted :: Chain value -> value -> Natural -> Bool
decodedAccepted owner selected index =
  case unrank (regionDominion owner selected) index of
    Nothing -> True
    Just datum -> regionAccepts owner selected datum

{-@ inverseAccepted :: owner:Chain value -> selected:value
      -> ChainedDominionCellData value target -> {result:Bool | result} @-}
inverseAccepted :: Chain value -> value -> ChainedDominionCellData value target -> Bool
inverseAccepted owner selected target =
  case extentToRegion owner selected target of
    Nothing -> True
    Just source -> regionAccepts owner selected source
"""
CHAINED_DATA_PUBLIC_GUARDS = {
    "chained region Dominion rejects extent-tagged data": r"""
proofGuard :: Chain value -> value -> ()
proofGuard owner selected =
  observedRegionRoundTrip owner selected (ChainedDominionExtentDatum selected)
""",
    "chained region Dominion requires the selected chain value": r"""
proofGuard :: Chain value -> value -> value -> ()
proofGuard owner selected other =
  observedRegionRoundTrip owner selected (ChainedDominionRegionDatum other)
""",
    "chained extent Dominion rejects region-tagged data": r"""
proofGuard :: Dominion value -> value -> ()
proofGuard owner value =
  observedExtentRoundTrip owner (ChainedDominionRegionDatum value)
""",
    "chained region inverse cannot return rejected data": r"""
{-@ proofGuard :: owner:Chain value -> selected:value
      -> ChainedDominionCellData value target -> {result:Bool | result} @-}
proofGuard :: Chain value -> value -> ChainedDominionCellData value target -> Bool
proofGuard owner selected target =
  case extentToRegion owner selected target of
    Nothing -> True
    Just source -> not (regionAccepts owner selected source)
""",
}


RANKED_ACTION_PUBLIC_SOURCE = r"""
{-# LANGUAGE CPP #-}
#include "LiquidPlugin.h"
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--higherorder" @-}
module RankedActionPublicGuard where
import Dominion (Dominion)
import Numeric.Natural (Natural)
import RankedDominionAtlas.Data (RankedDominionCellData)
import RankedDominionAtlas.Action
import DomanialInsertion (applyInsertion, preimage)
import PageElements.Structure (PageElement, normalizePageElementAt)

{-@ observedCellForward :: owner:Dominion value -> source:RankedDominionCell
      -> target:{RankedDominionCell | cellPrecedes source target}
      -> datum:{RankedDominionCellData value s | cellAccepts owner source datum}
      -> {result:RankedDominionCellData value t |
           cellAccepts owner target result && result == cellMap owner source target datum} @-}
observedCellForward :: Dominion value -> RankedDominionCell -> RankedDominionCell
  -> RankedDominionCellData value source -> RankedDominionCellData value target
observedCellForward owner source target datum =
  applyInsertion (cellInsertion owner source target) datum

{-@ observedCellInverse :: owner:Dominion value -> source:RankedDominionCell
      -> target:{RankedDominionCell | cellPrecedes source target}
      -> datum:{RankedDominionCellData value t | cellAccepts owner target datum}
      -> {result:Maybe ({candidate:RankedDominionCellData value s | cellAccepts owner source candidate}) |
           result == cellPreimage owner source target datum} @-}
observedCellInverse :: Dominion value -> RankedDominionCell -> RankedDominionCell
  -> RankedDominionCellData value target -> Maybe (RankedDominionCellData value source)
observedCellInverse owner source target datum =
  preimage (cellInsertion owner source target) datum

{-@ observedRawIdentity :: owner:Dominion value -> cell:RankedDominionCell
      -> datum:RankedDominionCellData value object
      -> {cellMap owner cell cell datum == datum && cellPreimage owner cell cell datum == Just datum} @-}
observedRawIdentity :: Dominion value -> RankedDominionCell -> RankedDominionCellData value object -> ()
observedRawIdentity = cellIdentity

{-@ observedRawComposition :: owner:Dominion value -> source:RankedDominionCell
      -> middle:{RankedDominionCell | cellPrecedes source middle}
      -> target:{RankedDominionCell | cellPrecedes middle target}
      -> datum:RankedDominionCellData value object
      -> {cellMap owner middle target (cellMap owner source middle datum) == cellMap owner source target datum} @-}
observedRawComposition :: Dominion value -> RankedDominionCell -> RankedDominionCell
  -> RankedDominionCell -> RankedDominionCellData value object -> ()
observedRawComposition = cellComposition

{-@ observedRawInverseComposition :: owner:Dominion value -> source:RankedDominionCell
      -> middle:{RankedDominionCell | cellPrecedes source middle}
      -> target:{RankedDominionCell | cellPrecedes middle target}
      -> datum:RankedDominionCellData value object
      -> {composedCellPreimage owner source middle target datum == cellPreimage owner source target datum} @-}
observedRawInverseComposition :: Dominion value -> RankedDominionCell -> RankedDominionCell
  -> RankedDominionCell -> RankedDominionCellData value object -> ()
observedRawInverseComposition = cellInverseComposition
"""
RANKED_ACTION_PUBLIC_GUARDS = {
    "ranked action cannot map the extent into a region": r"""
{-@ proofGuard :: owner:Dominion value -> selected:Natural
      -> datum:{RankedDominionCellData value s | cellAccepts owner ExtentCell datum}
      -> RankedDominionCellData value t @-}
proofGuard :: Dominion value -> Natural -> RankedDominionCellData value source -> RankedDominionCellData value target
proofGuard owner selected = observedCellForward owner ExtentCell (RegionCell selected)
""",
    "ranked action cannot connect unrelated regions": r"""
{-@ proofGuard :: owner:Dominion value -> first:Natural -> second:Natural
      -> datum:{RankedDominionCellData value s | cellAccepts owner (RegionCell first) datum}
      -> RankedDominionCellData value t @-}
proofGuard :: Dominion value -> Natural -> Natural -> RankedDominionCellData value source -> RankedDominionCellData value target
proofGuard owner first second = observedCellForward owner (RegionCell first) (RegionCell second)
""",
    "ranked action requires an accepted source datum": r"""
{-@ proofGuard :: owner:Dominion value -> source:RankedDominionCell
      -> target:{RankedDominionCell | cellPrecedes source target}
      -> RankedDominionCellData value s -> RankedDominionCellData value t @-}
proofGuard :: Dominion value -> RankedDominionCell -> RankedDominionCell
  -> RankedDominionCellData value source -> RankedDominionCellData value target
proofGuard = observedCellForward
""",
    "ranked action inverse cannot return rejected source data": r"""
{-@ proofGuard :: owner:Dominion value -> source:RankedDominionCell
      -> target:{RankedDominionCell | cellPrecedes source target}
      -> datum:{RankedDominionCellData value t | cellAccepts owner target datum}
      -> {result:Bool | result} @-}
proofGuard :: Dominion value -> RankedDominionCell -> RankedDominionCell
  -> RankedDominionCellData value target -> Bool
proofGuard owner source target datum =
  case observedCellInverse owner source target datum of
    Nothing -> True
    Just result -> not (cellAccepts owner source result)
""",
    "ranked action identity retains the exact datum": r"""
{-@ proofGuard :: owner:Dominion value -> cell:RankedDominionCell
      -> datum:RankedDominionCellData value object
      -> {cellMap owner cell cell datum /= datum} @-}
proofGuard :: Dominion value -> RankedDominionCell -> RankedDominionCellData value object -> ()
proofGuard = cellIdentity
""",
    "ranked action composition retains the exact forward map": r"""
{-@ proofGuard :: owner:Dominion value -> source:RankedDominionCell
      -> middle:{RankedDominionCell | cellPrecedes source middle}
      -> target:{RankedDominionCell | cellPrecedes middle target}
      -> datum:RankedDominionCellData value object
      -> {cellMap owner middle target (cellMap owner source middle datum) /= cellMap owner source target datum} @-}
proofGuard :: Dominion value -> RankedDominionCell -> RankedDominionCell
  -> RankedDominionCell -> RankedDominionCellData value object -> ()
proofGuard = cellComposition
""",
    "ranked action composition retains failed and successful inverses": r"""
{-@ proofGuard :: owner:Dominion value -> source:RankedDominionCell
      -> middle:{RankedDominionCell | cellPrecedes source middle}
      -> target:{RankedDominionCell | cellPrecedes middle target}
      -> datum:RankedDominionCellData value object
      -> {composedCellPreimage owner source middle target datum /= cellPreimage owner source target datum} @-}
proofGuard :: Dominion value -> RankedDominionCell -> RankedDominionCell
  -> RankedDominionCell -> RankedDominionCellData value object -> ()
proofGuard = cellInverseComposition
""",
    "ranked action normalization retains the selected cell": r"""
{-@ proofGuard :: occurrence:PageElement scope object
      -> {cellAt (normalizePageElementAt 1 2 occurrence) /= cellAt occurrence} @-}
proofGuard :: PageElement scope object -> ()
proofGuard = cellNormalization
""",
}


CHAINED_ACTION_PUBLIC_SOURCE = r"""
{-# LANGUAGE CPP #-}
#include "LiquidPlugin.h"
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--higherorder" @-}
module ChainedActionPublicGuard where
import Chain (Chain, chainPosition)
import ChainedDominionAtlas.Data (ChainedDominionCellData)
import ChainedDominionAtlas.Action
import DomanialInsertion (applyInsertion, preimage)
import PageElements.Structure (PageElement, normalizePageElementAt)

{-@ observedCellForward :: owner:Chain value -> source:ChainedDominionCell value
      -> target:{ChainedDominionCell value | cellPrecedes owner source target}
      -> datum:{ChainedDominionCellData value s | cellAccepts owner source datum}
      -> {result:ChainedDominionCellData value t |
           cellAccepts owner target result && result == cellMap owner source target datum} @-}
observedCellForward :: Chain value -> ChainedDominionCell value -> ChainedDominionCell value
  -> ChainedDominionCellData value source -> ChainedDominionCellData value target
observedCellForward owner source target datum =
  applyInsertion (cellInsertion owner source target) datum

{-@ observedCellInverse :: owner:Chain value -> source:ChainedDominionCell value
      -> target:{ChainedDominionCell value | cellPrecedes owner source target}
      -> datum:{ChainedDominionCellData value t | cellAccepts owner target datum}
      -> {result:Maybe ({candidate:ChainedDominionCellData value s | cellAccepts owner source candidate}) |
           result == cellPreimage owner source target datum} @-}
observedCellInverse :: Chain value -> ChainedDominionCell value -> ChainedDominionCell value
  -> ChainedDominionCellData value target -> Maybe (ChainedDominionCellData value source)
observedCellInverse owner source target datum =
  preimage (cellInsertion owner source target) datum
"""
CHAINED_ACTION_PUBLIC_GUARDS = {
    "chained action cannot map the extent into a region": r"""
{-@ proofGuard :: owner:Chain value -> selected:value
      -> datum:{ChainedDominionCellData value s | cellAccepts owner ExtentCell datum}
      -> ChainedDominionCellData value t @-}
proofGuard :: Chain value -> value -> ChainedDominionCellData value source -> ChainedDominionCellData value target
proofGuard owner selected = observedCellForward owner ExtentCell (RegionCell selected)
""",
    "chained action cannot connect unrelated regions": r"""
{-@ proofGuard :: owner:Chain value -> first:value -> second:value
      -> datum:{ChainedDominionCellData value s | cellAccepts owner (RegionCell first) datum}
      -> ChainedDominionCellData value t @-}
proofGuard :: Chain value -> value -> value -> ChainedDominionCellData value source -> ChainedDominionCellData value target
proofGuard owner first second = observedCellForward owner (RegionCell first) (RegionCell second)
""",
    "chained action requires an accepted source datum": r"""
{-@ proofGuard :: owner:Chain value -> source:ChainedDominionCell value
      -> target:{ChainedDominionCell value | cellPrecedes owner source target}
      -> ChainedDominionCellData value s -> ChainedDominionCellData value t @-}
proofGuard :: Chain value -> ChainedDominionCell value -> ChainedDominionCell value
  -> ChainedDominionCellData value source -> ChainedDominionCellData value target
proofGuard = observedCellForward
""",
    "chained action inverse cannot return rejected source data": r"""
{-@ proofGuard :: owner:Chain value -> source:ChainedDominionCell value
      -> target:{ChainedDominionCell value | cellPrecedes owner source target}
      -> datum:{ChainedDominionCellData value t | cellAccepts owner target datum}
      -> {result:Bool | result} @-}
proofGuard :: Chain value -> ChainedDominionCell value -> ChainedDominionCell value
  -> ChainedDominionCellData value target -> Bool
proofGuard owner source target datum =
  case observedCellInverse owner source target datum of
    Nothing -> True
    Just result -> not (cellAccepts owner source result)
""",
    "chained action identity retains the exact datum": r"""
{-@ proofGuard :: owner:Chain value -> cell:ChainedDominionCell value
      -> datum:{ChainedDominionCellData value object | cellAccepts owner cell datum}
      -> {cellMap owner cell cell datum /= datum} @-}
proofGuard :: Chain value -> ChainedDominionCell value -> ChainedDominionCellData value object -> ()
proofGuard = cellIdentity
""",
    "chained action composition retains the exact forward map": r"""
{-@ proofGuard :: owner:Chain value -> source:ChainedDominionCell value
      -> middle:{ChainedDominionCell value | cellPrecedes owner source middle}
      -> target:{ChainedDominionCell value | cellPrecedes owner middle target}
      -> datum:{ChainedDominionCellData value object | cellAccepts owner source datum}
      -> {cellMap owner middle target (cellMap owner source middle datum) /= cellMap owner source target datum} @-}
proofGuard :: Chain value -> ChainedDominionCell value -> ChainedDominionCell value
  -> ChainedDominionCell value -> ChainedDominionCellData value object -> ()
proofGuard = cellComposition
""",
    "chained action composition retains failed and successful inverses": r"""
{-@ proofGuard :: owner:Chain value -> source:ChainedDominionCell value
      -> middle:{ChainedDominionCell value | cellPrecedes owner source middle}
      -> target:{ChainedDominionCell value | cellPrecedes owner middle target}
      -> datum:{ChainedDominionCellData value object | cellAccepts owner target datum}
      -> {composedCellPreimage owner source middle target datum /= cellPreimage owner source target datum} @-}
proofGuard :: Chain value -> ChainedDominionCell value -> ChainedDominionCell value
  -> ChainedDominionCell value -> ChainedDominionCellData value object -> ()
proofGuard = cellInverseComposition
""",
    "chained action normalization retains the selected cell": r"""
{-@ proofGuard :: first:value -> owner:Chain value -> occurrence:PageElement scope object
      -> {chainedDominionCell first owner (normalizePageElementAt 1 2 occurrence)
           /= chainedDominionCell first owner occurrence} @-}
proofGuard :: value -> Chain value -> PageElement scope object -> ()
proofGuard = cellNormalization
""",
}

RANKED_PRESENTATION_PUBLIC_SOURCE = r"""
{-# LANGUAGE CPP #-}
#include "LiquidPlugin.h"
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--higherorder" @-}
module RankedPresentationPublicGuard where
import Chain (spine, spinePosition, chainPosition)
import Dominion (Dominion)
import Numeric.Natural (Natural)
import DatraOrdinal (finiteOrdinal)
import RankedDominionAtlas.Action (cellAt, spineRank, cellPrecedes, cellMap, cellPreimage)
import RankedDominionAtlas.Data (RankedDominionCellData)
import RankedDominionAtlas.Presentation
import DomanialInsertion (applyInsertion, preimage)
import Atlas (AtlasPresentation, atlasPresentationPagination, atlasPresentationAction, atlasActionDataAt)
import RankedDominionAtlas.Pagination (RankedDominionPaginationScope, rankedDominionPagination)
import Data.Proxy (Proxy)
import Pagination (Pagination, paginationPageElements)

{-@ opaque-reflect spine @-}
import Folio (folioLength, lastChain)
import PageElements (PageElements, pageElementsFolio, pageElementTraceValid)
import PageElements.Structure (PageElement, PageElementArrow, pageElementPage, pageElementPosition, arrowSource, arrowTarget)

{-@ observedPageForward :: category:{PageElements scope origin final |
           folioLength (pageElementsFolio category) == 2}
      -> owner:Dominion value
      -> arrow:{PageElementArrow scope source target |
           pageElementTraceValid category (arrowSource arrow)
           && pageElementTraceValid category (arrowTarget arrow)}
      -> datum:{RankedDominionCellData value source |
           rankedDominionAccepts owner (arrowSource arrow) datum}
      -> {result:RankedDominionCellData value target |
           rankedDominionAccepts owner (arrowTarget arrow) result
           && result == cellMap owner (cellAt (arrowSource arrow))
                (cellAt (arrowTarget arrow)) datum} @-}
observedPageForward :: PageElements scope origin final -> Dominion value
  -> PageElementArrow scope source target -> RankedDominionCellData value source
  -> RankedDominionCellData value target
observedPageForward category owner arrow datum =
  applyInsertion (rankedDominionDataMap category owner arrow) datum

{-@ observedPageInverse :: category:{PageElements scope origin final |
           folioLength (pageElementsFolio category) == 2}
      -> owner:Dominion value
      -> arrow:{PageElementArrow scope source target |
           pageElementTraceValid category (arrowSource arrow)
           && pageElementTraceValid category (arrowTarget arrow)}
      -> datum:{RankedDominionCellData value target |
           rankedDominionAccepts owner (arrowTarget arrow) datum}
      -> {result:Maybe ({candidate:RankedDominionCellData value source |
           rankedDominionAccepts owner (arrowSource arrow) candidate}) |
           result == cellPreimage owner (cellAt (arrowSource arrow))
                (cellAt (arrowTarget arrow)) datum} @-}
observedPageInverse :: PageElements scope origin final -> Dominion value
  -> PageElementArrow scope source target -> RankedDominionCellData value target
  -> Maybe (RankedDominionCellData value source)
observedPageInverse category owner arrow datum =
  preimage (rankedDominionDataMap category owner arrow) datum

{-@ observedPresentation :: pages:{Pagination scope origin Natural |
           folioLength (pageElementsFolio (paginationPageElements pages)) == 2
           && lastChain (pageElementsFolio (paginationPageElements pages)) == spine}
      -> owner:Dominion value
      -> {result:AtlasPresentation scope (RankedDominionCellData value) origin Natural |
           atlasPresentationPagination result == pages
           && atlasPresentationAction result == rankedDominionAction (paginationPageElements pages) owner
           && atlasActionDataAt (atlasPresentationAction result) == rankedDominionAt owner} @-}
observedPresentation :: Pagination scope origin Natural -> Dominion value
  -> AtlasPresentation scope (RankedDominionCellData value) origin Natural
observedPresentation = rankedDominionPresentation

{-@ observedPagination :: Proxy value
      -> {pages:Pagination (RankedDominionPaginationScope value) () Natural |
           folioLength (pageElementsFolio (paginationPageElements pages)) == 2
           && lastChain (pageElementsFolio (paginationPageElements pages)) == spine} @-}
observedPagination :: Proxy value -> Pagination (RankedDominionPaginationScope value) () Natural
observedPagination = rankedDominionPagination

{-@ observedSpinePosition :: value:Natural -> {chainPosition spine value == finiteOrdinal value} @-}
observedSpinePosition :: Natural -> ()
observedSpinePosition = spinePosition
"""
RANKED_PRESENTATION_PUBLIC_GUARDS = {
    "ranked presentation requires a two-page owning folio": r"""
{-@ proofGuard :: category:PageElements scope origin final
      -> arrow:{PageElementArrow scope source target |
           pageElementTraceValid category (arrowSource arrow)
           && pageElementTraceValid category (arrowTarget arrow)}
      -> {cellPrecedes (cellAt (arrowSource arrow))
           (cellAt (arrowTarget arrow))} @-}
proofGuard :: PageElements scope origin final
  -> PageElementArrow scope source target -> ()
proofGuard = rankedArrowCompatible
""",
    "ranked presentation requires source owning validity": r"""
{-@ proofGuard :: category:{PageElements scope origin final |
           folioLength (pageElementsFolio category) == 2}
      -> arrow:{PageElementArrow scope source target |
           pageElementTraceValid category (arrowTarget arrow)}
      -> {cellPrecedes (cellAt (arrowSource arrow))
           (cellAt (arrowTarget arrow))} @-}
proofGuard :: PageElements scope origin final
  -> PageElementArrow scope source target -> ()
proofGuard = rankedArrowCompatible
""",
    "ranked presentation requires target owning validity": r"""
{-@ proofGuard :: category:{PageElements scope origin final |
           folioLength (pageElementsFolio category) == 2}
      -> arrow:{PageElementArrow scope source target |
           pageElementTraceValid category (arrowSource arrow)}
      -> {cellPrecedes (cellAt (arrowSource arrow))
           (cellAt (arrowTarget arrow))} @-}
proofGuard :: PageElements scope origin final
  -> PageElementArrow scope source target -> ()
proofGuard = rankedArrowCompatible
""",
    "ranked presentation forward requires accepted source data": r"""
{-@ proofGuard :: category:{PageElements scope origin final |
           folioLength (pageElementsFolio category) == 2} -> owner:Dominion value
      -> arrow:{PageElementArrow scope source target |
           pageElementTraceValid category (arrowSource arrow)
           && pageElementTraceValid category (arrowTarget arrow)}
      -> RankedDominionCellData value source -> RankedDominionCellData value target @-}
proofGuard :: PageElements scope origin final -> Dominion value
  -> PageElementArrow scope source target -> RankedDominionCellData value source
  -> RankedDominionCellData value target
proofGuard = observedPageForward
""",
    "ranked presentation inverse requires accepted target data": r"""
{-@ proofGuard :: category:{PageElements scope origin final |
           folioLength (pageElementsFolio category) == 2} -> owner:Dominion value
      -> arrow:{PageElementArrow scope source target |
           pageElementTraceValid category (arrowSource arrow)
           && pageElementTraceValid category (arrowTarget arrow)}
      -> RankedDominionCellData value target -> Maybe (RankedDominionCellData value source) @-}
proofGuard :: PageElements scope origin final -> Dominion value
  -> PageElementArrow scope source target -> RankedDominionCellData value target
  -> Maybe (RankedDominionCellData value source)
proofGuard = observedPageInverse
""",
    "ranked presentation region selection requires the natural spine": r"""
{-@ proofGuard :: category:{PageElements scope origin Natural | folioLength (pageElementsFolio category) == 2}
      -> occurrence:{PageElement scope object | pageElementTraceValid category occurrence && pageElementPage occurrence > 0}
      -> {finiteOrdinal (spineRank (pageElementPosition occurrence)) == pageElementPosition occurrence} @-}
proofGuard :: PageElements scope origin Natural -> PageElement scope object -> ()
proofGuard = rankedRegionPosition
""",
    "ranked presentation region selection requires owning validity": r"""
{-@ proofGuard :: category:{PageElements scope origin Natural | folioLength (pageElementsFolio category) == 2 && lastChain (pageElementsFolio category) == spine}
      -> occurrence:{PageElement scope object | pageElementPage occurrence > 0}
      -> {finiteOrdinal (spineRank (pageElementPosition occurrence)) == pageElementPosition occurrence} @-}
proofGuard :: PageElements scope origin Natural -> PageElement scope object -> ()
proofGuard = rankedRegionPosition
""",
    "ranked presentation assembly requires two pages": r"""
{-@ proofGuard :: pages:{Pagination scope origin Natural | lastChain (pageElementsFolio (paginationPageElements pages)) == spine}
      -> Dominion value -> AtlasPresentation scope (RankedDominionCellData value) origin Natural @-}
proofGuard :: Pagination scope origin Natural -> Dominion value
  -> AtlasPresentation scope (RankedDominionCellData value) origin Natural
proofGuard = observedPresentation
""",
    "ranked presentation assembly requires the natural spine": r"""
{-@ proofGuard :: pages:{Pagination scope origin Natural | folioLength (pageElementsFolio (paginationPageElements pages)) == 2}
      -> Dominion value -> AtlasPresentation scope (RankedDominionCellData value) origin Natural @-}
proofGuard :: Pagination scope origin Natural -> Dominion value
  -> AtlasPresentation scope (RankedDominionCellData value) origin Natural
proofGuard = observedPresentation
""",
    "ranked presentation retains its exact action": r"""
{-@ proofGuard :: pages:{Pagination scope origin Natural |
           folioLength (pageElementsFolio (paginationPageElements pages)) == 2
           && lastChain (pageElementsFolio (paginationPageElements pages)) == spine}
      -> owner:Dominion value
      -> {result:AtlasPresentation scope (RankedDominionCellData value) origin Natural |
           atlasPresentationAction result /= rankedDominionAction (paginationPageElements pages) owner} @-}
proofGuard :: Pagination scope origin Natural -> Dominion value
  -> AtlasPresentation scope (RankedDominionCellData value) origin Natural
proofGuard = observedPresentation
""",
    "ranked presentation fixed pagination retains the natural spine": r"""
{-@ proofGuard :: Proxy value
      -> {pages:Pagination (RankedDominionPaginationScope value) () Natural |
           lastChain (pageElementsFolio (paginationPageElements pages)) /= spine} @-}
proofGuard :: Proxy value -> Pagination (RankedDominionPaginationScope value) () Natural
proofGuard = observedPagination
""",
    "ranked presentation spine positions are finite ordinals": r"""
{-@ proofGuard :: value:Natural -> {chainPosition spine value /= finiteOrdinal value} @-}
proofGuard :: Natural -> ()
proofGuard = observedSpinePosition
""",
}


CHAINED_PRESENTATION_PUBLIC_SOURCE = r"""
{-# LANGUAGE CPP #-}
#include "LiquidPlugin.h"
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--higherorder" @-}
module ChainedPresentationPublicGuard where
import Chain (Chain, chainPosition)
import ChainedDominionAtlas.Action (chainedDominionCell, chainValueAt, cellPrecedes, cellMap, cellPreimage)
import ChainedDominionAtlas.Data (ChainedDominionCellData)
import ChainedDominionAtlas.Presentation
import DomanialInsertion (applyInsertion, preimage)
import Folio (folioLength, lastChain)
import PageElements (PageElements, pageElementsFolio, pageElementTraceValid)
import PageElements.Structure (PageElement, PageElementArrow, pageElementPage, pageElementPosition, arrowSource, arrowTarget)

{-@ observedPageForward :: category:{PageElements scope origin final |
           folioLength (pageElementsFolio category) == 2}
      -> first:value -> owner:Chain value
      -> arrow:{PageElementArrow scope source target |
           pageElementTraceValid category (arrowSource arrow)
           && pageElementTraceValid category (arrowTarget arrow)}
      -> datum:{ChainedDominionCellData value source |
           chainedDominionAccepts first owner (arrowSource arrow) datum}
      -> {result:ChainedDominionCellData value target |
           chainedDominionAccepts first owner (arrowTarget arrow) result
           && result == cellMap owner (chainedDominionCell first owner (arrowSource arrow))
                (chainedDominionCell first owner (arrowTarget arrow)) datum} @-}
observedPageForward :: PageElements scope origin final -> value -> Chain value
  -> PageElementArrow scope source target -> ChainedDominionCellData value source
  -> ChainedDominionCellData value target
observedPageForward category first owner arrow datum =
  applyInsertion (chainedDominionDataMap category first owner arrow) datum

{-@ observedPageInverse :: category:{PageElements scope origin final |
           folioLength (pageElementsFolio category) == 2}
      -> first:value -> owner:Chain value
      -> arrow:{PageElementArrow scope source target |
           pageElementTraceValid category (arrowSource arrow)
           && pageElementTraceValid category (arrowTarget arrow)}
      -> datum:{ChainedDominionCellData value target |
           chainedDominionAccepts first owner (arrowTarget arrow) datum}
      -> {result:Maybe ({candidate:ChainedDominionCellData value source |
           chainedDominionAccepts first owner (arrowSource arrow) candidate}) |
           result == cellPreimage owner (chainedDominionCell first owner (arrowSource arrow))
                (chainedDominionCell first owner (arrowTarget arrow)) datum} @-}
observedPageInverse :: PageElements scope origin final -> value -> Chain value
  -> PageElementArrow scope source target -> ChainedDominionCellData value target
  -> Maybe (ChainedDominionCellData value source)
observedPageInverse category first owner arrow datum =
  preimage (chainedDominionDataMap category first owner arrow) datum
"""
CHAINED_PRESENTATION_PUBLIC_GUARDS = {
    "chained region selection requires the owning final chain": r"""
{-@ proofGuard :: category:{PageElements scope origin value |
           folioLength (pageElementsFolio category) == 2} -> first:value -> owner:Chain value
      -> occurrence:{PageElement scope object | pageElementTraceValid category occurrence
           && pageElementPage occurrence > 0}
      -> {chainPosition owner (chainValueAt first owner occurrence) == pageElementPosition occurrence} @-}
proofGuard :: PageElements scope origin value -> value -> Chain value -> PageElement scope object -> ()
proofGuard = chainedRegionPosition
""",
    "chained region selection requires owning validity": r"""
{-@ proofGuard :: category:{PageElements scope origin value |
           folioLength (pageElementsFolio category) == 2} -> first:value
      -> owner:{Chain value | owner == lastChain (pageElementsFolio category)}
      -> occurrence:{PageElement scope object | pageElementPage occurrence > 0}
      -> {chainPosition owner (chainValueAt first owner occurrence) == pageElementPosition occurrence} @-}
proofGuard :: PageElements scope origin value -> value -> Chain value -> PageElement scope object -> ()
proofGuard = chainedRegionPosition
""",
    "chained presentation requires a two-page owning folio": r"""
{-@ proofGuard :: category:PageElements scope origin final -> first:value -> owner:Chain value
      -> arrow:{PageElementArrow scope source target |
           pageElementTraceValid category (arrowSource arrow)
           && pageElementTraceValid category (arrowTarget arrow)}
      -> {cellPrecedes owner (chainedDominionCell first owner (arrowSource arrow))
           (chainedDominionCell first owner (arrowTarget arrow))} @-}
proofGuard :: PageElements scope origin final -> value -> Chain value
  -> PageElementArrow scope source target -> ()
proofGuard = chainedArrowCompatible
""",
    "chained presentation requires source owning validity": r"""
{-@ proofGuard :: category:{PageElements scope origin final |
           folioLength (pageElementsFolio category) == 2} -> first:value -> owner:Chain value
      -> arrow:{PageElementArrow scope source target |
           pageElementTraceValid category (arrowTarget arrow)}
      -> {cellPrecedes owner (chainedDominionCell first owner (arrowSource arrow))
           (chainedDominionCell first owner (arrowTarget arrow))} @-}
proofGuard :: PageElements scope origin final -> value -> Chain value
  -> PageElementArrow scope source target -> ()
proofGuard = chainedArrowCompatible
""",
    "chained presentation requires target owning validity": r"""
{-@ proofGuard :: category:{PageElements scope origin final |
           folioLength (pageElementsFolio category) == 2} -> first:value -> owner:Chain value
      -> arrow:{PageElementArrow scope source target |
           pageElementTraceValid category (arrowSource arrow)}
      -> {cellPrecedes owner (chainedDominionCell first owner (arrowSource arrow))
           (chainedDominionCell first owner (arrowTarget arrow))} @-}
proofGuard :: PageElements scope origin final -> value -> Chain value
  -> PageElementArrow scope source target -> ()
proofGuard = chainedArrowCompatible
""",
    "chained presentation forward requires accepted source data": r"""
{-@ proofGuard :: category:{PageElements scope origin final |
           folioLength (pageElementsFolio category) == 2} -> first:value -> owner:Chain value
      -> arrow:{PageElementArrow scope source target |
           pageElementTraceValid category (arrowSource arrow)
           && pageElementTraceValid category (arrowTarget arrow)}
      -> ChainedDominionCellData value source -> ChainedDominionCellData value target @-}
proofGuard :: PageElements scope origin final -> value -> Chain value
  -> PageElementArrow scope source target -> ChainedDominionCellData value source
  -> ChainedDominionCellData value target
proofGuard = observedPageForward
""",
    "chained presentation inverse requires accepted target data": r"""
{-@ proofGuard :: category:{PageElements scope origin final |
           folioLength (pageElementsFolio category) == 2} -> first:value -> owner:Chain value
      -> arrow:{PageElementArrow scope source target |
           pageElementTraceValid category (arrowSource arrow)
           && pageElementTraceValid category (arrowTarget arrow)}
      -> ChainedDominionCellData value target -> Maybe (ChainedDominionCellData value source) @-}
proofGuard :: PageElements scope origin final -> value -> Chain value
  -> PageElementArrow scope source target -> ChainedDominionCellData value target
  -> Maybe (ChainedDominionCellData value source)
proofGuard = observedPageInverse
""",
}

CHAINED_ASSEMBLY_PUBLIC_SOURCE = r"""
{-# LANGUAGE CPP #-}
#include "LiquidPlugin.h"
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--higherorder" @-}
module ChainedAssemblyPublicGuard where
import Atlas (AtlasPresentation, atlasPresentationPagination, atlasPresentationAction, atlasActionDataAt)
import Chain (Chain)
import ChainedDominionAtlas.Data (ChainedDominionCellData)
import ChainedDominionAtlas.Presentation
import Dominion (Dominion)
import Folio (Folio, folioLength, lastChain)
import PageElements (pageElementsFolio)
import Pagination (Pagination, paginationPageElements)

{-@ observedPresentation :: pages:{Pagination scope origin value |
           folioLength (pageElementsFolio (paginationPageElements pages)) == 2}
      -> first:value -> owner:{Chain value | owner == lastChain (pageElementsFolio (paginationPageElements pages))}
      -> valueDominion:Dominion value
      -> {result:AtlasPresentation scope (ChainedDominionCellData value) origin value |
           atlasPresentationPagination result == pages
           && atlasPresentationAction result == chainedDominionAction (paginationPageElements pages) first owner valueDominion
           && atlasActionDataAt (atlasPresentationAction result) == chainedDominionAt first owner valueDominion} @-}
observedPresentation :: Pagination scope origin value -> value -> Chain value -> Dominion value
  -> AtlasPresentation scope (ChainedDominionCellData value) origin value
observedPresentation = chainedDominionPresentation

{-@ observedFolio :: first:value -> owner:Chain value
      -> {pages:Folio () value | folioLength pages == 2 && lastChain pages == owner} @-}
observedFolio :: value -> Chain value -> Folio () value
observedFolio = chainedDominionFolio
"""
CHAINED_ASSEMBLY_PUBLIC_GUARDS = {
    "chained assembly requires a two-page folio": r"""
{-@ proofGuard :: pages:Pagination scope origin value -> first:value
      -> owner:{Chain value | owner == lastChain (pageElementsFolio (paginationPageElements pages))}
      -> Dominion value -> AtlasPresentation scope (ChainedDominionCellData value) origin value @-}
proofGuard :: Pagination scope origin value -> value -> Chain value -> Dominion value
  -> AtlasPresentation scope (ChainedDominionCellData value) origin value
proofGuard = observedPresentation
""",
    "chained assembly requires the owning final chain": r"""
{-@ proofGuard :: pages:{Pagination scope origin value |
           folioLength (pageElementsFolio (paginationPageElements pages)) == 2}
      -> value -> Chain value -> Dominion value
      -> AtlasPresentation scope (ChainedDominionCellData value) origin value @-}
proofGuard :: Pagination scope origin value -> value -> Chain value -> Dominion value
  -> AtlasPresentation scope (ChainedDominionCellData value) origin value
proofGuard = observedPresentation
""",
    "chained assembly retains the supplied pagination": r"""
{-@ proofGuard :: pages:{Pagination scope origin value |
           folioLength (pageElementsFolio (paginationPageElements pages)) == 2}
      -> first:value -> owner:{Chain value | owner == lastChain (pageElementsFolio (paginationPageElements pages))}
      -> Dominion value
      -> {result:AtlasPresentation scope (ChainedDominionCellData value) origin value |
           atlasPresentationPagination result /= pages} @-}
proofGuard :: Pagination scope origin value -> value -> Chain value -> Dominion value
  -> AtlasPresentation scope (ChainedDominionCellData value) origin value
proofGuard = observedPresentation
""",
    "chained assembly retains the supplied data action": r"""
{-@ proofGuard :: pages:{Pagination scope origin value |
           folioLength (pageElementsFolio (paginationPageElements pages)) == 2}
      -> first:value -> owner:{Chain value | owner == lastChain (pageElementsFolio (paginationPageElements pages))}
      -> valueDominion:Dominion value
      -> {result:AtlasPresentation scope (ChainedDominionCellData value) origin value |
           atlasPresentationAction result /= chainedDominionAction (paginationPageElements pages) first owner valueDominion} @-}
proofGuard :: Pagination scope origin value -> value -> Chain value -> Dominion value
  -> AtlasPresentation scope (ChainedDominionCellData value) origin value
proofGuard = observedPresentation
""",
    "chained assembly folio has exactly two pages": r"""
{-@ proofGuard :: value -> Chain value -> {pages:Folio () value | folioLength pages == 1} @-}
proofGuard :: value -> Chain value -> Folio () value
proofGuard = observedFolio
""",
    "chained assembly retains the supplied cell Dominions": r"""
{-@ proofGuard :: pages:{Pagination scope origin value |
           folioLength (pageElementsFolio (paginationPageElements pages)) == 2}
      -> first:value -> owner:{Chain value | owner == lastChain (pageElementsFolio (paginationPageElements pages))}
      -> valueDominion:Dominion value
      -> {result:AtlasPresentation scope (ChainedDominionCellData value) origin value |
           atlasActionDataAt (atlasPresentationAction result) /= chainedDominionAt first owner valueDominion} @-}
proofGuard :: Pagination scope origin value -> value -> Chain value -> Dominion value
  -> AtlasPresentation scope (ChainedDominionCellData value) origin value
proofGuard = observedPresentation
""",
}

RANKED_OWNER_PUBLIC_SOURCE = r"""
{-# LANGUAGE CPP #-}
#include "LiquidPlugin.h"
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--higherorder" @-}
module RankedOwnerPublicGuard where
import Atlas (Atlas, atlasDescription, atlasPageElements, atlasAcceptsDatum, atlasDataAt, mapAtlasData)
import Dominion (Dominion, rank, unrank)
import DomanialInsertion.Core (DomanialInsertion (..))
import Numeric.Natural (Natural)
import PageElements (PageElement, pageElementTraceValid)
import PageElements.Structure (PageElementArrow, arrowSource, arrowTarget)
import RankedDominionAtlas.Action (cellAt, cellMap, cellPreimage, cellRank, cellUnrank)
import RankedDominionAtlas.Data (RankedDominionCellData)
import RankedDominionAtlas.Owner
import RankedDominionAtlas.Pagination (RankedDominionPaginationScope, rankedPresentation)
import RankedDominionAtlas.Presentation (rankedDominionAccepts)

{-@ observedPresentation :: owner:RankedDominionAtlas ownerScope value
      -> {atlasDescription (rankedDominionAtlas owner) == rankedPresentation (rankedDominionValueDominion owner)} @-}
observedPresentation :: RankedDominionAtlas ownerScope value -> ()
observedPresentation owner = rankedDominionAtlas owner `seq` ()

{-@ observedDominion :: dominion:Dominion value -> {result:Dominion value | result == dominion} @-}
observedDominion :: Dominion value -> Dominion value
observedDominion dominion = withRankedDominionAtlas dominion rankedDominionValueDominion

{-@ observedAcceptance :: owner:RankedDominionAtlas ownerScope value
      -> occurrence:PageElement (RankedDominionPaginationScope value) object -> datum:RankedDominionCellData value object
      -> {result:Bool | result == rankedDominionAccepts (rankedDominionValueDominion owner) occurrence datum} @-}
observedAcceptance :: RankedDominionAtlas ownerScope value
  -> PageElement (RankedDominionPaginationScope value) object -> RankedDominionCellData value object -> Bool
observedAcceptance owner occurrence datum =
  rankedDominionMembership owner occurrence datum `seq`
    atlasAcceptsDatum (rankedDominionAtlas owner) occurrence datum

{-@ observedForward :: owner:RankedDominionAtlas ownerScope value
      -> arrow:{PageElementArrow (RankedDominionPaginationScope value) source target |
           pageElementTraceValid (atlasPageElements (rankedDominionAtlas owner)) (arrowSource arrow)
           && pageElementTraceValid (atlasPageElements (rankedDominionAtlas owner)) (arrowTarget arrow)}
      -> datum:{RankedDominionCellData value source | atlasAcceptsDatum (rankedDominionAtlas owner) (arrowSource arrow) datum}
      -> {result:RankedDominionCellData value target |
           result == cellMap (rankedDominionValueDominion owner) (cellAt (arrowSource arrow)) (cellAt (arrowTarget arrow)) datum} @-}
observedForward :: RankedDominionAtlas ownerScope value
  -> PageElementArrow (RankedDominionPaginationScope value) source target
  -> RankedDominionCellData value source -> RankedDominionCellData value target
observedForward owner arrow datum = rankedDominionTransport owner arrow datum `seq`
  case mapAtlasData (rankedDominionAtlas owner) arrow of
    DomanialInsertion forward _ _ -> forward datum

{-@ observedInverse :: owner:RankedDominionAtlas ownerScope value
      -> arrow:{PageElementArrow (RankedDominionPaginationScope value) source target |
           pageElementTraceValid (atlasPageElements (rankedDominionAtlas owner)) (arrowSource arrow)
           && pageElementTraceValid (atlasPageElements (rankedDominionAtlas owner)) (arrowTarget arrow)}
      -> datum:{RankedDominionCellData value target | atlasAcceptsDatum (rankedDominionAtlas owner) (arrowTarget arrow) datum}
      -> {result:Maybe (RankedDominionCellData value source) |
           result == cellPreimage (rankedDominionValueDominion owner) (cellAt (arrowSource arrow)) (cellAt (arrowTarget arrow)) datum} @-}
observedInverse :: RankedDominionAtlas ownerScope value
  -> PageElementArrow (RankedDominionPaginationScope value) source target
  -> RankedDominionCellData value target -> Maybe (RankedDominionCellData value source)
observedInverse owner arrow datum = rankedDominionInverseTransport owner arrow datum `seq`
  case mapAtlasData (rankedDominionAtlas owner) arrow of
    DomanialInsertion _ backward _ -> backward datum

{-@ observedRank :: owner:RankedDominionAtlas ownerScope value
      -> occurrence:{PageElement (RankedDominionPaginationScope value) object |
           pageElementTraceValid (atlasPageElements (rankedDominionAtlas owner)) occurrence}
      -> datum:{RankedDominionCellData value object | atlasAcceptsDatum (rankedDominionAtlas owner) occurrence datum}
      -> {result:Natural | result == cellRank (rankedDominionValueDominion owner) (cellAt occurrence) datum} @-}
observedRank :: RankedDominionAtlas ownerScope value
  -> PageElement (RankedDominionPaginationScope value) object -> RankedDominionCellData value object -> Natural
observedRank owner occurrence datum = rankedDominionDataAt owner occurrence `seq`
  rank (atlasDataAt (rankedDominionAtlas owner) occurrence) datum

{-@ observedUnrank :: owner:RankedDominionAtlas ownerScope value
      -> occurrence:{PageElement (RankedDominionPaginationScope value) object |
           pageElementTraceValid (atlasPageElements (rankedDominionAtlas owner)) occurrence}
      -> index:Natural
      -> {result:Maybe (RankedDominionCellData value object) |
           result == cellUnrank (rankedDominionValueDominion owner) (cellAt occurrence) index} @-}
observedUnrank :: RankedDominionAtlas ownerScope value
  -> PageElement (RankedDominionPaginationScope value) object -> Natural -> Maybe (RankedDominionCellData value object)
observedUnrank owner occurrence index = rankedDominionDataAt owner occurrence `seq`
  unrank (atlasDataAt (rankedDominionAtlas owner) occurrence) index
"""
RANKED_OWNER_PUBLIC_GUARDS = {
    "ranked owner retains its exact presentation": r"""
{-@ proofGuard :: owner:RankedDominionAtlas ownerScope value
      -> {atlasDescription (rankedDominionAtlas owner) /= rankedPresentation (rankedDominionValueDominion owner)} @-}
proofGuard :: RankedDominionAtlas ownerScope value -> ()
proofGuard = observedPresentation
""",
    "ranked owner allocation retains the supplied Dominion": r"""
{-@ proofGuard :: dominion:Dominion value -> {result:Dominion value | result /= dominion} @-}
proofGuard :: Dominion value -> Dominion value
proofGuard = observedDominion
""",
    "ranked owner cannot retain an uncertified Atlas": r"""
proofGuard :: Dominion value
  -> Atlas owner (RankedDominionPaginationScope value) (RankedDominionCellData value) () Natural
  -> RankedDominionAtlas owner value
proofGuard = retainRankedDominionAtlas
""",
    "ranked owner cannot substitute its value Dominion": r"""
proofGuard :: RankedDominionAtlas owner value -> Dominion value -> RankedDominionAtlas owner value
proofGuard owner replacement = retainRankedDominionAtlas replacement (rankedDominionAtlas owner)
""",
    "ranked owner membership retains the restricted cell predicate": r"""
{-@ proofGuard :: owner:RankedDominionAtlas ownerScope value
      -> occurrence:PageElement (RankedDominionPaginationScope value) object -> datum:RankedDominionCellData value object
      -> {result:Bool | result /= rankedDominionAccepts (rankedDominionValueDominion owner) occurrence datum} @-}
proofGuard :: RankedDominionAtlas ownerScope value
  -> PageElement (RankedDominionPaginationScope value) object -> RankedDominionCellData value object -> Bool
proofGuard = observedAcceptance
""",
    "ranked owner inverse agrees with its checked cell inverse": r"""
{-@ proofGuard :: owner:RankedDominionAtlas ownerScope value
      -> arrow:{PageElementArrow (RankedDominionPaginationScope value) source target |
           pageElementTraceValid (atlasPageElements (rankedDominionAtlas owner)) (arrowSource arrow)
           && pageElementTraceValid (atlasPageElements (rankedDominionAtlas owner)) (arrowTarget arrow)}
      -> datum:{RankedDominionCellData value target | atlasAcceptsDatum (rankedDominionAtlas owner) (arrowTarget arrow) datum}
      -> {result:Maybe (RankedDominionCellData value source) |
           result /= cellPreimage (rankedDominionValueDominion owner) (cellAt (arrowSource arrow)) (cellAt (arrowTarget arrow)) datum} @-}
proofGuard :: RankedDominionAtlas ownerScope value
  -> PageElementArrow (RankedDominionPaginationScope value) source target
  -> RankedDominionCellData value target -> Maybe (RankedDominionCellData value source)
proofGuard = observedInverse
""",
    "ranked owner lookup retains its exact rank": r"""
{-@ proofGuard :: owner:RankedDominionAtlas ownerScope value
      -> occurrence:{PageElement (RankedDominionPaginationScope value) object |
           pageElementTraceValid (atlasPageElements (rankedDominionAtlas owner)) occurrence}
      -> datum:{RankedDominionCellData value object | atlasAcceptsDatum (rankedDominionAtlas owner) occurrence datum}
      -> {result:Natural | result /= cellRank (rankedDominionValueDominion owner) (cellAt occurrence) datum} @-}
proofGuard :: RankedDominionAtlas ownerScope value
  -> PageElement (RankedDominionPaginationScope value) object -> RankedDominionCellData value object -> Natural
proofGuard = observedRank
""",
    "ranked owner lookup retains its exact decoder": r"""
{-@ proofGuard :: owner:RankedDominionAtlas ownerScope value
      -> occurrence:{PageElement (RankedDominionPaginationScope value) object |
           pageElementTraceValid (atlasPageElements (rankedDominionAtlas owner)) occurrence}
      -> index:Natural
      -> {result:Maybe (RankedDominionCellData value object) |
           result /= cellUnrank (rankedDominionValueDominion owner) (cellAt occurrence) index} @-}
proofGuard :: RankedDominionAtlas ownerScope value
  -> PageElement (RankedDominionPaginationScope value) object -> Natural -> Maybe (RankedDominionCellData value object)
proofGuard = observedUnrank
""",
}

CHAINED_OWNER_PUBLIC_SOURCE = r"""
{-# LANGUAGE CPP #-}
#include "LiquidPlugin.h"
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--higherorder" @-}
module ChainedOwnerPublicGuard where
import Atlas
  ( Atlas, AtlasDataAction, atlasFolio, atlasPageElements, atlasDescription, atlasPresentationAction, atlasAcceptsDatum, mapAtlasData )
import Chain (Chain)
import ChainedDominionAtlas.Action (chainedDominionCell, cellMap)
import ChainedDominionAtlas.Data (ChainedDominionCellData)
import ChainedDominionAtlas.Owner
import ChainedDominionAtlas.Presentation (chainedDominionAction, chainedDominionAccepts)
import Dominion (Dominion)
import DomanialInsertion.Core (DomanialInsertion (..))
import Folio (folioLength, lastChain)
import PageElements (PageElement, pageElementTraceValid)
import PageElements.Structure (PageElementArrow, arrowSource, arrowTarget)

{-@ observedTransport :: owner:ChainedDominionAtlas ownerScope scope value
      -> arrow:{PageElementArrow scope source target |
           pageElementTraceValid (atlasPageElements (chainedDominionAtlas owner)) (arrowSource arrow)
           && pageElementTraceValid (atlasPageElements (chainedDominionAtlas owner)) (arrowTarget arrow)}
      -> datum:{ChainedDominionCellData value source |
           atlasAcceptsDatum (chainedDominionAtlas owner) (arrowSource arrow) datum}
      -> {result:ChainedDominionCellData value target |
           atlasAcceptsDatum (chainedDominionAtlas owner) (arrowTarget arrow) result
           && result == cellMap (chainedDominionChain owner)
             (chainedDominionCell (chainedDominionFirst owner) (chainedDominionChain owner) (arrowSource arrow))
             (chainedDominionCell (chainedDominionFirst owner) (chainedDominionChain owner) (arrowTarget arrow)) datum} @-}
observedTransport :: ChainedDominionAtlas ownerScope scope value
  -> PageElementArrow scope source target -> ChainedDominionCellData value source -> ChainedDominionCellData value target
observedTransport owner arrow datum =
  chainedDominionTransport owner arrow datum `seq`
    case mapAtlasData (chainedDominionAtlas owner) arrow of
      DomanialInsertion forward _ _ -> forward datum

{-@ observedFinalChain :: owner:ChainedDominionAtlas ownerScope scope value
      -> {result:Chain value | result == chainedDominionChain owner} @-}
observedFinalChain :: ChainedDominionAtlas ownerScope scope value -> Chain value
observedFinalChain owner = lastChain (atlasFolio (chainedDominionAtlas owner))

{-@ observedStoredAction :: owner:ChainedDominionAtlas ownerScope scope value
      -> {action:AtlasDataAction scope (ChainedDominionCellData value) |
           action == chainedDominionAction (atlasPageElements (chainedDominionAtlas owner))
             (chainedDominionFirst owner) (chainedDominionChain owner) (chainedDominionValueDominion owner)} @-}
observedStoredAction :: ChainedDominionAtlas ownerScope scope value
  -> AtlasDataAction scope (ChainedDominionCellData value)
observedStoredAction owner = atlasPresentationAction (atlasDescription (chainedDominionAtlas owner))

{-@ observedAcceptance :: owner:ChainedDominionAtlas ownerScope scope value
      -> occurrence:PageElement scope object -> datum:ChainedDominionCellData value object
      -> {result:Bool | result == chainedDominionAccepts (chainedDominionFirst owner)
           (chainedDominionChain owner) occurrence datum} @-}
observedAcceptance :: ChainedDominionAtlas ownerScope scope value
  -> PageElement scope object -> ChainedDominionCellData value object -> Bool
observedAcceptance owner occurrence datum =
  chainedDominionMembership owner occurrence datum `seq`
    atlasAcceptsDatum (chainedDominionAtlas owner) occurrence datum

{-@ measure observedFirst @-}
{-@ measure observedChain @-}
{-@ measure observedDominion @-}
data OwnerObservation value = OwnerObservation
  { observedFirst :: value
  , observedChain :: Chain value
  , observedDominion :: Dominion value
  }

{-@ observedInputs :: first:value -> chain:Chain value -> dominion:Dominion value
      -> {result:OwnerObservation value | observedFirst result == first
           && observedChain result == chain && observedDominion result == dominion} @-}
observedInputs :: value -> Chain value -> Dominion value -> OwnerObservation value
observedInputs first chain dominion =
  withChainedDominionAtlas first chain dominion (\owner ->
    OwnerObservation (chainedDominionFirst owner) (observedFinalChain owner) (chainedDominionValueDominion owner))
"""
CHAINED_OWNER_PUBLIC_GUARDS = {
    "chained owner transport agrees with its checked cell map": r"""
{-@ proofGuard :: owner:ChainedDominionAtlas ownerScope scope value
      -> arrow:{PageElementArrow scope source target |
           pageElementTraceValid (atlasPageElements (chainedDominionAtlas owner)) (arrowSource arrow)
           && pageElementTraceValid (atlasPageElements (chainedDominionAtlas owner)) (arrowTarget arrow)}
      -> datum:{ChainedDominionCellData value source |
           atlasAcceptsDatum (chainedDominionAtlas owner) (arrowSource arrow) datum}
      -> {result:ChainedDominionCellData value target |
           result /= cellMap (chainedDominionChain owner)
             (chainedDominionCell (chainedDominionFirst owner) (chainedDominionChain owner) (arrowSource arrow))
             (chainedDominionCell (chainedDominionFirst owner) (chainedDominionChain owner) (arrowTarget arrow)) datum} @-}
proofGuard :: ChainedDominionAtlas ownerScope scope value
  -> PageElementArrow scope source target -> ChainedDominionCellData value source -> ChainedDominionCellData value target
proofGuard = observedTransport
""",
    "chained owner membership retains the restricted cell predicate": r"""
{-@ proofGuard :: owner:ChainedDominionAtlas ownerScope scope value
      -> occurrence:PageElement scope object -> datum:ChainedDominionCellData value object
      -> {result:Bool | result /= chainedDominionAccepts (chainedDominionFirst owner)
           (chainedDominionChain owner) occurrence datum} @-}
proofGuard :: ChainedDominionAtlas ownerScope scope value
  -> PageElement scope object -> ChainedDominionCellData value object -> Bool
proofGuard = observedAcceptance
""",
    "chained owner cannot retain an uncertified Atlas": r"""
proofGuard :: value -> Chain value -> Dominion value
  -> Atlas owner scope (ChainedDominionCellData value) () value -> ChainedDominionAtlas owner scope value
proofGuard = retainChainedDominionAtlas
""",
    "chained owner allocation retains the supplied first value": r"""
{-@ proofGuard :: first:value -> Chain value -> Dominion value
      -> {result:OwnerObservation value | observedFirst result /= first} @-}
proofGuard :: value -> Chain value -> Dominion value -> OwnerObservation value
proofGuard = observedInputs
""",
    "chained owner allocation retains the supplied chain": r"""
{-@ proofGuard :: value -> chain:Chain value -> Dominion value
      -> {result:OwnerObservation value | observedChain result /= chain} @-}
proofGuard :: value -> Chain value -> Dominion value -> OwnerObservation value
proofGuard = observedInputs
""",
    "chained owner allocation retains the supplied Dominion": r"""
{-@ proofGuard :: value -> Chain value -> dominion:Dominion value
      -> {result:OwnerObservation value | observedDominion result /= dominion} @-}
proofGuard :: value -> Chain value -> Dominion value -> OwnerObservation value
proofGuard = observedInputs
""",
    "chained owner final chain matches the stored chain": r"""
{-@ proofGuard :: owner:ChainedDominionAtlas ownerScope scope value
      -> {result:Chain value | result /= chainedDominionChain owner} @-}
proofGuard :: ChainedDominionAtlas ownerScope scope value -> Chain value
proofGuard = observedFinalChain
""",
    "chained owner retains the complete stored action": r"""
{-@ proofGuard :: owner:ChainedDominionAtlas ownerScope scope value
      -> {action:AtlasDataAction scope (ChainedDominionCellData value) |
           action /= chainedDominionAction (atlasPageElements (chainedDominionAtlas owner))
             (chainedDominionFirst owner) (chainedDominionChain owner) (chainedDominionValueDominion owner)} @-}
proofGuard :: ChainedDominionAtlas ownerScope scope value
  -> AtlasDataAction scope (ChainedDominionCellData value)
proofGuard = observedStoredAction
""",
    "chained owner cannot substitute its value Dominion": r"""
proofGuard :: ChainedDominionAtlas owner scope value -> Dominion value -> ChainedDominionAtlas owner scope value
proofGuard owner replacement =
  retainChainedDominionAtlas (chainedDominionFirst owner) (chainedDominionChain owner)
    replacement (chainedDominionAtlas owner)
""",
}

TWO_PAGE_COVERAGE_PUBLIC_SOURCE = r"""
{-# LANGUAGE CPP #-}
#include "LiquidPlugin.h"
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--higherorder" @-}
module TwoPageCoveragePublicGuard where
import Atlas (Atlas, atlasFolio, atlasAcceptsDatum)
import AtlasExtent (cellTraceValid)
import AtlasCoveredPageElement (CoverageWitness, coverageWitnessCovers)
import Folio (folioLength)
import PageElements (PageElement)
import PageElements.Structure (pageElementPage)
import TwoPageCoverage (twoPageRegionCoverage)

{-@ observedCoverage :: owner:{Atlas ownerScope scope cellData origin final | folioLength (atlasFolio owner) == 2}
      -> region:{PageElement scope object | cellTraceValid owner region && pageElementPage region == 1}
      -> datum:{cellData object | atlasAcceptsDatum owner region datum}
      -> {witness:CoverageWitness ownerScope scope cellData | coverageWitnessCovers owner region datum witness} @-}
observedCoverage :: Atlas ownerScope scope cellData origin final
  -> PageElement scope object -> cellData object -> CoverageWitness ownerScope scope cellData
observedCoverage = twoPageRegionCoverage
"""
TWO_PAGE_COVERAGE_PUBLIC_GUARDS = {
    "two-page coverage requires a two-page owning folio": r"""
{-@ proofGuard :: owner:Atlas ownerScope scope cellData origin final
      -> region:{PageElement scope object | cellTraceValid owner region && pageElementPage region == 1}
      -> datum:{cellData object | atlasAcceptsDatum owner region datum}
      -> CoverageWitness ownerScope scope cellData @-}
proofGuard :: Atlas ownerScope scope cellData origin final
  -> PageElement scope object -> cellData object -> CoverageWitness ownerScope scope cellData
proofGuard = observedCoverage
""",
    "two-page coverage requires the final region": r"""
{-@ proofGuard :: owner:{Atlas ownerScope scope cellData origin final | folioLength (atlasFolio owner) == 2}
      -> region:{PageElement scope object | cellTraceValid owner region}
      -> datum:{cellData object | atlasAcceptsDatum owner region datum}
      -> CoverageWitness ownerScope scope cellData @-}
proofGuard :: Atlas ownerScope scope cellData origin final
  -> PageElement scope object -> cellData object -> CoverageWitness ownerScope scope cellData
proofGuard = observedCoverage
""",
    "two-page coverage requires the owning trace": r"""
{-@ proofGuard :: owner:{Atlas ownerScope scope cellData origin final | folioLength (atlasFolio owner) == 2}
      -> region:{PageElement scope object | pageElementPage region == 1}
      -> datum:{cellData object | atlasAcceptsDatum owner region datum}
      -> CoverageWitness ownerScope scope cellData @-}
proofGuard :: Atlas ownerScope scope cellData origin final
  -> PageElement scope object -> cellData object -> CoverageWitness ownerScope scope cellData
proofGuard = observedCoverage
""",
    "two-page coverage requires accepted data": r"""
{-@ proofGuard :: owner:{Atlas ownerScope scope cellData origin final | folioLength (atlasFolio owner) == 2}
      -> region:{PageElement scope object | cellTraceValid owner region && pageElementPage region == 1}
      -> cellData object -> CoverageWitness ownerScope scope cellData @-}
proofGuard :: Atlas ownerScope scope cellData origin final
  -> PageElement scope object -> cellData object -> CoverageWitness ownerScope scope cellData
proofGuard = observedCoverage
""",
}

CHAINED_COVERAGE_PUBLIC_SOURCE = r"""
{-# LANGUAGE CPP #-}
#include "LiquidPlugin.h"
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--higherorder" @-}
module ChainedCoveragePublicGuard where
import Atlas (atlasAcceptsDatum)
import AtlasExtent (cellTraceValid)
import AtlasCoveredPageElement (CoverageWitness, coverageWitnessCovers)
import AtlasMap (AtlasMap)
import ChainedDominionAtlas (chainedDominionAtlasMap)
import ChainedDominionAtlas.Coverage (chainedDominionCoverage)
import ChainedDominionAtlas.Owner (ChainedDominionAtlas, ChainedDominionAtlasObject, chainedDominionAtlas)
import ChainedDominionAtlas.Data (ChainedDominionCellData)
import PageElements (PageElement)

{-@ observedCoverage :: owner:ChainedDominionAtlas ownerScope scope value
      -> source:{PageElement scope object | cellTraceValid (chainedDominionAtlas owner) source}
      -> datum:{ChainedDominionCellData value object | atlasAcceptsDatum (chainedDominionAtlas owner) source datum}
      -> {witness:CoverageWitness ownerScope scope (ChainedDominionCellData value) |
           coverageWitnessCovers (chainedDominionAtlas owner) source datum witness} @-}
observedCoverage :: ChainedDominionAtlas ownerScope scope value
  -> PageElement scope object -> ChainedDominionCellData value object
  -> CoverageWitness ownerScope scope (ChainedDominionCellData value)
observedCoverage = chainedDominionCoverage

{-@ observedMap :: ChainedDominionAtlas owner scope value -> AtlasMap (ChainedDominionAtlasObject owner scope value) @-}
observedMap :: ChainedDominionAtlas owner scope value -> AtlasMap (ChainedDominionAtlasObject owner scope value)
observedMap = chainedDominionAtlasMap
"""
CHAINED_COVERAGE_PUBLIC_GUARDS = {
    "chained coverage certifies its exact source datum": r"""
{-@ proofGuard :: owner:ChainedDominionAtlas ownerScope scope value
      -> source:{PageElement scope object | cellTraceValid (chainedDominionAtlas owner) source}
      -> datum:{ChainedDominionCellData value object | atlasAcceptsDatum (chainedDominionAtlas owner) source datum}
      -> {witness:CoverageWitness ownerScope scope (ChainedDominionCellData value) |
           not (coverageWitnessCovers (chainedDominionAtlas owner) source datum witness)} @-}
proofGuard :: ChainedDominionAtlas ownerScope scope value
  -> PageElement scope object -> ChainedDominionCellData value object
  -> CoverageWitness ownerScope scope (ChainedDominionCellData value)
proofGuard = observedCoverage
""",
    "chained coverage requires the owning source trace": r"""
{-@ proofGuard :: owner:ChainedDominionAtlas ownerScope scope value
      -> source:PageElement scope object
      -> datum:{ChainedDominionCellData value object | atlasAcceptsDatum (chainedDominionAtlas owner) source datum}
      -> CoverageWitness ownerScope scope (ChainedDominionCellData value) @-}
proofGuard :: ChainedDominionAtlas ownerScope scope value
  -> PageElement scope object -> ChainedDominionCellData value object
  -> CoverageWitness ownerScope scope (ChainedDominionCellData value)
proofGuard = observedCoverage
""",
    "chained coverage requires accepted data": r"""
{-@ proofGuard :: owner:ChainedDominionAtlas ownerScope scope value
      -> source:{PageElement scope object | cellTraceValid (chainedDominionAtlas owner) source}
      -> ChainedDominionCellData value object
      -> CoverageWitness ownerScope scope (ChainedDominionCellData value) @-}
proofGuard :: ChainedDominionAtlas ownerScope scope value
  -> PageElement scope object -> ChainedDominionCellData value object
  -> CoverageWitness ownerScope scope (ChainedDominionCellData value)
proofGuard = observedCoverage
""",
}

RANKED_COVERAGE_PUBLIC_SOURCE = r"""
{-# LANGUAGE CPP #-}
#include "LiquidPlugin.h"
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--higherorder" @-}
module RankedCoveragePublicGuard where
import Atlas (atlasAcceptsDatum)
import AtlasExtent (cellTraceValid)
import AtlasCoveredPageElement (CoverageWitness, coverageWitnessCovers)
import AtlasMap (AtlasMap)
import RankedDominionAtlas (rankedDominionAtlasMap)
import RankedDominionAtlas.Coverage (rankedDominionCoverage)
import RankedDominionAtlas.Owner (RankedDominionAtlas, RankedDominionAtlasObject, rankedDominionAtlas)
import RankedDominionAtlas.Data (RankedDominionCellData)
import RankedDominionAtlas.Pagination (RankedDominionPaginationScope)
import PageElements (PageElement)

{-@ observedCoverage :: owner:RankedDominionAtlas ownerScope value
      -> source:{PageElement (RankedDominionPaginationScope value) object | cellTraceValid (rankedDominionAtlas owner) source}
      -> datum:{RankedDominionCellData value object | atlasAcceptsDatum (rankedDominionAtlas owner) source datum}
      -> {witness:CoverageWitness ownerScope (RankedDominionPaginationScope value) (RankedDominionCellData value) |
           coverageWitnessCovers (rankedDominionAtlas owner) source datum witness} @-}
observedCoverage :: RankedDominionAtlas ownerScope value
  -> PageElement (RankedDominionPaginationScope value) object -> RankedDominionCellData value object
  -> CoverageWitness ownerScope (RankedDominionPaginationScope value) (RankedDominionCellData value)
observedCoverage = rankedDominionCoverage

{-@ observedMap :: RankedDominionAtlas owner value -> AtlasMap (RankedDominionAtlasObject owner value) @-}
observedMap :: RankedDominionAtlas owner value -> AtlasMap (RankedDominionAtlasObject owner value)
observedMap = rankedDominionAtlasMap
"""
RANKED_COVERAGE_PUBLIC_GUARDS = {
    "ranked coverage certifies its exact source datum": r"""
{-@ proofGuard :: owner:RankedDominionAtlas ownerScope value
      -> source:{PageElement (RankedDominionPaginationScope value) object | cellTraceValid (rankedDominionAtlas owner) source}
      -> datum:{RankedDominionCellData value object | atlasAcceptsDatum (rankedDominionAtlas owner) source datum}
      -> {witness:CoverageWitness ownerScope (RankedDominionPaginationScope value) (RankedDominionCellData value) |
           not (coverageWitnessCovers (rankedDominionAtlas owner) source datum witness)} @-}
proofGuard :: RankedDominionAtlas ownerScope value
  -> PageElement (RankedDominionPaginationScope value) object -> RankedDominionCellData value object
  -> CoverageWitness ownerScope (RankedDominionPaginationScope value) (RankedDominionCellData value)
proofGuard = observedCoverage
""",
    "ranked coverage requires the owning source trace": r"""
{-@ proofGuard :: owner:RankedDominionAtlas ownerScope value
      -> source:PageElement (RankedDominionPaginationScope value) object
      -> datum:{RankedDominionCellData value object | atlasAcceptsDatum (rankedDominionAtlas owner) source datum}
      -> CoverageWitness ownerScope (RankedDominionPaginationScope value) (RankedDominionCellData value) @-}
proofGuard :: RankedDominionAtlas ownerScope value
  -> PageElement (RankedDominionPaginationScope value) object -> RankedDominionCellData value object
  -> CoverageWitness ownerScope (RankedDominionPaginationScope value) (RankedDominionCellData value)
proofGuard = observedCoverage
""",
    "ranked coverage requires accepted data": r"""
{-@ proofGuard :: owner:RankedDominionAtlas ownerScope value
      -> source:{PageElement (RankedDominionPaginationScope value) object | cellTraceValid (rankedDominionAtlas owner) source}
      -> RankedDominionCellData value object
      -> CoverageWitness ownerScope (RankedDominionPaginationScope value) (RankedDominionCellData value) @-}
proofGuard :: RankedDominionAtlas ownerScope value
  -> PageElement (RankedDominionPaginationScope value) object -> RankedDominionCellData value object
  -> CoverageWitness ownerScope (RankedDominionPaginationScope value) (RankedDominionCellData value)
proofGuard = observedCoverage
""",
}


RANKED_COMPONENT_PUBLIC_SOURCE = r"""
{-# LANGUAGE CPP #-}
#include "LiquidPlugin.h"
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--higherorder" @-}
module RankedComponentPublicGuard where
import Atlas (atlasPageElements)
import AtlasExtent (cellTraceValid)
import Coalition.Element (coalitionElementAt)
import DomanialInsertion.Core (DomanialInsertion (..))
import PageElements (PageElement, originPageElement)
import PageElements.Structure (SomePageElement (..))
import RankedDominionAtlas.Coalition
import RankedDominionAtlas.Owner
import RankedDominionAtlas.Data (RankedDominionCellData, cellValue)
import RankedDominionAtlas.Pagination (RankedDominionPaginationScope)

{-@ observedComponentDecoded :: insertion:DomanialInsertion source value
      -> datum:RankedDominionCellData value object
      -> {result:Maybe source | result == preimage insertion (cellValue datum)} @-}
observedComponentDecoded :: DomanialInsertion source value -> RankedDominionCellData value object -> Maybe source
observedComponentDecoded = rankedComponentBackward

{-@ observedComponentRoundTrip :: owner:RankedDominionAtlas ownerScope value
      -> insertion:DomanialInsertion source value
      -> target:{PageElement (RankedDominionPaginationScope value) object |
           cellTraceValid (rankedDominionAtlas owner) target
           && SomePageElement target == originPageElement (atlasPageElements (rankedDominionAtlas owner))}
      -> value:source
      -> {rankedComponentBackward insertion
           (coalitionElementAt (rankedDominionAtlas owner) target (rankedCoalitionForward owner insertion value))
           == Just value} @-}
observedComponentRoundTrip :: RankedDominionAtlas ownerScope value -> DomanialInsertion source value
  -> PageElement (RankedDominionPaginationScope value) object -> source -> ()
observedComponentRoundTrip = rankedComponentLeftInverse
"""
RANKED_COMPONENT_PUBLIC_GUARDS = {
    "ranked component inverse retains raw datum decoding": r"""
{-@ proofGuard :: insertion:DomanialInsertion source value
      -> datum:RankedDominionCellData value object
      -> {result:Maybe source | result /= preimage insertion (cellValue datum)} @-}
proofGuard :: DomanialInsertion source value -> RankedDominionCellData value object -> Maybe source
proofGuard = observedComponentDecoded
""",
    "ranked component inverse retains its transported round trip": r"""
{-@ proofGuard :: owner:RankedDominionAtlas ownerScope value
      -> insertion:DomanialInsertion source value
      -> target:{PageElement (RankedDominionPaginationScope value) object |
           cellTraceValid (rankedDominionAtlas owner) target
           && SomePageElement target == originPageElement (atlasPageElements (rankedDominionAtlas owner))}
      -> value:source
      -> {rankedComponentBackward insertion
           (coalitionElementAt (rankedDominionAtlas owner) target (rankedCoalitionForward owner insertion value))
           /= Just value} @-}
proofGuard :: RankedDominionAtlas ownerScope value -> DomanialInsertion source value
  -> PageElement (RankedDominionPaginationScope value) object -> source -> ()
proofGuard = observedComponentRoundTrip
""",
    "ranked component inverse requires the owning origin": r"""
{-@ proofGuard :: owner:RankedDominionAtlas ownerScope value
      -> DomanialInsertion source value
      -> target:{PageElement (RankedDominionPaginationScope value) object |
           cellTraceValid (rankedDominionAtlas owner) target}
      -> source -> () @-}
proofGuard :: RankedDominionAtlas ownerScope value -> DomanialInsertion source value
  -> PageElement (RankedDominionPaginationScope value) object -> source -> ()
proofGuard = rankedComponentLeftInverse
""",
}

RANKED_COALITION_PUBLIC_SOURCE = r"""
{-# LANGUAGE CPP #-}
#include "LiquidPlugin.h"
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}
{-@ LIQUID "--higherorder" @-}
module RankedCoalitionPublicGuard where
import Atlas (atlasPageElements)
import Coalition.Element (CoalitionData, coalitionElementValid, coalitionElementSource, coalitionElementRank)
import Dominion (rank, unrank)
import DomanialInsertion.Core (DomanialInsertion (..))
import PageElements (originPageElement)
import RankedDominionAtlas.Coalition
import RankedDominionAtlas.Owner
import RankedDominionAtlas.Data (RankedDominionCellData)
import RankedDominionAtlas.Pagination (RankedDominionPaginationScope)

{-@ observedElement :: owner:RankedDominionAtlas ownerScope value -> value:value
      -> {element:CoalitionData ownerScope (RankedDominionPaginationScope value) (RankedDominionCellData value) |
           coalitionElementValid (rankedDominionAtlas owner) element
           && coalitionElementSource element == originPageElement (atlasPageElements (rankedDominionAtlas owner))
           && coalitionElementRank element == rank (rankedDominionValueDominion owner) value} @-}
observedElement :: RankedDominionAtlas ownerScope value -> value
  -> CoalitionData ownerScope (RankedDominionPaginationScope value) (RankedDominionCellData value)
observedElement = rankedDominionCoalitionElement

{-@ observedDecoded :: owner:RankedDominionAtlas ownerScope value -> insertion:DomanialInsertion source value
      -> element:CoalitionData ownerScope (RankedDominionPaginationScope value) (RankedDominionCellData value)
      -> decoded:{value | unrank (rankedDominionValueDominion owner) (coalitionElementRank element) == Just decoded}
      -> {result:Maybe source | result == preimage insertion decoded} @-}
observedDecoded :: RankedDominionAtlas ownerScope value -> DomanialInsertion source value
  -> CoalitionData ownerScope (RankedDominionPaginationScope value) (RankedDominionCellData value)
  -> value -> Maybe source
observedDecoded owner insertion element _ = rankedCoalitionBackward owner insertion element

{-@ observedMissing :: owner:RankedDominionAtlas ownerScope value -> DomanialInsertion source value
      -> element:{CoalitionData ownerScope (RankedDominionPaginationScope value) (RankedDominionCellData value) |
           unrank (rankedDominionValueDominion owner) (coalitionElementRank element) == Nothing}
      -> {result:Maybe source | result == Nothing} @-}
observedMissing :: RankedDominionAtlas ownerScope value -> DomanialInsertion source value
  -> CoalitionData ownerScope (RankedDominionPaginationScope value) (RankedDominionCellData value) -> Maybe source
observedMissing = rankedCoalitionBackward

{-@ observedRoundTrip :: owner:RankedDominionAtlas ownerScope value
      -> insertion:DomanialInsertion source value -> value:source
      -> {rankedCoalitionBackward owner insertion (rankedCoalitionForward owner insertion value) == Just value} @-}
observedRoundTrip :: RankedDominionAtlas ownerScope value -> DomanialInsertion source value -> source -> ()
observedRoundTrip owner insertion value = insertionLeftInverse (rankedCoalitionInsertion owner insertion) value
"""
RANKED_COALITION_PUBLIC_GUARDS = {
    "ranked coalition caches the original Dominion rank": r"""
{-@ proofGuard :: owner:RankedDominionAtlas ownerScope value -> value:value
      -> {element:CoalitionData ownerScope (RankedDominionPaginationScope value) (RankedDominionCellData value) |
           coalitionElementRank element /= rank (rankedDominionValueDominion owner) value} @-}
proofGuard :: RankedDominionAtlas ownerScope value -> value
  -> CoalitionData ownerScope (RankedDominionPaginationScope value) (RankedDominionCellData value)
proofGuard = observedElement
""",
    "ranked coalition constructor retains validity": r"""
{-@ proofGuard :: owner:RankedDominionAtlas ownerScope value -> value
      -> {element:CoalitionData ownerScope (RankedDominionPaginationScope value) (RankedDominionCellData value) |
           not (coalitionElementValid (rankedDominionAtlas owner) element)} @-}
proofGuard :: RankedDominionAtlas ownerScope value -> value
  -> CoalitionData ownerScope (RankedDominionPaginationScope value) (RankedDominionCellData value)
proofGuard = observedElement
""",
    "ranked coalition constructor retains the owning origin": r"""
{-@ proofGuard :: owner:RankedDominionAtlas ownerScope value -> value
      -> {element:CoalitionData ownerScope (RankedDominionPaginationScope value) (RankedDominionCellData value) |
           coalitionElementSource element /= originPageElement (atlasPageElements (rankedDominionAtlas owner))} @-}
proofGuard :: RankedDominionAtlas ownerScope value -> value
  -> CoalitionData ownerScope (RankedDominionPaginationScope value) (RankedDominionCellData value)
proofGuard = observedElement
""",
    "ranked coalition raw inverse uses the cached-rank decoder": r"""
{-@ proofGuard :: owner:RankedDominionAtlas ownerScope value -> insertion:DomanialInsertion source value
      -> element:CoalitionData ownerScope (RankedDominionPaginationScope value) (RankedDominionCellData value)
      -> decoded:{value | unrank (rankedDominionValueDominion owner) (coalitionElementRank element) == Just decoded}
      -> {result:Maybe source | result /= preimage insertion decoded} @-}
proofGuard :: RankedDominionAtlas ownerScope value -> DomanialInsertion source value
  -> CoalitionData ownerScope (RankedDominionPaginationScope value) (RankedDominionCellData value)
  -> value -> Maybe source
proofGuard = observedDecoded
""",
    "ranked coalition raw inverse preserves failed decoding": r"""
{-@ proofGuard :: owner:RankedDominionAtlas ownerScope value -> DomanialInsertion source value
      -> element:{CoalitionData ownerScope (RankedDominionPaginationScope value) (RankedDominionCellData value) |
           unrank (rankedDominionValueDominion owner) (coalitionElementRank element) == Nothing}
      -> {result:Maybe source | result /= Nothing} @-}
proofGuard :: RankedDominionAtlas ownerScope value -> DomanialInsertion source value
  -> CoalitionData ownerScope (RankedDominionPaginationScope value) (RankedDominionCellData value) -> Maybe source
proofGuard = observedMissing
""",
    "ranked coalition insertion retains its left inverse": r"""
{-@ proofGuard :: owner:RankedDominionAtlas ownerScope value
      -> insertion:DomanialInsertion source value -> value:source
      -> {rankedCoalitionBackward owner insertion (rankedCoalitionForward owner insertion value) /= Just value} @-}
proofGuard :: RankedDominionAtlas ownerScope value -> DomanialInsertion source value -> source -> ()
proofGuard = observedRoundTrip
""",
}

CHAINED_COALITION_PUBLIC_SOURCE = r"""
{-# LANGUAGE CPP #-}
#include "LiquidPlugin.h"
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--higherorder" @-}
module ChainedCoalitionPublicGuard where
import Atlas (atlasPageElements)
import ChainedDominionAtlas (ChainedDominionAtlas, chainedDominionAtlas, chainedDominionCoalitionElement)
import ChainedDominionAtlas.Coalition
  ( chainedCoalitionValue, chainedCoalitionReconstruct, chainedCoalitionInsertion, chainedCoalitionForward, chainedCoalitionBackward )
import ChainedDominionAtlas.Data (ChainedDominionCellData)
import Coalition.Element (CoalitionData, coalitionElementValid, coalitionElementSource)
import DomanialInsertion.Core (DomanialInsertion (..))
import PageElements (originPageElement)

{-@ observedCoalition :: owner:ChainedDominionAtlas ownerScope scope value -> value:value
      -> {element:CoalitionData ownerScope scope (ChainedDominionCellData value) |
           chainedCoalitionValue element == value
           && coalitionElementValid (chainedDominionAtlas owner) element
           && coalitionElementSource element == originPageElement (atlasPageElements (chainedDominionAtlas owner))} @-}
observedCoalition :: ChainedDominionAtlas ownerScope scope value -> value
  -> CoalitionData ownerScope scope (ChainedDominionCellData value)
observedCoalition = chainedDominionCoalitionElement

{-@ observedReconstruction :: owner:ChainedDominionAtlas ownerScope scope value
      -> element:{CoalitionData ownerScope scope (ChainedDominionCellData value) |
           coalitionElementValid (chainedDominionAtlas owner) element
           && coalitionElementSource element == originPageElement (atlasPageElements (chainedDominionAtlas owner))}
      -> {result:CoalitionData ownerScope scope (ChainedDominionCellData value) | result == element} @-}
observedReconstruction :: ChainedDominionAtlas ownerScope scope value
  -> CoalitionData ownerScope scope (ChainedDominionCellData value)
  -> CoalitionData ownerScope scope (ChainedDominionCellData value)
observedReconstruction owner element =
  chainedCoalitionReconstruct owner element `seq`
    chainedDominionCoalitionElement owner (chainedCoalitionValue element)

{-@ observedInverse :: owner:ChainedDominionAtlas ownerScope scope value
      -> insertion:DomanialInsertion source value
      -> element:{CoalitionData ownerScope scope (ChainedDominionCellData value) |
           coalitionElementValid (chainedDominionAtlas owner) element
           && coalitionElementSource element == originPageElement (atlasPageElements (chainedDominionAtlas owner))}
      -> {result:Maybe source | result == chainedCoalitionBackward insertion element} @-}
observedInverse :: ChainedDominionAtlas ownerScope scope value -> DomanialInsertion source value
  -> CoalitionData ownerScope scope (ChainedDominionCellData value) -> Maybe source
observedInverse owner insertion element =
  case chainedCoalitionInsertion owner insertion of
    DomanialInsertion _ backward _ -> backward element

{-@ observedRoundTrip :: owner:ChainedDominionAtlas ownerScope scope value
      -> insertion:DomanialInsertion source value -> value:source
      -> {result:Maybe source | result == Just value} @-}
observedRoundTrip :: ChainedDominionAtlas ownerScope scope value -> DomanialInsertion source value -> source -> Maybe source
observedRoundTrip owner insertion value =
  case chainedCoalitionInsertion owner insertion of
    DomanialInsertion forward backward leftInverse -> leftInverse value `seq` backward (forward value)
"""
CHAINED_COALITION_PUBLIC_GUARDS = {
    "chained coalition reconstruction retains the entire canonical element": r"""
{-@ proofGuard :: owner:ChainedDominionAtlas ownerScope scope value
      -> element:{CoalitionData ownerScope scope (ChainedDominionCellData value) |
           coalitionElementValid (chainedDominionAtlas owner) element
           && coalitionElementSource element == originPageElement (atlasPageElements (chainedDominionAtlas owner))}
      -> {result:CoalitionData ownerScope scope (ChainedDominionCellData value) | result /= element} @-}
proofGuard :: ChainedDominionAtlas ownerScope scope value
  -> CoalitionData ownerScope scope (ChainedDominionCellData value) -> CoalitionData ownerScope scope (ChainedDominionCellData value)
proofGuard = observedReconstruction
""",
    "chained coalition reconstruction requires a valid element": r"""
{-@ proofGuard :: owner:ChainedDominionAtlas ownerScope scope value
      -> element:{CoalitionData ownerScope scope (ChainedDominionCellData value) |
           coalitionElementSource element == originPageElement (atlasPageElements (chainedDominionAtlas owner))}
      -> CoalitionData ownerScope scope (ChainedDominionCellData value) @-}
proofGuard :: ChainedDominionAtlas ownerScope scope value
  -> CoalitionData ownerScope scope (ChainedDominionCellData value) -> CoalitionData ownerScope scope (ChainedDominionCellData value)
proofGuard = observedReconstruction
""",
    "chained coalition reconstruction requires the canonical origin": r"""
{-@ proofGuard :: owner:ChainedDominionAtlas ownerScope scope value
      -> element:{CoalitionData ownerScope scope (ChainedDominionCellData value) |
           coalitionElementValid (chainedDominionAtlas owner) element}
      -> CoalitionData ownerScope scope (ChainedDominionCellData value) @-}
proofGuard :: ChainedDominionAtlas ownerScope scope value
  -> CoalitionData ownerScope scope (ChainedDominionCellData value) -> CoalitionData ownerScope scope (ChainedDominionCellData value)
proofGuard = observedReconstruction
""",
    "chained coalition insertion preserves its partial inverse": r"""
{-@ proofGuard :: owner:ChainedDominionAtlas ownerScope scope value
      -> insertion:DomanialInsertion source value
      -> element:{CoalitionData ownerScope scope (ChainedDominionCellData value) |
           coalitionElementValid (chainedDominionAtlas owner) element
           && coalitionElementSource element == originPageElement (atlasPageElements (chainedDominionAtlas owner))}
      -> {result:Maybe source | result /= chainedCoalitionBackward insertion element} @-}
proofGuard :: ChainedDominionAtlas ownerScope scope value -> DomanialInsertion source value
  -> CoalitionData ownerScope scope (ChainedDominionCellData value) -> Maybe source
proofGuard = observedInverse
""",
    "chained coalition insertion preserves its left inverse": r"""
{-@ proofGuard :: owner:ChainedDominionAtlas ownerScope scope value
      -> DomanialInsertion source value -> value:source -> {result:Maybe source | result /= Just value} @-}
proofGuard :: ChainedDominionAtlas ownerScope scope value -> DomanialInsertion source value -> source -> Maybe source
proofGuard = observedRoundTrip
""",
    "chained coalition retains its input value": r"""
{-@ proofGuard :: owner:ChainedDominionAtlas ownerScope scope value -> value:value
      -> {element:CoalitionData ownerScope scope (ChainedDominionCellData value) | chainedCoalitionValue element /= value} @-}
proofGuard :: ChainedDominionAtlas ownerScope scope value -> value
  -> CoalitionData ownerScope scope (ChainedDominionCellData value)
proofGuard = observedCoalition
""",
    "chained coalition retains checked validity": r"""
{-@ proofGuard :: owner:ChainedDominionAtlas ownerScope scope value -> value
      -> {element:CoalitionData ownerScope scope (ChainedDominionCellData value) |
           not (coalitionElementValid (chainedDominionAtlas owner) element)} @-}
proofGuard :: ChainedDominionAtlas ownerScope scope value -> value
  -> CoalitionData ownerScope scope (ChainedDominionCellData value)
proofGuard = observedCoalition
""",
    "chained coalition retains the actual origin": r"""
{-@ proofGuard :: owner:ChainedDominionAtlas ownerScope scope value -> value
      -> {element:CoalitionData ownerScope scope (ChainedDominionCellData value) |
           coalitionElementSource element /= originPageElement (atlasPageElements (chainedDominionAtlas owner))} @-}
proofGuard :: ChainedDominionAtlas ownerScope scope value -> value
  -> CoalitionData ownerScope scope (ChainedDominionCellData value)
proofGuard = observedCoalition
""",
}

CHAINED_CANONICAL_PUBLIC_SOURCE = r"""
{-# LANGUAGE CPP #-}
{-# LANGUAGE ScopedTypeVariables #-}
#include "LiquidPlugin.h"
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--higherorder" @-}
module ChainedCanonicalPublicGuard where
import Atlas (Atlas, AtlasPresentation, atlasDescription, atlasPagination, atlasFolio)
import Chain (Chain)
import ChainedDominionAtlas
  ( ChainedDominionAtlas, CanonicalChainedDominion, CanonicalChainedAtlasScope
  , CanonicalChainedPaginationScope, canonicalChainedDominionAtlas, chainedDominionAtlas )
import ChainedDominionAtlas.Canonical
  ( canonicalChainedFirst, canonicalChainedChain, canonicalChainedValueDominion
  , canonicalPresentation, canonicalPagination )
import ChainedDominionAtlas.Data (ChainedDominionCellData)
import ChainedDominionAtlas.Owner (chainedDominionFirst, chainedDominionChain, chainedDominionValueDominion)
import Data.Proxy (Proxy (..))
import Folio (lastChain)
import Pagination (Pagination)

{-@ observedOwner :: CanonicalChainedDominion value => proxy:Proxy value
      -> {owner:ChainedDominionAtlas (CanonicalChainedAtlasScope value) (CanonicalChainedPaginationScope value) value |
           chainedDominionFirst owner == canonicalChainedFirst proxy
           && chainedDominionChain owner == canonicalChainedChain proxy
           && chainedDominionValueDominion owner == canonicalChainedValueDominion proxy
           && atlasDescription (chainedDominionAtlas owner) == canonicalPresentation proxy
           && atlasPagination (chainedDominionAtlas owner) == canonicalPagination proxy} @-}
observedOwner :: forall value. CanonicalChainedDominion value => Proxy value
  -> ChainedDominionAtlas (CanonicalChainedAtlasScope value) (CanonicalChainedPaginationScope value) value
observedOwner Proxy = canonicalChainedDominionAtlas

{-@ observedChain :: CanonicalChainedDominion value => proxy:Proxy value
      -> {chain:Chain value | chain == canonicalChainedChain proxy} @-}
observedChain :: CanonicalChainedDominion value => Proxy value -> Chain value
observedChain proxy = lastChain (atlasFolio (chainedDominionAtlas (observedOwner proxy)))

{-@ observedPresentation :: CanonicalChainedDominion value => proxy:Proxy value
      -> {presentation:AtlasPresentation (CanonicalChainedPaginationScope value) (ChainedDominionCellData value) () value |
           presentation == canonicalPresentation proxy} @-}
observedPresentation :: CanonicalChainedDominion value => Proxy value
  -> AtlasPresentation (CanonicalChainedPaginationScope value) (ChainedDominionCellData value) () value
observedPresentation proxy = readDescription (chainedDominionAtlas (observedOwner proxy))

-- Keep the newtype observation polymorphic before specializing the fixed scope.
{-@ readDescription :: value:Atlas owner scope datum origin final
      -> {presentation:AtlasPresentation scope datum origin final | presentation == atlasDescription value} @-}
readDescription :: Atlas owner scope datum origin final -> AtlasPresentation scope datum origin final
readDescription = atlasDescription

{-@ observedPagination :: CanonicalChainedDominion value => proxy:Proxy value
      -> {pages:Pagination (CanonicalChainedPaginationScope value) () value | pages == canonicalPagination proxy} @-}
observedPagination :: CanonicalChainedDominion value => Proxy value
  -> Pagination (CanonicalChainedPaginationScope value) () value
observedPagination proxy = atlasPagination (chainedDominionAtlas (observedOwner proxy))
"""
CHAINED_CANONICAL_PUBLIC_GUARDS = {
    "chained canonical allocation retains its first value": r"""
{-@ proofGuard :: CanonicalChainedDominion value => proxy:Proxy value
      -> {owner:ChainedDominionAtlas (CanonicalChainedAtlasScope value) (CanonicalChainedPaginationScope value) value |
           chainedDominionFirst owner /= canonicalChainedFirst proxy} @-}
proofGuard :: CanonicalChainedDominion value => Proxy value
  -> ChainedDominionAtlas (CanonicalChainedAtlasScope value) (CanonicalChainedPaginationScope value) value
proofGuard = observedOwner
""",
    "chained canonical allocation retains its final chain": r"""
{-@ proofGuard :: CanonicalChainedDominion value => proxy:Proxy value
      -> {chain:Chain value | chain /= canonicalChainedChain proxy} @-}
proofGuard :: CanonicalChainedDominion value => Proxy value -> Chain value
proofGuard = observedChain
""",
    "chained canonical allocation retains its Dominion": r"""
{-@ proofGuard :: CanonicalChainedDominion value => proxy:Proxy value
      -> {owner:ChainedDominionAtlas (CanonicalChainedAtlasScope value) (CanonicalChainedPaginationScope value) value |
           chainedDominionValueDominion owner /= canonicalChainedValueDominion proxy} @-}
proofGuard :: CanonicalChainedDominion value => Proxy value
  -> ChainedDominionAtlas (CanonicalChainedAtlasScope value) (CanonicalChainedPaginationScope value) value
proofGuard = observedOwner
""",
    "chained canonical allocation retains its exact presentation": r"""
{-@ proofGuard :: CanonicalChainedDominion value => proxy:Proxy value
      -> {presentation:AtlasPresentation (CanonicalChainedPaginationScope value) (ChainedDominionCellData value) () value |
           presentation /= canonicalPresentation proxy} @-}
proofGuard :: CanonicalChainedDominion value => Proxy value
  -> AtlasPresentation (CanonicalChainedPaginationScope value) (ChainedDominionCellData value) () value
proofGuard = observedPresentation
""",
    "chained canonical allocation retains its exact pagination": r"""
{-@ proofGuard :: CanonicalChainedDominion value => proxy:Proxy value
      -> {pages:Pagination (CanonicalChainedPaginationScope value) () value | pages /= canonicalPagination proxy} @-}
proofGuard :: CanonicalChainedDominion value => Proxy value
  -> Pagination (CanonicalChainedPaginationScope value) () value
proofGuard = observedPagination
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
        def check_group(source, guards):
            source = re.sub(r'#include "[^"]*LiquidPlugin.h"',
                            f'#include "{HASKELL / "src/DatraCore/LiquidPlugin.h"}"',
                            source)
            for description, guard in guards.items():
                if pattern and not re.search(pattern, description):
                    continue
                target.write_text(source + "\n" + guard)
                result = subprocess.run(command + [str(target)], cwd=HASKELL,
                                        text=True, capture_output=True)
                output = result.stdout + result.stderr
                error_lines = re.findall(re.escape(str(target)) + r":(\d+):\d+: error:", output)
                guard_start_line = source.count("\n") + 2
                if (result.returncode == 0 or "Liquid Type Mismatch" not in output
                        or not error_lines
                        or any(int(line) < guard_start_line for line in error_lines)):
                    raise SystemExit(f"Proof guard did not produce the required rejection: {description}\n{output}")
                print(f"Rejected false law: {description}")

        for source_path, guards in [(SOURCE, GUARDS), (CHAIN_SOURCE, CHAIN_GUARDS),
                                    (DATA_TRANSFORMATION_SOURCE, DATA_TRANSFORMATION_GUARDS),
                                    (DATA_TRANSFORMATION_CORE_SOURCE, DATA_TRANSFORMATION_CORE_GUARDS),
                                    (NATURAL_SEARCH_SOURCE, NATURAL_SEARCH_GUARDS),
                                    (CHAIN_SINGLETON_SOURCE, CHAIN_SINGLETON_GUARDS),
                                    (CONSOLIDATION_SOURCE, CONSOLIDATION_GUARDS),
                                    (ORDERED_CONSOLIDATION_SOURCE, ORDERED_CONSOLIDATION_GUARDS),
                                    (SUM_CONSOLIDATION_SOURCE, SUM_CONSOLIDATION_GUARDS),
                                    (REINDEX_CONSOLIDATION_SOURCE, REINDEX_CONSOLIDATION_GUARDS),
                                    (POSITION_SOURCE, POSITION_GUARDS),
                                    (ENDPOINTS_SOURCE, ENDPOINTS_GUARDS),
                                    (MERGE_ASSEMBLY_SOURCE, MERGE_ASSEMBLY_GUARDS),
                                    (MERGE_TRANSPORT_SOURCE, MERGE_TRANSPORT_GUARDS),
                                    (MERGE_ACTION_SOURCE, MERGE_ACTION_GUARDS),
                                    (SEQUENCE_MEMBER_SOURCE, SEQUENCE_MEMBER_GUARDS),
                                    (SEQUENCE_PAGE_SOURCE, SEQUENCE_PAGE_GUARDS),
                                    (SEQUENCE_ASSEMBLY_SOURCE, SEQUENCE_ASSEMBLY_GUARDS),
                                    (PAGE_TRACE_SOURCE, PAGE_TRACE_GUARDS),
                                    (MERGE_PAGE_SOURCE, MERGE_PAGE_GUARDS),
                                    (STABLE_SOURCE, STABLE_GUARDS),
                                    (DOMINC_SOURCE, DOMINC_GUARDS),
                                    (DOMINC_DATA_SOURCE, DOMINC_DATA_GUARDS),
                                    (DOMINC_PRESENTATION_SOURCE, DOMINC_PRESENTATION_GUARDS),
                                    (COALITION_ELEMENT_SOURCE, COALITION_ELEMENT_GUARDS),
                                    (TRANSVERSAL_SOURCE, TRANSVERSAL_GUARDS),
                                    (COVERED_API_SOURCE, COVERED_API_GUARDS),
                                    (COVERAGE_REPRESENTATION_SOURCE, COVERAGE_REPRESENTATION_GUARDS),
                                    (COVERAGE_PUBLIC_SOURCE, COVERAGE_PUBLIC_GUARDS),
                                    (ATLAS_MAP_SOURCE, ATLAS_MAP_GUARDS),
                                    (ATLAS_MAP_API_SOURCE, ATLAS_MAP_API_GUARDS),
                                    (CHARTER_SOURCE, CHARTER_GUARDS),
                                    (CHARTER_PRESENTATION_SOURCE, CHARTER_PRESENTATION_GUARDS),
                                    (RANK_IMAGE_SOURCE, RANK_IMAGE_GUARDS),
                                    (MERGE_SOURCE, MERGE_GUARDS),
                                    (SEQUENCE_SOURCE, SEQUENCE_GUARDS),
                                    (EXTENT_SOURCE, EXTENT_GUARDS),
                                    (FOLIO_SOURCE, FOLIO_GUARDS),
                                    (FOLIO_API_SOURCE, FOLIO_API_GUARDS),
                                    (PAGE_ARROW_SOURCE, PAGE_ARROW_GUARDS),
                                    (TERRITORY_SOURCE, TERRITORY_GUARDS),
                                    (PAGE_API_SOURCE, PAGE_API_GUARDS),
                                    (PAGE_CONSTRUCTION_SOURCE, PAGE_CONSTRUCTION_GUARDS),
                                    (DOMINION_LOOKUP_SOURCE, DOMINION_LOOKUP_GUARDS),
                                    (PAGINATION_API_SOURCE, PAGINATION_API_GUARDS),
                                    (PAGE_INDEX_SOURCE, PAGE_INDEX_GUARDS),
                                    (ATLAS_SOURCE, ATLAS_GUARDS),
                                    (ATLAS_PRESENTATION_SOURCE, ATLAS_PRESENTATION_GUARDS),
                                    (ATLAS_CONSTRUCTION_SOURCE, ATLAS_CONSTRUCTION_GUARDS),
                                    (ATLAS_DATA_SOURCE, ATLAS_DATA_GUARDS),
                                    (MEMBERSHIP_DOMINION_SOURCE, MEMBERSHIP_DOMINION_GUARDS),
                                    (MERGE_RESOLUTION_SOURCE, MERGE_RESOLUTION_GUARDS),
                                    (MERGE_CELL_SOURCE, MERGE_CELL_GUARDS),
                                    (SEQUENCE_RESOLUTION_SOURCE, SEQUENCE_RESOLUTION_GUARDS)]:
            check_group(source_path.read_text(), guards)

        check_group(COALITION_PUBLIC_SOURCE, COALITION_CANONICAL_GUARDS)
        check_group(COALITION_ACTION_PUBLIC_SOURCE, COALITION_ACTION_PUBLIC_GUARDS)
        check_group(COALITION_TRANSPORT_PUBLIC_SOURCE, COALITION_TRANSPORT_PUBLIC_GUARDS)
        check_group(TRANSVERSAL_PUBLIC_SOURCE, TRANSVERSAL_PUBLIC_GUARDS)
        check_group(INSERTION_COMPOSITION_PUBLIC_SOURCE, INSERTION_COMPOSITION_PUBLIC_GUARDS)
        check_group(STABLE_PREIMAGE_PUBLIC_SOURCE, STABLE_PREIMAGE_PUBLIC_GUARDS)
        check_group(PRIMITIVE_MORPHISM_SOURCE.read_text(), PRIMITIVE_MORPHISM_STORAGE_GUARDS)
        check_group(PRIMITIVE_MORPHISM_PUBLIC_SOURCE, PRIMITIVE_MORPHISM_PUBLIC_GUARDS)
        check_group(TOTAL_MAP_PUBLIC_SOURCE, TOTAL_MAP_PUBLIC_GUARDS)
        check_group(RANKED_DATA_PUBLIC_SOURCE, RANKED_DATA_PUBLIC_GUARDS)
        check_group(CHAINED_DATA_PUBLIC_SOURCE, CHAINED_DATA_PUBLIC_GUARDS)
        check_group(RANKED_ACTION_PUBLIC_SOURCE, RANKED_ACTION_PUBLIC_GUARDS)
        check_group(CHAINED_ACTION_PUBLIC_SOURCE, CHAINED_ACTION_PUBLIC_GUARDS)
        check_group(RANKED_PRESENTATION_PUBLIC_SOURCE, RANKED_PRESENTATION_PUBLIC_GUARDS)
        check_group(CHAINED_PRESENTATION_PUBLIC_SOURCE, CHAINED_PRESENTATION_PUBLIC_GUARDS)
        check_group(CHAINED_ASSEMBLY_PUBLIC_SOURCE, CHAINED_ASSEMBLY_PUBLIC_GUARDS)
        check_group(CHAINED_OWNER_PUBLIC_SOURCE, CHAINED_OWNER_PUBLIC_GUARDS)
        check_group(RANKED_OWNER_PUBLIC_SOURCE, RANKED_OWNER_PUBLIC_GUARDS)
        check_group(CHAINED_COVERAGE_PUBLIC_SOURCE, CHAINED_COVERAGE_PUBLIC_GUARDS)
        check_group(RANKED_COVERAGE_PUBLIC_SOURCE, RANKED_COVERAGE_PUBLIC_GUARDS)
        check_group(TWO_PAGE_COVERAGE_PUBLIC_SOURCE, TWO_PAGE_COVERAGE_PUBLIC_GUARDS)
        check_group(CHAINED_COALITION_PUBLIC_SOURCE, CHAINED_COALITION_PUBLIC_GUARDS)
        check_group(RANKED_COALITION_PUBLIC_SOURCE, RANKED_COALITION_PUBLIC_GUARDS)
        check_group(RANKED_COMPONENT_PUBLIC_SOURCE, RANKED_COMPONENT_PUBLIC_GUARDS)
        check_group(DOMINC_COMPONENT_PUBLIC_SOURCE, DOMINC_COMPONENT_PUBLIC_GUARDS)
        check_group(DOMINC_TRANSPORT_PUBLIC_SOURCE, DOMINC_TRANSPORT_PUBLIC_GUARDS)
        check_group(DOMINC_ACTION_PUBLIC_SOURCE, DOMINC_ACTION_PUBLIC_GUARDS)
        check_group(DOMINC_MAPPED_COMPONENT_PUBLIC_SOURCE, DOMINC_MAPPED_COMPONENT_PUBLIC_GUARDS)
        check_group(DOMINC_MORPHISM_PUBLIC_SOURCE, DOMINC_MORPHISM_PUBLIC_GUARDS)
        check_group(TRANSPOSAL_ELEMENT_PUBLIC_SOURCE, TRANSPOSAL_ELEMENT_PUBLIC_GUARDS)
        check_group(TRANSPOSAL_ACTION_PUBLIC_SOURCE, TRANSPOSAL_ACTION_PUBLIC_GUARDS)
        check_group(TRANSPOSAL_OBJECTS_PUBLIC_SOURCE, TRANSPOSAL_OBJECTS_PUBLIC_GUARDS)
        check_group(ATLAS_WITNESS_PUBLIC_SOURCE, ATLAS_WITNESS_PUBLIC_GUARDS)
        check_group(TRANSPOSAL_NATIVE_PUBLIC_SOURCE, TRANSPOSAL_NATIVE_PUBLIC_GUARDS)
        check_group(ORDERED_TRANSPOSAL_PUBLIC_SOURCE, ORDERED_TRANSPOSAL_PUBLIC_GUARDS)
        check_group(CHAINED_CANONICAL_PUBLIC_SOURCE, CHAINED_CANONICAL_PUBLIC_GUARDS)

        typing_guards = [
            ("module PublicCoveredGuard where\nimport AtlasCoveredPageElement (CoveredPageElement)\n",
             "covered carriers retain their Atlas owner",
             "proofGuard :: CoveredPageElement first s d -> CoveredPageElement second s d\nproofGuard = coerce\n",
             ("Couldn't match type", "coerce")),
            ("module PublicCoveredGuard where\nimport AtlasCoveredPageElement (CoveredPageElement)\n",
             "covered carriers retain their page owner",
             "proofGuard :: CoveredPageElement a first d -> CoveredPageElement a second d\nproofGuard = coerce\n",
             ("Couldn't match type", "coerce")),
            ("module PublicCoalitionGuard where\nimport Coalition.Element (CoalitionData)\n",
             "coalition carriers retain their Atlas owner",
             "proofGuard :: CoalitionData first s d -> CoalitionData second s d\nproofGuard = coerce\n",
             ("Couldn't match type", "coerce")),
            ("module PublicCoalitionGuard where\nimport Coalition.Element (CoalitionData)\n",
             "coalition carriers retain their page owner",
             "proofGuard :: CoalitionData a first d -> CoalitionData a second d\nproofGuard = coerce\n",
             ("Couldn't match type", "coerce")),
            ("module PublicChainedGuard where\nimport ChainedDominionAtlas\nimport Chain (Chain)\nimport Dominion (Dominion)\n",
             "chained Dominion construction cannot escape its owners",
             "proofGuard :: value -> Chain value -> Dominion value -> ChainedDominionAtlas chosen pages value\n"
             "proofGuard first values ranks = withChainedDominionAtlas first values ranks (\\owner -> owner)\n",
             ("Couldn't match type", "withChainedDominionAtlas")),
            ("module PublicChainedGuard where\nimport ChainedDominionAtlas\nimport Chain (Chain)\nimport Dominion (Dominion)\n",
             "chained Dominion Atlas owners cannot be coerced together",
             "proofGuard :: ChainedDominionAtlas first pages value -> ChainedDominionAtlas second pages value\n"
             "proofGuard = coerce\n",
             ("Couldn't match type", "coerce")),
            ("module PublicChainedGuard where\nimport ChainedDominionAtlas\nimport Chain (Chain)\nimport Dominion (Dominion)\n",
             "chained Dominion pagination owners cannot be coerced together",
             "proofGuard :: ChainedDominionAtlas owner first value -> ChainedDominionAtlas owner second value\n"
             "proofGuard = coerce\n",
             ("Couldn't match type", "coerce")),
            ("module PublicChainedCanonicalGuard where\nimport ChainedDominionAtlas\nimport Data.Proxy (Proxy)\n",
             "chained canonical construction cannot choose its owner scopes",
             "proofGuard :: CanonicalChainedDominion value => Proxy value -> ChainedDominionAtlas chosen pages value\n"
             "proofGuard _ = canonicalChainedDominionAtlas\n",
             ("Couldn't match type", "canonicalChainedDominionAtlas")),
            ("module PublicIndexedGuard where\nimport MapOperators.IndexedAtlasMap\nimport ChainedDominionAtlas (ChainedDominionAtlas)\n",
             "indexed Atlas elimination cannot escape its owners",
             "proofGuard :: IndexedAtlasMap value -> ChainedDominionAtlas chosen pages value\n"
             "proofGuard valueMap = withIndexedAtlas valueMap (\\owner -> owner)\n",
             ("Couldn't match type", "withIndexedAtlas")),
            ("module PublicRangeGuard where\nimport SuperEllipsisRange\n",
             "range elements cannot be coerced across owning ranges",
             "proofGuard :: SuperEllipsisRange target first -> SuperEllipsisRange target second -> SuperEllipsisRangeMember target first -> SuperEllipsisRangeMember target second\n"
             "proofGuard _ _ = coerce\n",
             ("Couldn't match type", "coerce")),

            (HASKELL / "src/DatraCore/Atlases/Derived/Coalitions/DomanialInclusion/Internal.hs",
             "Dominion inclusion cannot escape its owner scope",
             "proofGuard :: Dominion value -> DominionAtlas chosen value\n"
             "proofGuard source = withDominionAtlas source (\\owner -> owner)\n",
             ("Couldn't match type", "withDominionAtlas")),
            (HASKELL / "src/DatraCore/Atlases/Derived/Coalitions/DomanialInclusion/Internal.hs",
             "Dominion inclusion owners cannot be coerced together",
             "proofGuard :: DominionAtlas first value -> DominionAtlas second value\n"
             "proofGuard = coerce\n",
             ("Couldn't match type", "coerce")),
            (ATLAS_CONSTRUCTION_SOURCE, "fixed Atlas construction cannot choose its output scope",
             "proofGuard :: AtlasConstruction recipe s d o f => Proxy recipe -> Atlas chosen s d o f\n"
             "proofGuard = constructAtlas\n",
             ("Couldn't match type", "FixedAtlasScope")),
            (ATLAS_CONSTRUCTION_SOURCE, "fixed Atlas construction retains its recipe identity",
             "proofGuard :: Atlas (FixedAtlasScope first s d o f) s d o f -> Atlas (FixedAtlasScope second s d o f) s d o f\n"
             "proofGuard = coerce\n",
             ("Couldn't match type", "coerce")),
            (RANKED_DOMINION_SOURCE, "ranked Dominion construction cannot escape its owner scope",
             "proofGuard :: Dominion value -> RankedDominionAtlas chosen value\n"
             "proofGuard source = withRankedDominionAtlas source (\\owner -> owner)\n",
             ("Couldn't match type", "withRankedDominionAtlas")),
            (RANKED_DOMINION_SOURCE, "ranked Dominion owners cannot be coerced together",
             "proofGuard :: RankedDominionAtlas first value -> RankedDominionAtlas second value\n"
             "proofGuard = coerce\n",
             ("Couldn't match type", "coerce")),
            (PAGINATION_API_SOURCE, "generative pagination cannot escape its owner scope",
             "proofGuard :: Folio o f -> Pagination s o f\n"
             "proofGuard pages = pagination pages (\\value -> value)\n",
             ("Couldn't match type", "pagination")),
            (PAGE_CONSTRUCTION_SOURCE, "fixed page construction cannot choose its output scope",
             "proofGuard :: PageElementsConstruction recipe o f => Proxy recipe -> PageElements chosen o f\n"
             "proofGuard = constructPageElements\n",
             ("Couldn't match type", "ConstructedPageElementsScope")),
            (PAGE_CONSTRUCTION_SOURCE, "fixed page construction retains its recipe identity",
             "proofGuard :: PageElements (ConstructedPageElementsScope first o f) o f -> PageElements (ConstructedPageElementsScope second o f) o f\n"
             "proofGuard = coerce\n",
             ("Couldn't match type", "coerce")),
            (PAGINATION_API_SOURCE, "pagination assembly cannot change the occurrence owner",
             "proofGuard :: PageElements source o f -> Pagination target o f\n"
             "proofGuard = paginationFromPageElements\n",
             ("Couldn't match type", "paginationFromPageElements")),
            (ATLAS_CONSTRUCTION_SOURCE, "stable construction cannot choose its output scope",
             "proofGuard :: AtlasDataConstruction construction => Atlas a s d o f -> Atlas chosen s (construction a s d) o f\n"
             "proofGuard = constructAtlasData\n",
             ("Couldn't match type", "ConstructedAtlasScope")),
            (ATLAS_CONSTRUCTION_SOURCE, "construction scope retains its recipe identity",
             "proofGuard :: Atlas (ConstructedAtlasScope first a s d) s payload o f -> Atlas (ConstructedAtlasScope second a s d) s payload o f\n"
             "proofGuard = coerce\n",
             ("Couldn't match type", "coerce")),
            (ATLAS_CONSTRUCTION_SOURCE, "construction scope retains its original owner",
             "proofGuard :: Atlas (ConstructedAtlasScope recipe first s d) s payload o f -> Atlas (ConstructedAtlasScope recipe second s d) s payload o f\n"
             "proofGuard = coerce\n",
             ("Couldn't match type", "coerce")),
            (MERGE_SOURCE, "merge datums retain their cell identity",
             "proofGuard :: AtlasMergeDatum source -> AtlasMergeDatum target\nproofGuard = coerce\n",
             ("Couldn't match type", "coerce")),
            (SEQUENCE_SOURCE, "sequence datums retain their cell identity",
             "proofGuard :: AtlasSequenceDatum source -> AtlasSequenceDatum target\nproofGuard = coerce\n",
             ("Couldn't match type", "coerce")),
            (ATLAS_PRESENTATION_SOURCE, "Atlas presentation allocation keeps its scope generative",
             "proofGuard :: AtlasPresentation s d o f -> Atlas a s d o f\n"
             "proofGuard presentation = withAtlasPresentation presentation (\\value -> value)\n",
             ("Couldn't match type", "withAtlasPresentation")),
        ]
        for source_path, description, guard, diagnostics in typing_guards:
            if pattern and not re.search(pattern, description):
                continue
            source = re.sub(r'#include "[^"]*LiquidPlugin.h"',
                            f'#include "{HASKELL / "src/DatraCore/LiquidPlugin.h"}"',
                            source_path.read_text() if isinstance(source_path, Path) else source_path)
            if "coerce" in guard:
                source = re.sub(r"^import ", "import Data.Coerce (coerce)\nimport ", source, count=1, flags=re.M)
            target.write_text(source + "\n" + guard)
            result = subprocess.run(command + [str(target)], cwd=HASKELL, text=True, capture_output=True)
            output = result.stdout + result.stderr
            error_lines = re.findall(re.escape(str(target)) + r":(\d+):\d+: error:", output)
            if (result.returncode == 0 or not all(message in output for message in diagnostics)
                    or not any(int(line) > source.count("\n") for line in error_lines)):
                raise SystemExit(f"Type guard did not produce the required rejection: {description}\n{output}")
            print(f"Rejected invalid type use: {description}")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--filter", help="Run only guard descriptions matching this regular expression")
    run(parser.parse_args().filter)
