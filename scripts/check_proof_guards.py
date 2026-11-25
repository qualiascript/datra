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

COALITION_ELEMENT_SOURCE = HASKELL / "src/DatraCore/Atlases/Derived/Coalitions/Coalition/Element.hs"
COALITION_ELEMENT_GUARDS = {
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
    "stored transversal actions reject coverage evidence for the wrong image": """
{-@ proofGuard
      :: sourceAtlas:Atlas sa ss sd so sf -> targetAtlas:Atlas ta ts td to tf
      -> ordered:OrderedAtlasTransposal (AtlasObject sa ss sd) (AtlasObject ta ts td)
      -> badCoverage:(covered:AtlasCoveredPageElement (AtlasObject sa ss sd)
           -> {w:CoverageWitness ta ts td |
                not (transversalImageCovered sourceAtlas targetAtlas ordered covered w)})
      -> TransversalAction sa ss sd so sf ta ts td to tf @-}
proofGuard :: Atlas sa ss sd so sf -> Atlas ta ts td to tf
  -> OrderedAtlasTransposal (AtlasObject sa ss sd) (AtlasObject ta ts td)
  -> (AtlasCoveredPageElement (AtlasObject sa ss sd) -> CoverageWitness ta ts td)
  -> TransversalAction sa ss sd so sf ta ts td to tf
proofGuard = TransversalAction
""",
    "transversals reject coverage evidence for the wrong image": """
{-@
proofGuard
  :: sourceAtlas:Atlas sa ss sd so sf
  -> targetAtlas:Atlas ta ts td to tf
  -> ordered:OrderedAtlasTransposal (AtlasObject sa ss sd) (AtlasObject ta ts td)
  -> badCoverage:(covered:AtlasCoveredPageElement (AtlasObject sa ss sd)
       -> {w:CoverageWitness ta ts td |
         not (transversalImageCovered sourceAtlas targetAtlas ordered covered w)})
  -> AtlasTransversal (AtlasObject sa ss sd) (AtlasObject ta ts td)
@-}
proofGuard
  :: Atlas sa ss sd so sf
  -> Atlas ta ts td to tf
  -> OrderedAtlasTransposal (AtlasObject sa ss sd) (AtlasObject ta ts td)
  -> (AtlasCoveredPageElement (AtlasObject sa ss sd)
       -> CoverageWitness ta ts td)
  -> AtlasTransversal (AtlasObject sa ss sd) (AtlasObject ta ts td)
proofGuard sourceAtlas targetAtlas ordered badCoverage =
  atlasTransversal sourceAtlas targetAtlas ordered badCoverage
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
