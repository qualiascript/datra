{-# LANGUAGE CPP #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
#include "../../../../LiquidPlugin.h"
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple-local" @-}
{-@ LIQUID "--higherorder" @-}
{-@ qualif MergeAccepted(v:@(0), p:func(0, [@(0); bool])) { p v } @-}

-- | The checked insertion carried by an actual full-spine merge arrow.
module AtlasMerge.Action
  ( atlasMerge, mergeDominionAt, mergeDataMap, mergeDataMapApply, mergeDataAction
  , mergeActionIdentity, mergeActionComposition, mergeActionCoherence, mergeActionDisjoint ) where

import Atlas
  ( Atlas, atlasFolio, atlasForPredicate, AtlasDataAction, atlasPredicateDataAction, atlasMembership
  , atlasActionDomain, atlasActionMembership, atlasActionDataAt, atlasActionMap )
import AtlasMerge.Data (AtlasMergeDatum (..), mergeDatumInsertion, mergeDatumDominion, mergeDatumMap, mergeDatumPreimage, retagMergeDatum)
import AtlasMerge.Assembly (atlasMergeFolio, atlasMergeLength)
import AtlasMerge.Page (AtlasMergePageCell, mergePageContains)
import AtlasMerge.Resolution (mergeCellContains, mergeCellContainsDisjoint)
import AtlasMerge.Transport (mergeOccurrenceTraceValid, mergeCellContainsPreserved)
import DomanialInsertion.Core (DomanialInsertion, applyInsertion, preimage)
import Dominion (Dominion)
import Folio (folioLength)
import qualified Pagination as Pagination
import PageElements
  ( PageElements, pageElementsFolio, pageElementDomain, pageElementTraceValid
  , normalizePageElement, normalizePageElementArrow, pageElementTraceValidNormalize, pageElementValidArrowPosition )
import PageElements.Structure
  ( PageElement, PageElementArrow, arrowSource, arrowTarget, pageElementPage, pageElementPosition
  , identityPageElementArrow, composePageElementArrows )

-- | The final native chain retains the same accepted cells as the folio builder.
{-@ type MergeFinalCell L R = {cell:AtlasMergePageCell |
      mergePageContains (atlasFolio L) (atlasFolio R) (atlasMergeLength L R - 2) cell} @-}

-- ALIGN: MERGE-UNRANK-SOUND.
-- ALIGN: MERGE-BOUQUET-DATA-DECODE.
-- ALIGN: MERGE-DOMINION-ROUNDTRIP.
-- ALIGN: MERGE-DOMINION-INTERPRETATION.
-- ALIGN: MERGE-DOMINION-RANK.
-- ALIGN: MERGE-INDEXED-DOMINION.
-- ALIGN: MERGE-INDEXED-INTERPRETATION.
-- ALIGN: MERGE-ATLAS-RANK-INTERPRETATION.
-- ALIGN: MERGE-BOUQUET-DATA-EQUIVALENCE.
-- ALIGN: MERGE-BOUQUET-DATA-RANK.
-- ALIGN: MERGE-RAW-DOMINION.
{-@ opaque-reflect mergeDominionAt @-}
{-@ ple mergeDominionAt @-}
{-@ mergeDominionAt :: left:Atlas la ls ld lo lf -> right:Atlas ra rs rd ro rf
      -> occurrence:PageElement ms object
      -> Dominion ({datum:AtlasMergeDatum object | mergeCellContains left right occurrence datum}) @-}
mergeDominionAt
  :: Atlas leftAtlasScope leftScope leftData leftOrigin leftFinal
  -> Atlas rightAtlasScope rightScope rightData rightOrigin rightFinal
  -> PageElement mergeScope object
  -> Dominion (AtlasMergeDatum object)
mergeDominionAt left right occurrence =
  mergeDatumDominion (mergeCellContains left right occurrence)

-- ALIGN: MERGE-DATA-INSERTION.
-- ALIGN: MERGE-DATA-INTERPRETATION.
-- ALIGN: MERGE-DATA-IDENTITY.
-- ALIGN: MERGE-DATA-COMPOSITION.
-- ALIGN: MERGE-RESOLVED-ARROW.
-- ALIGN: MERGE-ATLAS-DATA-INTERPRETATION.
-- ALIGN: MERGE-BOUQUET-DATA-NATURALITY.
-- ALIGN: MERGE-RAW-DATA-INSERTION.
-- ALIGN: MERGE-RAW-DATA-PREIMAGE.
{-@ opaque-reflect mergeDataMap @-}
{-@ opaque-reflect mergeCellContainsPreserved @-}
{-@ ple mergeDataMap @-}
{-@ mergeDataMap :: left:Atlas la ls ld lo lf -> right:Atlas ra rs rd ro rf
      -> arrow:{PageElementArrow ms source target |
           mergeOccurrenceTraceValid left right (arrowSource arrow)
           && mergeOccurrenceTraceValid left right (arrowTarget arrow)}
      -> {mapping:DomanialInsertion
           ({datum:AtlasMergeDatum source | mergeCellContains left right (arrowSource arrow) datum})
           ({datum:AtlasMergeDatum target | mergeCellContains left right (arrowTarget arrow) datum}) |
           applyInsertion mapping == mergeDatumMap (mergeCellContains left right (arrowSource arrow))
             (mergeCellContains left right (arrowTarget arrow)) (mergeCellContainsPreserved left right arrow)
           && preimage mapping == mergeDatumPreimage (mergeCellContains left right (arrowSource arrow))} @-}
mergeDataMap :: Atlas la ls ld lo lf -> Atlas ra rs rd ro rf
  -> PageElementArrow ms source target
  -> DomanialInsertion (AtlasMergeDatum source) (AtlasMergeDatum target)
mergeDataMap left right arrow =
  mergeDatumInsertion
    (mergeCellContains left right (arrowSource arrow))
    (mergeCellContains left right (arrowTarget arrow))
    (mergeCellContainsPreserved left right arrow)

-- ALIGN: MERGE-RAW-DATA-APPLY.
{-@ mergeDataMapApply :: left:Atlas la ls ld lo lf -> right:Atlas ra rs rd ro rf
      -> arrow:{PageElementArrow ms source target |
           mergeOccurrenceTraceValid left right (arrowSource arrow)
           && mergeOccurrenceTraceValid left right (arrowTarget arrow)}
      -> datum:{AtlasMergeDatum source | mergeCellContains left right (arrowSource arrow) datum}
      -> {applyInsertion (mergeDataMap left right arrow) datum == retagMergeDatum datum} @-}
{-@ ple mergeDataMapApply @-}
mergeDataMapApply :: Atlas la ls ld lo lf -> Atlas ra rs rd ro rf
  -> PageElementArrow ms source target -> AtlasMergeDatum source -> ()
mergeDataMapApply left right arrow datum =
  mergeDataMap left right arrow `seq`
    mergeDatumMap (mergeCellContains left right (arrowSource arrow))
      (mergeCellContains left right (arrowTarget arrow)) (mergeCellContainsPreserved left right arrow) datum `seq` ()

-- ALIGN: MERGE-RAW-ACTION.
{-@ opaque-reflect mergeDataAction @-}
{-@ opaque-reflect atlasMembership @-}
{-@ opaque-reflect atlasActionDomain @-}
{-@ opaque-reflect atlasActionMembership @-}
{-@ opaque-reflect atlasActionDataAt @-}
{-@ opaque-reflect atlasActionMap @-}
{-@ mergeDataAction :: left:Atlas la ls ld lo lf -> right:Atlas ra rs rd ro rf
      -> category:{PageElements ms () (MergeFinalCell left right) | pageElementsFolio category == atlasMergeFolio left right}
      -> {action:AtlasDataAction ms AtlasMergeDatum |
           atlasActionDomain action == pageElementDomain category
           && atlasActionMembership action == atlasMembership (mergeCellContains left right)
           && atlasActionDataAt action == mergeDominionAt left right
           && atlasActionMap action == mergeDataMap left right} @-}
{-@ ple mergeDataAction @-}
mergeDataAction :: Atlas la ls ld lo lf -> Atlas ra rs rd ro rf
  -> PageElements ms () AtlasMergePageCell -> AtlasDataAction ms AtlasMergeDatum
mergeDataAction left right category =
  atlasPredicateDataAction category (mergeCellContains left right)
    (mergeDominionAt left right) (mergeDataMap left right)

{-@ mergeActionSameCell :: left:Atlas la ls ld lo lf -> right:Atlas ra rs rd ro rf
      -> category:{PageElements ms () (MergeFinalCell left right) | pageElementsFolio category == atlasMergeFolio left right}
      -> arrow:{PageElementArrow ms object object | pageElementTraceValid category (arrowSource arrow)
           && pageElementTraceValid category (arrowTarget arrow)}
      -> datum:{AtlasMergeDatum object | mergeCellContains left right (normalizePageElement category (arrowSource arrow)) datum}
      -> {applyInsertion (atlasActionMap (mergeDataAction left right category)
           (normalizePageElementArrow category arrow)) datum == datum} @-}
{-@ ple mergeActionSameCell @-}
mergeActionSameCell :: Atlas la ls ld lo lf -> Atlas ra rs rd ro rf
  -> PageElements ms () AtlasMergePageCell -> PageElementArrow ms object object -> AtlasMergeDatum object -> ()
mergeActionSameCell left right category arrow datum =
  pageElementTraceValidNormalize category (arrowSource arrow) `seq`
  pageElementTraceValidNormalize category (arrowTarget arrow) `seq`
  mergeDataAction left right category `seq`
  mergeDataMapApply left right (normalizePageElementArrow category arrow) datum `seq`
    case datum of
      AtlasMergeLeftDatum _ -> ()
      AtlasMergeRightDatum _ -> ()

-- ALIGN: MERGE-RAW-ACTION-IDENTITY.
{-@ mergeActionIdentity :: left:Atlas la ls ld lo lf -> right:Atlas ra rs rd ro rf
      -> category:{PageElements ms () (MergeFinalCell left right) | pageElementsFolio category == atlasMergeFolio left right}
      -> occurrence:{PageElement ms object | pageElementTraceValid category occurrence}
      -> datum:{AtlasMergeDatum object | mergeCellContains left right (normalizePageElement category occurrence) datum}
      -> {applyInsertion (atlasActionMap (mergeDataAction left right category)
           (normalizePageElementArrow category (identityPageElementArrow occurrence))) datum == datum} @-}
{-@ ple mergeActionIdentity @-}
mergeActionIdentity :: Atlas la ls ld lo lf -> Atlas ra rs rd ro rf
  -> PageElements ms () AtlasMergePageCell -> PageElement ms object -> AtlasMergeDatum object -> ()
mergeActionIdentity left right category occurrence =
  mergeActionSameCell left right category (identityPageElementArrow occurrence)

-- ALIGN: MERGE-RAW-ACTION-COMPOSITION.
{-@ mergeActionComposition :: left:Atlas la ls ld lo lf -> right:Atlas ra rs rd ro rf
      -> category:{PageElements ms () (MergeFinalCell left right) | pageElementsFolio category == atlasMergeFolio left right}
      -> second:{PageElementArrow ms middle target | pageElementTraceValid category (arrowSource second)
           && pageElementTraceValid category (arrowTarget second)}
      -> first:{PageElementArrow ms source middle | pageElementTraceValid category (arrowSource first)
           && pageElementTraceValid category (arrowTarget first)}
      -> alignment:{() | arrowTarget first == arrowSource second}
      -> datum:{AtlasMergeDatum source | mergeCellContains left right (normalizePageElement category (arrowSource first)) datum}
      -> {applyInsertion (atlasActionMap (mergeDataAction left right category)
             (normalizePageElementArrow category (composePageElementArrows second first))) datum
           == applyInsertion (atlasActionMap (mergeDataAction left right category) (normalizePageElementArrow category second))
                (applyInsertion (atlasActionMap (mergeDataAction left right category) (normalizePageElementArrow category first)) datum)} @-}
{-@ ple mergeActionComposition @-}
mergeActionComposition :: Atlas la ls ld lo lf -> Atlas ra rs rd ro rf
  -> PageElements ms () AtlasMergePageCell -> PageElementArrow ms middle target
  -> PageElementArrow ms source middle -> () -> AtlasMergeDatum source -> ()
mergeActionComposition left right category second first _ datum =
  pageElementTraceValidNormalize category (arrowSource first) `seq`
  pageElementTraceValidNormalize category (arrowTarget first) `seq`
  pageElementTraceValidNormalize category (arrowTarget second) `seq`
  mergeDataAction left right category `seq`
  let normalizedFirst = normalizePageElementArrow category first
      normalizedSecond = normalizePageElementArrow category second
      mapped = applyInsertion (mergeDataMap left right normalizedFirst) datum
  in mergeDataMapApply left right normalizedFirst datum `seq`
     mergeDataMapApply left right normalizedSecond mapped `seq`
     mergeDataMapApply left right (normalizePageElementArrow category (composePageElementArrows second first)) datum `seq`
     case datum of
       AtlasMergeLeftDatum _ -> ()
       AtlasMergeRightDatum _ -> ()

-- ALIGN: MERGE-RAW-ACTION-COHERENCE.
{-@ mergeActionCoherence :: left:Atlas la ls ld lo lf -> right:Atlas ra rs rd ro rf
      -> category:{PageElements ms () (MergeFinalCell left right) | pageElementsFolio category == atlasMergeFolio left right}
      -> occurrence:{PageElement ms object | pageElementTraceValid category occurrence}
      -> arrow:{PageElementArrow ms object object | pageElementTraceValid category (arrowSource arrow)
           && pageElementTraceValid category (arrowTarget arrow)}
      -> conditions:{() | arrowSource arrow == occurrence && arrowTarget arrow == normalizePageElement category occurrence}
      -> datum:{AtlasMergeDatum object | mergeCellContains left right (normalizePageElement category occurrence) datum}
      -> {applyInsertion (atlasActionMap (mergeDataAction left right category)
           (normalizePageElementArrow category arrow)) datum == datum} @-}
{-@ ple mergeActionCoherence @-}
mergeActionCoherence :: Atlas la ls ld lo lf -> Atlas ra rs rd ro rf
  -> PageElements ms () AtlasMergePageCell -> PageElement ms object
  -> PageElementArrow ms object object -> () -> AtlasMergeDatum object -> ()
mergeActionCoherence left right category _ arrow _ = mergeActionSameCell left right category arrow

-- ALIGN: MERGE-RAW-ACTION-DISJOINT.
{-@ mergeActionDisjoint :: left:Atlas la ls ld lo lf -> right:Atlas ra rs rd ro rf
      -> category:{PageElements ms () (MergeFinalCell left right) | pageElementsFolio category == atlasMergeFolio left right}
      -> first:{PageElement ms a | pageElementTraceValid category first}
      -> second:{PageElement ms b | pageElementTraceValid category second}
      -> firstArrow:{PageElementArrow ms a c | pageElementTraceValid category (arrowSource firstArrow)
           && pageElementTraceValid category (arrowTarget firstArrow)}
      -> secondArrow:{PageElementArrow ms b c | pageElementTraceValid category (arrowSource secondArrow)
           && pageElementTraceValid category (arrowTarget secondArrow)}
      -> conditions:{() | pageElementPage second == pageElementPage first
           && pageElementPosition second /= pageElementPosition first
           && pageElementPage first <= folioLength (pageElementsFolio category) - 1
           && arrowSource firstArrow == first && arrowSource secondArrow == second
           && pageElementPage (arrowTarget firstArrow) == 0
           && arrowTarget secondArrow == arrowTarget firstArrow}
      -> firstDatum:{AtlasMergeDatum a | mergeCellContains left right (normalizePageElement category first) firstDatum}
      -> secondDatum:{AtlasMergeDatum b | mergeCellContains left right (normalizePageElement category second) secondDatum}
      -> {applyInsertion (atlasActionMap (mergeDataAction left right category)
             (normalizePageElementArrow category firstArrow)) firstDatum
           /= applyInsertion (atlasActionMap (mergeDataAction left right category)
             (normalizePageElementArrow category secondArrow)) secondDatum} @-}
{-@ ple mergeActionDisjoint @-}
mergeActionDisjoint :: Atlas la ls ld lo lf -> Atlas ra rs rd ro rf
  -> PageElements ms () AtlasMergePageCell -> PageElement ms a -> PageElement ms b
  -> PageElementArrow ms a c -> PageElementArrow ms b c -> ()
  -> AtlasMergeDatum a -> AtlasMergeDatum b -> ()
mergeActionDisjoint left right category first second firstArrow secondArrow _ firstDatum secondDatum
  | pageElementPage first == 0 =
      pageElementValidArrowPosition category firstArrow `seq`
      pageElementValidArrowPosition category secondArrow `seq`
      pageElementValidArrowPosition category (identityPageElementArrow first) `seq`
      pageElementValidArrowPosition category (identityPageElementArrow second)
  | otherwise =
      pageElementTraceValidNormalize category first `seq`
      pageElementTraceValidNormalize category second `seq`
      pageElementTraceValidNormalize category (arrowTarget firstArrow) `seq`
      mergeDataAction left right category `seq`
      mergeDataMapApply left right (normalizePageElementArrow category firstArrow) firstDatum `seq`
      mergeDataMapApply left right (normalizePageElementArrow category secondArrow) secondDatum `seq`
      mergeCellContainsDisjoint left right (normalizePageElement category first)
        (normalizePageElement category second) firstDatum `seq`
      case (firstDatum, secondDatum) of
        (AtlasMergeLeftDatum _, AtlasMergeLeftDatum _) -> ()
        (AtlasMergeLeftDatum _, AtlasMergeRightDatum _) -> ()
        (AtlasMergeRightDatum _, AtlasMergeLeftDatum _) -> ()
        (AtlasMergeRightDatum _, AtlasMergeRightDatum _) -> ()

-- | Merge two atlases.  The result has a fresh singleton origin whose
-- dominion is the disjoint union of the input extents; result page @n + 1@
-- combines the full-spine page @n@ of each input componentwise.
--
-- The continuation keeps the freshly generated pagination and Atlas scopes
-- from escaping, following the construction style of 'Atlas.atlas'.
-- ALIGN: MERGE-ATLAS-IDENTITY.
-- ALIGN: MERGE-ATLAS-COMPOSITION.
-- ALIGN: MERGE-ATLAS-COHERENCE.
-- ALIGN: MERGE-ATLAS-DISJOINT.
-- ALIGN: MERGE-ATLAS-CONSTRUCTION.
-- ALIGN: MERGE-RAW-ATLAS-CONSTRUCTION.
-- ALIGN: MERGE-RAW-ATLAS-INTERPRETATION.
-- ALIGN: MERGE-FINITE-ELEMENTS-EQUIVALENCE.
-- ALIGN: MERGE-BOUQUET-ATLAS-ISOMORPHISM.
{-@ atlasMerge :: left:Atlas la ls ld lo lf -> right:Atlas ra rs rd ro rf
      -> (forall mergeAtlasScope mergeScope.
           Atlas mergeAtlasScope mergeScope AtlasMergeDatum ()
             (MergeFinalCell left right) -> result)
      -> result @-}
atlasMerge
  :: forall leftAtlasScope leftScope leftData leftOrigin leftFinal
            rightAtlasScope rightScope rightData rightOrigin rightFinal result.
     Atlas leftAtlasScope leftScope leftData leftOrigin leftFinal
  -> Atlas rightAtlasScope rightScope rightData rightOrigin rightFinal
  -> (forall mergeAtlasScope mergeScope.
       Atlas
         mergeAtlasScope
         mergeScope
         AtlasMergeDatum
         ()
         AtlasMergePageCell
       -> result)
  -> result
atlasMerge left right useMerge =
  let pages = atlasMergeFolio left right
      {-@ build :: forall mergeScope. value:{Pagination.Pagination mergeScope () (MergeFinalCell left right) |
            pageElementsFolio (Pagination.paginationPageElements value) == atlasMergeFolio left right} -> result @-}
      build :: forall mergeScope. Pagination.Pagination mergeScope () AtlasMergePageCell -> result
      build mergePagination =
        atlasForPredicate
          mergePagination
          (mergeCellContains left right)
          (mergeDataAction left right (Pagination.paginationPageElements mergePagination))
          (\occurrence datum -> mergeActionIdentity left right (Pagination.paginationPageElements mergePagination) occurrence datum)
          (\second first alignment datum -> mergeActionComposition left right (Pagination.paginationPageElements mergePagination) second first alignment datum)
          (\occurrence arrow conditions datum -> mergeActionCoherence left right (Pagination.paginationPageElements mergePagination) occurrence arrow conditions datum)
          (\first second firstArrow secondArrow conditions firstDatum secondDatum -> mergeActionDisjoint left right (Pagination.paginationPageElements mergePagination) first second firstArrow secondArrow conditions firstDatum secondDatum)
          useMerge
  in Pagination.pagination pages build
