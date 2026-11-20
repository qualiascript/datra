{-# LANGUAGE CPP #-}
{-# LANGUAGE RankNTypes #-}
#include "../../../LiquidPlugin.h"
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}
{-@ LIQUID "--higherorder" @-}

-- | Atlases and their morphisms, built over finite paginations with an
-- explicitly stable infinite padded spine.
--
-- Atlas object and primitive-morphism laws are checked by LiquidHaskell.
module Atlas
  ( Atlas
  , atlasPredicateDataAction
  , atlasActionDomain
  , atlasActionMembership
  , atlasActionDataAt
  , atlasActionMap
  , AtlasDataAction
  , AtlasMorphism
  , AtlasMorphismAction
  , AtlasObjectMap
  , AtlasMappedObject
  , IdentityAtlasObjectMap
  , AtlasMorphismImage
  , AtlasObject
  , AtlasObjectAtlasScope
  , AtlasObjectPaginationScope
  , AtlasObjectCellData
  , AtlasWitness
  , AtlasHom
  , identityAtlasHom
  , composeAtlasHoms
  , atlasDataAction
  , AtlasMembership
  , atlasMembership
  , atlasMembershipAccepts
  , atlasRestrictedDataAction
  , atlas
  , atlasForPredicate
  , atlasPagination
  , atlasFolio
  , atlasPageElements
  , atlasCardinality
  , normalizeAtlasElement
  , normalizeAtlasElementTraceValid
  , atlasAcceptsDatumNormalized
  , normalizeAtlasArrow
  , atlasCoherence
  , atlasDataAt
  , atlasAcceptsDatum
  , mapAtlasData
  , atlasDataCoherence
  , normalizeAtlasDatum
  , atlasMorphismAction
  , atlasMorphismActionNaturality
  , atlasMorphismObjectMapWitness
  , withAtlasMorphismAction
  , normalizeAtlasMorphismAction
  , atlasMorphismActionPreservesArrow
  , atlasMorphismSource
  , atlasMorphismTarget
  , mapAtlasMorphismActionComponent
  , mapAtlasMorphismActionObject
  , identityAtlasObjectMap
  , atlasObjectMap
  , withAtlasMorphismImage
  , atlasMorphism
  , atlasMorphismPagination
  , mapAtlasMorphismElement
  , mapAtlasMorphismArrow
  , mapAtlasMorphismData
  , identityAtlasMorphism
  , composeAtlasMorphisms
  , atlasWitness
  , withAtlasWitness
  , atlasHom
  , materializeAtlasHom
  , atlasHomPagination
  , mapAtlasHomElement
  , mapAtlasHomArrow
  , mapAtlasHomData
  , withAtlasPageChain
  , atlasPageCell
  , atlasOriginCell
  , atlasElementLT
  , atlasCoherenceIdempotent
  , atlasCompositionWitness
  , atlasDisjointWitness
  ) where

import Atlas.Internal
  ( Atlas
  , atlasPredicateDataAction
  , atlasActionDomain
  , atlasActionMembership
  , atlasActionDataAt
  , atlasActionMap
  , AtlasDataAction
  , atlas
  , atlasDataAction
  , AtlasMembership
  , atlasMembership
  , atlasMembershipAccepts
  , atlasRestrictedDataAction
  , atlasCardinality
  , atlasCoherence
  , atlasCoherenceIdempotent
  , atlasCompositionWitness
  , atlasDisjointWitness
  , atlasDataAt
  , atlasAcceptsDatum
  , atlasDataCoherence
  , atlasFolio
  , atlasElementLT
  , atlasOriginCell
  , atlasPageCell
  , atlasPageElements
  , atlasPagination
  , mapAtlasData
  , normalizeAtlasArrow
  , normalizeAtlasDatum
  , normalizeAtlasElement
  , withAtlasPageChain
  )
import qualified Atlas.Internal as Internal (normalizeAtlasElementTraceValid, atlasAcceptsDatumNormalized)
import Atlas.Morphism.Internal
  ( AtlasMorphism
  , AtlasMorphismAction
  , AtlasObjectMap
  , AtlasMappedObject
  , IdentityAtlasObjectMap
  , AtlasMorphismImage
  , AtlasObject
  , AtlasObjectAtlasScope
  , AtlasObjectPaginationScope
  , AtlasObjectCellData
  , AtlasWitness
  , AtlasHom
  , identityAtlasHom
  , composeAtlasHoms
  , atlasMorphism
  , atlasMorphismAction
  , atlasMorphismActionNaturality
  , atlasMorphismObjectMapWitness
  , withAtlasMorphismAction
  , normalizeAtlasMorphismAction
  , atlasMorphismActionPreservesArrow
  , atlasMorphismSource
  , atlasMorphismTarget
  , mapAtlasMorphismActionComponent
  , mapAtlasMorphismActionObject
  , identityAtlasObjectMap
  , atlasObjectMap
  , atlasMorphismPagination
  , atlasWitness
  , withAtlasWitness
  , atlasHom
  , materializeAtlasHom
  , atlasHomPagination
  , mapAtlasHomElement
  , mapAtlasHomArrow
  , mapAtlasHomData
  , composeAtlasMorphisms
  , identityAtlasMorphism
  , mapAtlasMorphismArrow
  , mapAtlasMorphismData
  , mapAtlasMorphismElement
  , withAtlasMorphismImage
  )

import qualified PageElements as Elements
import PageElements.Structure (PageElement, PageElementArrow, pageElementPage, pageElementPosition,
  arrowSource, arrowTarget, identityPageElementArrow, composePageElementArrows)
import Pagination (Pagination, paginationPageElements)
import Folio (folioLength)
import DomanialInsertion.Core (applyInsertion)

{-@ opaque-reflect atlasMembership @-}
{-@ opaque-reflect atlasActionDomain @-}
{-@ opaque-reflect atlasActionMembership @-}
{-@ opaque-reflect atlasActionMap @-}

-- ALIGN: ATLAS-PREDICATE-CONSTRUCTION.
-- | Assemble an Atlas from a predicate action whose laws use the public
-- owning-category validity and normalization operations.
{-@
atlasForPredicate
  :: paginationValue:Pagination scope origin final
  -> accepts:(forall object. PageElement scope object -> cellData object -> Bool)
  -> action:{AtlasDataAction scope cellData |
       atlasActionDomain action == Elements.pageElementDomain (paginationPageElements paginationValue)
       && atlasActionMembership action == atlasMembership accepts}
  -> identityLaw:(forall object.
       occurrence:{PageElement scope object | Elements.pageElementTraceValid (paginationPageElements paginationValue) occurrence}
       -> datum:{cellData object | accepts
            (Elements.normalizePageElement (paginationPageElements paginationValue) occurrence) datum}
       -> { proof:() |
            applyInsertion
              (atlasActionMap action
                (Elements.normalizePageElementArrow (paginationPageElements paginationValue)
                  (identityPageElementArrow occurrence)))
              datum
            == datum })
  -> compositionLaw:(forall source middle target.
       second:{PageElementArrow scope middle target | Elements.pageElementTraceValid (paginationPageElements paginationValue) (arrowSource second) && Elements.pageElementTraceValid (paginationPageElements paginationValue) (arrowTarget second)}
       -> first:{PageElementArrow scope source middle | Elements.pageElementTraceValid (paginationPageElements paginationValue) (arrowSource first) && Elements.pageElementTraceValid (paginationPageElements paginationValue) (arrowTarget first)}
       -> alignment:{() | arrowTarget first == arrowSource second}
       -> datum:{cellData source | accepts
            (Elements.normalizePageElement (paginationPageElements paginationValue) (arrowSource first)) datum}
       -> { proof:() |
            applyInsertion
              (atlasActionMap action
                (Elements.normalizePageElementArrow (paginationPageElements paginationValue)
                  (composePageElementArrows second first)))
              datum
            == applyInsertion
                 (atlasActionMap action
                   (Elements.normalizePageElementArrow (paginationPageElements paginationValue) second))
                 (applyInsertion
                   (atlasActionMap action
                     (Elements.normalizePageElementArrow (paginationPageElements paginationValue) first))
                   datum) })
  -> coherenceLaw:(forall object.
       occurrence:{PageElement scope object | Elements.pageElementTraceValid (paginationPageElements paginationValue) occurrence}
       -> coherenceArrow:{PageElementArrow scope object object | Elements.pageElementTraceValid (paginationPageElements paginationValue) (arrowSource coherenceArrow) && Elements.pageElementTraceValid (paginationPageElements paginationValue) (arrowTarget coherenceArrow)}
       -> conditions:{() |
            arrowSource coherenceArrow == occurrence
            && arrowTarget coherenceArrow == Elements.normalizePageElement (paginationPageElements paginationValue) occurrence}
       -> datum:{cellData object | accepts
            (Elements.normalizePageElement (paginationPageElements paginationValue) occurrence) datum}
       -> { proof:() |
            applyInsertion
              (atlasActionMap action
                (Elements.normalizePageElementArrow (paginationPageElements paginationValue) coherenceArrow))
              datum
            == datum })
  -> disjointLaw:(forall leftObject rightObject originObject.
       left:{PageElement scope leftObject | Elements.pageElementTraceValid (paginationPageElements paginationValue) left}
       -> right:{PageElement scope rightObject | Elements.pageElementTraceValid (paginationPageElements paginationValue) right}
       -> leftToOrigin:{PageElementArrow scope leftObject originObject | Elements.pageElementTraceValid (paginationPageElements paginationValue) (arrowSource leftToOrigin) && Elements.pageElementTraceValid (paginationPageElements paginationValue) (arrowTarget leftToOrigin)}
       -> rightToOrigin:{PageElementArrow scope rightObject originObject | Elements.pageElementTraceValid (paginationPageElements paginationValue) (arrowSource rightToOrigin) && Elements.pageElementTraceValid (paginationPageElements paginationValue) (arrowTarget rightToOrigin)}
       -> conditions:{() |
            pageElementPage right == pageElementPage left
            && pageElementPosition right /= pageElementPosition left
            && pageElementPage left <= folioLength (Elements.pageElementsFolio (paginationPageElements paginationValue)) - 1
            && arrowSource leftToOrigin == left
            && pageElementPage (arrowTarget leftToOrigin) == 0
            && arrowSource rightToOrigin == right
            && arrowTarget rightToOrigin == arrowTarget leftToOrigin}
       -> leftDatum:{cellData leftObject | accepts
            (Elements.normalizePageElement (paginationPageElements paginationValue) left) leftDatum}
       -> rightDatum:{cellData rightObject | accepts
            (Elements.normalizePageElement (paginationPageElements paginationValue) right) rightDatum}
       -> { proof:() |
            applyInsertion
              (atlasActionMap action
                (Elements.normalizePageElementArrow (paginationPageElements paginationValue) leftToOrigin))
              leftDatum
            /= applyInsertion
                 (atlasActionMap action
                   (Elements.normalizePageElementArrow (paginationPageElements paginationValue) rightToOrigin))
                 rightDatum })
  -> useAtlas:(forall atlasScope.
       Atlas atlasScope scope cellData origin final -> result)
  -> result
@-}
atlasForPredicate
  :: Pagination scope origin final
  -> (forall object. PageElement scope object -> cellData object -> Bool)
  -> AtlasDataAction scope cellData
  -> (forall object.
        PageElement scope object -> cellData object -> ())
  -> (forall source middle target.
        PageElementArrow scope middle target
        -> PageElementArrow scope source middle
        -> ()
        -> cellData source
        -> ())
  -> (forall object.
        PageElement scope object
        -> PageElementArrow scope object object
        -> ()
        -> cellData object
        -> ())
  -> (forall leftObject rightObject originObject.
        PageElement scope leftObject
        -> PageElement scope rightObject
        -> PageElementArrow scope leftObject originObject
        -> PageElementArrow scope rightObject originObject
        -> ()
        -> cellData leftObject
        -> cellData rightObject
        -> ())
  -> (forall atlasScope.
        Atlas atlasScope scope cellData origin final -> result)
  -> result
atlasForPredicate paginationValue accepts action identityLaw compositionLaw coherenceLaw disjointLaw useAtlas =
  atlasMembership accepts `seq`
    atlas paginationValue action identityLaw compositionLaw coherenceLaw disjointLaw useAtlas

-- | Preserve the owning trace and carrier membership under Atlas normalization.
{-@ normalizeAtlasElementTraceValid :: owner:Atlas a s d o f
      -> source:{PageElement s object | Elements.pageElementTraceValid (atlasPageElements owner) source}
      -> {Elements.pageElementTraceValid (atlasPageElements owner) (normalizeAtlasElement owner source)} @-}
normalizeAtlasElementTraceValid :: Atlas a s d o f -> PageElement s object -> ()
normalizeAtlasElementTraceValid = Internal.normalizeAtlasElementTraceValid

{-@ atlasAcceptsDatumNormalized :: owner:Atlas a s d o f
      -> source:PageElement s object -> datum:d object
      -> {atlasAcceptsDatum owner (normalizeAtlasElement owner source) datum
           == atlasAcceptsDatum owner source datum} @-}
atlasAcceptsDatumNormalized :: Atlas a s d o f -> PageElement s object -> d object -> ()
atlasAcceptsDatumNormalized = Internal.atlasAcceptsDatumNormalized
