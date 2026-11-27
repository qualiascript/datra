{-# LANGUAGE CPP #-}
{-# LANGUAGE RankNTypes #-}
#include "../../../LiquidPlugin.h"
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}
{-@ LIQUID "--higherorder" @-}

-- | Atlases and their morphisms, built over finite paginations with an
-- explicitly stable infinite padded spine.
--
-- Atlas object and primitive-morphism laws are checked by LiquidHaskell over
-- valid owning arrows and the corresponding accepted data carriers.
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
  , AtlasObjectEquality (..)
  , AtlasObjectAtlasScope
  , AtlasObjectPaginationScope
  , AtlasObjectCellData
  , AtlasWitness
  , AtlasWitnessData
  , AtlasOwner, atlasOwner, atlasWitnessOwner
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
  , AtlasPresentation
  , atlasPresentationForPredicate
  , atlasPresentationPagination
  , atlasPresentationAction
  , atlasDescription
  , atlasDescriptionMembership
  , atlasDescriptionMap
  , withAtlasPresentation
  , atlasPagination
  , atlasFolio
  , atlasPageElements
  , atlasCardinality
  , normalizeAtlasElement
  , normalizeAtlasElementTraceValid
  , atlasAcceptsDatumNormalized
  , normalizeAtlasArrow
  , atlasNormalizationArrow
  , atlasNormalizationAgrees
  , atlasArrowNormalizationAgrees
  , mapAtlasDataNormalized
  , normalizeAtlasArrowTraceValid
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
  , normalizeAtlasMorphismActionRetains
  , atlasMorphismActionPreservesArrow
  , atlasMorphismSource
  , atlasMorphismTarget
  , mapAtlasMorphismActionComponent
  , mapAtlasMorphismActionObject
  , mapAtlasMorphismActionElement
  , mapPrimitiveElement
  , identityAtlasObjectMap
  , identityAtlasMorphismObject
  , identityAtlasMorphismPreservesArrow
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
  , atlasWitnessElementValid
  , normalizeAtlasWitnessElement
  , atlasWitnessNormalizeValid
  , atlasHom
  , atlasHomTargetObjectEquality
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
  , atlasIdentityWitness
  , atlasCoherenceWitness
  , atlasCompositionWitness
  , atlasDisjointWitness
  ) where

import Atlas.Internal
  ( AtlasPresentation
  , atlasPresentationPagination
  , atlasPresentationAction
  , atlasDescription
  , atlasDescriptionMembership
  , Atlas
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
  , atlasIdentityWitness
  , atlasCoherenceWitness
  , atlasCompositionWitness
  , atlasDisjointWitness
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
import qualified Atlas.Internal as Internal (atlasDataAt, atlasDescriptionMap, atlasNormalizationAgrees, atlasArrowNormalizationAgrees, atlasPresentation, withAtlasPresentation, normalizeAtlasElementTraceValid, atlasAcceptsDatumNormalized, atlasNormalizationArrow, mapAtlasDataNormalized, normalizeAtlasArrowTraceValid)
import Atlas.Morphism
  ( AtlasMorphismAction
  , AtlasObjectMap
  , AtlasMappedObject
  , IdentityAtlasObjectMap
  , identityAtlasObjectMap
  , identityAtlasMorphismObject
  , identityAtlasMorphismPreservesArrow
  , atlasObjectMap
  , atlasMorphismAction
  , atlasMorphismSource
  , atlasMorphismTarget
  , mapAtlasMorphismActionObject
  , mapAtlasMorphismActionComponent
  , mapAtlasMorphismActionElement
  , mapPrimitiveElement
  , atlasMorphismActionPreservesArrow
  , atlasMorphismActionNaturality
  , atlasMorphismObjectMapWitness
  , normalizeAtlasMorphismAction
  , normalizeAtlasMorphismActionRetains
  )
import Atlas.Witness
  ( AtlasObjectEquality (..), AtlasObject, AtlasObjectAtlasScope, AtlasObjectPaginationScope, AtlasObjectCellData
  , AtlasOwner, atlasOwner, atlasWitnessOwner, AtlasWitness, AtlasWitnessData, atlasWitness, withAtlasWitness, atlasWitnessElementValid, normalizeAtlasWitnessElement, atlasWitnessNormalizeValid )
import Atlas.Morphism.Internal
  ( AtlasMorphism
  , AtlasMorphismImage
  , AtlasHom
  , identityAtlasHom
  , composeAtlasHoms
  , atlasMorphism
  , withAtlasMorphismAction
  , atlasMorphismPagination
  , atlasHom
  , atlasHomTargetObjectEquality
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
import Dominion (Dominion)

{-@ opaque-reflect atlasMembership @-}
{-@ opaque-reflect atlasActionDomain @-}
{-@ opaque-reflect atlasActionMembership @-}
{-@ opaque-reflect atlasActionDataAt @-}
{-@ opaque-reflect atlasActionMap @-}

-- | Retain the exact normalized lookup through the public Atlas interface.
{-@ opaque-reflect atlasDataAt @-}
{-@ atlasDataAt :: owner:Atlas a s d o f
      -> source:{PageElement s object | Elements.pageElementTraceValid (atlasPageElements owner) source}
      -> {result:Dominion ({datum:d object | atlasAcceptsDatum owner source datum}) |
           result == atlasActionDataAt (atlasPresentationAction (atlasDescription owner))
             (normalizeAtlasElement owner source)} @-}
atlasDataAt :: Atlas a s d o f -> PageElement s object -> Dominion (d object)
atlasDataAt owner source = Internal.atlasDataAt owner source

-- ALIGN: ATLAS-DESCRIPTION-MAP.
{-@ atlasDescriptionMap :: owner:Atlas a s d o f
      -> arrow:{PageElementArrow s source target |
           Elements.pageElementTraceValid (atlasPageElements owner) (arrowSource arrow)
           && Elements.pageElementTraceValid (atlasPageElements owner) (arrowTarget arrow)}
      -> {mapAtlasData owner arrow ==
           atlasActionMap (atlasPresentationAction (atlasDescription owner))
             (normalizeAtlasArrow owner arrow)} @-}
atlasDescriptionMap :: Atlas a s d o f -> PageElementArrow s source target -> ()
atlasDescriptionMap = Internal.atlasDescriptionMap

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
  withAtlasPresentation
    (atlasPresentationForPredicate paginationValue accepts action identityLaw compositionLaw coherenceLaw disjointLaw)
    useAtlas

-- | Certify predicate membership and all normalized laws before allocation.
-- ALIGN: ATLAS-PREDICATE-PRESENTATION.
{-@
atlasPresentationForPredicate
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
  -> {presentation:AtlasPresentation scope cellData origin final |
       atlasPresentationPagination presentation == paginationValue && atlasPresentationAction presentation == action}
@-}
atlasPresentationForPredicate
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
  -> AtlasPresentation scope cellData origin final
atlasPresentationForPredicate paginationValue accepts action identityLaw compositionLaw coherenceLaw disjointLaw =
  atlasMembership accepts `seq`
    Internal.atlasPresentation paginationValue action identityLaw compositionLaw coherenceLaw disjointLaw

-- ALIGN: ATLAS-PRESENTATION-CONTINUATION.
{-@ withAtlasPresentation :: presentation:AtlasPresentation s d o f
      -> (forall a. value:{Atlas a s d o f | atlasDescription value == presentation
           && atlasPagination value == atlasPresentationPagination presentation}
           -> result) -> result @-}
withAtlasPresentation :: AtlasPresentation s d o f -> (forall a. Atlas a s d o f -> result) -> result
withAtlasPresentation = Internal.withAtlasPresentation

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

-- | Expose the owning endpoints together with the normalization arrow.
{-@ atlasNormalizationArrow :: owner:Atlas a s d o f
      -> source:{PageElement s object | Elements.pageElementTraceValid (atlasPageElements owner) source}
      -> {arrow:PageElementArrow s object object |
           Elements.pageElementTraceValid (atlasPageElements owner) (arrowSource arrow)
           && Elements.pageElementTraceValid (atlasPageElements owner) (arrowTarget arrow)
           && arrowSource arrow == source && arrowTarget arrow == normalizeAtlasElement owner source} @-}
atlasNormalizationArrow :: Atlas a s d o f -> PageElement s object -> PageElementArrow s object object
atlasNormalizationArrow = Internal.atlasNormalizationArrow

{-@ normalizeAtlasArrowTraceValid :: owner:Atlas a s d o f
      -> arrow:{PageElementArrow s source target |
           Elements.pageElementTraceValid (atlasPageElements owner) (arrowSource arrow)
           && Elements.pageElementTraceValid (atlasPageElements owner) (arrowTarget arrow)}
      -> {Elements.pageElementTraceValid (atlasPageElements owner) (arrowSource (normalizeAtlasArrow owner arrow))
           && Elements.pageElementTraceValid (atlasPageElements owner) (arrowTarget (normalizeAtlasArrow owner arrow))} @-}
normalizeAtlasArrowTraceValid :: Atlas a s d o f -> PageElementArrow s source target -> ()
normalizeAtlasArrowTraceValid = Internal.normalizeAtlasArrowTraceValid

{-@ mapAtlasDataNormalized :: owner:Atlas a s d o f
      -> arrow:{PageElementArrow s source target |
           Elements.pageElementTraceValid (atlasPageElements owner) (arrowSource arrow)
           && Elements.pageElementTraceValid (atlasPageElements owner) (arrowTarget arrow)}
      -> {mapAtlasData owner (normalizeAtlasArrow owner arrow) == mapAtlasData owner arrow} @-}
mapAtlasDataNormalized :: Atlas a s d o f -> PageElementArrow s source target -> ()
mapAtlasDataNormalized = Internal.mapAtlasDataNormalized

-- ALIGN: ATLAS-NORMALIZATION-AGREES.
{-@ atlasNormalizationAgrees :: owner:Atlas a s d o f -> source:PageElement s object
      -> {normalizeAtlasElement owner source
           == Elements.normalizePageElement (atlasPageElements owner) source} @-}
atlasNormalizationAgrees :: Atlas a s d o f -> PageElement s object -> ()
atlasNormalizationAgrees = Internal.atlasNormalizationAgrees

-- ALIGN: ATLAS-ARROW-NORMALIZATION-AGREES.
{-@ atlasArrowNormalizationAgrees :: owner:Atlas a s d o f -> arrow:PageElementArrow s source target
      -> {normalizeAtlasArrow owner arrow
           == Elements.normalizePageElementArrow (atlasPageElements owner) arrow} @-}
atlasArrowNormalizationAgrees :: Atlas a s d o f -> PageElementArrow s source target -> ()
atlasArrowNormalizationAgrees = Internal.atlasArrowNormalizationAgrees
