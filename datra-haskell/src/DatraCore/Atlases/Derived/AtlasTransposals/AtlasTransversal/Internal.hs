{-# LANGUAGE CPP #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE RoleAnnotations #-}
{-# LANGUAGE TypeFamilies #-}
-- GHC does not count names referenced only by LiquidHaskell specifications.
{-# OPTIONS_GHC -Wno-unused-imports #-}
#include "../../../../LiquidPlugin.h"
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}
{-@ LIQUID "--higherorder" @-}
-- Explicit contracts avoid inferred predicates on existential GADT type arguments.
{-@ LIQUID "--fast" @-}

-- | Hidden implementation of Atlas transversals using Atlas coverage evidence.
module AtlasTransversal.Internal
  ( AtlasTransversal
  , atlasTransversal
  , withTransversalImage
  , transversalImageCovered
  , atlasTransversalOrderedTransposal
  , atlasTransversalTransposal
  , atlasTransversalHom
  , atlasTransversalPreservesCoverage
  , mapAtlasTransversalCoveredPageElement
  , withAtlasTransversalCoveredImage
  , atlasTransversalSize
  , identityAtlasTransversal
  , composeAtlasTransversals
  , mapAtlasTransversalObject
  , atlasTransversalPreimage
  , atlasTransversalLeftInverse
  , atlasTransversalPreservesOrder
  , atlasTransversalPagination
  , mapAtlasTransversalElement
  , mapAtlasTransversalArrow
  , mapAtlasTransversalData
  ) where

import Atlas
  ( Atlas
  , AtlasHom
  , AtlasMorphismImage
  , AtlasObject
  , AtlasObjectCellData
  , AtlasObjectPaginationScope
  , AtlasWitness
  , atlasWitness
  , withAtlasMorphismImage
  )
import AtlasCoveredPageElement
  ( CoverageWitness
  , CoveredPageElement
  , AtlasCoveredPageElement
  , withAtlasCoveredPageElement
  , atlasCoveredByWitness
  , coverageWitnessCovers
  , coveredPageElementValid
  , atlasCoveredPageElementWitness
  )
import AtlasTransposal (AtlasTransposal, AtlasTransposalElement)
import Control.Category (Category (..))
import DomanialInsertion (applyInsertion)
import OrderedAtlasTransposal
  ( OrderedAtlasTransposal
  , composeOrderedAtlasTransposals
  , identityOrderedAtlasTransposal
  , mapOrderedAtlasTransposalArrow
  , mapOrderedAtlasTransposalData
  , mapOrderedAtlasTransposalElement
  , mapOrderedAtlasTransposalObject
  , orderedAtlasTransposalHom
  , orderedAtlasTransposalLeftInverse
  , orderedAtlasTransposalPagination
  , orderedAtlasTransposalPreimage
  , orderedAtlasTransposalPreservesOrder
  , orderedAtlasTransposalTransposal
  )
import PageElements
  ( PageElement
  , PageElementArrow
  , SomePageElement
  )
import Pagination (PaginationMorphism, SomePageElementArrow)
import Prelude hiding ((.), id)

-- | A transversal is an ordered transposal whose data action maps every covered
-- source datum to coverage evidence for its exact target image. Primitive
-- arrows retain source and target Atlases so this condition can be checked;
-- identities and composites derive it structurally.
type role AtlasTransversal nominal nominal
data AtlasTransversal source target where
  PrimitiveAtlasTransversal
    :: TransversalAction sa ss sd so sf ta ts td to tf
    -> AtlasTransversal (AtlasObject sa ss sd) (AtlasObject ta ts td)
  IdentityAtlasTransversal
    :: AtlasTransversal object object
  CompositeAtlasTransversal
    :: AtlasTransversal middle target
    -> AtlasTransversal source middle
    -> AtlasTransversal source target

-- | A primitive action keeps its exact-image coverage law in the stored
-- field, so the law survives elimination of the outer categorical syntax.
type role TransversalAction nominal nominal nominal nominal nominal nominal nominal nominal nominal nominal
{-@ data TransversalAction sa ss sd so sf ta ts td to tf = TransversalAction
      { transversalSource :: Atlas sa ss sd so sf
      , transversalTarget :: Atlas ta ts td to tf
      , transversalOrdered :: OrderedAtlasTransposal (AtlasObject sa ss sd) (AtlasObject ta ts td)
      , transversalCoverage :: covered:CoveredPageElement sa ss sd
          -> {witness:CoverageWitness ta ts td |
                transversalImageCovered transversalSource transversalTarget transversalOrdered covered witness}
      } @-}
data TransversalAction sa ss sd so sf ta ts td to tf = TransversalAction
  { transversalSource :: Atlas sa ss sd so sf
  , transversalTarget :: Atlas ta ts td to tf
  , transversalOrdered :: OrderedAtlasTransposal (AtlasObject sa ss sd) (AtlasObject ta ts td)
  , transversalCoverage :: CoveredPageElement sa ss sd
      -> CoverageWitness ta ts td
  }

-- | A materialized dependent image shared by the coverage predicate and
-- the mapper. Its cell index remains existential rather than being erased.
type role TransversalImage nominal
data TransversalImage target where
  TransversalImage
    :: PageElement (AtlasObjectPaginationScope target) object
    -> AtlasObjectCellData target object
    -> TransversalImage target

{-@ opaque-reflect transversalImage @-}
transversalImage
  :: Atlas sa ss sd so sf
  -> OrderedAtlasTransposal (AtlasObject sa ss sd) target
  -> CoveredPageElement sa ss sd
  -> TransversalImage target
transversalImage sourceAtlas ordered covered =
  withAtlasCoveredPageElement covered $ \sourceOccurrence sourceDatum ->
  withAtlasMorphismImage
    (mapOrderedAtlasTransposalData (atlasWitness sourceAtlas) ordered sourceOccurrence) $
      \targetOccurrence insertion ->
        TransversalImage targetOccurrence (applyInsertion insertion sourceDatum)

-- | Inspect the exact dependent datum produced by an ordered transposal.
-- Both the preservation contract and the runtime mapper use this operation.
{-@ reflect withTransversalImage @-}
-- ALIGN: ATLAS-TRANSVERSAL-IMAGE.
withTransversalImage
  :: Atlas sourceAtlasScope sourceScope sourceCellData sourceOrigin sourceFinal
  -> OrderedAtlasTransposal (AtlasObject sourceAtlasScope sourceScope sourceCellData) target
  -> CoveredPageElement sourceAtlasScope sourceScope sourceCellData
  -> (forall object. PageElement (AtlasObjectPaginationScope target) object
        -> AtlasObjectCellData target object -> result)
  -> result
withTransversalImage sourceAtlas ordered covered useImage =
  case transversalImage sourceAtlas ordered covered of
    TransversalImage occurrence datum -> useImage occurrence datum

-- | Coverage is required for the actual image, not arbitrary target data.
{-@ reflect transversalImageCovered @-}
-- ALIGN: ATLAS-TRANSVERSAL-IMAGE-COVERAGE.
transversalImageCovered
  :: Atlas sourceAtlasScope sourceScope sourceCellData sourceOrigin sourceFinal
  -> Atlas targetAtlasScope targetScope targetCellData targetOrigin targetFinal
  -> OrderedAtlasTransposal
       (AtlasObject sourceAtlasScope sourceScope sourceCellData)
       (AtlasObject targetAtlasScope targetScope targetCellData)
  -> CoveredPageElement sourceAtlasScope sourceScope sourceCellData
  -> CoverageWitness targetAtlasScope targetScope targetCellData
  -> Bool
transversalImageCovered sourceAtlas targetAtlas ordered covered witness =
  case transversalImage sourceAtlas ordered covered of
    TransversalImage occurrence datum ->
      coverageWitnessCovers targetAtlas occurrence datum witness

-- | Add the covered-page-element clause to an ordered Atlas transposal.
-- The callback supplies evidence for the computed image of each covered source.
{-@
atlasTransversal
  :: sourceAtlas:Atlas
       sourceAtlasScope sourceScope sourceCellData sourceOrigin sourceFinal
  -> targetAtlas:Atlas
       targetAtlasScope targetScope targetCellData targetOrigin targetFinal
  -> ordered:OrderedAtlasTransposal
       (AtlasObject sourceAtlasScope sourceScope sourceCellData)
       (AtlasObject targetAtlasScope targetScope targetCellData)
  -> preservesCoverage:(covered:CoveredPageElement sourceAtlasScope sourceScope sourceCellData
       -> { witness:CoverageWitness targetAtlasScope targetScope targetCellData |
            transversalImageCovered sourceAtlas targetAtlas ordered covered witness })
  -> AtlasTransversal
       (AtlasObject sourceAtlasScope sourceScope sourceCellData)
       (AtlasObject targetAtlasScope targetScope targetCellData)
@-}
-- ALIGN: ATLAS-TRANSVERSAL-INTERPRETATION.
atlasTransversal
  :: Atlas
       sourceAtlasScope sourceScope sourceCellData sourceOrigin sourceFinal
  -> Atlas
       targetAtlasScope targetScope targetCellData targetOrigin targetFinal
  -> OrderedAtlasTransposal
       (AtlasObject sourceAtlasScope sourceScope sourceCellData)
       (AtlasObject targetAtlasScope targetScope targetCellData)
  -> (CoveredPageElement sourceAtlasScope sourceScope sourceCellData
       -> CoverageWitness targetAtlasScope targetScope targetCellData)
  -> AtlasTransversal
       (AtlasObject sourceAtlasScope sourceScope sourceCellData)
       (AtlasObject targetAtlasScope targetScope targetCellData)
atlasTransversal sourceAtlas targetAtlas ordered preservesCoverage =
  PrimitiveAtlasTransversal (TransversalAction sourceAtlas targetAtlas ordered preservesCoverage)

-- | Forget the coverage condition while retaining injectivity and order.
atlasTransversalOrderedTransposal
  :: AtlasTransversal source target
  -> OrderedAtlasTransposal source target
atlasTransversalOrderedTransposal
  (PrimitiveAtlasTransversal action) = transversalOrdered action
atlasTransversalOrderedTransposal IdentityAtlasTransversal =
  identityOrderedAtlasTransposal
atlasTransversalOrderedTransposal
  (CompositeAtlasTransversal second first) =
    composeOrderedAtlasTransposals
      (atlasTransversalOrderedTransposal second)
      (atlasTransversalOrderedTransposal first)

-- | Include a transversal into the category of Atlas transposals.
atlasTransversalTransposal
  :: AtlasTransversal source target
  -> AtlasTransposal source target
atlasTransversalTransposal =
  orderedAtlasTransposalTransposal . atlasTransversalOrderedTransposal

-- | Include a transversal all the way into the Atlas category.
atlasTransversalHom
  :: AtlasTransversal source target
  -> AtlasHom source target
atlasTransversalHom =
  orderedAtlasTransposalHom . atlasTransversalOrderedTransposal

-- | Package the primitive's exact image with its supplied witness, retaining
-- validity for the target Atlas stored in the same action.
-- ALIGN: ATLAS-TRANSVERSAL-PRIMITIVE-COVERED.
{-@ mapTransversalAction
      :: action:TransversalAction sa ss sd so sf ta ts td to tf
      -> covered:CoveredPageElement sa ss sd
      -> {result:CoveredPageElement ta ts td |
           coveredPageElementValid (transversalTarget action) result
           && atlasCoveredPageElementWitness result == transversalCoverage action covered} @-}
mapTransversalAction
  :: TransversalAction sa ss sd so sf ta ts td to tf
  -> CoveredPageElement sa ss sd
  -> CoveredPageElement ta ts td
mapTransversalAction action covered =
  let witness = transversalCoverage action covered
  in case transversalImage (transversalSource action) (transversalOrdered action) covered of
    TransversalImage targetOccurrence targetDatum ->
      atlasCoveredByWitness (transversalTarget action) targetOccurrence targetDatum witness

-- | Identity needs no new owner. Every actual image retains the Atlas used to
-- certify it, including when a later identity leaves that image unchanged.
type role TransversalCoveredImage nominal nominal
data TransversalCoveredImage source target where
  UnchangedTransversalCoveredImage :: TransversalCoveredImage object object
  MappedTransversalCoveredImage
    :: CoveredImageData a s d o f
    -> TransversalCoveredImage source (AtlasObject a s d)

type role CoveredImageData nominal nominal nominal nominal nominal
{-@ data CoveredImageData a s d o f = CoveredImageData
      { coveredImageOwner :: Atlas a s d o f
      , coveredImageValue :: {covered:CoveredPageElement a s d |
                               coveredPageElementValid coveredImageOwner covered}
      } @-}
data CoveredImageData a s d o f = CoveredImageData
  { coveredImageOwner :: Atlas a s d o f
  , coveredImageValue :: CoveredPageElement a s d
  }

{-@ withCoveredImageData :: image:CoveredImageData a s d o f
      -> (owner:Atlas a s d o f
            -> {covered:CoveredPageElement a s d | coveredPageElementValid owner covered}
            -> result)
      -> result @-}
withCoveredImageData :: CoveredImageData a s d o f
  -> (Atlas a s d o f -> CoveredPageElement a s d -> result) -> result
withCoveredImageData image useImage = useImage (coveredImageOwner image) (coveredImageValue image)

{-@ measure atlasTransversalSize @-}
{-@ atlasTransversalSize :: AtlasTransversal source target -> {size:Integer | size > 0} @-}
atlasTransversalSize :: AtlasTransversal source target -> Integer
atlasTransversalSize IdentityAtlasTransversal = 1
atlasTransversalSize (PrimitiveAtlasTransversal _) = 1
atlasTransversalSize (CompositeAtlasTransversal second first) =
  1 + atlasTransversalSize second + atlasTransversalSize first

-- ALIGN: ATLAS-TRANSVERSAL-OWNED-IMAGE.
{-@ transversalCoveredImage :: transversal:AtlasTransversal source target
      -> AtlasCoveredPageElement source -> TransversalCoveredImage source target
      / [atlasTransversalSize transversal] @-}
transversalCoveredImage
  :: AtlasTransversal source target
  -> AtlasCoveredPageElement source
  -> TransversalCoveredImage source target
transversalCoveredImage IdentityAtlasTransversal _ = UnchangedTransversalCoveredImage
transversalCoveredImage (PrimitiveAtlasTransversal action) covered =
  MappedTransversalCoveredImage
    (CoveredImageData (transversalTarget action) (mapTransversalAction action covered))
transversalCoveredImage (CompositeAtlasTransversal second first) covered =
  let mapSecond = transversalCoveredImage second
  in case transversalCoveredImage first covered of
    UnchangedTransversalCoveredImage -> mapSecond covered
    MappedTransversalCoveredImage image ->
      case mapSecond (coveredImageValue image) of
        UnchangedTransversalCoveredImage -> MappedTransversalCoveredImage image
        MappedTransversalCoveredImage result -> MappedTransversalCoveredImage result

-- | Inspect a covered image with the exact owner that certifies it. The target
-- origin and final-page carriers remain existential inside the callback.
-- ALIGN: ATLAS-TRANSVERSAL-OWNED-ELIMINATION.
{-@ withAtlasTransversalCoveredImage
      :: sourceOwner:Atlas sa ss sd so sf
      -> AtlasTransversal (AtlasObject sa ss sd) (AtlasObject ta ts td)
      -> source:{CoveredPageElement sa ss sd | coveredPageElementValid sourceOwner source}
      -> (forall o f. owner:Atlas ta ts td o f
            -> {image:CoveredPageElement ta ts td | coveredPageElementValid owner image}
            -> result)
      -> result @-}
withAtlasTransversalCoveredImage
  :: Atlas sa ss sd so sf
  -> AtlasTransversal (AtlasObject sa ss sd) (AtlasObject ta ts td)
  -> CoveredPageElement sa ss sd
  -> (forall o f. Atlas ta ts td o f -> CoveredPageElement ta ts td -> result)
  -> result
withAtlasTransversalCoveredImage sourceOwner transversal covered useImage =
  let sourceImage = CoveredImageData sourceOwner covered
  in case transversalCoveredImage transversal covered of
    UnchangedTransversalCoveredImage -> withCoveredImageData sourceImage useImage
    MappedTransversalCoveredImage image -> withCoveredImageData image useImage

-- | Map a covered page element and derive coverage of its exact target image. This
-- is total: malformed preservation callbacks are rejected when the primitive
-- transversal is compiled, rather than producing a runtime failure here.
-- ALIGN: ATLAS-TRANSVERSAL-COVERED-IMAGE.
mapAtlasTransversalCoveredPageElement
  :: AtlasTransversal source target
  -> AtlasCoveredPageElement source
  -> AtlasCoveredPageElement target
mapAtlasTransversalCoveredPageElement transversal covered =
  case transversalCoveredImage transversal covered of
    UnchangedTransversalCoveredImage -> covered
    MappedTransversalCoveredImage image -> coveredImageValue image

-- | The covered-page-element preservation condition of an Atlas transversal.
-- This is named separately from the operational mapper so downstream
-- restrictions can refer directly to the condition they inherit.
-- ALIGN: ATLAS-TRANSVERSAL-COVERAGE.
atlasTransversalPreservesCoverage
  :: AtlasTransversal source target
  -> AtlasCoveredPageElement source
  -> AtlasCoveredPageElement target
atlasTransversalPreservesCoverage = mapAtlasTransversalCoveredPageElement

-- | The identity transversal preserves every covered page element unchanged.
-- ALIGN: ATLAS-TRANSVERSAL-IDENTITY.
identityAtlasTransversal :: AtlasTransversal object object
identityAtlasTransversal = IdentityAtlasTransversal

-- | Compose Atlas transversals in categorical order.
-- ALIGN: ATLAS-TRANSVERSAL-COMPOSITION.
composeAtlasTransversals
  :: AtlasTransversal middle target
  -> AtlasTransversal source middle
  -> AtlasTransversal source target
composeAtlasTransversals IdentityAtlasTransversal first = first
composeAtlasTransversals second IdentityAtlasTransversal = second
composeAtlasTransversals second (CompositeAtlasTransversal middle first) =
  CompositeAtlasTransversal (composeAtlasTransversals second middle) first
composeAtlasTransversals second first =
  CompositeAtlasTransversal second first

-- | Atlas transversals form the next wide subcategory in the restriction
-- chain.
instance Category AtlasTransversal where
  id = identityAtlasTransversal
  (.) = composeAtlasTransversals

-- | Apply the inherited injective, order-preserving object map.
mapAtlasTransversalObject
  :: AtlasTransversal source target
  -> AtlasTransposalElement source
  -> AtlasTransposalElement target
mapAtlasTransversalObject transversal =
  mapOrderedAtlasTransposalObject
    (atlasTransversalOrderedTransposal transversal)

-- | Try to recover an element under the inherited injective object map.
atlasTransversalPreimage
  :: AtlasTransversal source target
  -> AtlasTransposalElement target
  -> Maybe (AtlasTransposalElement source)
atlasTransversalPreimage transversal =
  orderedAtlasTransposalPreimage
    (atlasTransversalOrderedTransposal transversal)

-- | Invoke the inherited injectivity certificate.
atlasTransversalLeftInverse
  :: AtlasTransversal source target
  -> AtlasTransposalElement source
  -> ()
atlasTransversalLeftInverse transversal =
  orderedAtlasTransposalLeftInverse
    (atlasTransversalOrderedTransposal transversal)

-- | Invoke the inherited strict-order preservation certificate.
atlasTransversalPreservesOrder
  :: AtlasTransversal source target
  -> AtlasTransposalElement source
  -> AtlasTransposalElement source
  -> ()
atlasTransversalPreservesOrder transversal =
  orderedAtlasTransposalPreservesOrder
    (atlasTransversalOrderedTransposal transversal)

-- | Recover the underlying pagination morphism.
atlasTransversalPagination
  :: AtlasWitness source
  -> AtlasTransversal source target
  -> PaginationMorphism
       (AtlasObjectPaginationScope source)
       (AtlasObjectPaginationScope target)
atlasTransversalPagination sourceWitness transversal =
  orderedAtlasTransposalPagination
    sourceWitness
    (atlasTransversalOrderedTransposal transversal)

-- | Apply the included arrow to a padded page element.
mapAtlasTransversalElement
  :: AtlasWitness source
  -> AtlasTransversal source target
  -> PageElement (AtlasObjectPaginationScope source) object
  -> SomePageElement (AtlasObjectPaginationScope target)
mapAtlasTransversalElement sourceWitness transversal =
  mapOrderedAtlasTransposalElement
    sourceWitness
    (atlasTransversalOrderedTransposal transversal)

-- | Apply the included arrow to a page-element arrow.
mapAtlasTransversalArrow
  :: AtlasWitness source
  -> AtlasTransversal source target
  -> PageElementArrow
       (AtlasObjectPaginationScope source) sourceObject targetObject
  -> SomePageElementArrow (AtlasObjectPaginationScope target)
mapAtlasTransversalArrow sourceWitness transversal =
  mapOrderedAtlasTransposalArrow
    sourceWitness
    (atlasTransversalOrderedTransposal transversal)

-- | Apply the included arrow to a cell and its dependent datum.
mapAtlasTransversalData
  :: AtlasWitness source
  -> AtlasTransversal source target
  -> PageElement (AtlasObjectPaginationScope source) sourceObject
  -> AtlasMorphismImage
       (AtlasObjectPaginationScope target)
       (AtlasObjectCellData source)
       (AtlasObjectCellData target)
       sourceObject
mapAtlasTransversalData sourceWitness transversal =
  mapOrderedAtlasTransposalData
    sourceWitness
    (atlasTransversalOrderedTransposal transversal)
