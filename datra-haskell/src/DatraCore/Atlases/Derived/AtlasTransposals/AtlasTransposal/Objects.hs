{-# LANGUAGE CPP #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE RoleAnnotations #-}
{-# LANGUAGE TypeFamilies #-}
#include "../../../../LiquidPlugin.h"
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}
{-@ LIQUID "--higherorder" @-}
{-@ LIQUID "--etabeta" @-}

-- | Retain one materialized object action when hiding its dependent indices.
module AtlasTransposal.Objects
  ( TransposalObjects, transposalObjects, transposalObjectsSource, transposalObjectsTarget
  , transposalObjectsSourceOwner, transposalObjectsTargetOwner
  , transposalObjectsWitnessAgrees
  , transposalObjectsTargetWitness, atlasHomTargetWitness
  , transposalObjectsTargetWitnessAgrees
  , homTransposalObjects, homTransposalObjectsRetains
  , atlasHomSourceOwner, atlasHomTargetOwner, atlasHomSourceValid, atlasHomTargetValid, mapAtlasHomObject
  , transposalObjectsMap, withTransposalObjects ) where

import Atlas (Atlas, AtlasMorphismAction, atlasMorphismSource, atlasMorphismTarget,
  AtlasHom, atlasHomTargetObjectEquality, materializeAtlasHom, withAtlasMorphismAction)
import Atlas.Witness (AtlasObjectEquality, atlasWitnessFor, AtlasOwner, atlasOwner, AtlasWitnessData, atlasWitnessOwner,
  AtlasWitness, AtlasObjectAtlasScope, AtlasObjectPaginationScope, AtlasObjectCellData)
import AtlasTransposal.Element
  (AtlasTransposalElement, TransposalElementData, transposalElementValid, transposalWitnessElementValid, transposalWitnessOwnerAgrees)
import AtlasTransposal.Action (mapTransposalMorphismElement)

type role TransposalObjects nominal nominal nominal nominal nominal nominal
data TransposalObjects sa ss sd ta ts td where
  TransposalObjects :: forall sa ss sd ta ts td m so sf to tf.
    AtlasMorphismAction m sa ta ss ts sd td so sf to tf
    -> TransposalObjects sa ss sd ta ts td

-- ALIGN: ATLAS-TRANSPOSAL-OBJECTS-OWNERS.
{-@ transposalObjects :: action:AtlasMorphismAction m sa ta ss ts sd td so sf to tf
      -> {objects:TransposalObjects sa ss sd ta ts td |
           transposalObjectsSourceOwner objects == atlasOwner (atlasMorphismSource action)
           && transposalObjectsTargetOwner objects == atlasOwner (atlasMorphismTarget action)} @-}
transposalObjects :: AtlasMorphismAction m sa ta ss ts sd td so sf to tf
  -> TransposalObjects sa ss sd ta ts td
transposalObjects = TransposalObjects

{-@ reflect transposalObjectsSourceOwner @-}
transposalObjectsSourceOwner :: TransposalObjects sa ss sd ta ts td -> AtlasOwner
transposalObjectsSourceOwner (TransposalObjects action) = atlasOwner (atlasMorphismSource action)

{-@ reflect transposalObjectsTargetOwner @-}
transposalObjectsTargetOwner :: TransposalObjects sa ss sd ta ts td -> AtlasOwner
transposalObjectsTargetOwner (TransposalObjects action) = atlasOwner (atlasMorphismTarget action)

-- | Use the target stored in this materialization, not an independently recovered owner.
-- ALIGN: ATLAS-TRANSPOSAL-OBJECTS-TARGET-WITNESS.
{-@ transposalObjectsTargetWitness :: AtlasObjectEquality target ta ts td
      -> objects:TransposalObjects sa ss sd ta ts td
      -> {witness:AtlasWitnessData target ta ts td | atlasWitnessOwner witness == transposalObjectsTargetOwner objects} @-}
transposalObjectsTargetWitness :: AtlasObjectEquality target ta ts td -> TransposalObjects sa ss sd ta ts td
  -> AtlasWitnessData target ta ts td
transposalObjectsTargetWitness equality (TransposalObjects action) = atlasWitnessFor equality (atlasMorphismTarget action)

{-@ transposalObjectsWitnessAgrees :: witness:AtlasWitnessData object sa ss sd
      -> objects:{TransposalObjects sa ss sd ta ts td |
           transposalObjectsSourceOwner objects == atlasWitnessOwner witness}
      -> element:TransposalElementData sa ss sd
      -> {transposalWitnessElementValid witness element <=> transposalObjectsSource objects element} @-}
transposalObjectsWitnessAgrees :: AtlasWitnessData object sa ss sd -> TransposalObjects sa ss sd ta ts td
  -> TransposalElementData sa ss sd -> ()
transposalObjectsWitnessAgrees witness (TransposalObjects action) element =
  transposalWitnessOwnerAgrees witness (atlasMorphismSource action) element

{-@ transposalObjectsTargetWitnessAgrees :: witness:AtlasWitnessData object ta ts td
      -> objects:{TransposalObjects sa ss sd ta ts td |
           transposalObjectsTargetOwner objects == atlasWitnessOwner witness}
      -> element:TransposalElementData ta ts td
      -> {transposalWitnessElementValid witness element <=> transposalObjectsTarget objects element} @-}
transposalObjectsTargetWitnessAgrees :: AtlasWitnessData object ta ts td -> TransposalObjects sa ss sd ta ts td
  -> TransposalElementData ta ts td -> ()
transposalObjectsTargetWitnessAgrees witness (TransposalObjects action) element =
  transposalWitnessOwnerAgrees witness (atlasMorphismTarget action) element

{-@ reflect transposalObjectsSource @-}
transposalObjectsSource :: TransposalObjects sa ss sd ta ts td
  -> TransposalElementData sa ss sd -> Bool
transposalObjectsSource (TransposalObjects action) = transposalElementValid (atlasMorphismSource action)

{-@ reflect transposalObjectsTarget @-}
transposalObjectsTarget :: TransposalObjects sa ss sd ta ts td
  -> TransposalElementData ta ts td -> Bool
transposalObjectsTarget (TransposalObjects action) = transposalElementValid (atlasMorphismTarget action)

{-@ reflect transposalObjectsMap @-}
{-@ transposalObjectsMap :: objects:TransposalObjects sa ss sd ta ts td
      -> source:TransposalElementData sa ss sd
      -> {target:TransposalElementData ta ts td |
           transposalObjectsSource objects source => transposalObjectsTarget objects target} @-}
transposalObjectsMap :: TransposalObjects sa ss sd ta ts td
  -> TransposalElementData sa ss sd -> TransposalElementData ta ts td
transposalObjectsMap (TransposalObjects action) source = mapTransposalMorphismElement action source

-- ALIGN: ATLAS-TRANSPOSAL-OBJECTS-ELIMINATION.
{-@ withTransposalObjects :: objects:TransposalObjects sa ss sd ta ts td
      -> (forall so sf to tf.
           sourceOwner:{Atlas sa ss sd so sf |
             atlasOwner sourceOwner == transposalObjectsSourceOwner objects
             && transposalElementValid sourceOwner == transposalObjectsSource objects}
           -> targetOwner:{Atlas ta ts td to tf |
             atlasOwner targetOwner == transposalObjectsTargetOwner objects
             && transposalElementValid targetOwner == transposalObjectsTarget objects}
           -> (source:TransposalElementData sa ss sd
                -> {target:TransposalElementData ta ts td |
                     (transposalElementValid sourceOwner source => transposalElementValid targetOwner target)
                     && target == transposalObjectsMap objects source})
           -> result)
      -> result @-}
withTransposalObjects :: TransposalObjects sa ss sd ta ts td
  -> (forall so sf to tf. Atlas sa ss sd so sf -> Atlas ta ts td to tf
        -> (TransposalElementData sa ss sd -> TransposalElementData ta ts td) -> result)
  -> result
withTransposalObjects (TransposalObjects action) useObjects =
  useObjects (atlasMorphismSource action) (atlasMorphismTarget action)
    (\source -> mapTransposalMorphismElement action source)

-- | Materialize once, retaining the exact object map and both owner domains.
{-@ opaque-reflect homTransposalObjects @-}
homTransposalObjects :: AtlasWitness source -> AtlasHom source target
  -> TransposalObjects (AtlasObjectAtlasScope source) (AtlasObjectPaginationScope source) (AtlasObjectCellData source)
       (AtlasObjectAtlasScope target) (AtlasObjectPaginationScope target) (AtlasObjectCellData target)
homTransposalObjects witness hom = withAtlasMorphismAction (materializeAtlasHom witness hom) transposalObjects

-- | The Hom's index evidence names the owner retained by its object package.
-- ALIGN: ATLAS-TRANSPOSAL-HOM-TARGET-WITNESS.
{-@ opaque-reflect atlasHomTargetWitness @-}
{-@ atlasHomTargetWitness :: sourceWitness:AtlasWitness source -> hom:AtlasHom source target
      -> {witness:AtlasWitness target | atlasWitnessOwner witness == atlasHomTargetOwner sourceWitness hom} @-}
atlasHomTargetWitness :: AtlasWitness source -> AtlasHom source target -> AtlasWitness target
atlasHomTargetWitness sourceWitness hom =
  transposalObjectsTargetWitness (atlasHomTargetObjectEquality sourceWitness hom) (homTransposalObjects sourceWitness hom)

{-@ reflect atlasHomSourceOwner @-}
atlasHomSourceOwner :: AtlasWitness source -> AtlasHom source target -> AtlasOwner
atlasHomSourceOwner witness hom = transposalObjectsSourceOwner (homTransposalObjects witness hom)

{-@ reflect atlasHomTargetOwner @-}
atlasHomTargetOwner :: AtlasWitness source -> AtlasHom source target -> AtlasOwner
atlasHomTargetOwner witness hom = transposalObjectsTargetOwner (homTransposalObjects witness hom)

{-@ reflect atlasHomSourceValid @-}
atlasHomSourceValid :: AtlasWitness source -> AtlasHom source target -> AtlasTransposalElement source -> Bool
atlasHomSourceValid witness hom = transposalObjectsSource (homTransposalObjects witness hom)

{-@ reflect atlasHomTargetValid @-}
atlasHomTargetValid :: AtlasWitness source -> AtlasHom source target -> AtlasTransposalElement target -> Bool
atlasHomTargetValid witness hom = transposalObjectsTarget (homTransposalObjects witness hom)

{-@ reflect mapAtlasHomObject @-}
{-@ mapAtlasHomObject :: witness:AtlasWitness source -> hom:AtlasHom source target
      -> sourceElement:AtlasTransposalElement source
      -> {targetElement:AtlasTransposalElement target |
           atlasHomSourceValid witness hom sourceElement => atlasHomTargetValid witness hom targetElement} @-}
mapAtlasHomObject
  :: AtlasWitness source
  -> AtlasHom source target
  -> AtlasTransposalElement source
  -> AtlasTransposalElement target
mapAtlasHomObject sourceWitness hom = transposalObjectsMap (homTransposalObjects sourceWitness hom)

{-@ homTransposalObjectsRetains :: witness:AtlasWitness source -> hom:AtlasHom source target
      -> {transposalObjectsSource (homTransposalObjects witness hom) == atlasHomSourceValid witness hom
           && transposalObjectsTarget (homTransposalObjects witness hom) == atlasHomTargetValid witness hom
           && transposalObjectsMap (homTransposalObjects witness hom) == mapAtlasHomObject witness hom} @-}
homTransposalObjectsRetains :: AtlasWitness source -> AtlasHom source target -> ()
homTransposalObjectsRetains _ _ = ()
