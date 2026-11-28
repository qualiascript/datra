{-# LANGUAGE CPP #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeFamilies #-}
#include "../../../../../LiquidPlugin.h"
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}
{-@ LIQUID "--higherorder" @-}
{-@ LIQUID "--etabeta" @-}

-- | Package a checked primitive action without losing its raw observations.
module AtlasTransposal.Primitive.Internal (primitiveAtlasTransposal, atlasTransposalFromAction) where

import Atlas (AtlasHom, AtlasObjectEquality (..), AtlasWitness, withAtlasWitness, AtlasMorphismAction, atlasHom, atlasMorphism, atlasMorphismSource, atlasMorphismTarget, AtlasObjectAtlasScope, AtlasObjectPaginationScope, AtlasObjectCellData)
import Atlas.Witness (atlasOwner)
import AtlasTransposal.Element (AtlasTransposalElement, transposalElementValid)
import AtlasTransposal.Action
  (TransposalAction, transposalAction, mapTransposalMorphismElement, transposalActionSource, transposalActionTarget, mapTransposalAction, transposalActionPreimage)
import AtlasTransposal.Syntax.Internal
  (AtlasTransposal (..), atlasTransposalSourceOwner, atlasTransposalTargetOwner,
   atlasTransposalSourceValid, atlasTransposalPathValid, mapAtlasTransposalObject, atlasTransposalPreimage)

{-@ primitiveAtlasTransposal :: hom:AtlasHom source target
      -> action:TransposalAction
           (AtlasObjectAtlasScope source) (AtlasObjectPaginationScope source) (AtlasObjectCellData source) so sf
           (AtlasObjectAtlasScope target) (AtlasObjectPaginationScope target) (AtlasObjectCellData target) to tf
      -> {result:AtlasTransposal source target |
           atlasTransposalOwnersCompatible result
           && atlasTransposalSourceOwner result == Just (atlasOwner (transposalActionSource action))
           && atlasTransposalTargetOwner result == Just (atlasOwner (transposalActionTarget action))
           && atlasTransposalSourceValid result == transposalElementValid (transposalActionSource action)
           && atlasTransposalPathValid result == transposalElementValid (transposalActionSource action)
           && mapAtlasTransposalObject result == mapTransposalAction action
           && atlasTransposalPreimage result == transposalActionPreimage action} @-}
primitiveAtlasTransposal :: AtlasHom source target
  -> TransposalAction
       (AtlasObjectAtlasScope source) (AtlasObjectPaginationScope source) (AtlasObjectCellData source) so sf
       (AtlasObjectAtlasScope target) (AtlasObjectPaginationScope target) (AtlasObjectCellData target) to tf
  -> AtlasTransposal source target
primitiveAtlasTransposal = PrimitiveAtlasTransposal


-- | Build the symbolic and raw primitive from the same checked materialized action.
-- ALIGN: ATLAS-TRANSPOSAL-ACTION-CONSTRUCTION.
{-@ atlasTransposalFromAction
      :: sourceWitness:AtlasWitness source -> targetWitness:AtlasWitness target
      -> action:AtlasMorphismAction m (AtlasObjectAtlasScope source) (AtlasObjectAtlasScope target)
           (AtlasObjectPaginationScope source) (AtlasObjectPaginationScope target)
           (AtlasObjectCellData source) (AtlasObjectCellData target) so sf to tf
      -> backward:(target:AtlasTransposalElement target
           -> Maybe ({source:AtlasTransposalElement source |
                transposalElementValid (atlasMorphismTarget action) target
                  => transposalElementValid (atlasMorphismSource action) source}))
      -> (source:{AtlasTransposalElement source | transposalElementValid (atlasMorphismSource action) source}
           -> {backward (mapTransposalMorphismElement action source) == Just source})
      -> {result:AtlasTransposal source target |
           atlasTransposalOwnersCompatible result
           && atlasTransposalSourceOwner result == Just (atlasOwner (atlasMorphismSource action))
           && atlasTransposalTargetOwner result == Just (atlasOwner (atlasMorphismTarget action))
           && atlasTransposalSourceValid result == transposalElementValid (atlasMorphismSource action)
           && atlasTransposalPathValid result == transposalElementValid (atlasMorphismSource action)
           && mapAtlasTransposalObject result == mapTransposalMorphismElement action
           && atlasTransposalPreimage result == backward} @-}
atlasTransposalFromAction :: AtlasWitness source -> AtlasWitness target
  -> AtlasMorphismAction m (AtlasObjectAtlasScope source) (AtlasObjectAtlasScope target)
       (AtlasObjectPaginationScope source) (AtlasObjectPaginationScope target)
       (AtlasObjectCellData source) (AtlasObjectCellData target) so sf to tf
  -> (AtlasTransposalElement target -> Maybe (AtlasTransposalElement source))
  -> (AtlasTransposalElement source -> ())
  -> AtlasTransposal source target
atlasTransposalFromAction sourceWitness targetWitness action backward leftInverse =
  primitiveAtlasTransposal (actionAtlasHom sourceWitness targetWitness action)
    (transposalAction (atlasMorphismSource action) (atlasMorphismTarget action)
      (mapTransposalMorphismElement action) backward leftInverse)

actionAtlasHom :: AtlasWitness source -> AtlasWitness target
  -> AtlasMorphismAction m (AtlasObjectAtlasScope source) (AtlasObjectAtlasScope target)
       (AtlasObjectPaginationScope source) (AtlasObjectPaginationScope target)
       (AtlasObjectCellData source) (AtlasObjectCellData target) so sf to tf
  -> AtlasHom source target
actionAtlasHom sourceWitness targetWitness action =
  withAtlasWitness sourceWitness $ \AtlasObjectEquality _ ->
  withAtlasWitness targetWitness $ \AtlasObjectEquality _ ->
    atlasHom (atlasMorphism action)
