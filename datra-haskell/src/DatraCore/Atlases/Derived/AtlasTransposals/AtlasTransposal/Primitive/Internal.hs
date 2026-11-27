{-# LANGUAGE CPP #-}
{-# LANGUAGE TypeFamilies #-}
#include "../../../../../LiquidPlugin.h"
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}
{-@ LIQUID "--higherorder" @-}
{-@ LIQUID "--etabeta" @-}

-- | Package a checked primitive action without losing its raw observations.
module AtlasTransposal.Primitive.Internal (primitiveAtlasTransposal) where

import Atlas (AtlasHom, AtlasObjectAtlasScope, AtlasObjectPaginationScope, AtlasObjectCellData)
import Atlas.Witness (atlasOwner)
import AtlasTransposal.Element (transposalElementValid)
import AtlasTransposal.Action
  (TransposalAction, transposalActionSource, transposalActionTarget, mapTransposalAction, transposalActionPreimage)
import AtlasTransposal.Syntax.Internal
  (AtlasTransposal (..), atlasTransposalSourceOwner, atlasTransposalTargetOwner,
   atlasTransposalSourceValid, atlasTransposalPathValid, mapAtlasTransposalObject, atlasTransposalPreimage)

{-@ primitiveAtlasTransposal :: hom:AtlasHom source target
      -> action:TransposalAction
           (AtlasObjectAtlasScope source) (AtlasObjectPaginationScope source) (AtlasObjectCellData source) so sf
           (AtlasObjectAtlasScope target) (AtlasObjectPaginationScope target) (AtlasObjectCellData target) to tf
      -> {result:AtlasTransposal source target |
           atlasTransposalSourceOwner result == Just (atlasOwner (transposalActionSource action))
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

