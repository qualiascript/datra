{-# LANGUAGE CPP #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeFamilies #-}
#include "../../../LiquidPlugin.h"
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--higherorder" @-}
{-@ opaque-reflect atlasOwner @-}
{-@ opaque-reflect atlasWitnessOwner @-}
{-@ opaque-reflect atlasWitnessElementValid @-}
{-@ opaque-reflect normalizeAtlasWitnessElement @-}

-- | Atlas object names with ownership retained through witness elimination.
module Atlas.Witness
  ( AtlasObjectEquality (..), AtlasObject, AtlasObjectAtlasScope, AtlasObjectPaginationScope, AtlasObjectCellData
  , AtlasOwner, atlasOwner, atlasWitnessOwner
  , AtlasWitness, AtlasWitnessData, atlasWitness, withAtlasWitness
  , atlasWitnessElementValid, normalizeAtlasWitnessElement, atlasWitnessNormalizeValid
  , atlasWitnessOwnerAgrees
  ) where

import Atlas.Witness.Internal
  ( AtlasObjectEquality (..), AtlasObject, AtlasObjectAtlasScope, AtlasObjectPaginationScope, AtlasObjectCellData
  , AtlasOwner, atlasOwner, atlasWitnessOwner
  , AtlasWitness, AtlasWitnessData
  , atlasWitnessElementValid, normalizeAtlasWitnessElement
  )

import qualified Atlas.Witness.Internal as Internal
  (atlasWitness, withAtlasWitness, atlasWitnessNormalizeValid, atlasWitnessOwnerAgrees)
import Atlas.Internal (Atlas, atlasPageElements, normalizeAtlasElement)
import PageElements (PageElement, pageElementTraceValid)

{-@ atlasWitness :: owner:Atlas a s d o f
      -> {witness:AtlasWitnessData (AtlasObject a s d) a s d | atlasWitnessOwner witness == atlasOwner owner} @-}
atlasWitness
  :: Atlas atlasScope paginationScope cellData origin final
  -> AtlasWitnessData (AtlasObject atlasScope paginationScope cellData) atlasScope paginationScope cellData
atlasWitness owner = Internal.atlasWitness owner

{-@ withAtlasWitness :: forall object a s d result. witness:AtlasWitnessData object a s d
      -> (forall origin final. AtlasObjectEquality object a s d
           -> owner:{Atlas a s d origin final | atlasOwner owner == atlasWitnessOwner witness} -> result)
      -> result @-}
withAtlasWitness
  :: forall object a s d result. AtlasWitnessData object a s d
  -> (forall origin final. AtlasObjectEquality object a s d
       -> Atlas a s d origin final -> result)
  -> result
withAtlasWitness witness useOwner = Internal.withAtlasWitness witness useOwner

{-@ atlasWitnessNormalizeValid :: witness:AtlasWitnessData object a s d
      -> source:PageElement s cell
      -> {(atlasWitnessElementValid witness source =>
             atlasWitnessElementValid witness (normalizeAtlasWitnessElement witness source))
           && normalizeAtlasWitnessElement witness (normalizeAtlasWitnessElement witness source)
             == normalizeAtlasWitnessElement witness source} @-}
atlasWitnessNormalizeValid :: AtlasWitnessData object a s d
  -> PageElement s cell -> ()
atlasWitnessNormalizeValid witness source = Internal.atlasWitnessNormalizeValid witness source

{-@ atlasWitnessOwnerAgrees :: witness:AtlasWitnessData object a s d
      -> owner:{Atlas a s d o f | atlasOwner owner == atlasWitnessOwner witness}
      -> source:PageElement s cell
      -> {(atlasWitnessElementValid witness source <=> pageElementTraceValid (atlasPageElements owner) source)
           && normalizeAtlasWitnessElement witness source == normalizeAtlasElement owner source} @-}
atlasWitnessOwnerAgrees :: AtlasWitnessData object a s d -> Atlas a s d o f
  -> PageElement s cell -> ()
atlasWitnessOwnerAgrees witness owner source = Internal.atlasWitnessOwnerAgrees witness owner source
