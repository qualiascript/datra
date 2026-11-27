{-# LANGUAGE CPP #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE RoleAnnotations #-}
{-# LANGUAGE TypeFamilies #-}
#include "../../../../LiquidPlugin.h"
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}
{-@ LIQUID "--higherorder" @-}

-- | Owning Atlas witnesses and their checked dependent elimination.
module Atlas.Witness.Internal
  ( AtlasObjectEquality (..), AtlasObject, AtlasObjectAtlasScope, AtlasObjectPaginationScope, AtlasObjectCellData
  , AtlasOwner, atlasOwner, atlasWitnessOwner
  , AtlasWitness, AtlasWitnessData (..), atlasWitness, withAtlasWitness
  , atlasWitnessElementValid, normalizeAtlasWitnessElement, atlasWitnessNormalizeValid
  , atlasWitnessOwnerAgrees
  ) where

import Atlas.Internal
  (Atlas, atlasPageElements, normalizeAtlasElement, normalizeAtlasElementTraceValid, atlasCoherenceIdempotent)
import Data.Kind (Type)
import PageElements (PageElement, pageElementTraceValid)

-- | A type-level name for one Atlas object. The generative Atlas token is the
-- decisive identity; the pagination scope and data family are retained so an
-- arrow's executable source and target types can be recovered.
type role AtlasObject nominal nominal nominal
data AtlasObject
  (atlasScope :: Type)
  (paginationScope :: Type)
  (cellData :: Type -> Type)

type family AtlasObjectAtlasScope object :: Type where
  AtlasObjectAtlasScope (AtlasObject atlasScope paginationScope cellData) =
    atlasScope

type family AtlasObjectPaginationScope object :: Type where
  AtlasObjectPaginationScope
    (AtlasObject atlasScope paginationScope cellData) = paginationScope

type family AtlasObjectCellData object :: Type -> Type where
  AtlasObjectCellData
    (AtlasObject atlasScope paginationScope cellData) = cellData

-- | Explicit evidence for the type equality recovered by witness elimination.
-- The sole constructor preserves the association with the actual object index.
type role AtlasObjectEquality nominal nominal nominal nominal
data AtlasObjectEquality object atlasScope paginationScope cellData where
  AtlasObjectEquality :: AtlasObjectEquality (AtlasObject a s d) a s d

-- | Runtime evidence for a type-level 'AtlasObject'. Origin and final-page
-- carrier types remain existential because morphism operations do not expose
-- them.
type AtlasWitness object = AtlasWitnessData object (AtlasObjectAtlasScope object)
  (AtlasObjectPaginationScope object) (AtlasObjectCellData object)

type role AtlasWitnessData nominal nominal nominal nominal
data AtlasWitnessData object a s d where
  AtlasWitness :: forall object a s d origin final.
    AtlasObjectEquality object a s d -> Atlas a s d origin final
    -> AtlasWitnessData object a s d

-- | Preserve the complete owner while hiding the nominal indices. This is a
-- data package, not a hash or an independently allocated identity token.
data AtlasOwner where
  AtlasOwner :: Atlas a s d o f -> AtlasOwner

{-@ reflect atlasOwner @-}
atlasOwner :: Atlas a s d o f -> AtlasOwner
atlasOwner = AtlasOwner

{-@ reflect atlasWitnessOwner @-}
atlasWitnessOwner :: AtlasWitnessData object a s d -> AtlasOwner
atlasWitnessOwner (AtlasWitness _ owner) = atlasOwner owner

-- | Name an Atlas value as a category object witness.
-- ALIGN: ATLAS-WITNESS-CONSTRUCTION.
{-@ reflect atlasWitness @-}
{-@ atlasWitness :: owner:Atlas a s d o f
      -> {witness:AtlasWitnessData (AtlasObject a s d) a s d | atlasWitnessOwner witness == atlasOwner owner} @-}
atlasWitness
  :: Atlas atlasScope paginationScope cellData origin final
  -> AtlasWitnessData (AtlasObject atlasScope paginationScope cellData) atlasScope paginationScope cellData
atlasWitness owner = AtlasWitness AtlasObjectEquality owner

-- | Eliminate a witness while retaining the actual stored Atlas.
-- ALIGN: ATLAS-WITNESS-ELIMINATION.
{-@ withAtlasWitness :: forall object a s d result. witness:AtlasWitnessData object a s d
      -> (forall origin final. AtlasObjectEquality object a s d
           -> owner:{Atlas a s d origin final | atlasOwner owner == atlasWitnessOwner witness} -> result)
      -> result @-}
withAtlasWitness
  :: forall object a s d result. AtlasWitnessData object a s d
  -> (forall origin final. AtlasObjectEquality object a s d
       -> Atlas a s d origin final -> result)
  -> result
withAtlasWitness (AtlasWitness equality valueAtlas) useAtlas = useAtlas equality valueAtlas

{-@ reflect atlasWitnessElementValid @-}
atlasWitnessElementValid :: AtlasWitnessData object a s d
  -> PageElement s cell -> Bool
atlasWitnessElementValid (AtlasWitness _ owner) element =
  pageElementTraceValid (atlasPageElements owner) element

{-@ reflect normalizeAtlasWitnessElement @-}
normalizeAtlasWitnessElement :: AtlasWitnessData object a s d
  -> PageElement s cell
  -> PageElement s cell
normalizeAtlasWitnessElement (AtlasWitness _ owner) element = normalizeAtlasElement owner element

-- | Equal complete owners induce the same raw trace domain and normalization.
-- ALIGN: ATLAS-WITNESS-OWNER-AGREEMENT.
{-@ atlasWitnessOwnerAgrees :: witness:AtlasWitnessData object a s d
      -> owner:{Atlas a s d o f | atlasOwner owner == atlasWitnessOwner witness}
      -> source:PageElement s cell
      -> {(atlasWitnessElementValid witness source <=> pageElementTraceValid (atlasPageElements owner) source)
           && normalizeAtlasWitnessElement witness source == normalizeAtlasElement owner source} @-}
atlasWitnessOwnerAgrees :: AtlasWitnessData object a s d -> Atlas a s d o f
  -> PageElement s cell -> ()
atlasWitnessOwnerAgrees (AtlasWitness _ _) _ _ = ()

-- | Normalization preserves the witnessed domain and is idempotent on every
-- raw occurrence, including inputs outside that domain.
-- ALIGN: ATLAS-WITNESS-NORMALIZATION.
{-@ atlasWitnessNormalizeValid :: witness:AtlasWitnessData object a s d
      -> source:PageElement s cell
      -> {(atlasWitnessElementValid witness source =>
             atlasWitnessElementValid witness (normalizeAtlasWitnessElement witness source))
           && normalizeAtlasWitnessElement witness (normalizeAtlasWitnessElement witness source)
             == normalizeAtlasWitnessElement witness source} @-}
atlasWitnessNormalizeValid :: AtlasWitnessData object a s d
  -> PageElement s cell -> ()
atlasWitnessNormalizeValid witness@(AtlasWitness _ owner) source =
  (if atlasWitnessElementValid witness source
     then normalizeAtlasElementTraceValid owner source else ()) `seq`
    atlasCoherenceIdempotent owner source
