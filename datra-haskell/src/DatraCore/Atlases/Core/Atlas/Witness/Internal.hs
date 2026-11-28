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
  , AtlasWitness, AtlasWitnessData (..), atlasWitnessFor, atlasWitnessData, atlasWitness, withAtlasWitnessData, withAtlasWitness
  , atlasWitnessElementValid, normalizeAtlasWitnessElement, atlasWitnessNormalizeValid
  , atlasWitnessOwnerAgrees, atlasOwnersMembershipAgrees, atlasOwnersMapDataAgree
  ) where

import Atlas.Internal
  (Atlas, atlasPageElements, normalizeAtlasElement, normalizeAtlasElementTraceValid, atlasCoherenceIdempotent, atlasAcceptsDatum, mapAtlasData)
import Data.Kind (Type)
import PageElements (PageElement, pageElementTraceValid)
import PageElements.Structure (PageElementArrow, arrowSource, arrowTarget)

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

-- | Retain an existing object index without specializing its carrier types.
-- ALIGN: ATLAS-WITNESS-INDEXED-OWNER.
{-@ reflect atlasWitnessFor @-}
{-@ atlasWitnessFor :: equality:AtlasObjectEquality object a s d -> owner:Atlas a s d o f
      -> {witness:AtlasWitnessData object a s d | atlasWitnessOwner witness == atlasOwner owner} @-}
atlasWitnessFor :: AtlasObjectEquality object a s d -> Atlas a s d o f -> AtlasWitnessData object a s d
atlasWitnessFor = AtlasWitness

-- | Retain explicit carrier parameters for proofs over raw owners.
-- ALIGN: ATLAS-WITNESS-RAW-CONSTRUCTION.
{-@ reflect atlasWitnessData @-}
{-@ atlasWitnessData :: owner:Atlas a s d o f
      -> {witness:AtlasWitnessData (AtlasObject a s d) a s d | atlasWitnessOwner witness == atlasOwner owner} @-}
atlasWitnessData
  :: Atlas atlasScope paginationScope cellData origin final
  -> AtlasWitnessData (AtlasObject atlasScope paginationScope cellData) atlasScope paginationScope cellData
atlasWitnessData owner = atlasWitnessFor AtlasObjectEquality owner

-- | Construct at the object-indexed boundary, retaining the actual owner.
-- ALIGN: ATLAS-WITNESS-CONSTRUCTION.
{-@ reflect atlasWitness @-}
{-@ atlasWitness :: owner:Atlas a s d o f
      -> {witness:AtlasWitness (AtlasObject a s d) | atlasWitnessOwner witness == atlasOwner owner} @-}
atlasWitness :: Atlas a s d o f -> AtlasWitness (AtlasObject a s d)
atlasWitness owner = AtlasWitness AtlasObjectEquality owner

-- | Eliminate a raw witness with its carrier parameters fixed.
-- ALIGN: ATLAS-WITNESS-RAW-ELIMINATION.
{-@ withAtlasWitnessData :: forall object a s d result. witness:AtlasWitnessData object a s d
      -> (forall origin final. AtlasObjectEquality object a s d
           -> owner:{Atlas a s d origin final | atlasOwner owner == atlasWitnessOwner witness} -> result)
      -> result @-}
withAtlasWitnessData
  :: forall object a s d result. AtlasWitnessData object a s d
  -> (forall origin final. AtlasObjectEquality object a s d
       -> Atlas a s d origin final -> result)
  -> result
withAtlasWitnessData (AtlasWitness equality valueAtlas) useAtlas = useAtlas equality valueAtlas

-- | Keep carrier parameters abstract until the callback consumes its explicit
-- equality evidence, preserving ownership across object-indexed construction.
-- ALIGN: ATLAS-WITNESS-ELIMINATION.
{-@ withAtlasWitness :: forall object result. witness:AtlasWitness object
      -> (forall a s d origin final. AtlasObjectEquality object a s d
           -> owner:{Atlas a s d origin final | atlasOwner owner == atlasWitnessOwner witness} -> result)
      -> result @-}
withAtlasWitness :: forall object result. AtlasWitness object
  -> (forall a s d origin final. AtlasObjectEquality object a s d
       -> Atlas a s d origin final -> result)
  -> result
withAtlasWitness (AtlasWitness equality owner) useOwner = useOwner equality owner

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

-- | Equality of the complete owner retains the raw accepted-data predicate,
-- including at occurrences outside the folio domain.
-- ALIGN: ATLAS-OWNERS-DATUM-AGREEMENT.
{-@ atlasOwnersMembershipAgrees :: first:Atlas a s d o f
      -> second:{Atlas a s d o2 f2 | atlasOwner second == atlasOwner first}
      -> occurrence:PageElement s cell
      -> {atlasAcceptsDatum first occurrence == atlasAcceptsDatum second occurrence} @-}
atlasOwnersMembershipAgrees :: Atlas a s d o f -> Atlas a s d o2 f2
  -> PageElement s cell -> ()
atlasOwnersMembershipAgrees _ _ _ = ()

-- | Owner equality retains the entire normalized insertion, so both forward
-- execution and partial inverse lookup agree.
-- ALIGN: ATLAS-OWNERS-DATA-MAP-AGREEMENT.
{-@ atlasOwnersMapDataAgree :: first:Atlas a s d o f
      -> second:{Atlas a s d o2 f2 | atlasOwner second == atlasOwner first}
      -> arrow:{PageElementArrow s source target |
           pageElementTraceValid (atlasPageElements first) (arrowSource arrow)
           && pageElementTraceValid (atlasPageElements first) (arrowTarget arrow)}
      -> {mapAtlasData first arrow == mapAtlasData second arrow} @-}
atlasOwnersMapDataAgree :: Atlas a s d o f -> Atlas a s d o2 f2
  -> PageElementArrow s source target -> ()
atlasOwnersMapDataAgree _ _ _ = ()
