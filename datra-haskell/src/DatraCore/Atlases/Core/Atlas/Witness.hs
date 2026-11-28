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
  , AtlasWitness, AtlasWitnessData, atlasWitnessFor, atlasWitnessData, atlasWitness, withAtlasWitnessData, withAtlasWitness
  , atlasWitnessElementValid, normalizeAtlasWitnessElement, atlasWitnessNormalizeValid
  , atlasWitnessOwnerAgrees, atlasOwnersMembershipAgrees, atlasOwnersMapDataAgree
  ) where

import Atlas.Witness.Internal
  ( AtlasObjectEquality (..), AtlasObject, AtlasObjectAtlasScope, AtlasObjectPaginationScope, AtlasObjectCellData
  , AtlasOwner, atlasOwner, atlasWitnessOwner
  , AtlasWitness, AtlasWitnessData
  , atlasWitnessElementValid, normalizeAtlasWitnessElement
  )

import qualified Atlas.Witness.Internal as Internal
  (atlasWitnessFor, atlasWitnessData, atlasWitness, withAtlasWitnessData, withAtlasWitness, atlasWitnessNormalizeValid, atlasWitnessOwnerAgrees, atlasOwnersMembershipAgrees, atlasOwnersMapDataAgree)
import Atlas.Internal (Atlas, atlasPageElements, normalizeAtlasElement, atlasAcceptsDatum, mapAtlasData)
import PageElements (PageElement, pageElementTraceValid)
import PageElements.Structure (PageElementArrow, arrowSource, arrowTarget)

{-@ atlasWitnessFor :: equality:AtlasObjectEquality object a s d -> owner:Atlas a s d o f
      -> {witness:AtlasWitnessData object a s d | atlasWitnessOwner witness == atlasOwner owner} @-}
atlasWitnessFor :: AtlasObjectEquality object a s d -> Atlas a s d o f -> AtlasWitnessData object a s d
atlasWitnessFor equality owner = Internal.atlasWitnessFor equality owner

{-@ atlasWitnessData :: owner:Atlas a s d o f
      -> {witness:AtlasWitnessData (AtlasObject a s d) a s d | atlasWitnessOwner witness == atlasOwner owner} @-}
atlasWitnessData
  :: Atlas atlasScope paginationScope cellData origin final
  -> AtlasWitnessData (AtlasObject atlasScope paginationScope cellData) atlasScope paginationScope cellData
atlasWitnessData owner = Internal.atlasWitnessData owner

{-@ atlasWitness :: owner:Atlas a s d o f
      -> {witness:AtlasWitness (AtlasObject a s d) | atlasWitnessOwner witness == atlasOwner owner} @-}
atlasWitness :: Atlas a s d o f -> AtlasWitness (AtlasObject a s d)
atlasWitness owner = Internal.atlasWitness owner

{-@ withAtlasWitnessData :: forall object a s d result. witness:AtlasWitnessData object a s d
      -> (forall origin final. AtlasObjectEquality object a s d
           -> owner:{Atlas a s d origin final | atlasOwner owner == atlasWitnessOwner witness} -> result)
      -> result @-}
withAtlasWitnessData
  :: forall object a s d result. AtlasWitnessData object a s d
  -> (forall origin final. AtlasObjectEquality object a s d
       -> Atlas a s d origin final -> result)
  -> result
withAtlasWitnessData witness useOwner = Internal.withAtlasWitnessData witness useOwner

{-@ withAtlasWitness :: forall object result. witness:AtlasWitness object
      -> (forall a s d origin final. AtlasObjectEquality object a s d
           -> owner:{Atlas a s d origin final | atlasOwner owner == atlasWitnessOwner witness} -> result)
      -> result @-}
withAtlasWitness :: forall object result. AtlasWitness object
  -> (forall a s d origin final. AtlasObjectEquality object a s d
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

-- | Equality of the complete owner retains the raw accepted-data predicate,
-- including at occurrences outside the folio domain.
{-@ atlasOwnersMembershipAgrees :: first:Atlas a s d o f
      -> second:{Atlas a s d o2 f2 | atlasOwner second == atlasOwner first}
      -> occurrence:PageElement s cell
      -> {atlasAcceptsDatum first occurrence == atlasAcceptsDatum second occurrence} @-}
atlasOwnersMembershipAgrees :: Atlas a s d o f -> Atlas a s d o2 f2
  -> PageElement s cell -> ()
atlasOwnersMembershipAgrees = Internal.atlasOwnersMembershipAgrees

-- | Owner equality retains the entire normalized insertion, so both forward
-- execution and partial inverse lookup agree.
{-@ atlasOwnersMapDataAgree :: first:Atlas a s d o f
      -> second:{Atlas a s d o2 f2 | atlasOwner second == atlasOwner first}
      -> arrow:{PageElementArrow s source target |
           pageElementTraceValid (atlasPageElements first) (arrowSource arrow)
           && pageElementTraceValid (atlasPageElements first) (arrowTarget arrow)}
      -> {mapAtlasData first arrow == mapAtlasData second arrow} @-}
atlasOwnersMapDataAgree :: Atlas a s d o f -> Atlas a s d o2 f2
  -> PageElementArrow s source target -> ()
atlasOwnersMapDataAgree = Internal.atlasOwnersMapDataAgree
