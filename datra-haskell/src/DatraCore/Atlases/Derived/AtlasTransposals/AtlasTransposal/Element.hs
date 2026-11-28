{-# LANGUAGE CPP #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
#include "../../../../LiquidPlugin.h"
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}
{-@ LIQUID "--higherorder" @-}

-- | Genuine elements relative to an actual owning Atlas presentation.
module AtlasTransposal.Element
  ( AtlasTransposalElement, TransposalElementData
  , transposalElementSource, transposalElementValid
  , transposalElementAt, withTransposalElementOf
  , transposalWitnessElementValid, transposalWitnessOwnerAgrees
  , transposalOwnersAgree
  ) where

import Atlas (Atlas, atlasPageElements, normalizeAtlasElement,
  normalizeAtlasElementTraceValid, atlasCoherenceIdempotent)
import AtlasTransposal.Element.Internal
  (AtlasTransposalElement, TransposalElementData (..))
import Atlas.Witness
  (AtlasWitnessData, atlasWitnessData, atlasOwner, atlasWitnessOwner, atlasWitnessElementValid,
   normalizeAtlasWitnessElement, atlasWitnessOwnerAgrees)
import PageElements (pageElementTraceValid)
import PageElements.Structure (PageElement, SomePageElement (..))

{-@ reflect transposalElementSource @-}
transposalElementSource :: TransposalElementData a s d -> SomePageElement s
transposalElementSource (AtlasTransposalElement source) = SomePageElement source

-- | Scope indices alone do not assert membership in a particular owner.
{-@ reflect transposalElementValid @-}
transposalElementValid :: Atlas a s d o f -> TransposalElementData a s d -> Bool
transposalElementValid owner (AtlasTransposalElement source) =
  pageElementTraceValid (atlasPageElements owner) source
    && normalizeAtlasElement owner source == source

{-@ reflect transposalWitnessElementValid @-}
transposalWitnessElementValid :: AtlasWitnessData object a s d -> TransposalElementData a s d -> Bool
transposalWitnessElementValid witness (AtlasTransposalElement source) =
  atlasWitnessElementValid witness source && normalizeAtlasWitnessElement witness source == source

{-@ transposalWitnessOwnerAgrees :: witness:AtlasWitnessData object a s d
      -> owner:{Atlas a s d o f | atlasOwner owner == atlasWitnessOwner witness}
      -> element:TransposalElementData a s d
      -> {transposalWitnessElementValid witness element <=> transposalElementValid owner element} @-}
transposalWitnessOwnerAgrees :: AtlasWitnessData object a s d -> Atlas a s d o f
  -> TransposalElementData a s d -> ()
transposalWitnessOwnerAgrees witness owner (AtlasTransposalElement source) =
  atlasWitnessOwnerAgrees witness owner source

-- | Hidden endpoint carriers may differ; equality of complete owners is the
-- evidence needed to transfer the normalized trace domain.
-- ALIGN: ATLAS-TRANSPOSAL-OWNER-DOMAIN-AGREEMENT.
{-@ transposalOwnersAgree :: first:Atlas a s d o f
      -> second:{Atlas a s d o2 f2 | atlasOwner second == atlasOwner first}
      -> element:TransposalElementData a s d
      -> {transposalElementValid first element <=> transposalElementValid second element} @-}
transposalOwnersAgree :: Atlas a s d o f -> Atlas a s d o2 f2 -> TransposalElementData a s d -> ()
transposalOwnersAgree first second element =
  let witness = atlasWitnessData first
  in transposalWitnessOwnerAgrees witness first element `seq`
    transposalWitnessOwnerAgrees witness second element

-- ALIGN: ATLAS-TRANSPOSAL-OWNED-ELEMENT.
{-@ transposalElementAt :: owner:Atlas a s d o f
      -> source:{PageElement s object | pageElementTraceValid (atlasPageElements owner) source}
      -> {element:TransposalElementData a s d | transposalElementValid owner element
           && transposalElementSource element == SomePageElement (normalizeAtlasElement owner source)} @-}
transposalElementAt :: Atlas a s d o f -> PageElement s object -> TransposalElementData a s d
transposalElementAt owner source =
  normalizeAtlasElementTraceValid owner source `seq`
  atlasCoherenceIdempotent owner source `seq`
  AtlasTransposalElement (normalizeAtlasElement owner source)

-- ALIGN: ATLAS-TRANSPOSAL-OWNED-ELIMINATION.
{-@ withTransposalElementOf :: owner:Atlas a s d o f
      -> element:{TransposalElementData a s d | transposalElementValid owner element}
      -> (forall object. {source:PageElement s object |
           pageElementTraceValid (atlasPageElements owner) source
           && normalizeAtlasElement owner source == source
           && SomePageElement source == transposalElementSource element} -> result)
      -> result @-}
withTransposalElementOf :: Atlas a s d o f -> TransposalElementData a s d
  -> (forall object. PageElement s object -> result) -> result
withTransposalElementOf _ (AtlasTransposalElement source) useSource = useSource source
