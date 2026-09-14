{-# LANGUAGE CPP #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE RoleAnnotations #-}
{-# LANGUAGE TypeFamilies #-}
#include "../../../../LiquidPlugin.h"
{-@ LIQUID "--reflection" @-}

-- | Hidden implementation of stable Atlas transversals.
module StableAtlasTransversal.Internal
  ( StableAtlasTransversal
  , stableAtlasTransversal
  , stableAtlasTransversalTransversal
  , stableAtlasTransversalOrderedTransposal
  , stableAtlasTransversalTransposal
  , stableAtlasTransversalHom
  , stableAtlasTransversalPreservesExtent
  , identityStableAtlasTransversal
  , composeStableAtlasTransversals
  , mapStableAtlasTransversalObject
  , stableAtlasTransversalPreimage
  , stableAtlasTransversalLeftInverse
  , stableAtlasTransversalPreservesOrder
  , stableAtlasTransversalPreservesCoverage
  , stableAtlasTransversalPagination
  , mapStableAtlasTransversalElement
  , mapStableAtlasTransversalArrow
  , mapStableAtlasTransversalData
  , mapStableAtlasTransversalCoveredDatum
  , stableOriginPreserved
  ) where

import Atlas
  ( Atlas
  , AtlasHom
  , AtlasMorphismImage
  , AtlasObject
  , AtlasObjectCellData
  , AtlasObjectPaginationScope
  , AtlasWitness
  , atlasOriginCell
  , atlasWitness
  )
import AtlasTransposal
  ( AtlasTransposal
  , AtlasTransposalElement
  , atlasTransposalElement
  , withAtlasTransposalElement
  )
import AtlasTransversal
  ( AtlasCoveredDatum
  , AtlasTransversal
  , atlasTransversalHom
  , atlasTransversalLeftInverse
  , atlasTransversalOrderedTransposal
  , atlasTransversalPagination
  , atlasTransversalPreimage
  , atlasTransversalPreservesCoverage
  , atlasTransversalPreservesOrder
  , atlasTransversalTransposal
  , composeAtlasTransversals
  , identityAtlasTransversal
  , mapAtlasTransversalArrow
  , mapAtlasTransversalCoveredDatum
  , mapAtlasTransversalData
  , mapAtlasTransversalElement
  , mapAtlasTransversalObject
  )
import Control.Category (Category (..))
import DatraOrdinal (Ordinal)
import Numeric.Natural (Natural)
import OrderedAtlasTransposal (OrderedAtlasTransposal)
import PageElements
  ( PageElement
  , PageElementArrow
  , SomePageElement
  , pageElementPage
  , pageElementPosition
  , withPageElement
  )
import Pagination (PaginationMorphism, SomePageElementArrow)
import Prelude hiding ((.), id)

-- | The canonical element supporting an Atlas extent.
{-@ reflect stableAtlasOrigin @-}
stableAtlasOrigin
  :: Atlas atlasScope scope cellData origin final
  -> AtlasTransposalElement
       (AtlasObject atlasScope scope cellData)
stableAtlasOrigin valueAtlas =
  withPageElement (atlasOriginCell valueAtlas) $ \origin ->
    atlasTransposalElement (atlasWitness valueAtlas) origin

{-@ reflect stableElementPage @-}
stableElementPage :: AtlasTransposalElement atlasObject -> Natural
stableElementPage element =
  withAtlasTransposalElement element pageElementPage

{-@ reflect stableElementPosition @-}
stableElementPosition :: AtlasTransposalElement atlasObject -> Ordinal
stableElementPosition element =
  withAtlasTransposalElement element pageElementPosition

-- | Lean's @IsStableTransversal@ proposition. Comparing the canonical page and
-- position is equality of Atlas elements, and specifically states that the
-- transversal sends the source origin/extent cell to the target origin/extent
-- cell.
{-@ reflect stableOriginPreserved @-}
stableOriginPreserved
  :: Atlas
       sourceAtlasScope sourceScope sourceCellData sourceOrigin sourceFinal
  -> Atlas
       targetAtlasScope targetScope targetCellData targetOrigin targetFinal
  -> AtlasTransversal
       (AtlasObject sourceAtlasScope sourceScope sourceCellData)
       (AtlasObject targetAtlasScope targetScope targetCellData)
  -> Bool
stableOriginPreserved sourceAtlas targetAtlas transversal =
  let mappedOrigin =
        mapAtlasTransversalObject
          transversal
          (stableAtlasOrigin sourceAtlas)
      targetOrigin = stableAtlasOrigin targetAtlas
  in stableElementPage mappedOrigin == stableElementPage targetOrigin
      && stableElementPosition mappedOrigin
        == stableElementPosition targetOrigin

-- | Preserve the refinement while moving the caller's erased proof into the
-- hidden categorical representation. Keeping this boundary explicit makes
-- LiquidHaskell verify the stored certificate rather than merely parsing a
-- refined constructor signature.
{-@
checkedStableOrigin
  :: sourceAtlas:Atlas
       sourceAtlasScope sourceScope sourceCellData sourceOrigin sourceFinal
  -> targetAtlas:Atlas
       targetAtlasScope targetScope targetCellData targetOrigin targetFinal
  -> transversal:AtlasTransversal
       (AtlasObject sourceAtlasScope sourceScope sourceCellData)
       (AtlasObject targetAtlasScope targetScope targetCellData)
  -> { proof:() |
       stableOriginPreserved sourceAtlas targetAtlas transversal }
  -> { checked:() |
       stableOriginPreserved sourceAtlas targetAtlas transversal }
@-}
checkedStableOrigin
  :: Atlas
       sourceAtlasScope sourceScope sourceCellData sourceOrigin sourceFinal
  -> Atlas
       targetAtlasScope targetScope targetCellData targetOrigin targetFinal
  -> AtlasTransversal
       (AtlasObject sourceAtlasScope sourceScope sourceCellData)
       (AtlasObject targetAtlasScope targetScope targetCellData)
  -> ()
  -> ()
checkedStableOrigin _ _ _ proof = proof

-- | The final restriction in the transposal hierarchy. Primitive arrows carry
-- a compile-time proof of extent preservation; identity and composition carry
-- the property structurally.
type role StableAtlasTransversal nominal nominal
data StableAtlasTransversal source target where
  PrimitiveStableAtlasTransversal
    :: Atlas
         sourceAtlasScope sourceScope sourceCellData sourceOrigin sourceFinal
    -> Atlas
         targetAtlasScope targetScope targetCellData targetOrigin targetFinal
    -> AtlasTransversal
         (AtlasObject sourceAtlasScope sourceScope sourceCellData)
         (AtlasObject targetAtlasScope targetScope targetCellData)
    -> ()
    -> StableAtlasTransversal
         (AtlasObject sourceAtlasScope sourceScope sourceCellData)
         (AtlasObject targetAtlasScope targetScope targetCellData)
  IdentityStableAtlasTransversal
    :: StableAtlasTransversal object object
  CompositeStableAtlasTransversal
    :: StableAtlasTransversal middle target
    -> StableAtlasTransversal source middle
    -> StableAtlasTransversal source target

-- | Restrict an Atlas transversal to arrows sending extent to extent.
{-@
stableAtlasTransversal
  :: sourceAtlas:Atlas
       sourceAtlasScope sourceScope sourceCellData sourceOrigin sourceFinal
  -> targetAtlas:Atlas
       targetAtlasScope targetScope targetCellData targetOrigin targetFinal
  -> transversal:AtlasTransversal
       (AtlasObject sourceAtlasScope sourceScope sourceCellData)
       (AtlasObject targetAtlasScope targetScope targetCellData)
  -> { proof:() |
       stableOriginPreserved sourceAtlas targetAtlas transversal }
  -> StableAtlasTransversal
       (AtlasObject sourceAtlasScope sourceScope sourceCellData)
       (AtlasObject targetAtlasScope targetScope targetCellData)
@-}
stableAtlasTransversal
  :: Atlas
       sourceAtlasScope sourceScope sourceCellData sourceOrigin sourceFinal
  -> Atlas
       targetAtlasScope targetScope targetCellData targetOrigin targetFinal
  -> AtlasTransversal
       (AtlasObject sourceAtlasScope sourceScope sourceCellData)
       (AtlasObject targetAtlasScope targetScope targetCellData)
  -> ()
  -> StableAtlasTransversal
       (AtlasObject sourceAtlasScope sourceScope sourceCellData)
       (AtlasObject targetAtlasScope targetScope targetCellData)
stableAtlasTransversal sourceAtlas targetAtlas transversal proof =
  PrimitiveStableAtlasTransversal
    sourceAtlas
    targetAtlas
    transversal
    (checkedStableOrigin sourceAtlas targetAtlas transversal proof)

-- | Forget the extent restriction while retaining every transversal law.
stableAtlasTransversalTransversal
  :: StableAtlasTransversal source target
  -> AtlasTransversal source target
stableAtlasTransversalTransversal
  (PrimitiveStableAtlasTransversal _ _ transversal _) = transversal
stableAtlasTransversalTransversal IdentityStableAtlasTransversal =
  identityAtlasTransversal
stableAtlasTransversalTransversal
  (CompositeStableAtlasTransversal second first) =
    composeAtlasTransversals
      (stableAtlasTransversalTransversal second)
      (stableAtlasTransversalTransversal first)

-- | Include a stable transversal into ordered Atlas transposals.
stableAtlasTransversalOrderedTransposal
  :: StableAtlasTransversal source target
  -> OrderedAtlasTransposal source target
stableAtlasTransversalOrderedTransposal =
  atlasTransversalOrderedTransposal . stableAtlasTransversalTransversal

-- | Include a stable transversal into Atlas transposals.
stableAtlasTransversalTransposal
  :: StableAtlasTransversal source target
  -> AtlasTransposal source target
stableAtlasTransversalTransposal =
  atlasTransversalTransposal . stableAtlasTransversalTransversal

-- | Include a stable transversal into the Atlas category.
stableAtlasTransversalHom
  :: StableAtlasTransversal source target
  -> AtlasHom source target
stableAtlasTransversalHom =
  atlasTransversalHom . stableAtlasTransversalTransversal

-- | Invoke the primitive or structurally derived extent-preservation proof.
stableAtlasTransversalPreservesExtent
  :: StableAtlasTransversal source target
  -> ()
stableAtlasTransversalPreservesExtent
  (PrimitiveStableAtlasTransversal _ _ _ proof) = proof
stableAtlasTransversalPreservesExtent IdentityStableAtlasTransversal = ()
stableAtlasTransversalPreservesExtent
  (CompositeStableAtlasTransversal second first) =
    stableAtlasTransversalPreservesExtent first `seq`
      stableAtlasTransversalPreservesExtent second

identityStableAtlasTransversal :: StableAtlasTransversal object object
identityStableAtlasTransversal = IdentityStableAtlasTransversal

composeStableAtlasTransversals
  :: StableAtlasTransversal middle target
  -> StableAtlasTransversal source middle
  -> StableAtlasTransversal source target
composeStableAtlasTransversals IdentityStableAtlasTransversal first = first
composeStableAtlasTransversals second IdentityStableAtlasTransversal = second
composeStableAtlasTransversals
  second
  (CompositeStableAtlasTransversal middle first) =
    CompositeStableAtlasTransversal
      (composeStableAtlasTransversals second middle)
      first
composeStableAtlasTransversals second first =
  CompositeStableAtlasTransversal second first

instance Category StableAtlasTransversal where
  id = identityStableAtlasTransversal
  (.) = composeStableAtlasTransversals

mapStableAtlasTransversalObject
  :: StableAtlasTransversal source target
  -> AtlasTransposalElement source
  -> AtlasTransposalElement target
mapStableAtlasTransversalObject stable =
  mapAtlasTransversalObject (stableAtlasTransversalTransversal stable)

stableAtlasTransversalPreimage
  :: StableAtlasTransversal source target
  -> AtlasTransposalElement target
  -> Maybe (AtlasTransposalElement source)
stableAtlasTransversalPreimage stable =
  atlasTransversalPreimage (stableAtlasTransversalTransversal stable)

stableAtlasTransversalLeftInverse
  :: StableAtlasTransversal source target
  -> AtlasTransposalElement source
  -> ()
stableAtlasTransversalLeftInverse stable =
  atlasTransversalLeftInverse (stableAtlasTransversalTransversal stable)

stableAtlasTransversalPreservesOrder
  :: StableAtlasTransversal source target
  -> AtlasTransposalElement source
  -> AtlasTransposalElement source
  -> ()
stableAtlasTransversalPreservesOrder stable =
  atlasTransversalPreservesOrder (stableAtlasTransversalTransversal stable)

stableAtlasTransversalPreservesCoverage
  :: StableAtlasTransversal source target
  -> AtlasCoveredDatum source
  -> AtlasCoveredDatum target
stableAtlasTransversalPreservesCoverage stable =
  atlasTransversalPreservesCoverage (stableAtlasTransversalTransversal stable)

stableAtlasTransversalPagination
  :: AtlasWitness source
  -> StableAtlasTransversal source target
  -> PaginationMorphism
       (AtlasObjectPaginationScope source)
       (AtlasObjectPaginationScope target)
stableAtlasTransversalPagination sourceWitness stable =
  atlasTransversalPagination
    sourceWitness
    (stableAtlasTransversalTransversal stable)

mapStableAtlasTransversalElement
  :: AtlasWitness source
  -> StableAtlasTransversal source target
  -> PageElement (AtlasObjectPaginationScope source) object
  -> SomePageElement (AtlasObjectPaginationScope target)
mapStableAtlasTransversalElement sourceWitness stable =
  mapAtlasTransversalElement
    sourceWitness
    (stableAtlasTransversalTransversal stable)

mapStableAtlasTransversalArrow
  :: AtlasWitness source
  -> StableAtlasTransversal source target
  -> PageElementArrow
       (AtlasObjectPaginationScope source) sourceObject targetObject
  -> SomePageElementArrow (AtlasObjectPaginationScope target)
mapStableAtlasTransversalArrow sourceWitness stable =
  mapAtlasTransversalArrow
    sourceWitness
    (stableAtlasTransversalTransversal stable)

mapStableAtlasTransversalData
  :: AtlasWitness source
  -> StableAtlasTransversal source target
  -> PageElement (AtlasObjectPaginationScope source) sourceObject
  -> AtlasMorphismImage
       (AtlasObjectPaginationScope target)
       (AtlasObjectCellData source)
       (AtlasObjectCellData target)
       sourceObject
mapStableAtlasTransversalData sourceWitness stable =
  mapAtlasTransversalData
    sourceWitness
    (stableAtlasTransversalTransversal stable)

mapStableAtlasTransversalCoveredDatum
  :: StableAtlasTransversal source target
  -> AtlasCoveredDatum source
  -> AtlasCoveredDatum target
mapStableAtlasTransversalCoveredDatum stable =
  mapAtlasTransversalCoveredDatum (stableAtlasTransversalTransversal stable)
