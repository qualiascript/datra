{-# LANGUAGE CPP #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE RoleAnnotations #-}
{-# LANGUAGE TypeFamilies #-}
{-# OPTIONS_GHC -Wno-unused-imports #-}
#include "../../../../LiquidPlugin.h"
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--higherorder" @-}
{-@ qualif StableSource(v:@(0), accepts:func(0, [@(0); bool])) { accepts v } @-}
{-@ qualif StableOrigin(v:@(0), key:func(0, [@(0); (PageElements.Structure.SomePageElement @(1))]),
      origin:(PageElements.Structure.SomePageElement @(1))) { key v == origin } @-}

-- | Hidden implementation of stable Atlas transversals.
module StableAtlasTransversal.Internal
  ( StableAtlasTransversal
  , stableAtlasTransversal
  , stableAtlasTransversalTransversal
  , stableAtlasTransversalOrderedTransposal
  , stableAtlasTransversalTransposal
  , stableAtlasTransversalHom
  , stableAtlasTransversalSourceWitness
  , stableAtlasTransversalCoalitionInsertion
  , withStableAtlasTransversalCoalitionPreimage
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
  , mapStableAtlasTransversalCoveredPageElement
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
  , atlasPageElements
  , atlasWitness
  )
import AtlasTransposal
  ( AtlasTransposal
  , AtlasTransposalElement
  , atlasTransposalElement
  , withAtlasTransposalElement
  )
import AtlasCoveredPageElement (AtlasCoveredPageElement)
import AtlasTransversal
  ( AtlasTransversal
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
  , mapAtlasTransversalCoveredPageElement
  , mapAtlasTransversalData
  , mapAtlasTransversalElement
  , mapAtlasTransversalObject
  )
import Coalition.Element
  ( CoalitionElement, CoalitionData, mapCoalitionElement
  , coalitionElementValid, coalitionElementSource, coalitionCounitInsertion )
import DomanialInsertion.Core
  ( DomanialInsertion (..), identityInsertion, composeInsertions
  , composePartialInverses )
import Control.Category (Category (..))
import DatraOrdinal (Ordinal)
import Numeric.Natural (Natural)
import OrderedAtlasTransposal (OrderedAtlasTransposal)
import PageElements
  ( PageElement
  , PageElementArrow
  , pageElementPage
  , pageElementPosition
  , withPageElement
  , originPageElement
  )
import PageElements.Structure (SomePageElement)
import Pagination (PaginationMorphism, SomePageElementArrow)
import Prelude hiding ((.), id)

-- | The canonical element supporting an Atlas extent.
{-@ reflect stableAtlasOrigin @-}
-- ALIGN: ATLAS-STABLE-ORIGIN.
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
-- ALIGN: ATLAS-STABLE-PREDICATE.
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
-- checked extent preservation and a coalition insertion with an explicit
-- inverse. Identity and composition derive both certificates structurally.
type role StableAtlasTransversal nominal nominal
data StableAtlasTransversal source target where
  PrimitiveStableAtlasTransversal
    :: StableTransversalAction sa ss sd so sf ta ts td to tf
    -> StableAtlasTransversal (AtlasObject sa ss sd) (AtlasObject ta ts td)
  IdentityStableAtlasTransversal
    :: StableAtlasTransversal object object
  CompositeStableAtlasTransversal
    :: StableAtlasTransversal middle target
    -> StableAtlasTransversal source middle
    -> StableAtlasTransversal source target

{-@ predicate StableCoalitionValid A E = coalitionElementValid A E
      && coalitionElementSource E == originPageElement (atlasPageElements A) @-}

type role StableTransversalAction nominal nominal nominal nominal nominal nominal nominal nominal nominal nominal
{-@ data StableTransversalAction sa ss sd so sf ta ts td to tf = StableTransversalAction
      { stableActionSource :: Atlas sa ss sd so sf
      , stableActionTarget :: Atlas ta ts td to tf
      , stableActionTransversal :: AtlasTransversal (AtlasObject sa ss sd) (AtlasObject ta ts td)
      , stableActionOrigin :: {proof:() |
           stableOriginPreserved stableActionSource stableActionTarget stableActionTransversal}
      , stableActionInsertion :: {insertion:DomanialInsertion
           ({value:CoalitionData sa ss sd | StableCoalitionValid stableActionSource value})
           (CoalitionData ta ts td) |
           applyInsertion insertion == mapCoalitionElement stableActionSource stableActionTransversal}
      } @-}
data StableTransversalAction sa ss sd so sf ta ts td to tf = StableTransversalAction
  { stableActionSource :: Atlas sa ss sd so sf
  , stableActionTarget :: Atlas ta ts td to tf
  , stableActionTransversal :: AtlasTransversal (AtlasObject sa ss sd) (AtlasObject ta ts td)
  , stableActionOrigin :: ()
  , stableActionInsertion :: DomanialInsertion (CoalitionData sa ss sd) (CoalitionData ta ts td)
  }

-- | Restrict an Atlas transversal to arrows sending extent to extent, with
-- an executable coalition inverse and its checked left-inverse law.
{-@
stableAtlasTransversal
  :: sourceAtlas:Atlas
       sourceAtlasScope sourceScope sourceCellData sourceOrigin sourceFinal
  -> targetAtlas:Atlas
       targetAtlasScope targetScope targetCellData targetOrigin targetFinal
  -> transversal:AtlasTransversal
       (AtlasObject sourceAtlasScope sourceScope sourceCellData)
       (AtlasObject targetAtlasScope targetScope targetCellData)
  -> { proof:() | stableOriginPreserved sourceAtlas targetAtlas transversal }
  -> backward:(CoalitionData targetAtlasScope targetScope targetCellData
       -> Maybe ({value:CoalitionData sourceAtlasScope sourceScope sourceCellData |
            StableCoalitionValid sourceAtlas value}))
  -> (value:{CoalitionData sourceAtlasScope sourceScope sourceCellData |
            StableCoalitionValid sourceAtlas value}
       -> { proof:() | backward (mapCoalitionElement sourceAtlas transversal value) == Just value })
  -> StableAtlasTransversal
       (AtlasObject sourceAtlasScope sourceScope sourceCellData)
       (AtlasObject targetAtlasScope targetScope targetCellData)
@-}
-- ALIGN: ATLAS-STABLE-INTERPRETATION.
-- ALIGN: ATLAS-STABLE-CARRIER-CONSTRUCTOR.
-- ALIGN: ATLAS-STABLE-CARRIER-FORWARD.
-- ALIGN: ATLAS-STABLE-CARRIER-INVERSE.
-- ALIGN: ATLAS-STABLE-SOURCE-PACKAGE.
stableAtlasTransversal
  :: Atlas sourceAtlasScope sourceScope sourceCellData sourceOrigin sourceFinal
  -> Atlas targetAtlasScope targetScope targetCellData targetOrigin targetFinal
  -> AtlasTransversal
       (AtlasObject sourceAtlasScope sourceScope sourceCellData)
       (AtlasObject targetAtlasScope targetScope targetCellData)
  -> ()
  -> (CoalitionData targetAtlasScope targetScope targetCellData
       -> Maybe (CoalitionData sourceAtlasScope sourceScope sourceCellData))
  -> (CoalitionData sourceAtlasScope sourceScope sourceCellData -> ())
  -> StableAtlasTransversal
       (AtlasObject sourceAtlasScope sourceScope sourceCellData)
       (AtlasObject targetAtlasScope targetScope targetCellData)
stableAtlasTransversal sourceAtlas targetAtlas transversal proof backward leftInverse =
  PrimitiveStableAtlasTransversal
    (StableTransversalAction sourceAtlas targetAtlas transversal
      (checkedStableOrigin sourceAtlas targetAtlas transversal proof)
      (coalitionCounitInsertion (coalitionElementValid sourceAtlas) coalitionElementSource
        (originPageElement (atlasPageElements sourceAtlas))
        (mapCoalitionElement sourceAtlas transversal) backward leftInverse))

-- | Primitive inverses are supplied with their exact-image law; identities and
-- composites use the ordinary checked insertion operations.
stableAtlasTransversalCoalitionInsertion
  :: StableAtlasTransversal source target
  -> DomanialInsertion (CoalitionElement source) (CoalitionElement target)
stableAtlasTransversalCoalitionInsertion
    (PrimitiveStableAtlasTransversal action) = stableActionInsertion action
stableAtlasTransversalCoalitionInsertion IdentityStableAtlasTransversal = identityInsertion
stableAtlasTransversalCoalitionInsertion (CompositeStableAtlasTransversal second first) =
  composeInsertions
    (stableAtlasTransversalCoalitionInsertion second)
    (stableAtlasTransversalCoalitionInsertion first)

-- | Keep a canonical value paired with the Atlas that certifies it while
-- transporting through the identity constructor's type equality.
type role CoalitionPreimageData nominal nominal nominal nominal nominal
{-@ data CoalitionPreimageData a s d o f = CoalitionPreimageData
      { coalitionPreimageOwner :: Atlas a s d o f
      , coalitionPreimageValue :: {value:CoalitionData a s d |
           StableCoalitionValid coalitionPreimageOwner value}
      } @-}
data CoalitionPreimageData a s d o f = CoalitionPreimageData
  { coalitionPreimageOwner :: Atlas a s d o f
  , coalitionPreimageValue :: CoalitionData a s d
  }

type role CoalitionInverseData nominal nominal nominal nominal nominal nominal nominal nominal
{-@ data CoalitionInverseData a s d o f ta ts td = CoalitionInverseData
      { coalitionInverseOwner :: Atlas a s d o f
      , coalitionInverseFunction :: CoalitionData ta ts td
          -> Maybe ({source:CoalitionData a s d | StableCoalitionValid coalitionInverseOwner source})
      } @-}
data CoalitionInverseData a s d o f ta ts td = CoalitionInverseData
  { coalitionInverseOwner :: Atlas a s d o f
  , coalitionInverseFunction :: CoalitionData ta ts td -> Maybe (CoalitionData a s d)
  }

type role StableCoalitionInverse nominal nominal
data StableCoalitionInverse source target where
  UnchangedCoalitionInverse :: StableCoalitionInverse object object
  RestoringCoalitionInverse :: CoalitionInverseData a s d o f ta ts td
    -> StableCoalitionInverse (AtlasObject a s d) (AtlasObject ta ts td)

{-@ composeCoalitionInverseData :: first:CoalitionInverseData a s d o f ma ms md
      -> second:(CoalitionData ta ts td -> Maybe (CoalitionData ma ms md))
      -> {result:CoalitionInverseData a s d o f ta ts td |
           coalitionInverseOwner result == coalitionInverseOwner first
           && coalitionInverseFunction result == composePartialInverses (coalitionInverseFunction first) second} @-}
composeCoalitionInverseData :: CoalitionInverseData a s d o f ma ms md
  -> (CoalitionData ta ts td -> Maybe (CoalitionData ma ms md))
  -> CoalitionInverseData a s d o f ta ts td
composeCoalitionInverseData (CoalitionInverseData owner first) second =
  CoalitionInverseData owner (composePartialInverses first second)

{-@ withCoalitionPreimageData :: image:CoalitionPreimageData a s d o f
      -> (owner:Atlas a s d o f
            -> {value:CoalitionData a s d | StableCoalitionValid owner value}
            -> result)
      -> result @-}
withCoalitionPreimageData :: CoalitionPreimageData a s d o f
  -> (Atlas a s d o f -> CoalitionData a s d -> result) -> result
withCoalitionPreimageData image usePreimage =
  usePreimage (coalitionPreimageOwner image) (coalitionPreimageValue image)

{-@ measure stableAtlasTransversalSize @-}
{-@ stableAtlasTransversalSize :: StableAtlasTransversal source target
      -> {size:Integer | size > 0} @-}
stableAtlasTransversalSize :: StableAtlasTransversal source target -> Integer
stableAtlasTransversalSize IdentityStableAtlasTransversal = 1
stableAtlasTransversalSize (PrimitiveStableAtlasTransversal _) = 1
stableAtlasTransversalSize (CompositeStableAtlasTransversal second first) =
  1 + stableAtlasTransversalSize second + stableAtlasTransversalSize first

-- ALIGN: ATLAS-STABLE-OWNED-INVERSE.
{-@ stableCoalitionInverse :: arrow:StableAtlasTransversal source target
      -> StableCoalitionInverse source target
      / [stableAtlasTransversalSize arrow] @-}
stableCoalitionInverse :: StableAtlasTransversal source target -> StableCoalitionInverse source target
stableCoalitionInverse IdentityStableAtlasTransversal = UnchangedCoalitionInverse
stableCoalitionInverse (PrimitiveStableAtlasTransversal action) =
  RestoringCoalitionInverse
    (CoalitionInverseData (stableActionSource action) (preimage (stableActionInsertion action)))
stableCoalitionInverse (CompositeStableAtlasTransversal second first) =
  composeStableCoalitionInverses (stableCoalitionInverse second) (stableCoalitionInverse first)

-- ALIGN: ATLAS-STABLE-OWNED-INVERSE-COMPOSITION.
composeStableCoalitionInverses :: StableCoalitionInverse middle target
  -> StableCoalitionInverse source middle -> StableCoalitionInverse source target
composeStableCoalitionInverses UnchangedCoalitionInverse first = first
composeStableCoalitionInverses (RestoringCoalitionInverse second) first =
  case first of
    UnchangedCoalitionInverse -> RestoringCoalitionInverse second
    RestoringCoalitionInverse source ->
      RestoringCoalitionInverse
        (composeCoalitionInverseData source (coalitionInverseFunction second))

{-@ withCoalitionInverseData :: inverse:CoalitionInverseData a s d o f ta ts td
      -> CoalitionData ta ts td
      -> (owner:Atlas a s d o f
            -> {source:CoalitionData a s d | StableCoalitionValid owner source}
            -> result)
      -> Maybe result @-}
withCoalitionInverseData :: CoalitionInverseData a s d o f ta ts td -> CoalitionData ta ts td
  -> (Atlas a s d o f -> CoalitionData a s d -> result) -> Maybe result
withCoalitionInverseData inverse target usePreimage =
  case coalitionInverseFunction inverse target of
    Nothing -> Nothing
    Just source -> Just (usePreimage (coalitionInverseOwner inverse) source)

-- | Inspect a successful inverse with the actual source owner. Identity keeps
-- the caller's target owner; a primitive inverse supplies its stored source.
-- ALIGN: ATLAS-STABLE-OWNED-PREIMAGE-ELIMINATION.
{-@ withStableAtlasTransversalCoalitionPreimage
      :: targetOwner:Atlas ta ts td to tf
      -> StableAtlasTransversal (AtlasObject sa ss sd) (AtlasObject ta ts td)
      -> target:{CoalitionData ta ts td | StableCoalitionValid targetOwner target}
      -> (forall o f. sourceOwner:Atlas sa ss sd o f
            -> {source:CoalitionData sa ss sd | StableCoalitionValid sourceOwner source}
            -> result)
      -> Maybe result @-}
withStableAtlasTransversalCoalitionPreimage
  :: Atlas ta ts td to tf
  -> StableAtlasTransversal (AtlasObject sa ss sd) (AtlasObject ta ts td)
  -> CoalitionData ta ts td
  -> (forall o f. Atlas sa ss sd o f -> CoalitionData sa ss sd -> result)
  -> Maybe result
withStableAtlasTransversalCoalitionPreimage targetOwner arrow =
  let inverse = stableCoalitionInverse arrow
  in \target usePreimage ->
    let targetImage = CoalitionPreimageData targetOwner target
    in case inverse of
      UnchangedCoalitionInverse -> Just (withCoalitionPreimageData targetImage usePreimage)
      RestoringCoalitionInverse restored -> withCoalitionInverseData restored target usePreimage

-- | Forget the extent restriction while retaining every transversal law.
stableAtlasTransversalTransversal
  :: StableAtlasTransversal source target
  -> AtlasTransversal source target
stableAtlasTransversalTransversal
  (PrimitiveStableAtlasTransversal action) = stableActionTransversal action
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

-- | Recover the source Atlas witness from the target witness carried by a
-- value.  This is the object action needed when a presheaf is restricted
-- along the wide inclusion of stable Atlas transversals.
stableAtlasTransversalSourceWitness
  :: StableAtlasTransversal source target
  -> AtlasWitness target
  -> AtlasWitness source
stableAtlasTransversalSourceWitness
    (PrimitiveStableAtlasTransversal action) _ =
  atlasWitness (stableActionSource action)
stableAtlasTransversalSourceWitness IdentityStableAtlasTransversal target =
  target
stableAtlasTransversalSourceWitness
    (CompositeStableAtlasTransversal second first) target =
  stableAtlasTransversalSourceWitness first
    (stableAtlasTransversalSourceWitness second target)

-- | Invoke the primitive or structurally derived extent-preservation proof.
-- ALIGN: ATLAS-STABLE-EXTENT.
stableAtlasTransversalPreservesExtent
  :: StableAtlasTransversal source target
  -> ()
stableAtlasTransversalPreservesExtent
  (PrimitiveStableAtlasTransversal action) = stableActionOrigin action
stableAtlasTransversalPreservesExtent IdentityStableAtlasTransversal = ()
stableAtlasTransversalPreservesExtent
  (CompositeStableAtlasTransversal second first) =
    stableAtlasTransversalPreservesExtent first `seq`
      stableAtlasTransversalPreservesExtent second

-- ALIGN: ATLAS-STABLE-IDENTITY.
identityStableAtlasTransversal :: StableAtlasTransversal object object
identityStableAtlasTransversal = IdentityStableAtlasTransversal

-- ALIGN: ATLAS-STABLE-COMPOSITION.
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
  -> AtlasCoveredPageElement source
  -> AtlasCoveredPageElement target
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

-- ALIGN: ATLAS-STABLE-COVERED.
mapStableAtlasTransversalCoveredPageElement
  :: StableAtlasTransversal source target
  -> AtlasCoveredPageElement source
  -> AtlasCoveredPageElement target
mapStableAtlasTransversalCoveredPageElement stable =
  mapAtlasTransversalCoveredPageElement (stableAtlasTransversalTransversal stable)
