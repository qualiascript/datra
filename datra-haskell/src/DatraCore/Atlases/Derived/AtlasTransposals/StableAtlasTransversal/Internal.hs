{-# LANGUAGE CPP #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE RoleAnnotations #-}
{-# LANGUAGE TypeFamilies #-}
{-# OPTIONS_GHC -Wno-unused-imports #-}
#include "../../../../LiquidPlugin.h"
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--higherorder" @-}
{-@ LIQUID "--ple" @-}
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
  , stableCoalitionSourceOwner, stableCoalitionTargetOwner, stableCoalitionOwnersEmpty
  , ScopedInsertionData, stableCoalitionInsertionData
  , scopedInsertionSource, scopedInsertionTarget, scopedInsertionValue
  , scopedInsertionForwardCodes, scopedInsertionInverseCodes
  , scopedInsertionForwardObservation, scopedInsertionInverseObservation
  , coalitionCodeExtensionality, coalitionMaybeCode, coalitionIdentityCode
  , stableAtlasTransversalSourceWitness
  , withStableAtlasTransversalCoalitionInsertion
  , withStableAtlasTransversalCoalitionPreimage
  , stableAtlasTransversalPreservesExtent
  , identityStableAtlasTransversal
  , composeStableAtlasTransversals
  , normalizedForwardCodes, normalizedInverseCodes
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
import Atlas.Witness (AtlasOwner, AtlasObjectAtlasScope, atlasOwner)
import AtlasTransposal.Element (TransposalElementData)
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
  , coalitionElementValid, coalitionElementSource, coalitionOwnersAgree, coalitionCounitInsertion
  , withMappedCoalitionAction, coalitionUnrank, coalitionElementCode, coalitionRankRoundTrip )
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
stableElementPage :: TransposalElementData a s d -> Natural
stableElementPage element =
  withAtlasTransposalElement element pageElementPage

{-@ reflect stableElementPosition @-}
stableElementPosition :: TransposalElementData a s d -> Ordinal
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
    :: StableTransversalAction sa ss sd so sf ta ts td to tf mo mf
    -> StableAtlasTransversal (AtlasObject sa ss sd) (AtlasObject ta ts td)
  IdentityStableAtlasTransversal
    :: StableAtlasTransversal object object
  CompositeStableAtlasTransversal
    :: StableAtlasTransversal middle target
    -> StableAtlasTransversal source middle
    -> StableAtlasTransversal source target

{-@ predicate StableCoalitionValid A E = coalitionElementValid A E
      && coalitionElementSource E == originPageElement (atlasPageElements A) @-}

type role StableTransversalAction nominal nominal nominal nominal nominal nominal nominal nominal nominal nominal nominal nominal
{-@ data StableTransversalAction sa ss sd so sf ta ts td to tf mo mf = StableTransversalAction
      { stableActionSource :: Atlas sa ss sd so sf
      , stableActionTarget :: Atlas ta ts td to tf
      , stableActionTransversal :: AtlasTransversal (AtlasObject sa ss sd) (AtlasObject ta ts td)
      , stableActionOrigin :: {proof:() |
           stableOriginPreserved stableActionSource stableActionTarget stableActionTransversal}
      , stableActionMappedTarget :: Atlas ta ts td mo mf
      , stableActionInsertion :: {insertion:DomanialInsertion
           ({value:CoalitionData sa ss sd | StableCoalitionValid stableActionSource value})
           (CoalitionData ta ts td) |
           applyInsertion insertion == mapCoalitionElement stableActionSource stableActionTransversal}
      , stableActionForwardValid :: value:{CoalitionData sa ss sd | StableCoalitionValid stableActionSource value}
          -> {StableCoalitionValid stableActionMappedTarget (applyInsertion stableActionInsertion value)}
      } @-}
data StableTransversalAction sa ss sd so sf ta ts td to tf mo mf = StableTransversalAction
  { stableActionSource :: Atlas sa ss sd so sf
  , stableActionTarget :: Atlas ta ts td to tf
  , stableActionTransversal :: AtlasTransversal (AtlasObject sa ss sd) (AtlasObject ta ts td)
  , stableActionOrigin :: ()
  , stableActionMappedTarget :: Atlas ta ts td mo mf
  , stableActionInsertion :: DomanialInsertion (CoalitionData sa ss sd) (CoalitionData ta ts td)
  , stableActionForwardValid :: CoalitionData sa ss sd -> ()
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
  withMappedCoalitionAction sourceAtlas transversal
    (retainStableCoalitionTarget sourceAtlas targetAtlas transversal proof backward leftInverse)

-- | Retain the canonical mapper's actual target owner while leaving the supplied
-- inverse defined on every raw target, including inputs outside the image.
-- ALIGN: ATLAS-STABLE-TARGET-PACKAGE.
{-@ retainStableCoalitionTarget
      :: sourceOwner:Atlas sa ss sd so sf
      -> targetOwner:Atlas ta ts td to tf
      -> transversal:AtlasTransversal (AtlasObject sa ss sd) (AtlasObject ta ts td)
      -> {proof:() | stableOriginPreserved sourceOwner targetOwner transversal}
      -> backward:(CoalitionData ta ts td
           -> Maybe ({value:CoalitionData sa ss sd | StableCoalitionValid sourceOwner value}))
      -> (value:{CoalitionData sa ss sd | StableCoalitionValid sourceOwner value}
           -> {backward (mapCoalitionElement sourceOwner transversal value) == Just value})
      -> mappedOwner:Atlas ta ts td mo mf
      -> ({value:CoalitionData sa ss sd | StableCoalitionValid sourceOwner value}
           -> {image:CoalitionData ta ts td | StableCoalitionValid mappedOwner image
                && image == mapCoalitionElement sourceOwner transversal value})
      -> StableAtlasTransversal (AtlasObject sa ss sd) (AtlasObject ta ts td) @-}
retainStableCoalitionTarget
  :: Atlas sa ss sd so sf -> Atlas ta ts td to tf
  -> AtlasTransversal (AtlasObject sa ss sd) (AtlasObject ta ts td)
  -> () -> (CoalitionData ta ts td -> Maybe (CoalitionData sa ss sd))
  -> (CoalitionData sa ss sd -> ())
  -> Atlas ta ts td mo mf -> (CoalitionData sa ss sd -> CoalitionData ta ts td)
  -> StableAtlasTransversal (AtlasObject sa ss sd) (AtlasObject ta ts td)
retainStableCoalitionTarget sourceOwner targetOwner transversal proof backward leftInverse mappedOwner forward =
  PrimitiveStableAtlasTransversal
    (StableTransversalAction sourceOwner targetOwner transversal
      (checkedStableOrigin sourceOwner targetOwner transversal proof)
      mappedOwner
      (coalitionCounitInsertion (coalitionElementValid sourceOwner) coalitionElementSource
        (originPageElement (atlasPageElements sourceOwner))
        (mapCoalitionElement sourceOwner transversal) backward leftInverse)
      (\source -> forward source `seq` ()))


-- | Feed a mapped canonical coalition into the next action's actual source domain.
-- ALIGN: ATLAS-STABLE-NEXT-SOURCE-DOMAIN.
{-@ stableActionNextSourceValid
      :: first:StableTransversalAction sa ss sd so sf ma ms md mo mf ro rf
      -> second:{StableTransversalAction ma ms md mo2 mf2 ta ts td to tf no nf |
           atlasOwner (stableActionSource second) == atlasOwner (stableActionMappedTarget first)}
      -> source:{CoalitionData sa ss sd | StableCoalitionValid (stableActionSource first) source}
      -> {StableCoalitionValid (stableActionSource second) (applyInsertion (stableActionInsertion first) source)} @-}
stableActionNextSourceValid
  :: StableTransversalAction sa ss sd so sf ma ms md mo mf ro rf
  -> StableTransversalAction ma ms md mo2 mf2 ta ts td to tf no nf
  -> CoalitionData sa ss sd -> ()
stableActionNextSourceValid first second source =
  stableActionForwardValid first source `seq`
    coalitionOwnersAgree (stableActionMappedTarget first) (stableActionSource second)
      (applyInsertion (stableActionInsertion first) source)

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
{-@ identityStableAtlasTransversal :: {arrow:StableAtlasTransversal object object |
      stableCoalitionSourceOwner arrow == Nothing
      && stableCoalitionTargetOwner arrow == Nothing
      && stableCoalitionOwnersCompatible arrow
      && stableCoalitionForwardCodes arrow == coalitionIdentityCode
      && stableCoalitionInverseCodes arrow == coalitionIdentityCode} @-}
identityStableAtlasTransversal :: StableAtlasTransversal object object
identityStableAtlasTransversal = IdentityStableAtlasTransversal

-- ALIGN: ATLAS-STABLE-COMPOSITION.
-- ALIGN: ATLAS-STABLE-NORMALIZED-OWNERS.
{-@ reflect composeStableAtlasTransversals @-}
{-@ composeStableAtlasTransversals :: second:StableAtlasTransversal middle target
      -> first:StableAtlasTransversal source middle
      -> {result:StableAtlasTransversal source target |
           stableCoalitionSourceOwner result == stableCoalitionSourceOwner (CompositeStableAtlasTransversal second first)
           && stableCoalitionTargetOwner result == stableCoalitionTargetOwner (CompositeStableAtlasTransversal second first)
           && (stableCoalitionOwnersCompatible result <=> stableCoalitionOwnersCompatible (CompositeStableAtlasTransversal second first))}
      / [stableAtlasTransversalSize first] @-}
composeStableAtlasTransversals
  :: StableAtlasTransversal middle target
  -> StableAtlasTransversal source middle
  -> StableAtlasTransversal source target
composeStableAtlasTransversals second first =
  normalizationResult (normalizedStableData second first)

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

{-@ reflect stableCoalitionSourceOwner @-}
stableCoalitionSourceOwner :: StableAtlasTransversal source target -> Maybe AtlasOwner
stableCoalitionSourceOwner (PrimitiveStableAtlasTransversal action) = Just (atlasOwner (stableActionSource action))
stableCoalitionSourceOwner IdentityStableAtlasTransversal = Nothing
stableCoalitionSourceOwner (CompositeStableAtlasTransversal second first) =
  case stableCoalitionSourceOwner first of
    Nothing -> stableCoalitionSourceOwner second
    Just owner -> Just owner

{-@ reflect stableCoalitionTargetOwner @-}
stableCoalitionTargetOwner :: StableAtlasTransversal source target -> Maybe AtlasOwner
stableCoalitionTargetOwner (PrimitiveStableAtlasTransversal action) = Just (atlasOwner (stableActionMappedTarget action))
stableCoalitionTargetOwner IdentityStableAtlasTransversal = Nothing
stableCoalitionTargetOwner (CompositeStableAtlasTransversal second first) =
  case stableCoalitionTargetOwner second of
    Nothing -> stableCoalitionTargetOwner first
    Just owner -> Just owner

{-@ measure stableCoalitionOwnersCompatible :: StableAtlasTransversal source target -> Bool
      stableCoalitionOwnersCompatible (PrimitiveStableAtlasTransversal action) = true
      stableCoalitionOwnersCompatible (IdentityStableAtlasTransversal) = true
      stableCoalitionOwnersCompatible (CompositeStableAtlasTransversal second first) =
        stableCoalitionOwnersCompatible first && stableCoalitionOwnersCompatible second
        && (stableCoalitionTargetOwner first == Nothing || stableCoalitionSourceOwner second == Nothing
          || stableCoalitionTargetOwner first == stableCoalitionSourceOwner second)
  @-}

{-@ stableCoalitionOwnersEmpty :: arrow:StableAtlasTransversal source target
      -> {(stableCoalitionSourceOwner arrow == Nothing) <=> (stableCoalitionTargetOwner arrow == Nothing)} @-}
stableCoalitionOwnersEmpty :: StableAtlasTransversal source target -> ()
stableCoalitionOwnersEmpty (PrimitiveStableAtlasTransversal _) = ()
stableCoalitionOwnersEmpty IdentityStableAtlasTransversal = ()
stableCoalitionOwnersEmpty (CompositeStableAtlasTransversal second first) =
  stableCoalitionOwnersEmpty first `seq` stableCoalitionOwnersEmpty second `seq`
    case (stableCoalitionSourceOwner first, stableCoalitionTargetOwner second) of
      (Nothing, Nothing) -> ()
      (Nothing, Just _) -> ()
      (Just _, Nothing) -> ()
      (Just _, Just _) -> ()

{-@ stableCoalitionOwnersAssociativity :: third:StableAtlasTransversal next target
      -> second:StableAtlasTransversal middle next -> first:StableAtlasTransversal source middle
      -> {stableCoalitionSourceOwner (CompositeStableAtlasTransversal third (CompositeStableAtlasTransversal second first))
             == stableCoalitionSourceOwner (CompositeStableAtlasTransversal (CompositeStableAtlasTransversal third second) first)
           && stableCoalitionTargetOwner (CompositeStableAtlasTransversal third (CompositeStableAtlasTransversal second first))
             == stableCoalitionTargetOwner (CompositeStableAtlasTransversal (CompositeStableAtlasTransversal third second) first)
           && (stableCoalitionOwnersCompatible (CompositeStableAtlasTransversal third (CompositeStableAtlasTransversal second first))
             <=> stableCoalitionOwnersCompatible (CompositeStableAtlasTransversal (CompositeStableAtlasTransversal third second) first))} @-}
stableCoalitionOwnersAssociativity :: StableAtlasTransversal next target -> StableAtlasTransversal middle next
  -> StableAtlasTransversal source middle -> ()
stableCoalitionOwnersAssociativity third second first =
  stableCompatibleAssociativity third second first `seq`
  case (stableCoalitionSourceOwner first, stableCoalitionTargetOwner third) of
    (Nothing, Nothing) -> ()
    (Nothing, Just _) -> ()
    (Just _, Nothing) -> ()
    (Just _, Just _) -> ()

{-@ stableCompatibleAssociativity :: third:StableAtlasTransversal next target
      -> second:StableAtlasTransversal middle next -> first:StableAtlasTransversal source middle
      -> {stableCoalitionOwnersCompatible (CompositeStableAtlasTransversal third (CompositeStableAtlasTransversal second first))
           <=> stableCoalitionOwnersCompatible (CompositeStableAtlasTransversal (CompositeStableAtlasTransversal third second) first)} @-}
stableCompatibleAssociativity :: StableAtlasTransversal next target -> StableAtlasTransversal middle next -> StableAtlasTransversal source middle -> ()
stableCompatibleAssociativity _ second _ =
  stableCoalitionOwnersEmpty second `seq`
  case (stableCoalitionSourceOwner second, stableCoalitionTargetOwner second) of
    (Nothing, Nothing) -> ()
    (Nothing, Just _) -> ()
    (Just _, Nothing) -> ()
    (Just _, Just _) -> ()

type role ScopedInsertionPayload nominal
{-@ data variance ScopedInsertionPayload invariant invariant @-}
{-@ data ScopedInsertionPayload atlas <owns :: atlas -> Bool> = ScopedInsertionPayload
      { scopedInsertionPayload :: atlas<owns> } @-}
data ScopedInsertionPayload atlas = ScopedInsertionPayload
  { scopedInsertionPayload :: atlas }

{-@ withScopedInsertionPayload :: forall <owns :: owner -> Bool>.
      ScopedInsertionPayload <owns> owner -> (owner<owns> -> result) -> result @-}
withScopedInsertionPayload :: ScopedInsertionPayload owner -> (owner -> result) -> result
withScopedInsertionPayload (ScopedInsertionPayload owner) useOwner = useOwner owner



type role ScopedInsertionData nominal nominal nominal nominal nominal nominal nominal nominal nominal nominal
-- | Keep owning domains and exact scalar observations together across index changes.
{-@ data ScopedInsertionData sa ss sd so sf ta ts td to tf = ScopedInsertionData
      { scopedInsertionSource :: Atlas sa ss sd so sf
      , scopedInsertionTarget :: Atlas ta ts td to tf
      , scopedInsertionValue :: DomanialInsertion
          ({v:CoalitionData sa ss sd | StableCoalitionValid scopedInsertionSource v})
          ({v:CoalitionData ta ts td | StableCoalitionValid scopedInsertionTarget v})
      , scopedInsertionForwardCodes :: Natural -> Maybe Natural
      , scopedInsertionInverseCodes :: Natural -> Maybe Natural
      , scopedInsertionForwardObservation ::
          source:{CoalitionData sa ss sd | StableCoalitionValid scopedInsertionSource source}
          -> {scopedInsertionForwardCodes (coalitionElementCode source)
               == Just (coalitionElementCode (applyInsertion scopedInsertionValue source))}
      , scopedInsertionInverseObservation ::
          target:{CoalitionData ta ts td | StableCoalitionValid scopedInsertionTarget target}
          -> {scopedInsertionInverseCodes (coalitionElementCode target)
               == coalitionMaybeCode (preimage scopedInsertionValue target)}
      } @-}
data ScopedInsertionData sa ss sd so sf ta ts td to tf = ScopedInsertionData
  { scopedInsertionSource :: Atlas sa ss sd so sf
  , scopedInsertionTarget :: Atlas ta ts td to tf
  , scopedInsertionValue :: DomanialInsertion (CoalitionData sa ss sd) (CoalitionData ta ts td)
  , scopedInsertionForwardCodes :: Natural -> Maybe Natural
  , scopedInsertionInverseCodes :: Natural -> Maybe Natural
  , scopedInsertionForwardObservation :: CoalitionData sa ss sd -> ()
  , scopedInsertionInverseObservation :: CoalitionData ta ts td -> () }

{-@ retainScopedInsertion :: sourceName:AtlasOwner -> targetName:AtlasOwner
      -> forwardCodes:(Natural -> Maybe Natural) -> inverseCodes:(Natural -> Maybe Natural)
      -> packet:{ScopedInsertionData sa ss sd so sf ta ts td to tf |
           atlasOwner (scopedInsertionSource packet) == sourceName
           && atlasOwner (scopedInsertionTarget packet) == targetName
           && scopedInsertionForwardCodes packet == forwardCodes
           && scopedInsertionInverseCodes packet == inverseCodes}
      -> ScopedInsertionPayload <{\v -> atlasOwner (scopedInsertionSource v) == sourceName
           && atlasOwner (scopedInsertionTarget v) == targetName
           && scopedInsertionForwardCodes v == forwardCodes
           && scopedInsertionInverseCodes v == inverseCodes}>
           (ScopedInsertionData sa ss sd so sf ta ts td to tf) @-}
retainScopedInsertion :: AtlasOwner -> AtlasOwner -> (Natural -> Maybe Natural) -> (Natural -> Maybe Natural)
  -> ScopedInsertionData sa ss sd so sf ta ts td to tf
  -> ScopedInsertionPayload (ScopedInsertionData sa ss sd so sf ta ts td to tf)
retainScopedInsertion _ _ _ _ packet = ScopedInsertionPayload packet

{-@ retargetScopedInsertion :: sourceOwner:Atlas sa ss sd so sf
      -> actualTarget:Atlas ta ts td ao af
      -> targetOwner:{Atlas ta ts td to tf | atlasOwner targetOwner == atlasOwner actualTarget}
      -> insertion:DomanialInsertion ({v:CoalitionData sa ss sd | StableCoalitionValid sourceOwner v})
           ({v:CoalitionData ta ts td | StableCoalitionValid actualTarget v})
      -> {result:DomanialInsertion ({v:CoalitionData sa ss sd | StableCoalitionValid sourceOwner v})
           ({v:CoalitionData ta ts td | StableCoalitionValid targetOwner v}) | result == insertion} @-}
retargetScopedInsertion :: Atlas sa ss sd so sf -> Atlas ta ts td ao af -> Atlas ta ts td to tf
  -> DomanialInsertion (CoalitionData sa ss sd) (CoalitionData ta ts td)
  -> DomanialInsertion (CoalitionData sa ss sd) (CoalitionData ta ts td)
retargetScopedInsertion _ _ _ insertion = insertion

{-@ scopedCoalitionInsertion :: sourceAccepts:(source -> Bool)
      -> sourceKey:(source -> SomePageElement ss) -> sourceOrigin:SomePageElement ss
      -> targetAccepts:(target -> Bool)
      -> targetKey:(target -> SomePageElement ts) -> targetOrigin:SomePageElement ts
      -> forward:({x:source | sourceAccepts x && sourceKey x == sourceOrigin}
           -> {y:target | targetAccepts y && targetKey y == targetOrigin})
      -> backward:({y:target | targetAccepts y && targetKey y == targetOrigin}
           -> Maybe ({x:source | sourceAccepts x && sourceKey x == sourceOrigin}))
      -> (x:{source | sourceAccepts x && sourceKey x == sourceOrigin}
           -> {backward (forward x) == Just x})
      -> {mapping:DomanialInsertion
           ({x:source | sourceAccepts x && sourceKey x == sourceOrigin})
           ({y:target | targetAccepts y && targetKey y == targetOrigin}) |
           applyInsertion mapping == forward && preimage mapping == backward} @-}
scopedCoalitionInsertion :: (source -> Bool) -> (source -> SomePageElement ss) -> SomePageElement ss
  -> (target -> Bool) -> (target -> SomePageElement ts) -> SomePageElement ts
  -> (source -> target) -> (target -> Maybe source) -> (source -> ())
  -> DomanialInsertion source target
scopedCoalitionInsertion _ _ _ _ _ _ forward backward inverse = DomanialInsertion forward backward inverse
{-@ opaque-reflect stableActionForwardFor @-}
{-@ stableActionForwardFor :: action:StableTransversalAction sa ss sd so sf ta ts td to tf mo mf
      -> owner:{Atlas ta ts td no nf | atlasOwner owner == atlasOwner (stableActionMappedTarget action)}
      -> source:{CoalitionData sa ss sd | StableCoalitionValid (stableActionSource action) source}
      -> {target:CoalitionData ta ts td | StableCoalitionValid owner target
           && target == applyInsertion (stableActionInsertion action) source} @-}
stableActionForwardFor :: StableTransversalAction sa ss sd so sf ta ts td to tf mo mf
  -> Atlas ta ts td no nf -> CoalitionData sa ss sd -> CoalitionData ta ts td
stableActionForwardFor action owner source =
  stableActionForwardValid action source `seq`
    let target = applyInsertion (stableActionInsertion action) source
    in coalitionOwnersAgree (stableActionMappedTarget action) owner target `seq` target

{-@ stableActionForwardForRoundTrip :: action:StableTransversalAction sa ss sd so sf ta ts td to tf mo mf
      -> owner:{Atlas ta ts td no nf | atlasOwner owner == atlasOwner (stableActionMappedTarget action)}
      -> source:{CoalitionData sa ss sd | StableCoalitionValid (stableActionSource action) source}
      -> {preimage (stableActionInsertion action) (stableActionForwardFor action owner source) == Just source} @-}
stableActionForwardForRoundTrip :: StableTransversalAction sa ss sd so sf ta ts td to tf mo mf
  -> Atlas ta ts td no nf -> CoalitionData sa ss sd -> ()
stableActionForwardForRoundTrip action owner source =
  stableActionForwardFor action owner source `seq` insertionLeftInverse (stableActionInsertion action) source

{-@ stableActionInsertionFor :: action:StableTransversalAction sa ss sd so sf ta ts td to tf mo mf
      -> owner:{Atlas ta ts td no nf | atlasOwner owner == atlasOwner (stableActionMappedTarget action)}
      -> {result:DomanialInsertion
           ({source:CoalitionData sa ss sd | StableCoalitionValid (stableActionSource action) source})
           ({target:CoalitionData ta ts td | StableCoalitionValid owner target}) | applyInsertion result == stableActionForwardFor action owner && preimage result == preimage (stableActionInsertion action)} @-}
stableActionInsertionFor :: StableTransversalAction sa ss sd so sf ta ts td to tf mo mf
  -> Atlas ta ts td no nf -> DomanialInsertion (CoalitionData sa ss sd) (CoalitionData ta ts td)
stableActionInsertionFor action owner =
  scopedCoalitionInsertion
    (coalitionElementValid (stableActionSource action)) coalitionElementSource
    (originPageElement (atlasPageElements (stableActionSource action)))
    (coalitionElementValid owner) coalitionElementSource
    (originPageElement (atlasPageElements owner))
    (stableActionForwardFor action owner)
    (preimage (stableActionInsertion action)) (stableActionForwardForRoundTrip action owner)



{-@ scopedCoalitionIdentity :: owner:Atlas a s d o f
      -> {result:DomanialInsertion ({v:CoalitionData a s d | StableCoalitionValid owner v})
           ({v:CoalitionData a s d | StableCoalitionValid owner v}) | result == identityInsertion} @-}
scopedCoalitionIdentity :: Atlas a s d o f
  -> DomanialInsertion (CoalitionData a s d) (CoalitionData a s d)
scopedCoalitionIdentity owner = scopedIdentityOn
  (coalitionElementValid owner) coalitionElementSource (originPageElement (atlasPageElements owner))

{-@ scopedIdentityOn :: accepts:(value -> Bool)
      -> key:(value -> SomePageElement s) -> origin:SomePageElement s
      -> {result:DomanialInsertion ({v:value | accepts v && key v == origin})
           ({v:value | accepts v && key v == origin}) | result == identityInsertion} @-}
scopedIdentityOn :: (value -> Bool) -> (value -> SomePageElement s) -> SomePageElement s
  -> DomanialInsertion value value
scopedIdentityOn _ _ _ = identityInsertion

{-@ scopedCompositionOn :: sourceAccepts:(source -> Bool)
      -> sourceKey:(source -> SomePageElement ss) -> sourceOrigin:SomePageElement ss
      -> middleAccepts:(middle -> Bool)
      -> middleKey:(middle -> SomePageElement ms) -> middleOrigin:SomePageElement ms
      -> targetAccepts:(target -> Bool)
      -> targetKey:(target -> SomePageElement ts) -> targetOrigin:SomePageElement ts
      -> first:DomanialInsertion ({v:source | sourceAccepts v && sourceKey v == sourceOrigin})
           ({v:middle | middleAccepts v && middleKey v == middleOrigin})
      -> second:DomanialInsertion ({v:middle | middleAccepts v && middleKey v == middleOrigin})
           ({v:target | targetAccepts v && targetKey v == targetOrigin})
      -> {result:DomanialInsertion ({v:source | sourceAccepts v && sourceKey v == sourceOrigin})
           ({v:target | targetAccepts v && targetKey v == targetOrigin}) | result == composeInsertions second first} @-}
scopedCompositionOn :: (source -> Bool) -> (source -> SomePageElement ss) -> SomePageElement ss
  -> (middle -> Bool) -> (middle -> SomePageElement ms) -> SomePageElement ms
  -> (target -> Bool) -> (target -> SomePageElement ts) -> SomePageElement ts
  -> DomanialInsertion source middle -> DomanialInsertion middle target
  -> DomanialInsertion source target
scopedCompositionOn _ _ _ _ _ _ _ _ _ first second = composeInsertions second first

{-@ composeScopedCoalitionInsertions :: sourceOwner:Atlas sa ss sd so sf
      -> middleOwner:Atlas ma ms md mo mf -> targetOwner:Atlas ta ts td to tf
      -> first:DomanialInsertion ({v:CoalitionData sa ss sd | StableCoalitionValid sourceOwner v})
           ({v:CoalitionData ma ms md | StableCoalitionValid middleOwner v})
      -> second:DomanialInsertion ({v:CoalitionData ma ms md | StableCoalitionValid middleOwner v})
           ({v:CoalitionData ta ts td | StableCoalitionValid targetOwner v})
      -> {result:DomanialInsertion ({v:CoalitionData sa ss sd | StableCoalitionValid sourceOwner v})
           ({v:CoalitionData ta ts td | StableCoalitionValid targetOwner v}) | result == composeInsertions second first} @-}
composeScopedCoalitionInsertions :: Atlas sa ss sd so sf -> Atlas ma ms md mo mf -> Atlas ta ts td to tf
  -> DomanialInsertion (CoalitionData sa ss sd) (CoalitionData ma ms md)
  -> DomanialInsertion (CoalitionData ma ms md) (CoalitionData ta ts td)
  -> DomanialInsertion (CoalitionData sa ss sd) (CoalitionData ta ts td)
composeScopedCoalitionInsertions sourceOwner middleOwner targetOwner =
  scopedCompositionOn
    (coalitionElementValid sourceOwner) coalitionElementSource (originPageElement (atlasPageElements sourceOwner))
    (coalitionElementValid middleOwner) coalitionElementSource (originPageElement (atlasPageElements middleOwner))
    (coalitionElementValid targetOwner) coalitionElementSource (originPageElement (atlasPageElements targetOwner))

-- | Interpret a compatible stable tree on its canonical source and requested target.
-- The callback receives the actual source owner, including through identities.
-- ALIGN: ATLAS-STABLE-SCOPED-INSERTION.
{-@ withStableAtlasTransversalCoalitionInsertion
      :: targetOwner:Atlas (AtlasObjectAtlasScope target) (AtlasObjectPaginationScope target) (AtlasObjectCellData target) to tf
      -> arrow:{StableAtlasTransversal source target |
           stableCoalitionOwnersCompatible arrow
           && (stableCoalitionTargetOwner arrow == Nothing
                || stableCoalitionTargetOwner arrow == Just (atlasOwner targetOwner))}
      -> (forall so sf. sourceOwner:{Atlas (AtlasObjectAtlasScope source) (AtlasObjectPaginationScope source) (AtlasObjectCellData source) so sf |
            stableCoalitionSourceOwner arrow == Just (atlasOwner sourceOwner)
            || (stableCoalitionSourceOwner arrow == Nothing && atlasOwner sourceOwner == atlasOwner targetOwner)}
           -> DomanialInsertion
                ({source:CoalitionElement source | StableCoalitionValid sourceOwner source})
                ({target:CoalitionElement target | StableCoalitionValid targetOwner target})
           -> result)
      -> result / [stableAtlasTransversalSize arrow] @-}
withStableAtlasTransversalCoalitionInsertion
  :: Atlas (AtlasObjectAtlasScope target) (AtlasObjectPaginationScope target) (AtlasObjectCellData target) to tf
  -> StableAtlasTransversal source target
  -> (forall so sf. Atlas (AtlasObjectAtlasScope source) (AtlasObjectPaginationScope source) (AtlasObjectCellData source) so sf
        -> DomanialInsertion (CoalitionElement source) (CoalitionElement target) -> result)
  -> result
withStableAtlasTransversalCoalitionInsertion targetOwner arrow useInsertion =
  withStableScopedPackage targetOwner arrow $ \package ->
    useInsertion (scopedInsertionSource package)
      (retargetScopedInsertion (scopedInsertionSource package) (scopedInsertionTarget package)
        targetOwner (scopedInsertionValue package))

-- | Open the complete payload only after leaving an indexed constructor case.
{-@ withStableScopedPackage
      :: targetOwner:Atlas (AtlasObjectAtlasScope target) (AtlasObjectPaginationScope target) (AtlasObjectCellData target) to tf
      -> arrow:{StableAtlasTransversal source target |
           stableCoalitionOwnersCompatible arrow
           && (stableCoalitionTargetOwner arrow == Nothing
                || stableCoalitionTargetOwner arrow == Just (atlasOwner targetOwner))}
      -> (forall so sf ao af.
            package:{ScopedInsertionData
              (AtlasObjectAtlasScope source) (AtlasObjectPaginationScope source) (AtlasObjectCellData source) so sf
              (AtlasObjectAtlasScope target) (AtlasObjectPaginationScope target) (AtlasObjectCellData target) ao af |
               (stableCoalitionSourceOwner arrow == Just (atlasOwner (scopedInsertionSource package))
                || (stableCoalitionSourceOwner arrow == Nothing
                     && atlasOwner (scopedInsertionSource package) == atlasOwner targetOwner))
               && atlasOwner (scopedInsertionTarget package) == atlasOwner targetOwner
               && scopedInsertionForwardCodes package == stableCoalitionForwardCodes arrow
               && scopedInsertionInverseCodes package == stableCoalitionInverseCodes arrow}
            -> result)
      -> result / [stableAtlasTransversalSize arrow] @-}
withStableScopedPackage
  :: Atlas (AtlasObjectAtlasScope target) (AtlasObjectPaginationScope target) (AtlasObjectCellData target) to tf
  -> StableAtlasTransversal source target
  -> (forall so sf ao af.
        ScopedInsertionData
          (AtlasObjectAtlasScope source) (AtlasObjectPaginationScope source) (AtlasObjectCellData source) so sf
          (AtlasObjectAtlasScope target) (AtlasObjectPaginationScope target) (AtlasObjectCellData target) ao af
        -> result)
  -> result
withStableScopedPackage targetOwner arrow usePackage =
  let targetName = atlasOwner targetOwner
      identityPackage = retainScopedInsertion targetName targetName coalitionIdentityCode coalitionIdentityCode
        (identityScopedInsertion targetOwner)
  in case arrow of
    PrimitiveStableAtlasTransversal action ->
      let sourceName = atlasOwner (stableActionSource action)
          package = retainScopedInsertion sourceName targetName (stableActionForwardCode action) (stableActionInverseCode action)
            (primitiveScopedInsertion action)
      in withScopedInsertionPayload package usePackage
    IdentityStableAtlasTransversal -> withScopedInsertionPayload identityPackage usePackage
    CompositeStableAtlasTransversal second first ->
      stableCoalitionOwnersEmpty second `seq`
      withStableScopedPackage targetOwner second $ \secondPackage ->
        let middleOwner = scopedInsertionSource secondPackage
        in withStableScopedPackage middleOwner first $ \firstPackage ->
          usePackage (composeScopedData
            (reownScopedData (scopedInsertionSource firstPackage) middleOwner firstPackage)
            (reownScopedData (scopedInsertionSource secondPackage) targetOwner secondPackage))

{-@ reflect stableActionForwardCode @-}
stableActionForwardCode :: StableTransversalAction sa ss sd so sf ta ts td to tf mo mf
  -> Natural -> Maybe Natural
stableActionForwardCode action code =
  case coalitionUnrank (stableActionSource action) code of
    Nothing -> Nothing
    Just source -> Just (coalitionElementCode (applyInsertion (stableActionInsertion action) source))

{-@ reflect stableActionInverseCode @-}
stableActionInverseCode :: StableTransversalAction sa ss sd so sf ta ts td to tf mo mf
  -> Natural -> Maybe Natural
stableActionInverseCode action code =
  case coalitionUnrank (stableActionMappedTarget action) code of
    Nothing -> Nothing
    Just target ->
      case preimage (stableActionInsertion action) target of
        Nothing -> Nothing
        Just source -> Just (coalitionElementCode source)

{-@ reflect coalitionIdentityCode @-}
coalitionIdentityCode :: Natural -> Maybe Natural
coalitionIdentityCode code = Just code

{-@ measure stableCoalitionForwardCodes :: StableAtlasTransversal source target -> (Natural -> Maybe Natural)
      stableCoalitionForwardCodes (PrimitiveStableAtlasTransversal action) = stableActionForwardCode action
      stableCoalitionForwardCodes (IdentityStableAtlasTransversal) = coalitionIdentityCode
      stableCoalitionForwardCodes (CompositeStableAtlasTransversal second first) =
        composePartialInverses (stableCoalitionForwardCodes second) (stableCoalitionForwardCodes first)
  @-}

{-@ measure stableCoalitionInverseCodes :: StableAtlasTransversal source target -> (Natural -> Maybe Natural)
      stableCoalitionInverseCodes (PrimitiveStableAtlasTransversal action) = stableActionInverseCode action
      stableCoalitionInverseCodes (IdentityStableAtlasTransversal) = coalitionIdentityCode
      stableCoalitionInverseCodes (CompositeStableAtlasTransversal second first) =
        composePartialInverses (stableCoalitionInverseCodes first) (stableCoalitionInverseCodes second)
  @-}

-- ALIGN: COALITION-CODE-EXTENSIONALITY.
{-@ coalitionCodeExtensionality :: owner:Atlas a s d o f
      -> left:{CoalitionData a s d | StableCoalitionValid owner left}
      -> right:{CoalitionData a s d | StableCoalitionValid owner right
           && coalitionElementCode left == coalitionElementCode right}
      -> {left == right} @-}
coalitionCodeExtensionality :: Atlas a s d o f -> CoalitionData a s d -> CoalitionData a s d -> ()
coalitionCodeExtensionality owner left right =
  coalitionRankRoundTrip owner left `seq` coalitionRankRoundTrip owner right

{-@ reflect coalitionMaybeCode @-}
coalitionMaybeCode :: Maybe (CoalitionData a s d) -> Maybe Natural
coalitionMaybeCode Nothing = Nothing
coalitionMaybeCode (Just source) = Just (coalitionElementCode source)

{-@ stableActionForwardCodeAt :: action:StableTransversalAction sa ss sd so sf ta ts td to tf mo mf
      -> source:{CoalitionData sa ss sd | StableCoalitionValid (stableActionSource action) source}
      -> {stableActionForwardCode action (coalitionElementCode source)
           == Just (coalitionElementCode (applyInsertion (stableActionInsertion action) source))} @-}
stableActionForwardCodeAt :: StableTransversalAction sa ss sd so sf ta ts td to tf mo mf
  -> CoalitionData sa ss sd -> ()
stableActionForwardCodeAt action source =
  coalitionRankRoundTrip (stableActionSource action) source

{-@ stableActionInverseCodeAt :: action:StableTransversalAction sa ss sd so sf ta ts td to tf mo mf
      -> target:{CoalitionData ta ts td | StableCoalitionValid (stableActionMappedTarget action) target}
      -> {stableActionInverseCode action (coalitionElementCode target)
           == coalitionMaybeCode (preimage (stableActionInsertion action) target)} @-}
stableActionInverseCodeAt :: StableTransversalAction sa ss sd so sf ta ts td to tf mo mf
  -> CoalitionData ta ts td -> ()
stableActionInverseCodeAt action target =
  coalitionRankRoundTrip (stableActionMappedTarget action) target `seq`
    case preimage (stableActionInsertion action) target of
      Nothing -> ()
      Just _ -> ()

{-@ primitiveForwardObservation :: action:StableTransversalAction sa ss sd so sf ta ts td to tf mo mf
      -> insertion:{DomanialInsertion
           ({v:CoalitionData sa ss sd | StableCoalitionValid (stableActionSource action) v})
           ({v:CoalitionData ta ts td | StableCoalitionValid (stableActionMappedTarget action) v}) |
           applyInsertion insertion == stableActionForwardFor action (stableActionMappedTarget action)}
      -> source:{CoalitionData sa ss sd | StableCoalitionValid (stableActionSource action) source}
      -> {stableActionForwardCode action (coalitionElementCode source)
           == Just (coalitionElementCode (applyInsertion insertion source))} @-}
primitiveForwardObservation :: StableTransversalAction sa ss sd so sf ta ts td to tf mo mf
  -> DomanialInsertion (CoalitionData sa ss sd) (CoalitionData ta ts td) -> CoalitionData sa ss sd -> ()
primitiveForwardObservation action _ source =
  stableActionForwardCodeAt action source `seq`
    stableActionForwardFor action (stableActionMappedTarget action) source `seq` ()

{-@ primitiveInverseObservation :: action:StableTransversalAction sa ss sd so sf ta ts td to tf mo mf
      -> insertion:{DomanialInsertion
           ({v:CoalitionData sa ss sd | StableCoalitionValid (stableActionSource action) v})
           ({v:CoalitionData ta ts td | StableCoalitionValid (stableActionMappedTarget action) v}) |
           preimage insertion == preimage (stableActionInsertion action)}
      -> target:{CoalitionData ta ts td | StableCoalitionValid (stableActionMappedTarget action) target}
      -> {stableActionInverseCode action (coalitionElementCode target)
           == coalitionMaybeCode (preimage insertion target)} @-}
primitiveInverseObservation :: StableTransversalAction sa ss sd so sf ta ts td to tf mo mf
  -> DomanialInsertion (CoalitionData sa ss sd) (CoalitionData ta ts td) -> CoalitionData ta ts td -> ()
primitiveInverseObservation action _ = stableActionInverseCodeAt action

{-@ primitiveScopedInsertion :: action:StableTransversalAction sa ss sd so sf ta ts td to tf mo mf
      -> {packet:ScopedInsertionData sa ss sd so sf ta ts td mo mf |
           scopedInsertionSource packet == stableActionSource action
           && scopedInsertionTarget packet == stableActionMappedTarget action
           && scopedInsertionForwardCodes packet == stableActionForwardCode action
           && scopedInsertionInverseCodes packet == stableActionInverseCode action} @-}
primitiveScopedInsertion :: StableTransversalAction sa ss sd so sf ta ts td to tf mo mf
  -> ScopedInsertionData sa ss sd so sf ta ts td mo mf
primitiveScopedInsertion action =
  let insertion = stableActionInsertionFor action (stableActionMappedTarget action)
  in ScopedInsertionData (stableActionSource action) (stableActionMappedTarget action) insertion
       (stableActionForwardCode action) (stableActionInverseCode action)
       (primitiveForwardObservation action insertion) (primitiveInverseObservation action insertion)

{-@ identityForwardObservation :: source:CoalitionData a s d
      -> {coalitionIdentityCode (coalitionElementCode source)
           == Just (coalitionElementCode (applyInsertion identityInsertion source))} @-}
identityForwardObservation :: CoalitionData a s d -> ()
identityForwardObservation _ = ()

{-@ identityInverseObservation :: target:CoalitionData a s d
      -> {coalitionIdentityCode (coalitionElementCode target)
           == coalitionMaybeCode (preimage identityInsertion target)} @-}
identityInverseObservation :: CoalitionData a s d -> ()
identityInverseObservation _ = ()

{-@ identityScopedInsertion :: owner:Atlas a s d o f
      -> {packet:ScopedInsertionData a s d o f a s d o f |
           scopedInsertionSource packet == owner && scopedInsertionTarget packet == owner
           && scopedInsertionForwardCodes packet == coalitionIdentityCode
           && scopedInsertionInverseCodes packet == coalitionIdentityCode} @-}
identityScopedInsertion :: Atlas a s d o f -> ScopedInsertionData a s d o f a s d o f
identityScopedInsertion owner = ScopedInsertionData owner owner (scopedCoalitionIdentity owner)
  coalitionIdentityCode coalitionIdentityCode identityForwardObservation identityInverseObservation


{-@ reownScopedData :: source:Atlas sa ss sd so sf -> target:Atlas ta ts td to tf
      -> packet:{ScopedInsertionData sa ss sd ao af ta ts td bo bf |
           atlasOwner (scopedInsertionSource packet) == atlasOwner source
           && atlasOwner (scopedInsertionTarget packet) == atlasOwner target}
      -> {result:ScopedInsertionData sa ss sd so sf ta ts td to tf |
           scopedInsertionSource result == source && scopedInsertionTarget result == target
           && scopedInsertionValue result == scopedInsertionValue packet
           && scopedInsertionForwardCodes result == scopedInsertionForwardCodes packet
           && scopedInsertionInverseCodes result == scopedInsertionInverseCodes packet} @-}
reownScopedData :: Atlas sa ss sd so sf -> Atlas ta ts td to tf
  -> ScopedInsertionData sa ss sd ao af ta ts td bo bf
  -> ScopedInsertionData sa ss sd so sf ta ts td to tf
reownScopedData source target packet = ScopedInsertionData source target
  (scopedInsertionValue packet)
  (scopedInsertionForwardCodes packet) (scopedInsertionInverseCodes packet)
  (scopedInsertionForwardObservation packet) (scopedInsertionInverseObservation packet)

{-@ predicate StableCoalitionOwned S T A =
      stableCoalitionOwnersCompatible A
      && (stableCoalitionSourceOwner A == Just (atlasOwner S)
           || (stableCoalitionSourceOwner A == Nothing && atlasOwner S == atlasOwner T))
      && (stableCoalitionTargetOwner A == Nothing || stableCoalitionTargetOwner A == Just (atlasOwner T)) @-}

{-@ opaque-reflect stableCoalitionInsertionData @-}
{-@ stableCoalitionInsertionData
      :: source:Atlas (AtlasObjectAtlasScope source) (AtlasObjectPaginationScope source) (AtlasObjectCellData source) so sf
      -> target:Atlas (AtlasObjectAtlasScope target) (AtlasObjectPaginationScope target) (AtlasObjectCellData target) to tf
      -> arrow:{StableAtlasTransversal source target | StableCoalitionOwned source target arrow}
      -> {result:ScopedInsertionData
           (AtlasObjectAtlasScope source) (AtlasObjectPaginationScope source) (AtlasObjectCellData source) so sf
           (AtlasObjectAtlasScope target) (AtlasObjectPaginationScope target) (AtlasObjectCellData target) to tf |
           scopedInsertionSource result == source && scopedInsertionTarget result == target
           && scopedInsertionForwardCodes result == stableCoalitionForwardCodes arrow
           && scopedInsertionInverseCodes result == stableCoalitionInverseCodes arrow} @-}
stableCoalitionInsertionData
  :: Atlas (AtlasObjectAtlasScope source) (AtlasObjectPaginationScope source) (AtlasObjectCellData source) so sf
  -> Atlas (AtlasObjectAtlasScope target) (AtlasObjectPaginationScope target) (AtlasObjectCellData target) to tf
  -> StableAtlasTransversal source target
  -> ScopedInsertionData
       (AtlasObjectAtlasScope source) (AtlasObjectPaginationScope source) (AtlasObjectCellData source) so sf
       (AtlasObjectAtlasScope target) (AtlasObjectPaginationScope target) (AtlasObjectCellData target) to tf
stableCoalitionInsertionData source target arrow =
  withStableScopedPackage target arrow $ \packet -> reownScopedData source target packet
{-@ composedForwardObservation :: first:ScopedInsertionData sa ss sd so sf ma ms md mo mf
      -> second:{ScopedInsertionData ma ms md no nf ta ts td to tf |
           atlasOwner (scopedInsertionSource second) == atlasOwner (scopedInsertionTarget first)}
      -> source:{CoalitionData sa ss sd | StableCoalitionValid (scopedInsertionSource first) source}
      -> {composePartialInverses (scopedInsertionForwardCodes second) (scopedInsertionForwardCodes first)
             (coalitionElementCode source)
           == Just (coalitionElementCode
                (applyInsertion (composeInsertions (scopedInsertionValue second) (scopedInsertionValue first)) source))} @-}
composedForwardObservation :: ScopedInsertionData sa ss sd so sf ma ms md mo mf
  -> ScopedInsertionData ma ms md no nf ta ts td to tf -> CoalitionData sa ss sd -> ()
composedForwardObservation first second source =
  scopedInsertionForwardObservation first source `seq`
    let middle = applyInsertion (scopedInsertionValue first) source
    in coalitionOwnersAgree (scopedInsertionTarget first) (scopedInsertionSource second) middle `seq`
       scopedInsertionForwardObservation second middle

{-@ composedInverseObservation :: first:ScopedInsertionData sa ss sd so sf ma ms md mo mf
      -> second:{ScopedInsertionData ma ms md no nf ta ts td to tf |
           atlasOwner (scopedInsertionSource second) == atlasOwner (scopedInsertionTarget first)}
      -> target:{CoalitionData ta ts td | StableCoalitionValid (scopedInsertionTarget second) target}
      -> {composePartialInverses (scopedInsertionInverseCodes first) (scopedInsertionInverseCodes second)
             (coalitionElementCode target)
           == coalitionMaybeCode
                (preimage (composeInsertions (scopedInsertionValue second) (scopedInsertionValue first)) target)} @-}
composedInverseObservation :: ScopedInsertionData sa ss sd so sf ma ms md mo mf
  -> ScopedInsertionData ma ms md no nf ta ts td to tf -> CoalitionData ta ts td -> ()
composedInverseObservation first second target =
  scopedInsertionInverseObservation second target `seq`
    case preimage (scopedInsertionValue second) target of
      Nothing -> ()
      Just middle ->
        coalitionOwnersAgree (scopedInsertionTarget first) (scopedInsertionSource second) middle `seq`
          scopedInsertionInverseObservation first middle

{-@ composeScopedData :: first:ScopedInsertionData sa ss sd so sf ma ms md mo mf
      -> second:{ScopedInsertionData ma ms md no nf ta ts td to tf |
           atlasOwner (scopedInsertionSource second) == atlasOwner (scopedInsertionTarget first)}
      -> {result:ScopedInsertionData sa ss sd so sf ta ts td to tf |
           scopedInsertionSource result == scopedInsertionSource first
           && scopedInsertionTarget result == scopedInsertionTarget second
           && scopedInsertionForwardCodes result ==
                composePartialInverses (scopedInsertionForwardCodes second) (scopedInsertionForwardCodes first)
           && scopedInsertionInverseCodes result ==
                composePartialInverses (scopedInsertionInverseCodes first) (scopedInsertionInverseCodes second)} @-}
composeScopedData :: ScopedInsertionData sa ss sd so sf ma ms md mo mf
  -> ScopedInsertionData ma ms md no nf ta ts td to tf -> ScopedInsertionData sa ss sd so sf ta ts td to tf
composeScopedData first second =
  let source = scopedInsertionSource first
      middle = scopedInsertionSource second
      target = scopedInsertionTarget second
      firstInsertion = retargetScopedInsertion source (scopedInsertionTarget first) middle (scopedInsertionValue first)
      insertion = composeScopedCoalitionInsertions source middle target firstInsertion (scopedInsertionValue second)
  in ScopedInsertionData source target insertion
       (composePartialInverses (scopedInsertionForwardCodes second) (scopedInsertionForwardCodes first))
       (composePartialInverses (scopedInsertionInverseCodes first) (scopedInsertionInverseCodes second))
       (composedForwardObservation first second) (composedInverseObservation first second)
{-@ data CoalitionCodeFunctions = CoalitionCodeFunctions
      { observedForwardCodes :: Natural -> Maybe Natural
      , observedInverseCodes :: Natural -> Maybe Natural } @-}

data CoalitionCodeFunctions = CoalitionCodeFunctions
  { observedForwardCodes :: Natural -> Maybe Natural
  , observedInverseCodes :: Natural -> Maybe Natural }

-- ALIGN: ATLAS-STABLE-CODE-OBSERVATIONS.
{-@ coalitionCodeFunctions :: arrow:StableAtlasTransversal source target
      -> {observed:CoalitionCodeFunctions |
           observedForwardCodes observed == stableCoalitionForwardCodes arrow
           && observedInverseCodes observed == stableCoalitionInverseCodes arrow}
      / [stableAtlasTransversalSize arrow] @-}
coalitionCodeFunctions :: StableAtlasTransversal source target -> CoalitionCodeFunctions
coalitionCodeFunctions (PrimitiveStableAtlasTransversal action) =
  CoalitionCodeFunctions (stableActionForwardCode action) (stableActionInverseCode action)
coalitionCodeFunctions IdentityStableAtlasTransversal =
  CoalitionCodeFunctions coalitionIdentityCode coalitionIdentityCode
coalitionCodeFunctions (CompositeStableAtlasTransversal second first) =
  let observedFirst = coalitionCodeFunctions first
      observedSecond = coalitionCodeFunctions second
  in CoalitionCodeFunctions
       (composePartialInverses (observedForwardCodes observedSecond) (observedForwardCodes observedFirst))
       (composePartialInverses (observedInverseCodes observedFirst) (observedInverseCodes observedSecond))

{-@ codeCompositionAssociative :: third:(Natural -> Maybe Natural) -> second:(Natural -> Maybe Natural)
      -> first:(Natural -> Maybe Natural) -> code:Natural
      -> {composePartialInverses third (composePartialInverses second first) code
           == composePartialInverses (composePartialInverses third second) first code} @-}
codeCompositionAssociative :: (Natural -> Maybe Natural) -> (Natural -> Maybe Natural)
  -> (Natural -> Maybe Natural) -> Natural -> ()
codeCompositionAssociative _ second first code =
  case first code of
    Nothing -> ()
    Just middle -> case second middle of
      Nothing -> ()
      Just _ -> ()


type role NormalizedStable nominal nominal
{-@ data NormalizedStable source target = NormalizedStable
      { normalizationOriginal :: StableAtlasTransversal source target
      , normalizationResult :: {arrow:StableAtlasTransversal source target |
           stableCoalitionSourceOwner arrow == stableCoalitionSourceOwner normalizationOriginal
           && stableCoalitionTargetOwner arrow == stableCoalitionTargetOwner normalizationOriginal
           && (stableCoalitionOwnersCompatible arrow <=> stableCoalitionOwnersCompatible normalizationOriginal)}
      , normalizationForward :: code:Natural
           -> {stableCoalitionForwardCodes normalizationResult code == stableCoalitionForwardCodes normalizationOriginal code}
      , normalizationInverse :: code:Natural
           -> {stableCoalitionInverseCodes normalizationResult code == stableCoalitionInverseCodes normalizationOriginal code}
      } @-}
data NormalizedStable source target = NormalizedStable
  { normalizationOriginal :: StableAtlasTransversal source target
  , normalizationResult :: StableAtlasTransversal source target
  , normalizationForward :: Natural -> ()
  , normalizationInverse :: Natural -> () }

{-@ predicate SameStableObservations A B =
      stableCoalitionSourceOwner A == stableCoalitionSourceOwner B
      && stableCoalitionTargetOwner A == stableCoalitionTargetOwner B
      && (stableCoalitionOwnersCompatible A <=> stableCoalitionOwnersCompatible B)
      && stableCoalitionForwardCodes A == stableCoalitionForwardCodes B
      && stableCoalitionInverseCodes A == stableCoalitionInverseCodes B @-}

{-@ retainNormalization :: original:StableAtlasTransversal originalSource originalTarget
      -> packet:{NormalizedStable source target | SameStableObservations (normalizationOriginal packet) original}
      -> ScopedInsertionPayload <{\p -> SameStableObservations (normalizationOriginal p) original}>
           (NormalizedStable source target) @-}
retainNormalization :: StableAtlasTransversal originalSource originalTarget -> NormalizedStable source target
  -> ScopedInsertionPayload (NormalizedStable source target)
retainNormalization _ packet = ScopedInsertionPayload packet

{-@ unchangedNormalization :: arrow:StableAtlasTransversal source target
      -> {packet:NormalizedStable source target |
           normalizationOriginal packet == arrow && normalizationResult packet == arrow} @-}
unchangedNormalization :: StableAtlasTransversal source target -> NormalizedStable source target
unchangedNormalization arrow = NormalizedStable arrow arrow (\_ -> ()) (\_ -> ())


{-@ codeLeftIdentity :: mapping:(Natural -> Maybe Natural) -> code:Natural
      -> {mapping code == composePartialInverses coalitionIdentityCode mapping code} @-}
codeLeftIdentity :: (Natural -> Maybe Natural) -> Natural -> ()
codeLeftIdentity mapping code = case mapping code of
  Nothing -> ()
  Just _ -> ()

{-@ codeRightIdentity :: mapping:(Natural -> Maybe Natural) -> code:Natural
      -> {mapping code == composePartialInverses mapping coalitionIdentityCode code} @-}
codeRightIdentity :: (Natural -> Maybe Natural) -> Natural -> ()
codeRightIdentity _ _ = ()

{-@ codeReassociatedForward :: first:(Natural -> Maybe Natural) -> middle:(Natural -> Maybe Natural)
      -> second:(Natural -> Maybe Natural) -> normalized:(Natural -> Maybe Natural)
      -> (n:Natural -> {normalized n == composePartialInverses second middle n})
      -> code:Natural
      -> {composePartialInverses normalized first code
           == composePartialInverses second (composePartialInverses middle first) code} @-}
codeReassociatedForward :: (Natural -> Maybe Natural) -> (Natural -> Maybe Natural)
  -> (Natural -> Maybe Natural) -> (Natural -> Maybe Natural) -> (Natural -> ()) -> Natural -> ()
codeReassociatedForward first middle second _ childProof code =
  codeCompositionAssociative second middle first code `seq`
    case first code of
      Nothing -> ()
      Just intermediate -> childProof intermediate

{-@ codeReassociatedInverse :: first:(Natural -> Maybe Natural) -> middle:(Natural -> Maybe Natural)
      -> second:(Natural -> Maybe Natural) -> normalized:(Natural -> Maybe Natural)
      -> (n:Natural -> {normalized n == composePartialInverses middle second n})
      -> code:Natural
      -> {composePartialInverses first normalized code
           == composePartialInverses (composePartialInverses first middle) second code} @-}
codeReassociatedInverse :: (Natural -> Maybe Natural) -> (Natural -> Maybe Natural)
  -> (Natural -> Maybe Natural) -> (Natural -> Maybe Natural) -> (Natural -> ()) -> Natural -> ()
codeReassociatedInverse first middle second normalized childProof code =
  childProof code `seq`
    case normalized code of
      Nothing -> codeCompositionAssociative first middle second code
      Just _ -> codeCompositionAssociative first middle second code

{-@ predicate NormalizedComposition SECOND FIRST P =
      stableCoalitionSourceOwner (normalizationOriginal P) ==
        stableCoalitionSourceOwner (CompositeStableAtlasTransversal SECOND FIRST)
      && stableCoalitionTargetOwner (normalizationOriginal P) ==
        stableCoalitionTargetOwner (CompositeStableAtlasTransversal SECOND FIRST)
      && (stableCoalitionOwnersCompatible (normalizationOriginal P) <=>
        stableCoalitionOwnersCompatible (CompositeStableAtlasTransversal SECOND FIRST))
      && stableCoalitionForwardCodes (normalizationOriginal P) ==
        composePartialInverses (stableCoalitionForwardCodes SECOND) (stableCoalitionForwardCodes FIRST)
      && stableCoalitionInverseCodes (normalizationOriginal P) ==
        composePartialInverses (stableCoalitionInverseCodes FIRST) (stableCoalitionInverseCodes SECOND) @-}

{-@ identityLeftNormalization :: first:StableAtlasTransversal source target
      -> {packet:NormalizedStable source target |
           stableCoalitionSourceOwner (normalizationOriginal packet) == stableCoalitionSourceOwner first
           && stableCoalitionTargetOwner (normalizationOriginal packet) == stableCoalitionTargetOwner first
           && (stableCoalitionOwnersCompatible (normalizationOriginal packet) <=> stableCoalitionOwnersCompatible first)
           && stableCoalitionForwardCodes (normalizationOriginal packet) ==
                composePartialInverses coalitionIdentityCode (stableCoalitionForwardCodes first)
           && stableCoalitionInverseCodes (normalizationOriginal packet) ==
                composePartialInverses (stableCoalitionInverseCodes first) coalitionIdentityCode} @-}
identityLeftNormalization :: StableAtlasTransversal source target -> NormalizedStable source target
identityLeftNormalization first =
  let observed = coalitionCodeFunctions first
      original = CompositeStableAtlasTransversal IdentityStableAtlasTransversal first
  in NormalizedStable original first
       (codeLeftIdentity (observedForwardCodes observed))
       (codeRightIdentity (observedInverseCodes observed))

{-@ identityRightNormalization :: second:StableAtlasTransversal source target
      -> {packet:NormalizedStable source target |
           stableCoalitionSourceOwner (normalizationOriginal packet) == stableCoalitionSourceOwner second
           && stableCoalitionTargetOwner (normalizationOriginal packet) == stableCoalitionTargetOwner second
           && (stableCoalitionOwnersCompatible (normalizationOriginal packet) <=> stableCoalitionOwnersCompatible second)
           && stableCoalitionForwardCodes (normalizationOriginal packet) ==
                composePartialInverses (stableCoalitionForwardCodes second) coalitionIdentityCode
           && stableCoalitionInverseCodes (normalizationOriginal packet) ==
                composePartialInverses coalitionIdentityCode (stableCoalitionInverseCodes second)} @-}
identityRightNormalization :: StableAtlasTransversal source target -> NormalizedStable source target
identityRightNormalization second =
  let observed = coalitionCodeFunctions second
      original = CompositeStableAtlasTransversal second IdentityStableAtlasTransversal
  in NormalizedStable original second
       (codeRightIdentity (observedForwardCodes observed))
       (codeLeftIdentity (observedInverseCodes observed))

{-@ reassociatedNormalization :: second:StableAtlasTransversal next target -> middle:StableAtlasTransversal mid next
      -> first:StableAtlasTransversal source mid
      -> child:{NormalizedStable mid target | NormalizedComposition second middle child}
      -> {packet:NormalizedStable source target |
           stableCoalitionSourceOwner (normalizationOriginal packet) ==
             stableCoalitionSourceOwner (CompositeStableAtlasTransversal second (CompositeStableAtlasTransversal middle first))
           && stableCoalitionTargetOwner (normalizationOriginal packet) ==
             stableCoalitionTargetOwner (CompositeStableAtlasTransversal second (CompositeStableAtlasTransversal middle first))
           && (stableCoalitionOwnersCompatible (normalizationOriginal packet) <=>
             stableCoalitionOwnersCompatible (CompositeStableAtlasTransversal second (CompositeStableAtlasTransversal middle first)))
           && stableCoalitionForwardCodes (normalizationOriginal packet) ==
             composePartialInverses (stableCoalitionForwardCodes second)
               (composePartialInverses (stableCoalitionForwardCodes middle) (stableCoalitionForwardCodes first))
           && stableCoalitionInverseCodes (normalizationOriginal packet) ==
             composePartialInverses (composePartialInverses (stableCoalitionInverseCodes first) (stableCoalitionInverseCodes middle))
               (stableCoalitionInverseCodes second)} @-}
reassociatedNormalization :: StableAtlasTransversal next target -> StableAtlasTransversal mid next
  -> StableAtlasTransversal source mid -> NormalizedStable mid target -> NormalizedStable source target
reassociatedNormalization second middle first child =
  stableCoalitionOwnersAssociativity second middle first `seq`
    let firstCodes = coalitionCodeFunctions first
        middleCodes = coalitionCodeFunctions middle
        secondCodes = coalitionCodeFunctions second
        normalizedCodes = coalitionCodeFunctions (normalizationResult child)
        original = CompositeStableAtlasTransversal second (CompositeStableAtlasTransversal middle first)
        result = CompositeStableAtlasTransversal (normalizationResult child) first
    in NormalizedStable original result
         (codeReassociatedForward (observedForwardCodes firstCodes) (observedForwardCodes middleCodes)
           (observedForwardCodes secondCodes) (observedForwardCodes normalizedCodes) (normalizationForward child))
         (codeReassociatedInverse (observedInverseCodes firstCodes) (observedInverseCodes middleCodes)
           (observedInverseCodes secondCodes) (observedInverseCodes normalizedCodes) (normalizationInverse child))

{-@ withNormalizedStable :: second:StableAtlasTransversal middle target
      -> first:StableAtlasTransversal source middle
      -> (packet:{NormalizedStable source target |
           NormalizedComposition second first packet} -> result)
      -> result / [stableAtlasTransversalSize first] @-}
withNormalizedStable :: StableAtlasTransversal middle target -> StableAtlasTransversal source middle
  -> (NormalizedStable source target -> result) -> result
withNormalizedStable second first usePacket =
  let original = CompositeStableAtlasTransversal second first
      unchanged = unchangedNormalization original
  in case second of
    IdentityStableAtlasTransversal ->
      withScopedInsertionPayload (retainNormalization original (identityLeftNormalization first)) usePacket
    _ -> case first of
      IdentityStableAtlasTransversal ->
        withScopedInsertionPayload (retainNormalization original (identityRightNormalization second)) usePacket
      CompositeStableAtlasTransversal middle firstPart ->
        withNormalizedStable second middle $ \child ->
          withScopedInsertionPayload
            (retainNormalization original (reassociatedNormalization second middle firstPart child)) usePacket
      PrimitiveStableAtlasTransversal _ -> usePacket unchanged

-- ALIGN: ATLAS-STABLE-NORMALIZATION-PACKAGE.
{-@ opaque-reflect normalizedStableData @-}
{-@ normalizedStableData :: second:StableAtlasTransversal middle target
      -> first:StableAtlasTransversal source middle
      -> {packet:NormalizedStable source target |
           NormalizedComposition second first packet} @-}
normalizedStableData :: StableAtlasTransversal middle target -> StableAtlasTransversal source middle
  -> NormalizedStable source target
normalizedStableData second first = withNormalizedStable second first (\packet -> packet)

-- ALIGN: ATLAS-STABLE-NORMALIZED-FORWARD-CODES.
{-@ normalizedForwardCodes :: second:StableAtlasTransversal middle target
      -> first:StableAtlasTransversal source middle -> code:Natural
      -> {stableCoalitionForwardCodes (composeStableAtlasTransversals second first) code
           == composePartialInverses (stableCoalitionForwardCodes second) (stableCoalitionForwardCodes first) code} @-}
normalizedForwardCodes :: StableAtlasTransversal middle target -> StableAtlasTransversal source middle -> Natural -> ()
normalizedForwardCodes second first = normalizationForward (normalizedStableData second first)

-- ALIGN: ATLAS-STABLE-NORMALIZED-INVERSE-CODES.
{-@ normalizedInverseCodes :: second:StableAtlasTransversal middle target
      -> first:StableAtlasTransversal source middle -> code:Natural
      -> {stableCoalitionInverseCodes (composeStableAtlasTransversals second first) code
           == composePartialInverses (stableCoalitionInverseCodes first) (stableCoalitionInverseCodes second) code} @-}
normalizedInverseCodes :: StableAtlasTransversal middle target -> StableAtlasTransversal source middle -> Natural -> ()
normalizedInverseCodes second first = normalizationInverse (normalizedStableData second first)
