{-# LANGUAGE CPP #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE RoleAnnotations #-}
#include "../../../LiquidPlugin.h"
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}
{-@ LIQUID "--higherorder" @-}

-- | LiquidHaskell-verified data assignment carried by an Atlas object.
module Atlas.LiquidInternal
  ( AtlasAction
  , atlasAction
  , atlasActionDataAt
  , atlasActionMap
  , AtlasData
  , atlasActionData
  , atlasDataFinalPage
  , atlasDataTraceLimit
  , atlasDataIdentityLaw
  , atlasDataCompositionLaw
  , atlasDataCoherenceLaw
  , atlasDataDisjointLaw
  , atlasData
  ) where

import Data.Kind (Type)
import DomanialInsertion.LiquidInternal
import Dominion.Internal (Dominion)
import Numeric.Natural (Natural)
import PageElements.LiquidInternal

-- | The two rank-2 operations of the dependent data assignment.  Packaging
-- them lets refinements mention the specialized accessors as first-order
-- functions while retaining the indexed result type.
type role AtlasAction nominal nominal
data AtlasAction
  (scope :: Type)
  (cellData :: Type -> Type) = AtlasAction
  (forall object.
    PageElement scope object -> Dominion (cellData object))
  (forall source target.
    PageElementArrow scope source target
    -> DomanialInsertion (cellData source) (cellData target))

atlasAction
  :: (forall object.
        PageElement scope object -> Dominion (cellData object))
  -> (forall source target.
        PageElementArrow scope source target
        -> DomanialInsertion (cellData source) (cellData target))
  -> AtlasAction scope cellData
atlasAction = AtlasAction

{-@ reflect atlasActionDataAt @-}
atlasActionDataAt
  :: AtlasAction scope cellData
  -> PageElement scope object
  -> Dominion (cellData object)
atlasActionDataAt (AtlasAction dataAt _) = dataAt

{-@ reflect atlasActionMap @-}
atlasActionMap
  :: AtlasAction scope cellData
  -> PageElementArrow scope source target
  -> DomanialInsertion (cellData source) (cellData target)
atlasActionMap (AtlasAction _ mapData) = mapData

-- | A canonical data assignment and pointwise witnesses for its Atlas laws.
-- The page bound and trace bound are copied from the owning pagination so the
-- refinements can state the padded-spine normalization equations directly.
{-@ predicate AtlasIdentityAt A F T X D =
      applyInsertion (atlasActionMap A
        (normalizePageElementArrowAt F T (identityPageElementArrow X))) D == D @-}
{-@ predicate AtlasCompositionAt A F T G H D =
      applyInsertion (atlasActionMap A
        (normalizePageElementArrowAt F T (composePageElementArrows G H))) D
      == applyInsertion (atlasActionMap A (normalizePageElementArrowAt F T G))
           (applyInsertion (atlasActionMap A (normalizePageElementArrowAt F T H)) D) @-}
{-@ predicate AtlasCoherenceConditions F T X H =
      arrowSource H == X && arrowTarget H == normalizePageElementAt F T X @-}
{-@ predicate AtlasCoherenceAt A F T H D =
      applyInsertion (atlasActionMap A (normalizePageElementArrowAt F T H)) D == D @-}
{-@ predicate AtlasDisjointConditions F X Y H K =
      pageElementPage Y == pageElementPage X
      && pageElementPosition Y /= pageElementPosition X
      && pageElementPage X <= F
      && arrowSource H == X && pageElementPage (arrowTarget H) == 0
      && arrowSource K == Y && arrowTarget K == arrowTarget H @-}
{-@ predicate AtlasDisjointAt A F T H K D E =
      applyInsertion (atlasActionMap A (normalizePageElementArrowAt F T H)) D
      /= applyInsertion (atlasActionMap A (normalizePageElementArrowAt F T K)) E @-}

{-@ data AtlasData scope cellData = AtlasData
      { atlasDataFinalPage :: Natural
      , atlasDataTraceLimit :: Int
      , atlasActionData :: AtlasAction scope cellData
      , atlasDataIdentityLaw :: forall object.
          occurrence:PageElement scope object -> datum:cellData object
          -> {AtlasIdentityAt atlasActionData atlasDataFinalPage atlasDataTraceLimit occurrence datum}
      , atlasDataCompositionLaw :: forall source middle target.
          second:PageElementArrow scope middle target
          -> first:PageElementArrow scope source middle -> datum:cellData source
          -> {arrowTarget first == arrowSource second =>
                AtlasCompositionAt atlasActionData atlasDataFinalPage atlasDataTraceLimit second first datum}
      , atlasDataCoherenceLaw :: forall object.
          occurrence:PageElement scope object -> coherenceArrow:PageElementArrow scope object object
          -> datum:cellData object
          -> {AtlasCoherenceConditions atlasDataFinalPage atlasDataTraceLimit occurrence coherenceArrow =>
                AtlasCoherenceAt atlasActionData atlasDataFinalPage atlasDataTraceLimit coherenceArrow datum}
      , atlasDataDisjointLaw :: forall leftObject rightObject originObject.
          left:PageElement scope leftObject -> right:PageElement scope rightObject
          -> leftToOrigin:PageElementArrow scope leftObject originObject
          -> rightToOrigin:PageElementArrow scope rightObject originObject
          -> leftDatum:cellData leftObject -> rightDatum:cellData rightObject
          -> {AtlasDisjointConditions atlasDataFinalPage left right leftToOrigin rightToOrigin =>
                AtlasDisjointAt atlasActionData atlasDataFinalPage atlasDataTraceLimit
                  leftToOrigin rightToOrigin leftDatum rightDatum}
      } @-}
type role AtlasData nominal nominal
data AtlasData
  (scope :: Type)
  (cellData :: Type -> Type) = AtlasData
  { atlasDataFinalPage :: Natural
  , atlasDataTraceLimit :: Int
  , atlasActionData :: AtlasAction scope cellData
  , atlasDataIdentityLaw :: forall object.
      PageElement scope object -> cellData object -> ()
  , atlasDataCompositionLaw :: forall source middle target.
      PageElementArrow scope middle target -> PageElementArrow scope source middle
      -> cellData source -> ()
  , atlasDataCoherenceLaw :: forall object.
      PageElement scope object -> PageElementArrow scope object object -> cellData object -> ()
  , atlasDataDisjointLaw :: forall leftObject rightObject originObject.
      PageElement scope leftObject -> PageElement scope rightObject
      -> PageElementArrow scope leftObject originObject
      -> PageElementArrow scope rightObject originObject
      -> cellData leftObject -> cellData rightObject -> ()
  }

-- | Smart constructor for a checked Atlas data assignment.  LiquidHaskell
-- validates each supplied witness against the corresponding record field.
{-@ atlasData
      :: finalPage:Natural -> traceLimit:Int -> action:AtlasAction scope cellData
      -> identityLaw:(forall object.
           occurrence:PageElement scope object -> datum:cellData object
           -> {AtlasIdentityAt action finalPage traceLimit occurrence datum})
      -> compositionLaw:(forall source middle target.
           second:PageElementArrow scope middle target
           -> first:PageElementArrow scope source middle
           -> alignment:{() | arrowTarget first == arrowSource second}
           -> datum:cellData source
           -> {AtlasCompositionAt action finalPage traceLimit second first datum})
      -> coherenceLaw:(forall object.
           occurrence:PageElement scope object -> coherenceArrow:PageElementArrow scope object object
           -> conditions:{() | AtlasCoherenceConditions finalPage traceLimit occurrence coherenceArrow}
           -> datum:cellData object -> {AtlasCoherenceAt action finalPage traceLimit coherenceArrow datum})
      -> disjointLaw:(forall leftObject rightObject originObject.
           left:PageElement scope leftObject -> right:PageElement scope rightObject
           -> leftToOrigin:PageElementArrow scope leftObject originObject
           -> rightToOrigin:PageElementArrow scope rightObject originObject
           -> conditions:{() | AtlasDisjointConditions finalPage left right leftToOrigin rightToOrigin}
           -> leftDatum:cellData leftObject -> rightDatum:cellData rightObject
           -> {AtlasDisjointAt action finalPage traceLimit leftToOrigin rightToOrigin leftDatum rightDatum})
      -> {stored:AtlasData scope cellData |
           atlasDataFinalPage stored == finalPage && atlasDataTraceLimit stored == traceLimit
           && atlasActionData stored == action} @-}
-- ALIGN: ATLAS-DATA-FUNCTOR.
-- ALIGN: ATLAS-DATA-DISJOINT.
atlasData
  :: Natural
  -> Int
  -> AtlasAction scope cellData
  -> (forall object.
        PageElement scope object -> cellData object -> ())
  -> (forall source middle target.
        PageElementArrow scope middle target
        -> PageElementArrow scope source middle
        -> ()
        -> cellData source
        -> ())
  -> (forall object.
        PageElement scope object
        -> PageElementArrow scope object object
        -> ()
        -> cellData object
        -> ())
  -> (forall leftObject rightObject originObject.
        PageElement scope leftObject
        -> PageElement scope rightObject
        -> PageElementArrow scope leftObject originObject
        -> PageElementArrow scope rightObject originObject
        -> ()
        -> cellData leftObject
        -> cellData rightObject
        -> ())
  -> AtlasData scope cellData
atlasData
  finalPage
  traceLimit
  action
  identityLaw
  compositionLaw
  coherenceLaw
  disjointLaw =
    AtlasData
      finalPage
      traceLimit
      action
      identityLaw
      checkedCompositionLaw
      checkedCoherenceLaw
      checkedDisjointLaw
  where
    checkedCompositionLaw second first datum
      | arrowTarget first == arrowSource second =
          compositionLaw second first () datum
      | otherwise = ()

    checkedCoherenceLaw occurrence coherenceArrow datum
      | arrowSource coherenceArrow == occurrence
          && arrowTarget coherenceArrow
            == normalizePageElementAt finalPage traceLimit occurrence =
              coherenceLaw occurrence coherenceArrow () datum
      | otherwise = ()

    checkedDisjointLaw
      left
      right
      leftToOrigin
      rightToOrigin
      leftDatum
      rightDatum
        | pageElementPage right == pageElementPage left
            && pageElementPosition right /= pageElementPosition left
            && pageElementPage left <= finalPage
            && arrowSource leftToOrigin == left
            && pageElementPage (arrowTarget leftToOrigin) == 0
            && arrowSource rightToOrigin == right
            && arrowTarget rightToOrigin == arrowTarget leftToOrigin =
              disjointLaw
                left
                right
                leftToOrigin
                rightToOrigin
                ()
                leftDatum
                rightDatum
        | otherwise = ()
