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
  ( AtlasMembership (..)
  , atlasMembership
  , atlasMembershipAccepts
  , AtlasAction
  , atlasAction
  , atlasRestrictedAction
  , atlasActionAccepts
  , atlasActionMembership
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

-- | A first-order membership package keeps the rank-2 predicate's identity
-- available when checking dependent object and arrow actions.
type role AtlasMembership nominal nominal
data AtlasMembership (scope :: Type) (cellData :: Type -> Type)
  = AllAtlasData
  | AtlasMembership (forall object. PageElement scope object -> cellData object -> Bool)

{-@ atlasMembership
      :: accepts:(forall object. PageElement scope object -> cellData object -> Bool)
      -> {membership:AtlasMembership scope cellData | membership == AtlasMembership accepts} @-}
atlasMembership
  :: (forall object. PageElement scope object -> cellData object -> Bool)
  -> AtlasMembership scope cellData
atlasMembership = AtlasMembership

{-@ reflect atlasMembershipAccepts @-}
-- ALIGN: ATLAS-MEMBERSHIP-PREDICATE.
atlasMembershipAccepts
  :: AtlasMembership scope cellData -> PageElement scope object -> cellData object -> Bool
atlasMembershipAccepts AllAtlasData _ _ = True
atlasMembershipAccepts (AtlasMembership accepts) occurrence datum = accepts occurrence datum

-- | A dependent data assignment retains its cell-membership predicate.
-- Dominion coherence and arrow inverses range over accepted cell data.
type role AtlasAction nominal nominal
{-@ data AtlasAction scope cellData = AtlasAction
      { atlasActionMembership :: AtlasMembership scope cellData
      , atlasActionDataAt :: forall object. occurrence:PageElement scope object
          -> Dominion ({datum:cellData object |
               atlasMembershipAccepts atlasActionMembership occurrence datum})
      , atlasActionMap :: forall source target. arrow:PageElementArrow scope source target
          -> DomanialInsertion
               ({datum:cellData source |
                    atlasMembershipAccepts atlasActionMembership (arrowSource arrow) datum})
               ({datum:cellData target |
                    atlasMembershipAccepts atlasActionMembership (arrowTarget arrow) datum})
      } @-}
data AtlasAction
  (scope :: Type)
  (cellData :: Type -> Type) = AtlasAction
  { atlasActionMembership :: AtlasMembership scope cellData
  , atlasActionDataAt :: forall object.
      PageElement scope object -> Dominion (cellData object)
  , atlasActionMap :: forall source target.
      PageElementArrow scope source target
      -> DomanialInsertion (cellData source) (cellData target)
  }

{-@ reflect atlasActionAccepts @-}
atlasActionAccepts
  :: AtlasAction scope cellData -> PageElement scope object -> cellData object -> Bool
atlasActionAccepts action occurrence datum =
  atlasMembershipAccepts (atlasActionMembership action) occurrence datum

-- | Package a carrier whose Haskell type already enforces membership.
atlasAction
  :: (forall object.
        PageElement scope object -> Dominion (cellData object))
  -> (forall source target.
        PageElementArrow scope source target
        -> DomanialInsertion (cellData source) (cellData target))
  -> AtlasAction scope cellData
atlasAction dataAt mapData = AtlasAction AllAtlasData dataAt mapData

-- | Package a value-dependent carrier without discarding its predicate.
{-@ atlasRestrictedAction
      :: membership:AtlasMembership scope cellData
      -> dataAt:(forall object. occurrence:PageElement scope object
           -> Dominion ({datum:cellData object | atlasMembershipAccepts membership occurrence datum}))
      -> mapData:(forall source target. arrow:PageElementArrow scope source target
           -> DomanialInsertion
                ({datum:cellData source | atlasMembershipAccepts membership (arrowSource arrow) datum})
                ({datum:cellData target | atlasMembershipAccepts membership (arrowTarget arrow) datum}))
      -> {action:AtlasAction scope cellData | atlasActionMembership action == membership} @-}
-- ALIGN: ATLAS-MEMBERSHIP-ACTION.
atlasRestrictedAction
  :: AtlasMembership scope cellData
  -> (forall object. PageElement scope object -> Dominion (cellData object))
  -> (forall source target. PageElementArrow scope source target
        -> DomanialInsertion (cellData source) (cellData target))
  -> AtlasAction scope cellData
atlasRestrictedAction = AtlasAction

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
          occurrence:PageElement scope object -> datum:{cellData object | atlasActionAccepts atlasActionData (normalizePageElementAt atlasDataFinalPage atlasDataTraceLimit occurrence) datum}
          -> {AtlasIdentityAt atlasActionData atlasDataFinalPage atlasDataTraceLimit occurrence datum}
      , atlasDataCompositionLaw :: forall source middle target.
          second:PageElementArrow scope middle target
          -> first:PageElementArrow scope source middle -> datum:{cellData source | atlasActionAccepts atlasActionData (normalizePageElementAt atlasDataFinalPage atlasDataTraceLimit (arrowSource first)) datum}
          -> {arrowTarget first == arrowSource second =>
                AtlasCompositionAt atlasActionData atlasDataFinalPage atlasDataTraceLimit second first datum}
      , atlasDataCoherenceLaw :: forall object.
          occurrence:PageElement scope object -> coherenceArrow:PageElementArrow scope object object
          -> datum:{cellData object | atlasActionAccepts atlasActionData (normalizePageElementAt atlasDataFinalPage atlasDataTraceLimit occurrence) datum}
          -> {AtlasCoherenceConditions atlasDataFinalPage atlasDataTraceLimit occurrence coherenceArrow =>
                AtlasCoherenceAt atlasActionData atlasDataFinalPage atlasDataTraceLimit coherenceArrow datum}
      , atlasDataDisjointLaw :: forall leftObject rightObject originObject.
          left:PageElement scope leftObject -> right:PageElement scope rightObject
          -> leftToOrigin:PageElementArrow scope leftObject originObject
          -> rightToOrigin:PageElementArrow scope rightObject originObject
          -> leftDatum:{cellData leftObject | atlasActionAccepts atlasActionData (normalizePageElementAt atlasDataFinalPage atlasDataTraceLimit left) leftDatum} -> rightDatum:{cellData rightObject | atlasActionAccepts atlasActionData (normalizePageElementAt atlasDataFinalPage atlasDataTraceLimit right) rightDatum}
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
           occurrence:PageElement scope object -> datum:{cellData object | atlasActionAccepts action (normalizePageElementAt finalPage traceLimit occurrence) datum}
           -> {AtlasIdentityAt action finalPage traceLimit occurrence datum})
      -> compositionLaw:(forall source middle target.
           second:PageElementArrow scope middle target
           -> first:PageElementArrow scope source middle
           -> alignment:{() | arrowTarget first == arrowSource second}
           -> datum:{cellData source | atlasActionAccepts action (normalizePageElementAt finalPage traceLimit (arrowSource first)) datum}
           -> {AtlasCompositionAt action finalPage traceLimit second first datum})
      -> coherenceLaw:(forall object.
           occurrence:PageElement scope object -> coherenceArrow:PageElementArrow scope object object
           -> conditions:{() | AtlasCoherenceConditions finalPage traceLimit occurrence coherenceArrow}
           -> datum:{cellData object | atlasActionAccepts action (normalizePageElementAt finalPage traceLimit occurrence) datum} -> {AtlasCoherenceAt action finalPage traceLimit coherenceArrow datum})
      -> disjointLaw:(forall leftObject rightObject originObject.
           left:PageElement scope leftObject -> right:PageElement scope rightObject
           -> leftToOrigin:PageElementArrow scope leftObject originObject
           -> rightToOrigin:PageElementArrow scope rightObject originObject
           -> conditions:{() | AtlasDisjointConditions finalPage left right leftToOrigin rightToOrigin}
           -> leftDatum:{cellData leftObject | atlasActionAccepts action (normalizePageElementAt finalPage traceLimit left) leftDatum} -> rightDatum:{cellData rightObject | atlasActionAccepts action (normalizePageElementAt finalPage traceLimit right) rightDatum}
           -> {AtlasDisjointAt action finalPage traceLimit leftToOrigin rightToOrigin leftDatum rightDatum})
      -> {stored:AtlasData scope cellData |
           atlasDataFinalPage stored == finalPage && atlasDataTraceLimit stored == traceLimit
           && atlasActionData stored == action} @-}
-- ALIGN: ATLAS-MEMBERSHIP-LAWS-INTERPRETATION.
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
