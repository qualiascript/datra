{-# LANGUAGE CPP #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE RoleAnnotations #-}
#include "../LiquidPlugin.h"
{-# OPTIONS_GHC -Wno-unused-imports -Wno-unused-top-binds #-}
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
  , atlasData
  ) where

import Data.Kind (Type)
import Chain.Internal (Chain (..))
import DatraOrdinal (Ordinal)
import DomanialInsertion.LiquidInternal
  ( DomanialInsertion
  , applyInsertion
  )
import Dominion.Internal (Dominion)
import Numeric.Natural (Natural)
import PageElements.LiquidInternal
  ( PageElement
  , PageElementCell (..)
  , PageElementArrow
  , arrowSource
  , arrowTarget
  , clampPage
  , composePageElementArrows
  , identityPageElementArrow
  , normalizePageElementArrowAt
  , normalizePageElementAt
  , pageElementArrow
  , pageElementPage
  , pageElementPosition
  , pageElementPrecedes
  , pageElementTransported
  , traceSuffix
  , trimTrace
  )

-- Keep the reflected page-element relations and their component types in
-- LiquidHaskell's imported logical environment.  Version 0.9.4 otherwise
-- prunes these transitive symbols while checking higher-rank law callbacks.
pageElementTypeWitness :: Maybe (Ordinal, Natural)
pageElementTypeWitness = Nothing

pageElementRelationWitness
  :: PageElement scope source
  -> PageElement scope target
  -> (Bool, Bool)
pageElementRelationWitness source target =
  ( pageElementPrecedes source target
  , pageElementTransported source target
  )

pageElementNormalizationWitness
  :: Natural
  -> Int
  -> PageElement scope object
  -> (Natural, [Ordinal])
pageElementNormalizationWitness finalPage traceLimit occurrence =
  ( clampPage (pageElementPage occurrence) finalPage
  , trimTrace traceLimit []
  )

pageElementTraceSuffixWitness :: [Ordinal] -> [Ordinal] -> Bool
pageElementTraceSuffixWitness = traceSuffix

-- | The two rank-2 operations of the dependent data assignment.  Packaging
-- them lets refinements mention the specialized accessors as first-order
-- functions; LiquidHaskell 0.9.4 cannot put refinements directly on a
-- higher-rank field whose result uses an indexed type family.
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
type role AtlasData nominal nominal
data AtlasData
  (scope :: Type)
  (cellData :: Type -> Type) = AtlasData
  { atlasFinalPageData :: Natural
  , atlasTraceLimitData :: Int
  , atlasActionData :: AtlasAction scope cellData
  , atlasDataIdentityLawData
      :: forall object.
         PageElement scope object
      -> cellData object
      -> ()
  , atlasDataCompositionLawData
      :: forall source middle target.
         PageElementArrow scope middle target
      -> PageElementArrow scope source middle
      -> cellData source
      -> ()
  , atlasDataCoherenceLawData
      :: forall object.
         PageElement scope object
      -> PageElementArrow scope object object
      -> cellData object
      -> ()
  , atlasPagewiseDisjointLawData
      :: forall leftObject rightObject originObject.
         PageElement scope leftObject
      -> PageElement scope rightObject
      -> PageElementArrow scope leftObject originObject
      -> PageElementArrow scope rightObject originObject
      -> cellData leftObject
      -> cellData rightObject
      -> ()
  }

-- | Smart constructor for a checked Atlas data assignment.  LiquidHaskell
-- validates each supplied witness against the corresponding record field.
{-@
atlasData
  :: finalPage:Natural
  -> traceLimit:Int
  -> action:AtlasAction scope cellData
  -> identityLaw:(forall object.
       occurrence:PageElement scope object
       -> datum:cellData object
       -> { proof:() |
            applyInsertion
              (atlasActionMap action
                (normalizePageElementArrowAt
                  finalPage traceLimit
                  (identityPageElementArrow occurrence)))
              datum
            == datum })
  -> compositionLaw:(forall source middle target.
       second:PageElementArrow scope middle target
       -> first:PageElementArrow scope source middle
       -> alignment:{() | arrowTarget first == arrowSource second}
       -> datum:cellData source
       -> { proof:() |
            applyInsertion
              (atlasActionMap action
                (normalizePageElementArrowAt finalPage traceLimit
                  (composePageElementArrows second first)))
              datum
            == applyInsertion
                 (atlasActionMap action
                   (normalizePageElementArrowAt
                     finalPage traceLimit second))
                 (applyInsertion
                   (atlasActionMap action
                     (normalizePageElementArrowAt
                       finalPage traceLimit first))
                   datum) })
  -> coherenceLaw:(forall object.
       occurrence:PageElement scope object
       -> coherenceArrow:PageElementArrow scope object object
       -> conditions:{() |
            arrowSource coherenceArrow == occurrence
            && arrowTarget coherenceArrow ==
                 normalizePageElementAt finalPage traceLimit occurrence}
       -> datum:cellData object
       -> { proof:() |
            applyInsertion
              (atlasActionMap action
                (normalizePageElementArrowAt
                  finalPage traceLimit coherenceArrow))
              datum
            == datum })
  -> disjointLaw:(forall leftObject rightObject originObject.
       left:PageElement scope leftObject
       -> right:PageElement scope rightObject
       -> leftToOrigin:PageElementArrow scope leftObject originObject
       -> rightToOrigin:PageElementArrow scope rightObject originObject
       -> conditions:{() |
            pageElementPage right == pageElementPage left
            && pageElementPosition right /= pageElementPosition left
            && pageElementPage left <= finalPage
            && arrowSource leftToOrigin == left
            && pageElementPage (arrowTarget leftToOrigin) == 0
            && arrowSource rightToOrigin == right
            && arrowTarget rightToOrigin == arrowTarget leftToOrigin}
       -> leftDatum:cellData leftObject
       -> rightDatum:cellData rightObject
       -> { proof:() |
            applyInsertion
              (atlasActionMap action
                (normalizePageElementArrowAt
                  finalPage traceLimit leftToOrigin))
              leftDatum
            /= applyInsertion
                 (atlasActionMap action
                   (normalizePageElementArrowAt
                     finalPage traceLimit rightToOrigin))
                 rightDatum })
  -> AtlasData scope cellData
@-}
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
