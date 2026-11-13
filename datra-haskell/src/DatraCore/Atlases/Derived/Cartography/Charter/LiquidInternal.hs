{-# LANGUAGE CPP #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE RoleAnnotations #-}
{-# LANGUAGE TypeFamilies #-}
-- GHC does not count imports referenced only by refinement signatures.
{-# OPTIONS_GHC -Wno-unused-top-binds -Wno-unused-imports #-}
#include "../../../../LiquidPlugin.h"
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}
{-@ LIQUID "--higherorder" @-}

-- | Proof-transparent carrier operations used by the Charter functor.
--
-- This module deliberately uses no @data@ declaration. The charted carrier is
-- a zero-cost newtype, while the four equations below are the pointwise data
-- equations in Lean's two inverse and two naturality proofs for
-- @chartHomEquiv@.
module Charter.LiquidInternal
  ( ChartedCellData
  , chartCellData
  , chartCounitInsertion
  , chartMapInsertion
  , chartedCellData
  , chartedCellDataValue
  , mapChartedCellData
  , charterIdentityValue
  , charterCompositionValue
  , chartHomToValue
  , chartHomFromValue
  , chartHomLeftInverseValue
  , chartHomRightInverseValue
  , chartHomNaturalityLeftValue
  , chartHomNaturalityRightValue
  ) where

import Atlas (Atlas, AtlasObject, AtlasObjectCellData)
import AtlasCoveredPageElement.Internal (AtlasCoverageWitness, coverageWitnessCovers)
import DomanialInsertion
  ( DomanialInsertion, domanialInsertion, applyInsertion, preimage, insertionLeftInverse )
import PageElements (PageElement)
import Data.Kind (Type)

-- | A datum retained by the charted Atlas. Coverage at its selected page
-- occurrence is a constructor obligation. The hidden wrapper stores only the
-- original datum; the coverage proof is erased at runtime.
type role ChartedCellData nominal nominal
newtype ChartedCellData atlasObject (object :: Type) =
  ChartedCellData (AtlasObjectCellData atlasObject object)

{-@ reflect chartedCellDataValue @-}
chartedCellDataValue
  :: ChartedCellData atlasObject object
  -> AtlasObjectCellData atlasObject object
chartedCellDataValue (ChartedCellData value) = value

{-@ reflect chartedCellData @-}
chartedCellData
  :: AtlasObjectCellData atlasObject object
  -> ChartedCellData atlasObject object
chartedCellData = ChartedCellData

-- | Introduce a charted datum from checked coverage evidence.
{-@
chartCellData
  :: valueAtlas:Atlas atlasScope scope cellData origin final
  -> occurrence:PageElement scope object
  -> datum:cellData object
  -> witness:AtlasCoverageWitness (AtlasObject atlasScope scope cellData)
  -> {proof:() | coverageWitnessCovers valueAtlas occurrence datum witness}
  -> ChartedCellData (AtlasObject atlasScope scope cellData) object
@-}
-- ALIGN: CHARTER-CELL-CONSTRUCTOR.
chartCellData
  :: Atlas atlasScope scope cellData origin final
  -> PageElement scope object
  -> cellData object
  -> AtlasCoverageWitness (AtlasObject atlasScope scope cellData)
  -> ()
  -> ChartedCellData (AtlasObject atlasScope scope cellData) object
chartCellData _ _ datum _ proof = proof `seq` chartedCellData datum

-- | The counit needs a partial inverse on every original datum. Searching for
-- coverage cannot supply that operation on uncovered data.
{-@
chartCounitInsertion
  :: backward:(AtlasObjectCellData atlasObject object -> Maybe (ChartedCellData atlasObject object))
  -> (charted:ChartedCellData atlasObject object ->
       {backward (chartedCellDataValue charted) == Just charted})
  -> DomanialInsertion (ChartedCellData atlasObject object) (AtlasObjectCellData atlasObject object)
@-}
-- ALIGN: CHARTER-COUNIT-INSERTION.
-- ALIGN: CHARTER-COUNIT-INTERPRETATION.
chartCounitInsertion
  :: (AtlasObjectCellData atlasObject object -> Maybe (ChartedCellData atlasObject object))
  -> (ChartedCellData atlasObject object -> ())
  -> DomanialInsertion (ChartedCellData atlasObject object) (AtlasObjectCellData atlasObject object)
chartCounitInsertion backward leftInverse =
  domanialInsertion chartedCellDataValue backward leftInverse

-- | Restrict a complete component to covered data. The source inverse checks
-- coverage of every candidate, including candidates outside the original image.
{-@
chartMapInsertion
  :: original:DomanialInsertion (AtlasObjectCellData source sourceObject)
       (AtlasObjectCellData target targetObject)
  -> backward:(AtlasObjectCellData source sourceObject -> Maybe (ChartedCellData source sourceObject))
  -> (charted:ChartedCellData source sourceObject ->
       {backward (chartedCellDataValue charted) == Just charted})
  -> DomanialInsertion (ChartedCellData source sourceObject) (ChartedCellData target targetObject)
@-}
-- ALIGN: CHARTER-MAP-INSERTION.
-- ALIGN: CHARTER-MAP-INVERSE.
chartMapInsertion
  :: DomanialInsertion (AtlasObjectCellData source sourceObject) (AtlasObjectCellData target targetObject)
  -> (AtlasObjectCellData source sourceObject -> Maybe (ChartedCellData source sourceObject))
  -> (ChartedCellData source sourceObject -> ())
  -> DomanialInsertion (ChartedCellData source sourceObject) (ChartedCellData target targetObject)
chartMapInsertion original backward leftInverse =
  domanialInsertion
    (mapChartedCellData (applyInsertion original))
    (\target -> case preimage original (chartedCellDataValue target) of
      Nothing -> Nothing
      Just candidate -> backward candidate)
    (\source -> insertionLeftInverse original (chartedCellDataValue source) `seq` leftInverse source)

{-@ reflect mapChartedCellData @-}
mapChartedCellData
  :: (AtlasObjectCellData source sourceObject
      -> AtlasObjectCellData target targetObject)
  -> ChartedCellData source sourceObject
  -> ChartedCellData target targetObject
mapChartedCellData function (ChartedCellData value) =
  ChartedCellData (function value)

{-@ reflect composeValues @-}
composeValues :: (b -> c) -> (a -> b) -> a -> c
composeValues after before value = after (before value)

{-@ reflect identityValue @-}
identityValue :: a -> a
identityValue value = value

-- | Pointwise identity law for the Charter arrow action.
{-@
charterIdentityValue
  :: value:ChartedCellData atlasObject object
  -> { proof:() |
       mapChartedCellData identityValue value == value }
@-}
-- ALIGN: CHARTER-FUNCTOR-IDENTITY.
charterIdentityValue
  :: ChartedCellData atlasObject object
  -> ()
charterIdentityValue _ = ()

-- | Pointwise composition law for the Charter arrow action.
{-@
charterCompositionValue
  :: first:(AtlasObjectCellData source sourceObject
       -> AtlasObjectCellData middle middleObject)
  -> second:(AtlasObjectCellData middle middleObject
       -> AtlasObjectCellData target targetObject)
  -> value:ChartedCellData source sourceObject
  -> { proof:() |
       mapChartedCellData second (mapChartedCellData first value)
         == mapChartedCellData (composeValues second first) value }
@-}
-- ALIGN: CHARTER-FUNCTOR-COMPOSITION.
charterCompositionValue
  :: forall source sourceObject middle middleObject target targetObject.
     (AtlasObjectCellData source sourceObject
      -> AtlasObjectCellData middle middleObject)
  -> (AtlasObjectCellData middle middleObject
      -> AtlasObjectCellData target targetObject)
  -> ChartedCellData source sourceObject
  -> ()
charterCompositionValue _ _ _ = ()

-- | Data component of @chartLift@: apply the original component and retain
-- its covered result in the charted target.
{-@ reflect chartHomToValue @-}
chartHomToValue
  :: (sourceValue -> AtlasObjectCellData target targetObject)
  -> sourceValue
  -> ChartedCellData target targetObject
chartHomToValue function value = ChartedCellData (function value)

-- | Data component of composition with the chart counit.
{-@ reflect chartHomFromValue @-}
chartHomFromValue
  :: (sourceValue -> ChartedCellData target targetObject)
  -> sourceValue
  -> AtlasObjectCellData target targetObject
chartHomFromValue function value =
  chartedCellDataValue (function value)

-- | Lean's @chartHomEquiv.left_inv@, pointwise on cell data.
{-@
chartHomLeftInverseValue
  :: function:(sourceValue -> AtlasObjectCellData target targetObject)
  -> value:sourceValue
  -> { proof:() |
       chartHomFromValue (chartHomToValue function) value
         == function value }
@-}
-- ALIGN: CHARTER-HOM-LEFT-INVERSE.
chartHomLeftInverseValue
  :: forall sourceValue target targetObject.
     (sourceValue -> AtlasObjectCellData target targetObject)
  -> sourceValue
  -> ()
chartHomLeftInverseValue _ _ = ()

-- | Lean's @chartHomEquiv.right_inv@, pointwise on cell data. Newtype eta is
-- the Haskell counterpart of Lean's final @Subtype.ext; proof evidence is not
-- part of the runtime equality.
{-@
chartHomRightInverseValue
  :: function:(sourceValue -> ChartedCellData target targetObject)
  -> value:sourceValue
  -> { proof:() |
       chartHomToValue (chartHomFromValue function) value
         == function value }
@-}
-- ALIGN: CHARTER-HOM-RIGHT-INVERSE.
chartHomRightInverseValue
  :: forall sourceValue target targetObject.
     (sourceValue -> ChartedCellData target targetObject)
  -> sourceValue
  -> ()
chartHomRightInverseValue _ _ = ()

-- | Naturality of @chartHomEquiv@ in its Atlas-map argument: Charter
-- commutes with precomposition.
{-@
chartHomNaturalityLeftValue
  :: before:(firstValue -> secondValue)
  -> function:(secondValue -> AtlasObjectCellData target targetObject)
  -> value:firstValue
  -> { proof:() |
       chartHomToValue (composeValues function before) value
         == chartHomToValue function (before value) }
@-}
-- ALIGN: CHARTER-HOM-NATURALITY-LEFT.
chartHomNaturalityLeftValue
  :: forall firstValue secondValue target targetObject.
     (firstValue -> secondValue)
  -> (secondValue -> AtlasObjectCellData target targetObject)
  -> firstValue
  -> ()
chartHomNaturalityLeftValue _ _ _ = ()

-- | Naturality in the Atlas-transversal argument: Charter commutes with
-- postcomposition.
{-@
chartHomNaturalityRightValue
  :: function:(sourceValue -> AtlasObjectCellData middle middleObject)
  -> after:(AtlasObjectCellData middle middleObject
       -> AtlasObjectCellData target targetObject)
  -> value:sourceValue
  -> { proof:() |
       chartHomToValue (composeValues after function) value
         == mapChartedCellData after
              (chartHomToValue function value) }
@-}
-- ALIGN: CHARTER-HOM-NATURALITY-RIGHT.
chartHomNaturalityRightValue
  :: forall sourceValue middle middleObject target targetObject.
     (sourceValue -> AtlasObjectCellData middle middleObject)
  -> (AtlasObjectCellData middle middleObject
      -> AtlasObjectCellData target targetObject)
  -> sourceValue
  -> ()
chartHomNaturalityRightValue _ _ _ = ()
