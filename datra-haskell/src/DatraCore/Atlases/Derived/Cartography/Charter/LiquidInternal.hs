{-# LANGUAGE CPP #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE RoleAnnotations #-}
{-# LANGUAGE TypeFamilies #-}
{-# OPTIONS_GHC -Wno-unused-top-binds #-}
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

import Atlas (AtlasObjectCellData)
import Data.Kind (Type)

-- | A datum retained by the charted Atlas. Coverage is enforced by the
-- charted dominion and by the smart operations in "Charter.Internal"; it is
-- proof-irrelevant at runtime, so the representation stores only the original
-- datum, exactly as Lean's subtype coercion does computationally.
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
chartHomNaturalityRightValue
  :: forall sourceValue middle middleObject target targetObject.
     (sourceValue -> AtlasObjectCellData middle middleObject)
  -> (AtlasObjectCellData middle middleObject
      -> AtlasObjectCellData target targetObject)
  -> sourceValue
  -> ()
chartHomNaturalityRightValue _ _ _ = ()
