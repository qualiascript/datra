{-# LANGUAGE CPP #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE RoleAnnotations #-}
#include "../../../../LiquidPlugin.h"
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}
{-@ LIQUID "--higherorder" @-}

-- | Checked constant carriers, their executable inverses, and value-level laws.
module DomanialInclusion.Data
  ( DominionCellData
  , constantDominion
  , identityDominionCellInsertion
  , identityCellMap
  , identityCellPreimage
  , identityCellMapIdentity
  , identityCellMapComposition
  , dominionCellData
  , dominionCellDataValue
  , dominionCellDataReconstruct
  , mapDominionCellData
  , dominionFunctorIdentityValue
  , dominionFunctorCompositionValue
  , domIncHomToValue
  , domIncHomFromValue
  , domIncHomLeftInverseValue
  , domIncHomRightInverseValue
  , domIncHomNaturalityLeftValue
  , domIncHomNaturalityRightValue
  , dominionCellProjection
  ) where

import Data.Kind (Type)
import DomanialInsertion.Core (DomanialInsertion (..), domanialInsertion)
import Dominion (Dominion, dominion, rank, unrank, dominionCoherence)
import Numeric.Natural (Natural)

{-@ opaque-reflect rank @-}
{-@ opaque-reflect unrank @-}

-- | The constant data family on the one cell of the included atlas.
type role DominionCellData nominal nominal
data DominionCellData a (object :: Type) = DominionCellData a
  deriving (Eq, Show)

{-@ reflect dominionCellData @-}
dominionCellData :: a -> DominionCellData a object
dominionCellData = DominionCellData

{-@ reflect dominionCellDataValue @-}
dominionCellDataValue :: DominionCellData a object -> a
dominionCellDataValue (DominionCellData value) = value

-- | Projection retains the entire constant datum, including its cell index.
-- ALIGN: DOMINC-CELL-RECONSTRUCTION.
{-@ dominionCellDataReconstruct :: datum:DominionCellData a object
      -> {dominionCellData (dominionCellDataValue datum) == datum} @-}
dominionCellDataReconstruct :: DominionCellData a object -> ()
dominionCellDataReconstruct (DominionCellData _) = ()

{-@ reflect mapDominionCellData @-}
mapDominionCellData
  :: (a -> b)
  -> DominionCellData a sourceObject
  -> DominionCellData b targetObject
mapDominionCellData function (DominionCellData value) =
  DominionCellData (function value)

{-@ reflect composeValues @-}
composeValues :: (b -> c) -> (a -> b) -> a -> c
composeValues after before value = after (before value)

{-@ reflect identityValue @-}
identityValue :: a -> a
identityValue value = value

{-@
dominionFunctorIdentityValue
  :: value:DominionCellData a object
  -> { proof:() | mapDominionCellData identityValue value == value }
@-}
-- ALIGN: DOMINC-FUNCTOR-IDENTITY.
dominionFunctorIdentityValue :: DominionCellData a object -> ()
dominionFunctorIdentityValue (DominionCellData _) = ()

{-@
dominionFunctorCompositionValue
  :: first:(a -> b)
  -> second:(b -> c)
  -> value:DominionCellData a sourceObject
  -> { proof:() |
       mapDominionCellData second (mapDominionCellData first value)
         == mapDominionCellData (composeValues second first) value }
@-}
-- ALIGN: DOMINC-FUNCTOR-COMPOSITION.
dominionFunctorCompositionValue
  :: (a -> b)
  -> (b -> c)
  -> DominionCellData a sourceObject
  -> ()
dominionFunctorCompositionValue _ _ (DominionCellData _) = ()

-- | Preserve the complete executable Dominion while wrapping its carrier.
-- ALIGN: DOMINC-CONSTANT-DOMINION.
{-@ constantDominion :: owner:Dominion a
      -> {wrapped:Dominion (DominionCellData a object) |
           rank wrapped == constantCellRank owner && unrank wrapped == constantCellUnrank owner} @-}
constantDominion :: Dominion a -> Dominion (DominionCellData a object)
constantDominion owner = dominion (constantCellRank owner) (constantCellUnrank owner)
  (constantCellRoundTrip owner)

{-@ reflect constantCellRank @-}
constantCellRank :: Dominion a -> DominionCellData a object -> Natural
constantCellRank owner (DominionCellData value) = rank owner value

{-@ reflect constantCellUnrank @-}
constantCellUnrank :: Dominion a -> Natural -> Maybe (DominionCellData a object)
constantCellUnrank owner index = case unrank owner index of
  Nothing -> Nothing
  Just value -> Just (DominionCellData value)

-- ALIGN: DOMINC-CONSTANT-ROUNDTRIP.
{-@ constantCellRoundTrip :: owner:Dominion a -> datum:DominionCellData a object
      -> {constantCellUnrank owner (constantCellRank owner datum) == Just datum} @-}
constantCellRoundTrip :: Dominion a -> DominionCellData a object -> ()
constantCellRoundTrip owner (DominionCellData value) = dominionCoherence owner value

-- | The constant action preserves the underlying value in both directions.
-- ALIGN: DOMINC-IDENTITY-INSERTION.
{-@ identityDominionCellInsertion :: {value:DomanialInsertion (DominionCellData a source) (DominionCellData a target) |
      applyInsertion value == identityCellMap && preimage value == identityCellPreimage} @-}
identityDominionCellInsertion :: DomanialInsertion (DominionCellData a source) (DominionCellData a target)
identityDominionCellInsertion = domanialInsertion identityCellMap identityCellPreimage identityCellRoundTrip

{-@ reflect identityCellMap @-}
identityCellMap :: DominionCellData a source -> DominionCellData a target
identityCellMap (DominionCellData value) = DominionCellData value

{-@ identityCellMapIdentity :: datum:DominionCellData a object
      -> {identityCellMap datum == datum} @-}
identityCellMapIdentity :: DominionCellData a object -> ()
identityCellMapIdentity (DominionCellData _) = ()

{-@ identityCellMapComposition :: datum:DominionCellData a object
      -> {identityCellMap (identityCellMap datum) == identityCellMap datum} @-}
identityCellMapComposition :: DominionCellData a object -> ()
identityCellMapComposition (DominionCellData _) = ()

{-@ reflect identityCellPreimage @-}
identityCellPreimage :: DominionCellData a target -> Maybe (DominionCellData a source)
identityCellPreimage datum = Just (identityCellMap datum)

-- ALIGN: DOMINC-IDENTITY-ROUNDTRIP.
{-@ identityCellRoundTrip :: datum:DominionCellData a source
      -> {identityCellPreimage (identityCellMap datum) == Just datum} @-}
identityCellRoundTrip :: DominionCellData a source -> ()
identityCellRoundTrip (DominionCellData _) = ()

-- These two maps are the data components of the hom-set correspondence.
{-@ reflect domIncHomToValue @-}
domIncHomToValue :: (DominionCellData a object -> b) -> a -> b
domIncHomToValue function value = function (DominionCellData value)

{-@ reflect domIncHomFromValue @-}
domIncHomFromValue :: (a -> b) -> DominionCellData a object -> b
domIncHomFromValue function (DominionCellData value) = function value

{-@
domIncHomLeftInverseValue
  :: function:(DominionCellData a object -> b)
  -> value:DominionCellData a object
  -> { proof:() |
       domIncHomFromValue (domIncHomToValue function) value
         == function value }
@-}
-- ALIGN: DOMINC-HOM-LEFT-INVERSE.
domIncHomLeftInverseValue
  :: (DominionCellData a object -> b)
  -> DominionCellData a object
  -> ()
domIncHomLeftInverseValue _ (DominionCellData _) = ()

{-@
domIncHomRightInverseValue
  :: function:(a -> b)
  -> value:a
  -> { proof:() |
       domIncHomToValue (domIncHomFromValue function) value
         == function value }
@-}
-- ALIGN: DOMINC-HOM-RIGHT-INVERSE.
domIncHomRightInverseValue :: (a -> b) -> a -> ()
domIncHomRightInverseValue _ _ = ()

{-@
domIncHomNaturalityLeftValue
  :: before:(a' -> a)
  -> function:(DominionCellData a object -> b)
  -> value:a'
  -> { proof:() |
       domIncHomToValue
         (composeValues function (mapDominionCellData before)) value
         == domIncHomToValue function (before value) }
@-}
-- ALIGN: DOMINC-HOM-NATURALITY-LEFT.
domIncHomNaturalityLeftValue
  :: (a' -> a)
  -> (DominionCellData a object -> b)
  -> a'
  -> ()
domIncHomNaturalityLeftValue _ _ _ = ()

{-@
domIncHomNaturalityRightValue
  :: function:(DominionCellData a object -> b)
  -> after:(b -> c)
  -> value:a
  -> { proof:() |
       domIncHomToValue (composeValues after function) value
         == after (domIncHomToValue function value) }
@-}
-- ALIGN: DOMINC-HOM-NATURALITY-RIGHT.
domIncHomNaturalityRightValue
  :: (DominionCellData a object -> b)
  -> (b -> c)
  -> a
  -> ()
domIncHomNaturalityRightValue _ _ _ = ()

-- | The data wrapper and its projection are an explicit carrier equivalence.
dominionCellProjection :: DomanialInsertion (DominionCellData a object) a
dominionCellProjection =
  domanialInsertion
    dominionCellDataValue
    dominionCellProjectionPreimage
    dominionCellProjectionRoundTrip

{-@ reflect dominionCellProjectionPreimage @-}
dominionCellProjectionPreimage :: a -> Maybe (DominionCellData a object)
dominionCellProjectionPreimage value = Just (dominionCellData value)

{-@ dominionCellProjectionRoundTrip :: value:DominionCellData a object
      -> {dominionCellProjectionPreimage (dominionCellDataValue value) == Just value} @-}
dominionCellProjectionRoundTrip :: DominionCellData a object -> ()
dominionCellProjectionRoundTrip (DominionCellData _) = ()
