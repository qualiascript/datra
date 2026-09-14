{-# LANGUAGE CPP #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE RoleAnnotations #-}
{-# OPTIONS_GHC -Wno-unused-top-binds #-}
#include "../../../../LiquidPlugin.h"
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}
{-@ LIQUID "--higherorder" @-}

-- | Proof-transparent carrier operations for the Domanial Inclusion.
module DomanialInclusion.LiquidInternal
  ( DominionCellData
  , dominionCellData
  , dominionCellDataValue
  , mapDominionCellData
  , dominionFunctorIdentityValue
  , dominionFunctorCompositionValue
  , domIncHomToValue
  , domIncHomFromValue
  , domIncHomLeftInverseValue
  , domIncHomRightInverseValue
  , domIncHomNaturalityLeftValue
  , domIncHomNaturalityRightValue
  ) where

import Data.Kind (Type)

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
dominionFunctorCompositionValue
  :: (a -> b)
  -> (b -> c)
  -> DominionCellData a sourceObject
  -> ()
dominionFunctorCompositionValue _ _ (DominionCellData _) = ()

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
domIncHomNaturalityRightValue
  :: (DominionCellData a object -> b)
  -> (b -> c)
  -> a
  -> ()
domIncHomNaturalityRightValue _ _ _ = ()
