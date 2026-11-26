{-# LANGUAGE CPP #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE RoleAnnotations #-}
#include "../../../LiquidPlugin.h"
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}
{-@ LIQUID "--higherorder" @-}

-- | LiquidHaskell-verified presheaf actions on the Atlas category.
module DataTransformation.Core
  ( presheafIdentity
  , presheafCompose
  , DataTransformationValue
  , DataTransformation
  , dataTransformation
  , mapDataTransformation
  , dataTransformationIdentity
  , dataTransformationComposition
  , DataTransformationNatural
  , dataTransformationNatural
  , mapDataTransformationNatural
  , dataTransformationNaturalNaturality
  , YonedaPresheaf
  , Yoneda (..)
  , yoneda
  , mapYoneda
  , mapYonedaNatural
  , yonedaNaturality
  , yonedaActionAgrees
  ) where

import Atlas.Presheaf
  ( AtlasHom, presheafIdentity, presheafCompose
  , presheafRightIdentity, presheafAssociativity )
import Data.Kind (Type)

-- | Apply an indexed presheaf value family to an Atlas.
type DataTransformationValue (values :: Type -> Type) (atlas :: Type) = values atlas

type YonedaPresheaf represented = Yoneda represented

-- | One value of the representable presheaf @Hom(-, represented)@.
type role Yoneda nominal nominal
data Yoneda (represented :: Type) (atlas :: Type) = Yoneda
  { getYoneda :: AtlasHom atlas represented
  }

-- | The contravariant arrow action of a presheaf, packaged so refinements can
-- refer to its rank-N function through a first-order accessor.
type role DataTransformationAction nominal
data DataTransformationAction (values :: Type -> Type) =
  DataTransformationAction
    (forall source target.
      AtlasHom source target
      -> DataTransformationValue values target
      -> DataTransformationValue values source)

-- ALIGN: PRESHEAF-ACTION-ELIM.
{-@ reflect mapDataTransformationAction @-}
mapDataTransformationAction
  :: DataTransformationAction values
  -> AtlasHom source target
  -> DataTransformationValue values target
  -> DataTransformationValue values source
mapDataTransformationAction
  (DataTransformationAction action) arrow value = action arrow value

-- | A law-bearing presheaf action.
type role DataTransformation nominal
{-@
data DataTransformation values = DataTransformation
  { storedDataTransformationAction :: DataTransformationAction values
  , storedDataTransformationIdentity :: forall object.
      value:DataTransformationValue values object
      -> { proof:() |
           mapDataTransformationAction
             storedDataTransformationAction presheafIdentity value
           == value }
  , storedDataTransformationComposition :: forall source middle target.
      second:AtlasHom middle target
      -> first:AtlasHom source middle
      -> value:DataTransformationValue values target
      -> { proof:() |
           mapDataTransformationAction
             storedDataTransformationAction
             (presheafCompose second first)
             value
           == mapDataTransformationAction
                storedDataTransformationAction first
                (mapDataTransformationAction
                  storedDataTransformationAction second value) }
  }
@-}
data DataTransformation (values :: Type -> Type) = DataTransformation
  (DataTransformationAction values)
  (forall object. DataTransformationValue values object -> ())
  (forall source middle target.
    AtlasHom middle target
    -> AtlasHom source middle
    -> DataTransformationValue values target
    -> ())

-- | Construct a presheaf. LiquidHaskell checks the identity and
-- contravariant-composition equations at every verified call site.
-- ALIGN: PRESHEAF-PACKAGE.
{-@
dataTransformation
  :: actionFunction:(forall source target.
       AtlasHom source target
       -> DataTransformationValue values target
       -> DataTransformationValue values source)
  -> identityLaw:(forall object.
       value:DataTransformationValue values object
       -> { proof:() |
            actionFunction presheafIdentity value == value })
  -> compositionLaw:(forall source middle target.
       second:AtlasHom middle target
       -> first:AtlasHom source middle
       -> value:DataTransformationValue values target
       -> { proof:() |
            actionFunction (presheafCompose second first) value
            == actionFunction first (actionFunction second value) })
  -> DataTransformation values
@-}
dataTransformation
  :: (forall source target.
       AtlasHom source target
       -> DataTransformationValue values target
       -> DataTransformationValue values source)
  -> (forall object. DataTransformationValue values object -> ())
  -> (forall source middle target.
       AtlasHom middle target
       -> AtlasHom source middle
       -> DataTransformationValue values target
       -> ())
  -> DataTransformation values
{-@ reflect dataTransformation @-}
dataTransformation action =
  DataTransformation (DataTransformationAction action)

-- | Apply a DaTra set contravariantly to an Atlas arrow.
-- ALIGN: PRESHEAF-MAP.
{-@ reflect mapDataTransformation @-}
mapDataTransformation
  :: DataTransformation values
  -> AtlasHom source target
  -> DataTransformationValue values target
  -> DataTransformationValue values source
mapDataTransformation (DataTransformation action _ _) =
  mapDataTransformationAction action

-- | Invoke the LiquidHaskell-checked identity law.
-- ALIGN: PRESHEAF-IDENTITY.
{-@
dataTransformationIdentity
  :: transformation:DataTransformation values
  -> value:DataTransformationValue values object
  -> { proof:() |
       mapDataTransformation transformation presheafIdentity value == value }
@-}
dataTransformationIdentity
  :: DataTransformation values
  -> DataTransformationValue values object
  -> ()
dataTransformationIdentity
  (DataTransformation _ identityLaw _) = identityLaw

-- | Invoke the LiquidHaskell-checked contravariant composition law.
-- ALIGN: PRESHEAF-COMPOSITION.
{-@
dataTransformationComposition
  :: transformation:DataTransformation values
  -> second:AtlasHom middle target
  -> first:AtlasHom source middle
  -> value:DataTransformationValue values target
  -> { proof:() |
       mapDataTransformation transformation
         (presheafCompose second first) value
       == mapDataTransformation transformation first
            (mapDataTransformation transformation second value) }
@-}
dataTransformationComposition
  :: DataTransformation values
  -> AtlasHom middle target
  -> AtlasHom source middle
  -> DataTransformationValue values target
  -> ()
dataTransformationComposition
  (DataTransformation _ _ compositionLaw) = compositionLaw

-- | A rank-N component family, packaged so LiquidHaskell can mention its
-- specializations in the naturality equation.
type role DataTransformationComponent nominal nominal
data DataTransformationComponent
  (source :: Type -> Type)
  (target :: Type -> Type) = DataTransformationComponent
  (forall atlas.
    DataTransformationValue source atlas
    -> DataTransformationValue target atlas)

-- ALIGN: PRESHEAF-COMPONENT-ELIM.
{-@ reflect mapDataTransformationComponent @-}
mapDataTransformationComponent
  :: DataTransformationComponent source target
  -> DataTransformationValue source atlas
  -> DataTransformationValue target atlas
mapDataTransformationComponent
  (DataTransformationComponent component) value = component value

-- | A primitive natural transformation checked relative to its exact source
-- and target presheaf actions.
type role DataTransformationNatural nominal nominal
{-@
data DataTransformationNatural source target = DataTransformationNatural
  { storedNaturalSource :: DataTransformation source
  , storedNaturalTarget :: DataTransformation target
  , storedNaturalComponent :: DataTransformationComponent source target
  , storedNaturality :: forall sourceAtlas targetAtlas.
      arrow:AtlasHom sourceAtlas targetAtlas
      -> value:DataTransformationValue source targetAtlas
      -> { proof:() |
           mapDataTransformationComponent storedNaturalComponent
             (mapDataTransformation storedNaturalSource arrow value)
           == mapDataTransformation storedNaturalTarget arrow
                (mapDataTransformationComponent storedNaturalComponent value) }
  }
@-}
data DataTransformationNatural
  (source :: Type -> Type)
  (target :: Type -> Type) = DataTransformationNatural
    (DataTransformation source)
    (DataTransformation target)
    (DataTransformationComponent source target)
    (forall sourceAtlas targetAtlas.
      AtlasHom sourceAtlas targetAtlas
      -> DataTransformationValue source targetAtlas
      -> ())

-- | Check one primitive natural transformation.
-- ALIGN: PRESHEAF-NATURAL-PACKAGE.
{-@
dataTransformationNatural
  :: sourceTransformation:DataTransformation source
  -> targetTransformation:DataTransformation target
  -> componentFunction:(forall atlas.
       DataTransformationValue source atlas
       -> DataTransformationValue target atlas)
  -> naturalityLaw:(forall sourceAtlas targetAtlas.
       arrow:AtlasHom sourceAtlas targetAtlas
       -> value:DataTransformationValue source targetAtlas
       -> { proof:() |
            componentFunction
              (mapDataTransformation sourceTransformation arrow value)
            == mapDataTransformation targetTransformation arrow
                 (componentFunction value) })
  -> DataTransformationNatural source target
@-}
dataTransformationNatural
  :: DataTransformation source
  -> DataTransformation target
  -> (forall atlas.
       DataTransformationValue source atlas
       -> DataTransformationValue target atlas)
  -> (forall sourceAtlas targetAtlas.
       AtlasHom sourceAtlas targetAtlas
       -> DataTransformationValue source targetAtlas
       -> ())
  -> DataTransformationNatural source target
{-@ reflect dataTransformationNatural @-}
dataTransformationNatural source target component =
  DataTransformationNatural
    source
    target
    (DataTransformationComponent component)

-- | Evaluate one component of a checked primitive natural transformation.
-- ALIGN: PRESHEAF-NATURAL-MAP.
{-@ reflect mapDataTransformationNatural @-}
mapDataTransformationNatural
  :: DataTransformationNatural source target
  -> DataTransformationValue source atlas
  -> DataTransformationValue target atlas
mapDataTransformationNatural
  (DataTransformationNatural _ _ component _) value =
    mapDataTransformationComponent component value

-- | Invoke a primitive's LiquidHaskell-checked naturality square.
-- ALIGN: PRESHEAF-NATURALITY.
{-@
dataTransformationNaturalNaturality
  :: natural:DataTransformationNatural source target
  -> arrow:AtlasHom sourceAtlas targetAtlas
  -> value:DataTransformationValue source targetAtlas
  -> { proof:() |
       mapDataTransformationNatural natural
         (mapDataTransformation (storedNaturalSource natural) arrow value)
       == mapDataTransformation (storedNaturalTarget natural) arrow
            (mapDataTransformationNatural natural value) }
@-}
dataTransformationNaturalNaturality
  :: DataTransformationNatural source target
  -> AtlasHom sourceAtlas targetAtlas
  -> DataTransformationValue source targetAtlas
  -> ()
dataTransformationNaturalNaturality
  (DataTransformationNatural _ _ _ naturality) arrow value =
    naturality arrow value

-- ALIGN: YONEDA-ACTION-INTERPRETATION.
-- Fix the represented Atlas before abstracting over the varying endpoints;
-- this ordering retains the action's refinement in the rank-N package.
{-@ reflect mapYoneda @-}
mapYoneda
  :: forall represented source target. AtlasHom source target
  -> Yoneda represented target
  -> Yoneda represented source
mapYoneda arrow (Yoneda representedArrow) =
  Yoneda (presheafCompose representedArrow arrow)

{-@
yonedaIdentity
  :: value:Yoneda represented atlas
  -> { proof:() | mapYoneda presheafIdentity value == value }
@-}
-- ALIGN: YONEDA-IDENTITY.

yonedaIdentity :: forall represented atlas. Yoneda represented atlas -> ()
yonedaIdentity (Yoneda representedArrow) =
  presheafRightIdentity representedArrow

{-@
yonedaComposition
  :: second:AtlasHom middle target
  -> first:AtlasHom source middle
  -> value:Yoneda represented target
  -> { proof:() |
       mapYoneda (presheafCompose second first) value
       == mapYoneda first (mapYoneda second value) }
@-}
-- ALIGN: YONEDA-COMPOSITION.

yonedaComposition
  :: forall represented source middle target. AtlasHom middle target
  -> AtlasHom source middle
  -> Yoneda represented target
  -> ()
yonedaComposition second first (Yoneda representedArrow) =
  presheafAssociativity representedArrow second first

-- | The representable action with its checked identity and composition laws.
{-@ reflect yoneda @-}
-- ALIGN: YONEDA-PACKAGE.

yoneda :: DataTransformation (YonedaPresheaf represented)
yoneda =
  DataTransformation
    (DataTransformationAction mapYoneda)
    yonedaIdentity
    yonedaComposition

-- ALIGN: YONEDA-COMPONENT-INTERPRETATION.
{-@ reflect mapYonedaNatural @-}
mapYonedaNatural
  :: AtlasHom representedSource representedTarget
  -> Yoneda representedSource atlas
  -> Yoneda representedTarget atlas
mapYonedaNatural arrow (Yoneda representedArrow) =
  Yoneda (presheafCompose arrow representedArrow)

{-@
yonedaNaturality
  :: representedArrow:AtlasHom representedSource representedTarget
  -> arrow:AtlasHom sourceAtlas targetAtlas
  -> value:Yoneda representedSource targetAtlas
  -> { proof:() |
       mapYonedaNatural representedArrow (mapYoneda arrow value)
       == mapYoneda arrow (mapYonedaNatural representedArrow value) }
@-}
-- ALIGN: YONEDA-NATURALITY.

yonedaNaturality
  :: AtlasHom representedSource representedTarget
  -> AtlasHom sourceAtlas targetAtlas
  -> Yoneda representedSource targetAtlas
  -> ()
yonedaNaturality representedArrow arrow (Yoneda value) =
  presheafAssociativity representedArrow value arrow

-- | Recover the concrete representable action across the public package.
-- ALIGN: YONEDA-PACKAGE-ACTION.
{-@ yonedaActionAgrees :: arrow:AtlasHom source target -> value:Yoneda represented target
      -> {mapDataTransformation yoneda arrow value == mapYoneda arrow value} @-}
yonedaActionAgrees :: AtlasHom source target -> Yoneda represented target -> ()
yonedaActionAgrees _ _ = ()
