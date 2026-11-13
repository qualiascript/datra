{-# LANGUAGE CPP #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE RoleAnnotations #-}
{-# LANGUAGE TypeFamilyDependencies #-}
#include "../../../LiquidPlugin.h"
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}
{-@ LIQUID "--higherorder" @-}
-- The endpoints are phantom in this proof-only wrapper. The Lean erasure is
-- injective at each pair of endpoints; no AtlasHom indices are erased.
{-@ embed AtlasEquality * as TypeEquality @-}

-- | LiquidHaskell-verified presheaf actions on the Atlas category.
module DataTransformation.LiquidInternal
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
  , yonedaNatural
  ) where

import Atlas.Morphism.Internal (AtlasHom (..), AtlasEquality (..))
import Data.Kind (Type)
import Data.Type.Equality ((:~:) (Refl))

-- | Interpret a defunctionalized presheaf value-family symbol at an Atlas.
type family DataTransformationValue
  (values :: Type)
  (atlas :: Type) = (value :: Type) | value -> values atlas

-- | The value-family symbol of the representable presheaf.
data YonedaPresheaf (represented :: Type)

-- | One value of the representable presheaf @Hom(-, represented)@.
type role Yoneda nominal nominal
data Yoneda (represented :: Type) (atlas :: Type) = Yoneda
  { getYoneda :: AtlasHom atlas represented
  }

type instance
  DataTransformationValue (YonedaPresheaf represented) atlas =
    Yoneda represented atlas

-- A polymorphic nullary value must be inlined into refinement expressions.
{-@ inline presheafIdentity @-}
presheafIdentity :: AtlasHom object object
presheafIdentity = IdentityAtlasHom (AtlasEquality Refl)

-- ALIGN: ATLASHOM-IDENTITY-WITNESS.
{-@ reflect presheafCompose @-}
presheafCompose
  :: AtlasHom middle target
  -> AtlasHom source middle
  -> AtlasHom source target
presheafCompose second (IdentityAtlasHom (AtlasEquality Refl)) = second
presheafCompose second (CompositeAtlasHom middle first) =
  CompositeAtlasHom (presheafCompose second middle) first
presheafCompose second first@(PrimitiveAtlasHom _ _ _) =
  CompositeAtlasHom second first

{-@
presheafRightIdentity
  :: arrow:AtlasHom source target
  -> { proof:() |
       presheafCompose arrow presheafIdentity == arrow }
@-}
-- ALIGN: ATLASHOM-RIGHT-IDENTITY.

presheafRightIdentity :: AtlasHom source target -> ()
presheafRightIdentity (IdentityAtlasHom (AtlasEquality Refl)) = ()
presheafRightIdentity (PrimitiveAtlasHom _ _ _) = ()
presheafRightIdentity (CompositeAtlasHom _ _) = ()

{-@
equalityUnique
  :: first:AtlasEquality a b
  -> second:AtlasEquality c d
  -> { first == second }
@-}
-- ALIGN: ATLAS-EQUALITY-ERASURE-INJECTIVE.
-- ALIGN: ATLAS-EQUALITY-UNIQUE.
equalityUnique :: AtlasEquality a b -> AtlasEquality c d -> ()
equalityUnique (AtlasEquality Refl) (AtlasEquality Refl) = ()

{-@
presheafAssociativity
  :: third:AtlasHom secondMiddle target
  -> second:AtlasHom firstMiddle secondMiddle
  -> first:AtlasHom source firstMiddle
  -> { proof:() |
       presheafCompose third (presheafCompose second first)
       == presheafCompose (presheafCompose third second) first }
@-}
-- ALIGN: ATLASHOM-ASSOC.

presheafAssociativity
  :: AtlasHom secondMiddle target
  -> AtlasHom firstMiddle secondMiddle
  -> AtlasHom source firstMiddle
  -> ()
presheafAssociativity third second (IdentityAtlasHom equality@(AtlasEquality Refl)) =
  equalityUnique equality (AtlasEquality Refl :: AtlasEquality () ()) `seq`
  presheafRightIdentity second `seq`
    presheafRightIdentity (presheafCompose third second)
presheafAssociativity _ _ (PrimitiveAtlasHom _ _ _) = ()
presheafAssociativity third second
  (CompositeAtlasHom middle first) =
    presheafAssociativity third second middle `seq` first `seq` ()

-- | The contravariant arrow action of a presheaf, packaged so refinements can
-- refer to its rank-N function through a first-order accessor.
type role DataTransformationAction nominal
data DataTransformationAction (values :: Type) =
  DataTransformationAction
    (forall source target.
      AtlasHom source target
      -> DataTransformationValue values target
      -> DataTransformationValue values source)

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
data DataTransformation (values :: Type) = DataTransformation
  (DataTransformationAction values)
  (forall object. DataTransformationValue values object -> ())
  (forall source middle target.
    AtlasHom middle target
    -> AtlasHom source middle
    -> DataTransformationValue values target
    -> ())

-- | Construct a presheaf. LiquidHaskell checks the identity and
-- contravariant-composition equations at every verified call site.
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
dataTransformation action =
  DataTransformation (DataTransformationAction action)

-- | Apply a DaTra set contravariantly to an Atlas arrow.
{-@ reflect mapDataTransformation @-}
mapDataTransformation
  :: DataTransformation values
  -> AtlasHom source target
  -> DataTransformationValue values target
  -> DataTransformationValue values source
mapDataTransformation (DataTransformation action _ _) =
  mapDataTransformationAction action

-- | Invoke the LiquidHaskell-checked identity law.
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
  (source :: Type)
  (target :: Type) = DataTransformationComponent
  (forall atlas.
    DataTransformationValue source atlas
    -> DataTransformationValue target atlas)

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
  (source :: Type)
  (target :: Type) = DataTransformationNatural
    (DataTransformation source)
    (DataTransformation target)
    (DataTransformationComponent source target)
    (forall sourceAtlas targetAtlas.
      AtlasHom sourceAtlas targetAtlas
      -> DataTransformationValue source targetAtlas
      -> ())

-- | Check one primitive natural transformation.
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
dataTransformationNatural source target component =
  DataTransformationNatural
    source
    target
    (DataTransformationComponent component)

-- | Evaluate one component of a checked primitive natural transformation.
{-@ reflect mapDataTransformationNatural @-}
mapDataTransformationNatural
  :: DataTransformationNatural source target
  -> DataTransformationValue source atlas
  -> DataTransformationValue target atlas
mapDataTransformationNatural
  (DataTransformationNatural _ _ component _) value =
    mapDataTransformationComponent component value

-- | Invoke a primitive's LiquidHaskell-checked naturality square.
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
{-@ reflect mapYoneda @-}
mapYoneda
  :: AtlasHom source target
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

yonedaIdentity :: Yoneda represented atlas -> ()
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
  :: AtlasHom middle target
  -> AtlasHom source middle
  -> Yoneda represented target
  -> ()
yonedaComposition second first (Yoneda representedArrow) =
  presheafAssociativity representedArrow second first

-- | The LiquidHaskell-checked Yoneda presheaf represented by an Atlas.
-- LiquidHaskell checks 'yonedaIdentity' and 'yonedaComposition' above, but
-- LiquidHaskell 0.9.14.1.1 cannot propagate those refinements when the
-- rank-N functions are stored in 'DataTransformationAction'. Attempts to
-- replace the defunctionalized family by a higher-kinded family verify this
-- package, but then fail in 'yonedaNatural': GHC 9.14 emits coercions between
-- a partially applied 'Yoneda' constructor and its applied value type, which
-- Liquid's sort checker cannot unify. Keep this assumption until that
-- higher-rank/type-family packaging limitation is fixed upstream.
{-@
assume yoneda
  :: DataTransformation (YonedaPresheaf represented)
@-}
{-@ ignore yoneda @-}
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

-- | The checked natural transformation induced by Yoneda on an Atlas arrow.
-- The pointwise theorem 'yonedaNaturality' is verified. What remains assumed
-- is only its storage in the rank-N 'DataTransformationComponent': on GHC
-- 9.14, both the defunctionalized encoding and the higher-kinded alternative
-- produce coercion terms that LiquidHaskell either loses at the constructor
-- boundary or rejects while elaborating the naturality equality.
{-@
assume yonedaNatural
  :: AtlasHom source target
  -> DataTransformationNatural
       (YonedaPresheaf source)
       (YonedaPresheaf target)
@-}
{-@ ignore yonedaNatural @-}
-- ALIGN: YONEDA-NATURAL-PACKAGE.

yonedaNatural
  :: AtlasHom source target
  -> DataTransformationNatural
       (YonedaPresheaf source)
       (YonedaPresheaf target)
yonedaNatural arrow =
  DataTransformationNatural
    yoneda
    yoneda
    (DataTransformationComponent (mapYonedaNatural arrow))
    (yonedaNaturality arrow)
