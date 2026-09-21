{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE RoleAnnotations #-}
{-# LANGUAGE TypeFamilyDependencies #-}

-- | Hidden representation of presheaves on stable Atlas transversals.
module StableDataTransversal.Internal
  ( StableDataTransversalValue
  , StableDataTransversal
  , stableDataTransversal
  , mapStableDataTransversal
  , stableDataTransversalIdentity
  , stableDataTransversalComposition
  , StableDataTransversalHom
  , stableDataTransversalHom
  , mapStableDataTransversalHom
  , stableDataTransversalHomNaturality
  , ExtendedStableDataTransversal
  , LeftKanExtensionValue
  , leftKanExtensionValue
  , withLeftKanExtensionValue
  , extendStableDataTransversalToDataTransformation
  , extendStableDataTransversalHomToDataTransformation
  , StableDataTransversalExtensionFunctor (..)
  , stableDataTransversalExtensionFunctor
  ) where

import Atlas (AtlasHom, AtlasWitness, composeAtlasHoms)
import Control.Category (Category (..))
import Data.Kind (Type)
import DataTransformation
  ( DataTransformation
  , DataTransformationHom
  , DataTransformationValue
  , dataTransformation
  , dataTransformationHom
  )
import Prelude hiding ((.), id)
import StableAtlasTransversal (StableAtlasTransversal)

-- | Interpret a defunctionalized stable Data-transversal carrier at an Atlas.
type family StableDataTransversalValue
  (values :: Type)
  (atlas :: Type) = (value :: Type) | value -> values atlas

type role StableDataTransversal nominal
data StableDataTransversal (values :: Type) = StableDataTransversal
  (forall source target.
    StableAtlasTransversal source target
    -> StableDataTransversalValue values target
    -> StableDataTransversalValue values source)
  (forall object. StableDataTransversalValue values object -> ())
  (forall source middle target.
    StableAtlasTransversal middle target
    -> StableAtlasTransversal source middle
    -> StableDataTransversalValue values target
    -> ())

-- | Construct a contravariant functor on stable Atlas transversals.
stableDataTransversal
  :: (forall source target.
       StableAtlasTransversal source target
       -> StableDataTransversalValue values target
       -> StableDataTransversalValue values source)
  -> (forall object. StableDataTransversalValue values object -> ())
  -> (forall source middle target.
       StableAtlasTransversal middle target
       -> StableAtlasTransversal source middle
       -> StableDataTransversalValue values target
       -> ())
  -> StableDataTransversal values
stableDataTransversal = StableDataTransversal

mapStableDataTransversal
  :: StableDataTransversal values
  -> StableAtlasTransversal source target
  -> StableDataTransversalValue values target
  -> StableDataTransversalValue values source
mapStableDataTransversal (StableDataTransversal action _ _) = action

stableDataTransversalIdentity
  :: StableDataTransversal values
  -> StableDataTransversalValue values object
  -> ()
stableDataTransversalIdentity
  (StableDataTransversal _ identityLaw _) = identityLaw

stableDataTransversalComposition
  :: StableDataTransversal values
  -> StableAtlasTransversal middle target
  -> StableAtlasTransversal source middle
  -> StableDataTransversalValue values target
  -> ()
stableDataTransversalComposition
  (StableDataTransversal _ _ compositionLaw) = compositionLaw

type role StableDataTransversalHom nominal nominal
data StableDataTransversalHom (source :: Type) (target :: Type) where
  PrimitiveStableDataTransversalHom
    :: StableDataTransversal source
    -> StableDataTransversal target
    -> (forall atlas.
         StableDataTransversalValue source atlas
         -> StableDataTransversalValue target atlas)
    -> (forall sourceAtlas targetAtlas.
         StableAtlasTransversal sourceAtlas targetAtlas
         -> StableDataTransversalValue source targetAtlas
         -> ())
    -> StableDataTransversalHom source target
  IdentityStableDataTransversalHom
    :: StableDataTransversalHom values values
  CompositeStableDataTransversalHom
    :: StableDataTransversalHom middle target
    -> StableDataTransversalHom source middle
    -> StableDataTransversalHom source target

stableDataTransversalHom
  :: StableDataTransversal source
  -> StableDataTransversal target
  -> (forall atlas.
       StableDataTransversalValue source atlas
       -> StableDataTransversalValue target atlas)
  -> (forall sourceAtlas targetAtlas.
       StableAtlasTransversal sourceAtlas targetAtlas
       -> StableDataTransversalValue source targetAtlas
       -> ())
  -> StableDataTransversalHom source target
stableDataTransversalHom = PrimitiveStableDataTransversalHom

mapStableDataTransversalHom
  :: StableDataTransversalHom source target
  -> StableDataTransversalValue source atlas
  -> StableDataTransversalValue target atlas
mapStableDataTransversalHom
  (PrimitiveStableDataTransversalHom _ _ component _) = component
mapStableDataTransversalHom IdentityStableDataTransversalHom = id
mapStableDataTransversalHom
  (CompositeStableDataTransversalHom second first) =
    mapStableDataTransversalHom second . mapStableDataTransversalHom first

stableDataTransversalHomNaturality
  :: StableDataTransversalHom source target
  -> StableAtlasTransversal sourceAtlas targetAtlas
  -> StableDataTransversalValue source targetAtlas
  -> ()
stableDataTransversalHomNaturality
  (PrimitiveStableDataTransversalHom _ _ _ naturality) arrow value =
    naturality arrow value
stableDataTransversalHomNaturality IdentityStableDataTransversalHom _ _ = ()
stableDataTransversalHomNaturality
  (CompositeStableDataTransversalHom second first) arrow value =
    stableDataTransversalHomNaturality first arrow value `seq`
      stableDataTransversalHomNaturality
        second arrow (mapStableDataTransversalHom first value)

instance Category StableDataTransversalHom where
  id = IdentityStableDataTransversalHom
  IdentityStableDataTransversalHom . first = first
  second . IdentityStableDataTransversalHom = second
  second . first = CompositeStableDataTransversalHom second first

-- | Defunctionalized carrier of the left Kan extension from stable Atlas
-- transversals to all Atlas morphisms.
data ExtendedStableDataTransversal stableValues

-- | One coend presentation @[A -> i(B), value in F(B)]@.  Haskell retains a
-- representative of the mathematical quotient; the coend relation is
-- proof-irrelevant at runtime, so eliminators must be invariant under stable
-- reindexing of the represented value.
type role LeftKanExtensionValue nominal nominal
data LeftKanExtensionValue stableValues source where
  LeftKanExtensionValue
    :: AtlasWitness target
    -> AtlasHom source target
    -> StableDataTransversalValue stableValues target
    -> LeftKanExtensionValue stableValues source

type instance
  DataTransformationValue
    (ExtendedStableDataTransversal stableValues)
    source =
      LeftKanExtensionValue stableValues source

leftKanExtensionValue
  :: AtlasWitness target
  -> AtlasHom source target
  -> StableDataTransversalValue stableValues target
  -> LeftKanExtensionValue stableValues source
leftKanExtensionValue = LeftKanExtensionValue

withLeftKanExtensionValue
  :: LeftKanExtensionValue stableValues source
  -> (forall target.
       AtlasWitness target
       -> AtlasHom source target
       -> StableDataTransversalValue stableValues target
       -> result)
  -> result
withLeftKanExtensionValue
    (LeftKanExtensionValue target arrow value) useValue =
  useValue target arrow value

-- | Left Kan extend a presheaf on the wide stable-transversal subcategory to
-- a presheaf on all Atlases.  Atlas reindexing precomposes the coend arrow;
-- the coend relation accounts for stable reindexing of the stored value.
extendStableDataTransversalToDataTransformation
  :: StableDataTransversal stableValues
  -> DataTransformation (ExtendedStableDataTransversal stableValues)
extendStableDataTransversalToDataTransformation _ =
  dataTransformation
    (\arrow (LeftKanExtensionValue target represented value) ->
      LeftKanExtensionValue
        target
        (composeAtlasHoms represented arrow)
        value)
    (const ())
    (\_ _ _ -> ())

-- | The arrow action of left Kan extension.  It changes only the stored
-- presheaf value and retains the representing Atlas arrow.
extendStableDataTransversalHomToDataTransformation
  :: StableDataTransversalHom source target
  -> DataTransformationHom
       (ExtendedStableDataTransversal source)
       (ExtendedStableDataTransversal target)
extendStableDataTransversalHomToDataTransformation
    (PrimitiveStableDataTransversalHom source target component _) =
  dataTransformationHom
    (extendStableDataTransversalToDataTransformation source)
    (extendStableDataTransversalToDataTransformation target)
    (\(LeftKanExtensionValue witness represented value) ->
      LeftKanExtensionValue witness represented (component value))
    (\_ _ -> ())
extendStableDataTransversalHomToDataTransformation
    IdentityStableDataTransversalHom = id
extendStableDataTransversalHomToDataTransformation
    (CompositeStableDataTransversalHom second first) =
  extendStableDataTransversalHomToDataTransformation second
    . extendStableDataTransversalHomToDataTransformation first

-- | Executable object and arrow action of
-- @StaDaTrav.extendToDaTra = Lan_(StaAtlTravInc^op)@.
data StableDataTransversalExtensionFunctor =
  StableDataTransversalExtensionFunctor
    { stableDataTransversalExtensionObject
        :: forall values.
           StableDataTransversal values
        -> DataTransformation (ExtendedStableDataTransversal values)
    , stableDataTransversalExtensionHom
        :: forall source target.
           StableDataTransversalHom source target
        -> DataTransformationHom
             (ExtendedStableDataTransversal source)
             (ExtendedStableDataTransversal target)
    }

stableDataTransversalExtensionFunctor
  :: StableDataTransversalExtensionFunctor
stableDataTransversalExtensionFunctor =
  StableDataTransversalExtensionFunctor
    { stableDataTransversalExtensionObject =
        extendStableDataTransversalToDataTransformation
    , stableDataTransversalExtensionHom =
        extendStableDataTransversalHomToDataTransformation
    }
