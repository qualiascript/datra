{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE RoleAnnotations #-}
{-# LANGUAGE TypeFamilyDependencies #-}

-- | Hidden representation of presheaves on Atlas transversals.
module DataTransversal.Internal
  ( DataTransversalValue
  , DataTransversal
  , dataTransversal
  , mapDataTransversal
  , dataTransversalIdentity
  , dataTransversalComposition
  , DataTransversalHom
  , dataTransversalHom
  , mapDataTransversalHom
  , dataTransversalHomNaturality
  ) where

import AtlasTransversal (AtlasTransversal)
import Control.Category (Category (..))
import Data.Kind (Type)
import Prelude hiding ((.), id)

-- | Interpret a defunctionalized Data-transversal carrier at an Atlas.
type family DataTransversalValue
  (values :: Type)
  (atlas :: Type) = (value :: Type) | value -> values atlas

type role DataTransversal nominal
data DataTransversal (values :: Type) = DataTransversal
  (forall source target.
    AtlasTransversal source target
    -> DataTransversalValue values target
    -> DataTransversalValue values source)
  (forall object. DataTransversalValue values object -> ())
  (forall source middle target.
    AtlasTransversal middle target
    -> AtlasTransversal source middle
    -> DataTransversalValue values target
    -> ())

-- | Construct a contravariant functor on Atlas transversals.
dataTransversal
  :: (forall source target.
       AtlasTransversal source target
       -> DataTransversalValue values target
       -> DataTransversalValue values source)
  -> (forall object. DataTransversalValue values object -> ())
  -> (forall source middle target.
       AtlasTransversal middle target
       -> AtlasTransversal source middle
       -> DataTransversalValue values target
       -> ())
  -> DataTransversal values
dataTransversal = DataTransversal

mapDataTransversal
  :: DataTransversal values
  -> AtlasTransversal source target
  -> DataTransversalValue values target
  -> DataTransversalValue values source
mapDataTransversal (DataTransversal action _ _) = action

dataTransversalIdentity
  :: DataTransversal values
  -> DataTransversalValue values object
  -> ()
dataTransversalIdentity (DataTransversal _ identityLaw _) = identityLaw

dataTransversalComposition
  :: DataTransversal values
  -> AtlasTransversal middle target
  -> AtlasTransversal source middle
  -> DataTransversalValue values target
  -> ()
dataTransversalComposition
  (DataTransversal _ _ compositionLaw) = compositionLaw

type role DataTransversalHom nominal nominal
data DataTransversalHom (source :: Type) (target :: Type) where
  PrimitiveDataTransversalHom
    :: DataTransversal source
    -> DataTransversal target
    -> (forall atlas.
         DataTransversalValue source atlas
         -> DataTransversalValue target atlas)
    -> (forall sourceAtlas targetAtlas.
         AtlasTransversal sourceAtlas targetAtlas
         -> DataTransversalValue source targetAtlas
         -> ())
    -> DataTransversalHom source target
  IdentityDataTransversalHom
    :: DataTransversalHom values values
  CompositeDataTransversalHom
    :: DataTransversalHom middle target
    -> DataTransversalHom source middle
    -> DataTransversalHom source target

dataTransversalHom
  :: DataTransversal source
  -> DataTransversal target
  -> (forall atlas.
       DataTransversalValue source atlas
       -> DataTransversalValue target atlas)
  -> (forall sourceAtlas targetAtlas.
       AtlasTransversal sourceAtlas targetAtlas
       -> DataTransversalValue source targetAtlas
       -> ())
  -> DataTransversalHom source target
dataTransversalHom = PrimitiveDataTransversalHom

mapDataTransversalHom
  :: DataTransversalHom source target
  -> DataTransversalValue source atlas
  -> DataTransversalValue target atlas
mapDataTransversalHom
  (PrimitiveDataTransversalHom _ _ component _) = component
mapDataTransversalHom IdentityDataTransversalHom = id
mapDataTransversalHom (CompositeDataTransversalHom second first) =
  mapDataTransversalHom second . mapDataTransversalHom first

dataTransversalHomNaturality
  :: DataTransversalHom source target
  -> AtlasTransversal sourceAtlas targetAtlas
  -> DataTransversalValue source targetAtlas
  -> ()
dataTransversalHomNaturality
  (PrimitiveDataTransversalHom _ _ _ naturality) arrow value =
    naturality arrow value
dataTransversalHomNaturality IdentityDataTransversalHom _ _ = ()
dataTransversalHomNaturality
  (CompositeDataTransversalHom second first) arrow value =
    dataTransversalHomNaturality first arrow value `seq`
      dataTransversalHomNaturality
        second arrow (mapDataTransversalHom first value)

instance Category DataTransversalHom where
  id = IdentityDataTransversalHom
  IdentityDataTransversalHom . first = first
  second . IdentityDataTransversalHom = second
  second . first = CompositeDataTransversalHom second first
