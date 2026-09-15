{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE RoleAnnotations #-}
{-# LANGUAGE TypeFamilyDependencies #-}

-- | Hidden representation of presheaves on Atlas transversals.
module DataTraversal.Internal
  ( DataTraversalValue
  , DataTraversal
  , dataTraversal
  , mapDataTraversal
  , dataTraversalIdentity
  , dataTraversalComposition
  , DataTraversalHom
  , dataTraversalHom
  , mapDataTraversalHom
  , dataTraversalHomNaturality
  ) where

import AtlasTransversal (AtlasTransversal)
import Control.Category (Category (..))
import Data.Kind (Type)
import Prelude hiding ((.), id)

-- | Interpret a defunctionalized Data-traversal carrier at an Atlas.
type family DataTraversalValue
  (values :: Type)
  (atlas :: Type) = (value :: Type) | value -> values atlas

type role DataTraversal nominal
data DataTraversal (values :: Type) = DataTraversal
  (forall source target.
    AtlasTransversal source target
    -> DataTraversalValue values target
    -> DataTraversalValue values source)
  (forall object. DataTraversalValue values object -> ())
  (forall source middle target.
    AtlasTransversal middle target
    -> AtlasTransversal source middle
    -> DataTraversalValue values target
    -> ())

-- | Construct a contravariant functor on Atlas transversals.
dataTraversal
  :: (forall source target.
       AtlasTransversal source target
       -> DataTraversalValue values target
       -> DataTraversalValue values source)
  -> (forall object. DataTraversalValue values object -> ())
  -> (forall source middle target.
       AtlasTransversal middle target
       -> AtlasTransversal source middle
       -> DataTraversalValue values target
       -> ())
  -> DataTraversal values
dataTraversal = DataTraversal

mapDataTraversal
  :: DataTraversal values
  -> AtlasTransversal source target
  -> DataTraversalValue values target
  -> DataTraversalValue values source
mapDataTraversal (DataTraversal action _ _) = action

dataTraversalIdentity
  :: DataTraversal values
  -> DataTraversalValue values object
  -> ()
dataTraversalIdentity (DataTraversal _ identityLaw _) = identityLaw

dataTraversalComposition
  :: DataTraversal values
  -> AtlasTransversal middle target
  -> AtlasTransversal source middle
  -> DataTraversalValue values target
  -> ()
dataTraversalComposition
  (DataTraversal _ _ compositionLaw) = compositionLaw

type role DataTraversalHom nominal nominal
data DataTraversalHom (source :: Type) (target :: Type) where
  PrimitiveDataTraversalHom
    :: DataTraversal source
    -> DataTraversal target
    -> (forall atlas.
         DataTraversalValue source atlas
         -> DataTraversalValue target atlas)
    -> (forall sourceAtlas targetAtlas.
         AtlasTransversal sourceAtlas targetAtlas
         -> DataTraversalValue source targetAtlas
         -> ())
    -> DataTraversalHom source target
  IdentityDataTraversalHom
    :: DataTraversalHom values values
  CompositeDataTraversalHom
    :: DataTraversalHom middle target
    -> DataTraversalHom source middle
    -> DataTraversalHom source target

dataTraversalHom
  :: DataTraversal source
  -> DataTraversal target
  -> (forall atlas.
       DataTraversalValue source atlas
       -> DataTraversalValue target atlas)
  -> (forall sourceAtlas targetAtlas.
       AtlasTransversal sourceAtlas targetAtlas
       -> DataTraversalValue source targetAtlas
       -> ())
  -> DataTraversalHom source target
dataTraversalHom = PrimitiveDataTraversalHom

mapDataTraversalHom
  :: DataTraversalHom source target
  -> DataTraversalValue source atlas
  -> DataTraversalValue target atlas
mapDataTraversalHom
  (PrimitiveDataTraversalHom _ _ component _) = component
mapDataTraversalHom IdentityDataTraversalHom = id
mapDataTraversalHom (CompositeDataTraversalHom second first) =
  mapDataTraversalHom second . mapDataTraversalHom first

dataTraversalHomNaturality
  :: DataTraversalHom source target
  -> AtlasTransversal sourceAtlas targetAtlas
  -> DataTraversalValue source targetAtlas
  -> ()
dataTraversalHomNaturality
  (PrimitiveDataTraversalHom _ _ _ naturality) arrow value =
    naturality arrow value
dataTraversalHomNaturality IdentityDataTraversalHom _ _ = ()
dataTraversalHomNaturality
  (CompositeDataTraversalHom second first) arrow value =
    dataTraversalHomNaturality first arrow value `seq`
      dataTraversalHomNaturality
        second arrow (mapDataTraversalHom first value)

instance Category DataTraversalHom where
  id = IdentityDataTraversalHom
  IdentityDataTraversalHom . first = first
  second . IdentityDataTraversalHom = second
  second . first = CompositeDataTraversalHom second first
