{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE RoleAnnotations #-}
{-# LANGUAGE TypeFamilyDependencies #-}

-- | Hidden representation of presheaves on Atlas transposals.
module DataTransposal.Internal
  ( DataTransposalValue
  , DataTransposal
  , dataTransposal
  , mapDataTransposal
  , dataTransposalIdentity
  , dataTransposalComposition
  , DataTransposalHom
  , dataTransposalHom
  , mapDataTransposalHom
  , dataTransposalHomNaturality
  ) where

import AtlasTransposal (AtlasTransposal)
import Control.Category (Category (..))
import Data.Kind (Type)
import Prelude hiding ((.), id)

-- | Interpret a defunctionalized Data-transposal carrier at an Atlas.
type family DataTransposalValue
  (values :: Type)
  (atlas :: Type) = (value :: Type) | value -> values atlas

type role DataTransposal nominal
data DataTransposal (values :: Type) = DataTransposal
  (forall source target.
    AtlasTransposal source target
    -> DataTransposalValue values target
    -> DataTransposalValue values source)
  (forall object. DataTransposalValue values object -> ())
  (forall source middle target.
    AtlasTransposal middle target
    -> AtlasTransposal source middle
    -> DataTransposalValue values target
    -> ())

-- | Construct a contravariant functor on Atlas transposals.
dataTransposal
  :: (forall source target.
       AtlasTransposal source target
       -> DataTransposalValue values target
       -> DataTransposalValue values source)
  -> (forall object. DataTransposalValue values object -> ())
  -> (forall source middle target.
       AtlasTransposal middle target
       -> AtlasTransposal source middle
       -> DataTransposalValue values target
       -> ())
  -> DataTransposal values
dataTransposal = DataTransposal

mapDataTransposal
  :: DataTransposal values
  -> AtlasTransposal source target
  -> DataTransposalValue values target
  -> DataTransposalValue values source
mapDataTransposal (DataTransposal action _ _) = action

dataTransposalIdentity
  :: DataTransposal values
  -> DataTransposalValue values object
  -> ()
dataTransposalIdentity (DataTransposal _ identityLaw _) = identityLaw

dataTransposalComposition
  :: DataTransposal values
  -> AtlasTransposal middle target
  -> AtlasTransposal source middle
  -> DataTransposalValue values target
  -> ()
dataTransposalComposition
  (DataTransposal _ _ compositionLaw) = compositionLaw

type role DataTransposalHom nominal nominal
data DataTransposalHom (source :: Type) (target :: Type) where
  PrimitiveDataTransposalHom
    :: DataTransposal source
    -> DataTransposal target
    -> (forall atlas.
         DataTransposalValue source atlas
         -> DataTransposalValue target atlas)
    -> (forall sourceAtlas targetAtlas.
         AtlasTransposal sourceAtlas targetAtlas
         -> DataTransposalValue source targetAtlas
         -> ())
    -> DataTransposalHom source target
  IdentityDataTransposalHom
    :: DataTransposalHom values values
  CompositeDataTransposalHom
    :: DataTransposalHom middle target
    -> DataTransposalHom source middle
    -> DataTransposalHom source target

-- | Construct a pointwise natural transformation between Data transposals.
dataTransposalHom
  :: DataTransposal source
  -> DataTransposal target
  -> (forall atlas.
       DataTransposalValue source atlas
       -> DataTransposalValue target atlas)
  -> (forall sourceAtlas targetAtlas.
       AtlasTransposal sourceAtlas targetAtlas
       -> DataTransposalValue source targetAtlas
       -> ())
  -> DataTransposalHom source target
dataTransposalHom = PrimitiveDataTransposalHom

mapDataTransposalHom
  :: DataTransposalHom source target
  -> DataTransposalValue source atlas
  -> DataTransposalValue target atlas
mapDataTransposalHom
  (PrimitiveDataTransposalHom _ _ component _) = component
mapDataTransposalHom IdentityDataTransposalHom = id
mapDataTransposalHom (CompositeDataTransposalHom second first) =
  mapDataTransposalHom second . mapDataTransposalHom first

dataTransposalHomNaturality
  :: DataTransposalHom source target
  -> AtlasTransposal sourceAtlas targetAtlas
  -> DataTransposalValue source targetAtlas
  -> ()
dataTransposalHomNaturality
  (PrimitiveDataTransposalHom _ _ _ naturality) arrow value =
    naturality arrow value
dataTransposalHomNaturality IdentityDataTransposalHom _ _ = ()
dataTransposalHomNaturality
  (CompositeDataTransposalHom second first) arrow value =
    dataTransposalHomNaturality first arrow value `seq`
      dataTransposalHomNaturality
        second arrow (mapDataTransposalHom first value)

instance Category DataTransposalHom where
  id = IdentityDataTransposalHom
  IdentityDataTransposalHom . first = first
  second . IdentityDataTransposalHom = second
  second . first = CompositeDataTransposalHom second first
