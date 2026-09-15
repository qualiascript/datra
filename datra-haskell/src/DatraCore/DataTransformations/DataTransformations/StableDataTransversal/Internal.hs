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
  ) where

import Control.Category (Category (..))
import Data.Kind (Type)
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
