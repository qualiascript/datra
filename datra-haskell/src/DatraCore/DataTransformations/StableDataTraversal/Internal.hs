{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE RoleAnnotations #-}
{-# LANGUAGE TypeFamilyDependencies #-}

-- | Hidden representation of presheaves on stable Atlas transversals.
module StableDataTraversal.Internal
  ( StableDataTraversalValue
  , StableDataTraversal
  , stableDataTraversal
  , mapStableDataTraversal
  , stableDataTraversalIdentity
  , stableDataTraversalComposition
  , StableDataTraversalHom
  , stableDataTraversalHom
  , mapStableDataTraversalHom
  , stableDataTraversalHomNaturality
  ) where

import Control.Category (Category (..))
import Data.Kind (Type)
import Prelude hiding ((.), id)
import StableAtlasTransversal (StableAtlasTransversal)

-- | Interpret a defunctionalized stable Data-traversal carrier at an Atlas.
type family StableDataTraversalValue
  (values :: Type)
  (atlas :: Type) = (value :: Type) | value -> values atlas

type role StableDataTraversal nominal
data StableDataTraversal (values :: Type) = StableDataTraversal
  (forall source target.
    StableAtlasTransversal source target
    -> StableDataTraversalValue values target
    -> StableDataTraversalValue values source)
  (forall object. StableDataTraversalValue values object -> ())
  (forall source middle target.
    StableAtlasTransversal middle target
    -> StableAtlasTransversal source middle
    -> StableDataTraversalValue values target
    -> ())

-- | Construct a contravariant functor on stable Atlas transversals.
stableDataTraversal
  :: (forall source target.
       StableAtlasTransversal source target
       -> StableDataTraversalValue values target
       -> StableDataTraversalValue values source)
  -> (forall object. StableDataTraversalValue values object -> ())
  -> (forall source middle target.
       StableAtlasTransversal middle target
       -> StableAtlasTransversal source middle
       -> StableDataTraversalValue values target
       -> ())
  -> StableDataTraversal values
stableDataTraversal = StableDataTraversal

mapStableDataTraversal
  :: StableDataTraversal values
  -> StableAtlasTransversal source target
  -> StableDataTraversalValue values target
  -> StableDataTraversalValue values source
mapStableDataTraversal (StableDataTraversal action _ _) = action

stableDataTraversalIdentity
  :: StableDataTraversal values
  -> StableDataTraversalValue values object
  -> ()
stableDataTraversalIdentity
  (StableDataTraversal _ identityLaw _) = identityLaw

stableDataTraversalComposition
  :: StableDataTraversal values
  -> StableAtlasTransversal middle target
  -> StableAtlasTransversal source middle
  -> StableDataTraversalValue values target
  -> ()
stableDataTraversalComposition
  (StableDataTraversal _ _ compositionLaw) = compositionLaw

type role StableDataTraversalHom nominal nominal
data StableDataTraversalHom (source :: Type) (target :: Type) where
  PrimitiveStableDataTraversalHom
    :: StableDataTraversal source
    -> StableDataTraversal target
    -> (forall atlas.
         StableDataTraversalValue source atlas
         -> StableDataTraversalValue target atlas)
    -> (forall sourceAtlas targetAtlas.
         StableAtlasTransversal sourceAtlas targetAtlas
         -> StableDataTraversalValue source targetAtlas
         -> ())
    -> StableDataTraversalHom source target
  IdentityStableDataTraversalHom
    :: StableDataTraversalHom values values
  CompositeStableDataTraversalHom
    :: StableDataTraversalHom middle target
    -> StableDataTraversalHom source middle
    -> StableDataTraversalHom source target

stableDataTraversalHom
  :: StableDataTraversal source
  -> StableDataTraversal target
  -> (forall atlas.
       StableDataTraversalValue source atlas
       -> StableDataTraversalValue target atlas)
  -> (forall sourceAtlas targetAtlas.
       StableAtlasTransversal sourceAtlas targetAtlas
       -> StableDataTraversalValue source targetAtlas
       -> ())
  -> StableDataTraversalHom source target
stableDataTraversalHom = PrimitiveStableDataTraversalHom

mapStableDataTraversalHom
  :: StableDataTraversalHom source target
  -> StableDataTraversalValue source atlas
  -> StableDataTraversalValue target atlas
mapStableDataTraversalHom
  (PrimitiveStableDataTraversalHom _ _ component _) = component
mapStableDataTraversalHom IdentityStableDataTraversalHom = id
mapStableDataTraversalHom
  (CompositeStableDataTraversalHom second first) =
    mapStableDataTraversalHom second . mapStableDataTraversalHom first

stableDataTraversalHomNaturality
  :: StableDataTraversalHom source target
  -> StableAtlasTransversal sourceAtlas targetAtlas
  -> StableDataTraversalValue source targetAtlas
  -> ()
stableDataTraversalHomNaturality
  (PrimitiveStableDataTraversalHom _ _ _ naturality) arrow value =
    naturality arrow value
stableDataTraversalHomNaturality IdentityStableDataTraversalHom _ _ = ()
stableDataTraversalHomNaturality
  (CompositeStableDataTraversalHom second first) arrow value =
    stableDataTraversalHomNaturality first arrow value `seq`
      stableDataTraversalHomNaturality
        second arrow (mapStableDataTraversalHom first value)

instance Category StableDataTraversalHom where
  id = IdentityStableDataTraversalHom
  IdentityStableDataTraversalHom . first = first
  second . IdentityStableDataTraversalHom = second
  second . first = CompositeStableDataTraversalHom second first
