{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE RoleAnnotations #-}
{-# LANGUAGE TypeFamilyDependencies #-}

-- | Hidden representation of presheaves on Atlas confederations.
module StableConfederalDataTransversal.Internal
  ( StableConfederalDataTransversalValue
  , StableConfederalDataTransversal
  , stableConfederalDataTransversal
  , mapStableConfederalDataTransversal
  , stableConfederalDataTransversalIdentity
  , stableConfederalDataTransversalComposition
  , StableConfederalDataTransversalHom
  , stableConfederalDataTransversalHom
  , mapStableConfederalDataTransversalHom
  , stableConfederalDataTransversalHomNaturality
  , EmptyMapValues
  , emptyMap
  ) where

import AtlasConfederation
  ( AtlasConfederationHom
  , AtlasConfederationObject
  , EmptyAtlasConfederationScope
  , composeAtlasConfederationHoms
  )
import Control.Category (Category (..))
import Data.Kind (Type)
import Data.Void (Void)
import Prelude hiding ((.), id)

-- | Interpret a defunctionalized stable-confederal carrier at an Atlas
-- confederation.
type family StableConfederalDataTransversalValue
  (values :: Type)
  (confederation :: Type) = (value :: Type)
  | value -> values confederation

-- | A contravariant functor from Atlas confederations to Haskell types.
--
-- Atlas-confederation arrows already contain stable Atlas transversals in
-- every component, so stability is enforced by the indexing category.
type role StableConfederalDataTransversal nominal
data StableConfederalDataTransversal (values :: Type) =
  StableConfederalDataTransversal
    (forall source target.
      AtlasConfederationHom source target
      -> StableConfederalDataTransversalValue values target
      -> StableConfederalDataTransversalValue values source)
    (forall object.
      StableConfederalDataTransversalValue values object
      -> ())
    (forall source middle target.
      AtlasConfederationHom middle target
      -> AtlasConfederationHom source middle
      -> StableConfederalDataTransversalValue values target
      -> ())

-- | Construct a stable confederal data transversal.
stableConfederalDataTransversal
  :: (forall source target.
       AtlasConfederationHom source target
       -> StableConfederalDataTransversalValue values target
       -> StableConfederalDataTransversalValue values source)
  -> (forall object.
       StableConfederalDataTransversalValue values object
       -> ())
  -> (forall source middle target.
       AtlasConfederationHom middle target
       -> AtlasConfederationHom source middle
       -> StableConfederalDataTransversalValue values target
       -> ())
  -> StableConfederalDataTransversal values
stableConfederalDataTransversal = StableConfederalDataTransversal

-- | Reindex a value contravariantly along an Atlas-confederation arrow.
mapStableConfederalDataTransversal
  :: StableConfederalDataTransversal values
  -> AtlasConfederationHom source target
  -> StableConfederalDataTransversalValue values target
  -> StableConfederalDataTransversalValue values source
mapStableConfederalDataTransversal
  (StableConfederalDataTransversal action _ _) = action

-- | Invoke the identity-law witness of a stable confederal data transversal.
stableConfederalDataTransversalIdentity
  :: StableConfederalDataTransversal values
  -> StableConfederalDataTransversalValue values object
  -> ()
stableConfederalDataTransversalIdentity
  (StableConfederalDataTransversal _ identityLaw _) = identityLaw

-- | Invoke the composition-law witness of a stable confederal data
-- transversal.
stableConfederalDataTransversalComposition
  :: StableConfederalDataTransversal values
  -> AtlasConfederationHom middle target
  -> AtlasConfederationHom source middle
  -> StableConfederalDataTransversalValue values target
  -> ()
stableConfederalDataTransversalComposition
  (StableConfederalDataTransversal _ _ compositionLaw) = compositionLaw

-- | Natural transformations between stable confederal data transversals.
type role StableConfederalDataTransversalHom nominal nominal
data StableConfederalDataTransversalHom
  (source :: Type)
  (target :: Type) where
  PrimitiveStableConfederalDataTransversalHom
    :: StableConfederalDataTransversal source
    -> StableConfederalDataTransversal target
    -> (forall confederation.
         StableConfederalDataTransversalValue source confederation
         -> StableConfederalDataTransversalValue target confederation)
    -> (forall sourceConfederation targetConfederation.
         AtlasConfederationHom sourceConfederation targetConfederation
         -> StableConfederalDataTransversalValue
              source targetConfederation
         -> ())
    -> StableConfederalDataTransversalHom source target
  IdentityStableConfederalDataTransversalHom
    :: StableConfederalDataTransversalHom values values
  CompositeStableConfederalDataTransversalHom
    :: StableConfederalDataTransversalHom middle target
    -> StableConfederalDataTransversalHom source middle
    -> StableConfederalDataTransversalHom source target

-- | Construct a natural transformation.
stableConfederalDataTransversalHom
  :: StableConfederalDataTransversal source
  -> StableConfederalDataTransversal target
  -> (forall confederation.
       StableConfederalDataTransversalValue source confederation
       -> StableConfederalDataTransversalValue target confederation)
  -> (forall sourceConfederation targetConfederation.
       AtlasConfederationHom sourceConfederation targetConfederation
       -> StableConfederalDataTransversalValue source targetConfederation
       -> ())
  -> StableConfederalDataTransversalHom source target
stableConfederalDataTransversalHom =
  PrimitiveStableConfederalDataTransversalHom

-- | Evaluate one component of a natural transformation.
mapStableConfederalDataTransversalHom
  :: StableConfederalDataTransversalHom source target
  -> StableConfederalDataTransversalValue source confederation
  -> StableConfederalDataTransversalValue target confederation
mapStableConfederalDataTransversalHom
  (PrimitiveStableConfederalDataTransversalHom _ _ component _) = component
mapStableConfederalDataTransversalHom
  IdentityStableConfederalDataTransversalHom = id
mapStableConfederalDataTransversalHom
  (CompositeStableConfederalDataTransversalHom second first) =
    mapStableConfederalDataTransversalHom second
      . mapStableConfederalDataTransversalHom first

-- | Invoke or derive the naturality witness for a natural transformation.
stableConfederalDataTransversalHomNaturality
  :: StableConfederalDataTransversalHom source target
  -> AtlasConfederationHom sourceConfederation targetConfederation
  -> StableConfederalDataTransversalValue source targetConfederation
  -> ()
stableConfederalDataTransversalHomNaturality
  (PrimitiveStableConfederalDataTransversalHom _ _ _ naturality)
  arrow value = naturality arrow value
stableConfederalDataTransversalHomNaturality
  IdentityStableConfederalDataTransversalHom _ _ = ()
stableConfederalDataTransversalHomNaturality
  (CompositeStableConfederalDataTransversalHom second first) arrow value =
    stableConfederalDataTransversalHomNaturality first arrow value `seq`
      stableConfederalDataTransversalHomNaturality
        second arrow (mapStableConfederalDataTransversalHom first value)

instance Category StableConfederalDataTransversalHom where
  id = IdentityStableConfederalDataTransversalHom
  IdentityStableConfederalDataTransversalHom . first = first
  second . IdentityStableConfederalDataTransversalHom = second
  second . first =
    CompositeStableConfederalDataTransversalHom second first

-- | Defunctionalized carrier of the empty map.  Its value at @X@ is
-- @Hom(X, EmptyAtlasConfederation)@, the Yoneda presheaf represented by the
-- empty Atlas confederation.
data EmptyMapValues

type instance
  StableConfederalDataTransversalValue EmptyMapValues confederation =
    AtlasConfederationHom
      confederation
      (AtlasConfederationObject EmptyAtlasConfederationScope Void)

-- | The empty map, represented by the empty Atlas confederation.
emptyMap :: StableConfederalDataTransversal EmptyMapValues
emptyMap =
  stableConfederalDataTransversal
    (flip composeAtlasConfederationHoms)
    (const ())
    (\_ _ _ -> ())
