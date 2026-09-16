{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE RoleAnnotations #-}
{-# LANGUAGE TypeFamilyDependencies #-}

-- | Hidden representation of presheaves on Atlas confederations.
module StableConfederalData.Internal
  ( StableConfederalDataValue
  , StableConfederalData
  , stableConfederalData
  , mapStableConfederalData
  , stableConfederalDataIdentity
  , stableConfederalDataComposition
  , StableConfederalDataHom
  , stableConfederalDataHom
  , mapStableConfederalDataHom
  , stableConfederalDataHomNaturality
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
type family StableConfederalDataValue
  (values :: Type)
  (confederation :: Type) = (value :: Type)
  | value -> values confederation

-- | A contravariant functor from Atlas confederations to Haskell types.
--
-- Atlas-confederation arrows already contain stable Atlas transversals in
-- every component, so stability is enforced by the indexing category.
type role StableConfederalData nominal
data StableConfederalData (values :: Type) =
  StableConfederalData
    (forall source target.
      AtlasConfederationHom source target
      -> StableConfederalDataValue values target
      -> StableConfederalDataValue values source)
    (forall object.
      StableConfederalDataValue values object
      -> ())
    (forall source middle target.
      AtlasConfederationHom middle target
      -> AtlasConfederationHom source middle
      -> StableConfederalDataValue values target
      -> ())

-- | Construct a stable confederal data object.
stableConfederalData
  :: (forall source target.
       AtlasConfederationHom source target
       -> StableConfederalDataValue values target
       -> StableConfederalDataValue values source)
  -> (forall object.
       StableConfederalDataValue values object
       -> ())
  -> (forall source middle target.
       AtlasConfederationHom middle target
       -> AtlasConfederationHom source middle
       -> StableConfederalDataValue values target
       -> ())
  -> StableConfederalData values
stableConfederalData = StableConfederalData

-- | Reindex a value contravariantly along an Atlas-confederation arrow.
mapStableConfederalData
  :: StableConfederalData values
  -> AtlasConfederationHom source target
  -> StableConfederalDataValue values target
  -> StableConfederalDataValue values source
mapStableConfederalData
  (StableConfederalData action _ _) = action

-- | Invoke the identity-law witness of stable confederal data.
stableConfederalDataIdentity
  :: StableConfederalData values
  -> StableConfederalDataValue values object
  -> ()
stableConfederalDataIdentity
  (StableConfederalData _ identityLaw _) = identityLaw

-- | Invoke the composition-law witness of stable confederal data.
stableConfederalDataComposition
  :: StableConfederalData values
  -> AtlasConfederationHom middle target
  -> AtlasConfederationHom source middle
  -> StableConfederalDataValue values target
  -> ()
stableConfederalDataComposition
  (StableConfederalData _ _ compositionLaw) = compositionLaw

-- | Natural transformations between stable confederal data.
type role StableConfederalDataHom nominal nominal
data StableConfederalDataHom
  (source :: Type)
  (target :: Type) where
  PrimitiveStableConfederalDataHom
    :: StableConfederalData source
    -> StableConfederalData target
    -> (forall confederation.
         StableConfederalDataValue source confederation
         -> StableConfederalDataValue target confederation)
    -> (forall sourceConfederation targetConfederation.
         AtlasConfederationHom sourceConfederation targetConfederation
         -> StableConfederalDataValue
              source targetConfederation
         -> ())
    -> StableConfederalDataHom source target
  IdentityStableConfederalDataHom
    :: StableConfederalDataHom values values
  CompositeStableConfederalDataHom
    :: StableConfederalDataHom middle target
    -> StableConfederalDataHom source middle
    -> StableConfederalDataHom source target

-- | Construct a natural transformation.
stableConfederalDataHom
  :: StableConfederalData source
  -> StableConfederalData target
  -> (forall confederation.
       StableConfederalDataValue source confederation
       -> StableConfederalDataValue target confederation)
  -> (forall sourceConfederation targetConfederation.
       AtlasConfederationHom sourceConfederation targetConfederation
       -> StableConfederalDataValue source targetConfederation
       -> ())
  -> StableConfederalDataHom source target
stableConfederalDataHom =
  PrimitiveStableConfederalDataHom

-- | Evaluate one component of a natural transformation.
mapStableConfederalDataHom
  :: StableConfederalDataHom source target
  -> StableConfederalDataValue source confederation
  -> StableConfederalDataValue target confederation
mapStableConfederalDataHom
  (PrimitiveStableConfederalDataHom _ _ component _) = component
mapStableConfederalDataHom
  IdentityStableConfederalDataHom = id
mapStableConfederalDataHom
  (CompositeStableConfederalDataHom second first) =
    mapStableConfederalDataHom second
      . mapStableConfederalDataHom first

-- | Invoke or derive the naturality witness for a natural transformation.
stableConfederalDataHomNaturality
  :: StableConfederalDataHom source target
  -> AtlasConfederationHom sourceConfederation targetConfederation
  -> StableConfederalDataValue source targetConfederation
  -> ()
stableConfederalDataHomNaturality
  (PrimitiveStableConfederalDataHom _ _ _ naturality)
  arrow value = naturality arrow value
stableConfederalDataHomNaturality
  IdentityStableConfederalDataHom _ _ = ()
stableConfederalDataHomNaturality
  (CompositeStableConfederalDataHom second first) arrow value =
    stableConfederalDataHomNaturality first arrow value `seq`
      stableConfederalDataHomNaturality
        second arrow (mapStableConfederalDataHom first value)

instance Category StableConfederalDataHom where
  id = IdentityStableConfederalDataHom
  IdentityStableConfederalDataHom . first = first
  second . IdentityStableConfederalDataHom = second
  second . first =
    CompositeStableConfederalDataHom second first

-- | Defunctionalized carrier of the empty map.  Its value at @X@ is
-- @Hom(X, EmptyAtlasConfederation)@, the Yoneda presheaf represented by the
-- empty Atlas confederation.
data EmptyMapValues

type instance
  StableConfederalDataValue EmptyMapValues confederation =
    AtlasConfederationHom
      confederation
      (AtlasConfederationObject EmptyAtlasConfederationScope Void)

-- | The empty map, represented by the empty Atlas confederation.
emptyMap :: StableConfederalData EmptyMapValues
emptyMap =
  stableConfederalData
    (flip composeAtlasConfederationHoms)
    (const ())
    (\_ _ _ -> ())
