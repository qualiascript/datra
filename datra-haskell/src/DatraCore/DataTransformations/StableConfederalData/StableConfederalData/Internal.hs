{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE RoleAnnotations #-}
{-# LANGUAGE ScopedTypeVariables #-}
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
  , EmbeddedAtlasMap
  , embedAtlasMap
  , RestrictedStableConfederalData
  , RestrictedStableConfederalDataValue
  , restrictedStableConfederalDataValue
  , withRestrictedStableConfederalDataValue
  , restrictStableConfederalDataToStableAtlases
  , restrictStableConfederalDataHomToStableAtlases
  , ForgottenStableConfederalData
  , forgetStableConfederalDataToDataTransformation
  , forgetStableConfederalDataHomToDataTransformation
  , StableConfederalDataForgetfulFunctor (..)
  , stableConfederalDataForgetfulFunctor
  , EmbeddedAtlasFederation
  , EmbeddedAtlasFederationValue
  , embeddedAtlasFederationValue
  , withEmbeddedAtlasFederationValue
  , embedAtlasFederation
  , ForgottenAtlasFederation
  , forgetAtlasFederationToDataTransformation
  ) where

import AtlasConfederation
  ( AtlasConfederationHom
  , AtlasConfederationObject
  , EmptyAtlasConfederationScope
  , SingletonAtlasConfederationScope
  , composeAtlasConfederationHoms
  , singletonAtlasConfederation
  , singletonAtlasConfederationHom
  )
import Atlas.Morphism.Internal (AtlasWitness (..))
import AtlasFederation
  ( AtlasFederation
  , atlasFederationConfederation
  )
import AtlasMap (AtlasMap, atlasMapAtlas)
import Control.Category (Category (..))
import Data.Kind (Type)
import DataTransformation
  ( DataTransformation
  , DataTransformationHom
  )
import Data.Void (Void)
import Prelude hiding ((.), id)
import StableAtlasTransversal
  ( StableAtlasTransversal
  , stableAtlasTransversalSourceWitness
  )
import StableDataTransversal
  ( ExtendedStableDataTransversal
  , StableDataTransversal
  , StableDataTransversalHom
  , StableDataTransversalValue
  , extendStableDataTransversalHomToDataTransformation
  , extendStableDataTransversalToDataTransformation
  , stableDataTransversal
  , stableDataTransversalHom
  )

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

-- | Defunctionalized carrier of the Yoneda embedding of an Atlas map. The
-- Atlas map first becomes a singleton stable Atlas confederation; its value at
-- @X@ is therefore the hom-set from @X@ to that singleton confederation.
data EmbeddedAtlasMap atlasObject

type instance
  StableConfederalDataValue
    (EmbeddedAtlasMap atlasObject)
    confederation =
      AtlasConfederationHom
        confederation
        (AtlasConfederationObject
          (SingletonAtlasConfederationScope atlasObject)
          ())

-- | Embed an Atlas map into stable confederal data by the singleton-family
-- embedding followed by Yoneda.
embedAtlasMap
  :: AtlasMap atlasObject
  -> StableConfederalData (EmbeddedAtlasMap atlasObject)
embedAtlasMap valueMap =
  case atlasMapAtlas valueMap of
    AtlasWitness valueAtlas ->
      singletonAtlasConfederation valueAtlas `seq`
        stableConfederalData
          (flip composeAtlasConfederationHoms)
          (const ())
          (\_ _ _ -> ())

-- | Carrier obtained by restricting stable confederal data to singleton
-- Atlas confederations.
data RestrictedStableConfederalData confederalValues

type role RestrictedStableConfederalDataValue nominal nominal
data RestrictedStableConfederalDataValue confederalValues atlas where
  RestrictedStableConfederalDataValue
    :: AtlasWitness atlas
    -> StableConfederalDataValue
         confederalValues
         (AtlasConfederationObject
           (SingletonAtlasConfederationScope atlas)
           ())
    -> RestrictedStableConfederalDataValue confederalValues atlas

type instance
  StableDataTransversalValue
    (RestrictedStableConfederalData confederalValues)
    atlas =
      RestrictedStableConfederalDataValue confederalValues atlas

restrictedStableConfederalDataValue
  :: AtlasWitness atlas
  -> StableConfederalDataValue
       confederalValues
       (AtlasConfederationObject
         (SingletonAtlasConfederationScope atlas)
         ())
  -> RestrictedStableConfederalDataValue confederalValues atlas
restrictedStableConfederalDataValue = RestrictedStableConfederalDataValue

withRestrictedStableConfederalDataValue
  :: RestrictedStableConfederalDataValue confederalValues atlas
  -> ( AtlasWitness atlas
       -> StableConfederalDataValue
            confederalValues
            (AtlasConfederationObject
              (SingletonAtlasConfederationScope atlas)
              ())
       -> result
     )
  -> result
withRestrictedStableConfederalDataValue
    (RestrictedStableConfederalDataValue witness value) useValue =
  useValue witness value

-- | Restrict stable confederal data along the singleton-confederation
-- embedding.  This is the first half of @StaConfDa.forgetToDaTra@.
restrictStableConfederalDataToStableAtlases
  :: forall confederalValues.
     StableConfederalData confederalValues
  -> StableDataTransversal
       (RestrictedStableConfederalData confederalValues)
restrictStableConfederalDataToStableAtlases stableData =
  stableDataTransversal action (const ()) (\_ _ _ -> ())
  where
    action
      :: StableAtlasTransversal source target
      -> RestrictedStableConfederalDataValue confederalValues target
      -> RestrictedStableConfederalDataValue confederalValues source
    action transversal
        (RestrictedStableConfederalDataValue targetWitness value) =
      let sourceWitness =
            stableAtlasTransversalSourceWitness transversal targetWitness
      in case (sourceWitness, targetWitness) of
          (AtlasWitness sourceAtlas, AtlasWitness targetAtlas) ->
            RestrictedStableConfederalDataValue
              sourceWitness
              (mapStableConfederalData
                stableData
                (singletonAtlasConfederationHom
                  sourceAtlas targetAtlas transversal)
                value)

-- | Restrict a stable-confederal natural transformation along the
-- singleton-confederation embedding.
restrictStableConfederalDataHomToStableAtlases
  :: forall source target.
     StableConfederalDataHom source target
  -> StableDataTransversalHom
       (RestrictedStableConfederalData source)
       (RestrictedStableConfederalData target)
restrictStableConfederalDataHomToStableAtlases
    (PrimitiveStableConfederalDataHom
      source target component naturality) =
  stableDataTransversalHom
    (restrictStableConfederalDataToStableAtlases source)
    (restrictStableConfederalDataToStableAtlases target)
    (\(RestrictedStableConfederalDataValue witness value) ->
      RestrictedStableConfederalDataValue witness (component value))
    restrictedNaturality
  where
    restrictedNaturality
      :: StableAtlasTransversal sourceAtlas targetAtlas
      -> RestrictedStableConfederalDataValue source targetAtlas
      -> ()
    restrictedNaturality transversal
        (RestrictedStableConfederalDataValue targetWitness value) =
      let sourceWitness =
            stableAtlasTransversalSourceWitness transversal targetWitness
      in case (sourceWitness, targetWitness) of
          (AtlasWitness sourceAtlas, AtlasWitness targetAtlas) ->
            naturality
              (singletonAtlasConfederationHom
                sourceAtlas targetAtlas transversal)
              value
restrictStableConfederalDataHomToStableAtlases
    IdentityStableConfederalDataHom = id
restrictStableConfederalDataHomToStableAtlases
    (CompositeStableConfederalDataHom second first) =
  restrictStableConfederalDataHomToStableAtlases second
    . restrictStableConfederalDataHomToStableAtlases first

-- | The defunctionalized carrier of the canonical forgotten DaTra set.
type ForgottenStableConfederalData confederalValues =
  ExtendedStableDataTransversal
    (RestrictedStableConfederalData confederalValues)

-- | Forget stable confederal data to a DaTra presheaf by restriction to
-- singleton confederations followed by left Kan extension.
forgetStableConfederalDataToDataTransformation
  :: StableConfederalData confederalValues
  -> DataTransformation (ForgottenStableConfederalData confederalValues)
forgetStableConfederalDataToDataTransformation =
  extendStableDataTransversalToDataTransformation
    . restrictStableConfederalDataToStableAtlases

-- | The arrow action of stable-confederal forgetting.
forgetStableConfederalDataHomToDataTransformation
  :: StableConfederalDataHom source target
  -> DataTransformationHom
       (ForgottenStableConfederalData source)
       (ForgottenStableConfederalData target)
forgetStableConfederalDataHomToDataTransformation =
  extendStableDataTransversalHomToDataTransformation
    . restrictStableConfederalDataHomToStableAtlases

-- | The Haskell port of @StaConfDa.forgetToDaTra@: singleton restriction
-- followed by left Kan extension, on both objects and arrows.
data StableConfederalDataForgetfulFunctor =
  StableConfederalDataForgetfulFunctor
    { stableConfederalDataForgetfulObject
        :: forall values.
           StableConfederalData values
        -> DataTransformation (ForgottenStableConfederalData values)
    , stableConfederalDataForgetfulHom
        :: forall source target.
           StableConfederalDataHom source target
        -> DataTransformationHom
             (ForgottenStableConfederalData source)
             (ForgottenStableConfederalData target)
    }

stableConfederalDataForgetfulFunctor
  :: StableConfederalDataForgetfulFunctor
stableConfederalDataForgetfulFunctor =
  StableConfederalDataForgetfulFunctor
    { stableConfederalDataForgetfulObject =
        forgetStableConfederalDataToDataTransformation
    , stableConfederalDataForgetfulHom =
        forgetStableConfederalDataHomToDataTransformation
    }

-- | Defunctionalized carrier of the stable-confederal Yoneda embedding of an
-- Atlas federation.  'embedAtlasFederation' checks the federation refinement
-- at the boundary; presheaf values are morphisms into its underlying
-- confederation.
data EmbeddedAtlasFederation federationScope index

type role EmbeddedAtlasFederationValue nominal nominal nominal
newtype EmbeddedAtlasFederationValue federationScope index confederation =
  EmbeddedAtlasFederationValue
    (AtlasConfederationHom
      confederation
      (AtlasConfederationObject federationScope index))

type instance
  StableConfederalDataValue
    (EmbeddedAtlasFederation federationScope index)
    confederation =
      EmbeddedAtlasFederationValue
        federationScope index confederation

embeddedAtlasFederationValue
  :: AtlasConfederationHom
       confederation
       (AtlasConfederationObject federationScope index)
  -> EmbeddedAtlasFederationValue
       federationScope index confederation
embeddedAtlasFederationValue = EmbeddedAtlasFederationValue

withEmbeddedAtlasFederationValue
  :: EmbeddedAtlasFederationValue
       federationScope index confederation
  -> ( AtlasConfederationHom
         confederation
         (AtlasConfederationObject federationScope index)
       -> result
     )
  -> result
withEmbeddedAtlasFederationValue
    (EmbeddedAtlasFederationValue value) useValue =
  useValue value

-- | Embed an Atlas federation in stable confederal data by Yoneda.
embedAtlasFederation
  :: AtlasFederation federationScope index
  -> StableConfederalData
       (EmbeddedAtlasFederation federationScope index)
embedAtlasFederation federation =
  atlasFederationConfederation federation `seq`
    stableConfederalData
      (\arrow (EmbeddedAtlasFederationValue value) ->
        EmbeddedAtlasFederationValue
          (composeAtlasConfederationHoms value arrow))
      (const ())
      (\_ _ _ -> ())

-- | Carrier of the DaTra presheaf obtained by forgetting an Atlas federation.
type ForgottenAtlasFederation federationScope index =
  ForgottenStableConfederalData
    (EmbeddedAtlasFederation federationScope index)

-- | Forget an Atlas federation to DaTra.  This is Yoneda into stable
-- confederal data followed by singleton restriction and left Kan extension.
forgetAtlasFederationToDataTransformation
  :: AtlasFederation federationScope index
  -> DataTransformation
       (ForgottenAtlasFederation federationScope index)
forgetAtlasFederationToDataTransformation =
  forgetStableConfederalDataToDataTransformation
    . embedAtlasFederation
