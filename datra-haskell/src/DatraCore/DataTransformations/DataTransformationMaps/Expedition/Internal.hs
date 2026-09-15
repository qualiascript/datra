{-# LANGUAGE CPP #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE RoleAnnotations #-}
{-# LANGUAGE TypeFamilies #-}
-- GHC does not count names referenced only by LiquidHaskell specifications.
{-# OPTIONS_GHC -Wno-unused-imports #-}
#include "../../../LiquidPlugin.h"
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}
{-@ LIQUID "--higherorder" @-}

-- | Hidden implementation of expeditions into DaTra sets.
module Expedition.Internal
  ( Expedition
  , expedition
  , expeditionFromNavigation
  , expeditionAtlasMap
  , expeditionNavigation
  , expeditionAtlas
  , expeditionHom
  , mapExpedition
  , expeditionPreimage
  , expeditionLeftInverse
  ) where

import Atlas (AtlasWitness)
import AtlasMap (AtlasMap, atlasMapAtlas)
import Data.Kind (Type)
import DataTransformation.Internal
  ( DataTransformationHom
  , DataTransformationValue
  , Yoneda
  , YonedaPresheaf
  )
import Navigation.Internal
  ( Navigation
  , mapNavigationHom
  , mapNavigation
  , navigation
  , navigationAtlas
  , navigationHom
  , navigationLeftInverse
  , navigationPreimage
  )

-- | A navigation whose representing Atlas satisfies @IsAtlasMap@.
--
-- 'AtlasMap' is the Haskell witness for Lean's @IsAtlasMap A@ field. The
-- shared @atlas@ index keeps that witness aligned with the representable
-- source of the navigation.
type role Expedition nominal nominal
data Expedition
  (atlas :: Type)
  (values :: Type) = Expedition
  (AtlasMap atlas)
  (Navigation atlas values)

-- | Construct an expedition directly from its Atlas-map witness, natural
-- transformation, and componentwise monomorphism certificate.
{-@
expedition
  :: valueAtlasMap:AtlasMap atlas
  -> hom:DataTransformationHom (YonedaPresheaf atlas) values
  -> preimageFunction:(forall object.
       DataTransformationValue values object
       -> Maybe (Yoneda atlas object))
  -> leftInverse:(forall object.
       source:Yoneda atlas object
       -> { proof:() |
            preimageFunction (mapNavigationHom hom source)
            == Just source })
  -> Expedition atlas values
@-}
expedition
  :: AtlasMap atlas
  -> DataTransformationHom (YonedaPresheaf atlas) values
  -> (forall object.
       DataTransformationValue values object
       -> Maybe (Yoneda atlas object))
  -> (forall object. Yoneda atlas object -> ())
  -> Expedition atlas values
expedition valueAtlasMap hom preimageFunction leftInverse =
  Expedition
    valueAtlasMap
    (navigation
      (atlasMapAtlas valueAtlasMap)
      hom
      preimageFunction
      leftInverse)

-- | Refine an existing navigation after supplying the @IsAtlasMap@ witness
-- for its representing Atlas.
expeditionFromNavigation
  :: AtlasMap atlas
  -> Navigation atlas values
  -> Expedition atlas values
expeditionFromNavigation = Expedition

-- | Recover the Atlas-map restriction on the representing object.
expeditionAtlasMap :: Expedition atlas values -> AtlasMap atlas
expeditionAtlasMap (Expedition valueAtlasMap _) = valueAtlasMap

-- | Forget the Atlas-map restriction and retain the underlying navigation.
expeditionNavigation
  :: Expedition atlas values
  -> Navigation atlas values
expeditionNavigation (Expedition _ valueNavigation) = valueNavigation

-- | Recover the representing Atlas, corresponding to the inherited @A@
-- field of Lean's @Expedition@ structure.
expeditionAtlas :: Expedition atlas values -> AtlasWitness atlas
expeditionAtlas = navigationAtlas . expeditionNavigation

-- | Recover the natural transformation @Yo(A) ⟶ D@.
expeditionHom
  :: Expedition atlas values
  -> DataTransformationHom (YonedaPresheaf atlas) values
expeditionHom = navigationHom . expeditionNavigation

-- | Evaluate the underlying navigation at one Atlas component.
mapExpedition
  :: Expedition atlas values
  -> Yoneda atlas object
  -> DataTransformationValue values object
mapExpedition = mapNavigation . expeditionNavigation

-- | Try to recover a Yoneda element from the expedition's image.
expeditionPreimage
  :: Expedition atlas values
  -> DataTransformationValue values object
  -> Maybe (Yoneda atlas object)
expeditionPreimage = navigationPreimage . expeditionNavigation

-- | Invoke the underlying navigation's componentwise left-inverse witness.
expeditionLeftInverse
  :: Expedition atlas values
  -> Yoneda atlas object
  -> ()
expeditionLeftInverse = navigationLeftInverse . expeditionNavigation
