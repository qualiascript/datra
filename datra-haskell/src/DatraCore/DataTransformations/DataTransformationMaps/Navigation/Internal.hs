{-# LANGUAGE CPP #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE RoleAnnotations #-}
{-# LANGUAGE TypeFamilies #-}
#include "../../../LiquidPlugin.h"
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}
{-@ LIQUID "--higherorder" @-}

-- | Hidden implementation of navigations into DaTra sets.
module Navigation.Internal
  ( Navigation
  , navigation
  , navigationAtlas
  , navigationHom
  , mapNavigation
  , navigationPreimage
  , navigationLeftInverse
  , mapNavigationHom
  ) where

import Atlas (AtlasWitness)
import Data.Kind (Type)
import DataTransformation.Internal
  ( DataTransformationHom
  , DataTransformationValue
  , Yoneda
  , YonedaPresheaf
  , mapDataTransformationHom
  )

-- | The componentwise partial inverse of a navigation.
--
-- A separate rank-N wrapper lets LiquidHaskell refer to each specialization
-- in the monomorphism law without exposing the representation publicly.
type role NavigationPreimage nominal nominal
data NavigationPreimage
  (atlas :: Type)
  (values :: Type) = NavigationPreimage
  (forall object.
    DataTransformationValue values object
    -> Maybe (Yoneda atlas object))

{-@ reflect applyNavigationPreimage @-}
applyNavigationPreimage
  :: NavigationPreimage atlas values
  -> DataTransformationValue values object
  -> Maybe (Yoneda atlas object)
applyNavigationPreimage (NavigationPreimage preimage) = preimage

-- | Specialize a natural transformation component to a Yoneda source. This
-- named specialization exposes the @DataTransformationValue@ type-family
-- reduction to LiquidHaskell's logic.
{-@ reflect mapNavigationHom @-}
mapNavigationHom
  :: DataTransformationHom (YonedaPresheaf atlas) values
  -> Yoneda atlas object
  -> DataTransformationValue values object
mapNavigationHom = mapDataTransformationHom

-- | A navigation represented at a named Atlas object.
--
-- This is the direct executable counterpart of Lean's @Navigation D@: the
-- Atlas witness is @A@, the natural transformation is @Yo(A) ⟶ D@, and
-- the componentwise left inverse witnesses that transformation as monic.
-- Monomorphisms in a presheaf category are exactly the pointwise injections.
type role Navigation nominal nominal
{-@
data Navigation atlas values = Navigation
  { storedNavigationAtlas :: AtlasWitness atlas
  , storedNavigationHom :: DataTransformationHom
      (YonedaPresheaf atlas) values
  , storedNavigationPreimage :: NavigationPreimage atlas values
  , storedNavigationLeftInverse :: forall object.
      source:Yoneda atlas object
      -> { proof:() |
           applyNavigationPreimage storedNavigationPreimage
             (mapNavigationHom storedNavigationHom source)
           == Just source }
  }
@-}
data Navigation
  (atlas :: Type)
  (values :: Type) = Navigation
  (AtlasWitness atlas)
  (DataTransformationHom (YonedaPresheaf atlas) values)
  (NavigationPreimage atlas values)
  (forall object. Yoneda atlas object -> ())

-- | Construct a navigation from a natural transformation and a pointwise
-- partial left inverse. LiquidHaskell checks the left-inverse equation at
-- every Atlas component, which supplies Lean's @Mono hom@ field.
{-@
navigation
  :: atlasWitness:AtlasWitness atlas
  -> hom:DataTransformationHom (YonedaPresheaf atlas) values
  -> preimageFunction:(forall object.
       DataTransformationValue values object
       -> Maybe (Yoneda atlas object))
  -> leftInverse:(forall object.
       source:Yoneda atlas object
       -> { proof:() |
            preimageFunction (mapNavigationHom hom source)
            == Just source })
  -> Navigation atlas values
@-}
navigation
  :: AtlasWitness atlas
  -> DataTransformationHom (YonedaPresheaf atlas) values
  -> (forall object.
       DataTransformationValue values object
       -> Maybe (Yoneda atlas object))
  -> (forall object. Yoneda atlas object -> ())
  -> Navigation atlas values
navigation atlasWitness hom preimageFunction =
  Navigation
    atlasWitness
    hom
    (NavigationPreimage preimageFunction)

-- | Recover the representing Atlas object.
navigationAtlas :: Navigation atlas values -> AtlasWitness atlas
navigationAtlas (Navigation atlasWitness _ _ _) = atlasWitness

-- | Forget the monomorphism certificate and recover @Yo(A) ⟶ D@.
navigationHom
  :: Navigation atlas values
  -> DataTransformationHom (YonedaPresheaf atlas) values
navigationHom (Navigation _ hom _ _) = hom

-- | Evaluate the navigation at one Atlas component.
{-@ reflect mapNavigation @-}
mapNavigation
  :: Navigation atlas values
  -> Yoneda atlas object
  -> DataTransformationValue values object
mapNavigation (Navigation _ hom _ _) = mapNavigationHom hom

-- | Try to recover a Yoneda element from the image of a navigation.
{-@ reflect navigationPreimage @-}
navigationPreimage
  :: Navigation atlas values
  -> DataTransformationValue values object
  -> Maybe (Yoneda atlas object)
navigationPreimage (Navigation _ _ preimageFunction _) =
  applyNavigationPreimage preimageFunction

-- | Invoke the stored componentwise left-inverse certificate.
{-@
navigationLeftInverse
  :: valueNavigation:Navigation atlas values
  -> source:Yoneda atlas object
  -> { proof:() |
       navigationPreimage valueNavigation
         (mapNavigation valueNavigation source)
       == Just source }
@-}
navigationLeftInverse
  :: Navigation atlas values
  -> Yoneda atlas object
  -> ()
navigationLeftInverse (Navigation _ _ _ leftInverse) = leftInverse
