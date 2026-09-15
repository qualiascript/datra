{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE RoleAnnotations #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}

-- | Hidden implementation of Day convolution on stable confederal data
-- transversals.
module HorizontalSum.Internal
  ( HorizontalSumValues
  , HorizontalSumValue (..)
  , horizontalSumValue
  , horizontalSum
  , (|+|)
  , horizontalSumHom
  ) where

import AtlasConfederation
  ( AtlasConfederation
  , AtlasConfederationHom
  , AtlasConfederationObject
  , MergedAtlasConfederationScope
  , composeAtlasConfederationHoms
  , identityAtlasConfederationHom
  )
import Data.Kind (Type)
import Prelude (Either, const)
import StableConfederalDataTransversal
  ( StableConfederalDataTransversal
  , StableConfederalDataTransversalHom
  , StableConfederalDataTransversalValue
  , mapStableConfederalDataTransversalHom
  , stableConfederalDataTransversal
  , stableConfederalDataTransversalHom
  )

-- | Defunctionalized carrier for the Day convolution of two stable
-- confederal data transversals.
data HorizontalSumValues (left :: Type) (right :: Type)

-- | A Day-convolution generator at @object@.
--
-- It consists of left and right Atlas confederations, a value of each input
-- presheaf at those confederations, and an arrow from @object@ into their
-- Atlas horizontal sum.
type role HorizontalSumValue nominal nominal nominal
data HorizontalSumValue
  (left :: Type)
  (right :: Type)
  (object :: Type) where
  HorizontalSumValue
    :: AtlasConfederation leftScope leftIndex
    -> AtlasConfederation rightScope rightIndex
    -> AtlasConfederationHom
         object
         (AtlasConfederationObject
           (MergedAtlasConfederationScope leftScope rightScope)
           (Either leftIndex rightIndex))
    -> StableConfederalDataTransversalValue
         left (AtlasConfederationObject leftScope leftIndex)
    -> StableConfederalDataTransversalValue
         right (AtlasConfederationObject rightScope rightIndex)
    -> HorizontalSumValue left right object

type instance
  StableConfederalDataTransversalValue
    (HorizontalSumValues left right) object =
      HorizontalSumValue left right object

-- | Introduce a generator at the horizontal sum of its two indexing
-- confederations.
horizontalSumValue
  :: AtlasConfederation leftScope leftIndex
  -> AtlasConfederation rightScope rightIndex
  -> StableConfederalDataTransversalValue
       left (AtlasConfederationObject leftScope leftIndex)
  -> StableConfederalDataTransversalValue
       right (AtlasConfederationObject rightScope rightIndex)
  -> HorizontalSumValue
       left
       right
       (AtlasConfederationObject
         (MergedAtlasConfederationScope leftScope rightScope)
         (Either leftIndex rightIndex))
horizontalSumValue left right =
  HorizontalSumValue left right identityAtlasConfederationHom

-- | Day convolution extending Atlas horizontal sum to stable confederal data
-- transversals.
horizontalSum
  :: StableConfederalDataTransversal left
  -> StableConfederalDataTransversal right
  -> StableConfederalDataTransversal (HorizontalSumValues left right)
horizontalSum _ _ =
  stableConfederalDataTransversal
    reindex
    (const ())
    (\_ _ _ -> ())
  where
    reindex
      :: AtlasConfederationHom source target
      -> HorizontalSumValue left right target
      -> HorizontalSumValue left right source
    reindex arrow
      (HorizontalSumValue left right represented leftValue rightValue) =
        HorizontalSumValue
          left
          right
          (composeAtlasConfederationHoms represented arrow)
          leftValue
          rightValue

-- | Infix alias for 'horizontalSum'.
infixr 6 |+|

(|+|)
  :: StableConfederalDataTransversal left
  -> StableConfederalDataTransversal right
  -> StableConfederalDataTransversal (HorizontalSumValues left right)
(|+|) = horizontalSum

-- | Apply two natural transformations under horizontal sum.
horizontalSumHom
  :: forall leftSource rightSource leftTarget rightTarget.
     StableConfederalDataTransversal leftSource
  -> StableConfederalDataTransversal rightSource
  -> StableConfederalDataTransversal leftTarget
  -> StableConfederalDataTransversal rightTarget
  -> StableConfederalDataTransversalHom leftSource leftTarget
  -> StableConfederalDataTransversalHom rightSource rightTarget
  -> StableConfederalDataTransversalHom
       (HorizontalSumValues leftSource rightSource)
       (HorizontalSumValues leftTarget rightTarget)
horizontalSumHom
  leftSource rightSource leftTarget rightTarget leftHom rightHom =
    stableConfederalDataTransversalHom
      (horizontalSum leftSource rightSource)
      (horizontalSum leftTarget rightTarget)
      mapComponents
      (\_ _ -> ())
  where
    mapComponents
      :: HorizontalSumValue leftSource rightSource object
      -> HorizontalSumValue leftTarget rightTarget object
    mapComponents
      (HorizontalSumValue left right represented leftValue rightValue) =
        HorizontalSumValue
          left
          right
          represented
          (mapStableConfederalDataTransversalHom leftHom leftValue)
          (mapStableConfederalDataTransversalHom rightHom rightValue)
