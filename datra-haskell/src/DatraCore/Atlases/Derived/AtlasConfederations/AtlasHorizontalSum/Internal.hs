-- | Hidden implementation of the Atlas horizontal sum.
module AtlasHorizontalSum.Internal
  ( AtlasConfederationIsomorphism
  , atlasHorizontalSum
  , atlasHorizontalSumHom
  , horizontalLemma
  , atlasBraiderHom
  , atlasBraider
  , atlasAssociatorHom
  , atlasAssociatorInv
  , atlasAssociator
  , atlasLeftUnitorHom
  , atlasLeftUnitorInv
  , atlasLeftUnitor
  , atlasRightUnitorHom
  , atlasRightUnitorInv
  , atlasRightUnitor
  ) where

import AtlasConfederation
  ( AtlasConfederation
  , AtlasConfederationComponent
  , AtlasConfederationHom
  , AtlasConfederationObject
  , EmptyAtlasConfederationScope
  , MergedAtlasConfederationScope
  , atlasConfederationComponent
  , atlasConfederationHom
  , emptyAtlasConfederation
  , identityAtlasConfederationComponentHom
  , mergeAtlasConfederationHoms
  , mergeAtlasConfederations
  )
import Data.Void (Void, absurd)

-- | A confederation isomorphism represented by its forward and inverse
-- morphisms, following the pair convention used by the other Haskell APIs.
type AtlasConfederationIsomorphism source target =
  ( AtlasConfederationHom source target
  , AtlasConfederationHom target source
  )

type HorizontalSumObject leftScope leftIndex rightScope rightIndex =
  AtlasConfederationObject
    (MergedAtlasConfederationScope leftScope rightScope)
    (Either leftIndex rightIndex)

type LeftAssociatedObject
    leftScope leftIndex middleScope middleIndex rightScope rightIndex =
  HorizontalSumObject
    (MergedAtlasConfederationScope leftScope middleScope)
    (Either leftIndex middleIndex)
    rightScope
    rightIndex

type RightAssociatedObject
    leftScope leftIndex middleScope middleIndex rightScope rightIndex =
  HorizontalSumObject
    leftScope
    leftIndex
    (MergedAtlasConfederationScope middleScope rightScope)
    (Either middleIndex rightIndex)

identityComponentAt
  :: AtlasConfederation scope index
  -> index
  -> AtlasConfederationComponent
identityComponentAt = atlasConfederationComponent

reindexingHom
  :: AtlasConfederation sourceScope sourceIndex
  -> AtlasConfederation targetScope targetIndex
  -> (sourceIndex -> targetIndex)
  -> AtlasConfederationHom
       (AtlasConfederationObject sourceScope sourceIndex)
       (AtlasConfederationObject targetScope targetIndex)
reindexingHom source target indexMap =
  atlasConfederationHom
    source
    target
    indexMap
    (identityAtlasConfederationComponentHom . identityComponentAt source)

-- | The object action of the Atlas horizontal-sum bifunctor. It preserves the
-- left and right tags and merges their stored Atlas presentations.
atlasHorizontalSum
  :: AtlasConfederation leftScope leftIndex
  -> AtlasConfederation rightScope rightIndex
  -> AtlasConfederation
       (MergedAtlasConfederationScope leftScope rightScope)
       (Either leftIndex rightIndex)
atlasHorizontalSum = mergeAtlasConfederations

-- | The arrow action of the Atlas horizontal-sum bifunctor. Each component
-- morphism is applied independently on its side of the disjoint tag union.
atlasHorizontalSumHom
  :: AtlasConfederation leftSourceScope leftSourceIndex
  -> AtlasConfederation rightSourceScope rightSourceIndex
  -> AtlasConfederation leftTargetScope leftTargetIndex
  -> AtlasConfederation rightTargetScope rightTargetIndex
  -> AtlasConfederationHom
       (AtlasConfederationObject leftSourceScope leftSourceIndex)
       (AtlasConfederationObject leftTargetScope leftTargetIndex)
  -> AtlasConfederationHom
       (AtlasConfederationObject rightSourceScope rightSourceIndex)
       (AtlasConfederationObject rightTargetScope rightTargetIndex)
  -> AtlasConfederationHom
       (AtlasConfederationObject
         (MergedAtlasConfederationScope
           leftSourceScope rightSourceScope)
         (Either leftSourceIndex rightSourceIndex))
       (AtlasConfederationObject
         (MergedAtlasConfederationScope
           leftTargetScope rightTargetScope)
         (Either leftTargetIndex rightTargetIndex))
atlasHorizontalSumHom = mergeAtlasConfederationHoms

-- | Haskell witness of the horizontal lemma: the horizontal-sum function
-- exists and is given by 'atlasHorizontalSum'.
horizontalLemma
  :: AtlasConfederation leftScope leftIndex
  -> AtlasConfederation rightScope rightIndex
  -> AtlasConfederation
       (MergedAtlasConfederationScope leftScope rightScope)
       (Either leftIndex rightIndex)
horizontalLemma = atlasHorizontalSum

-- | Swap the left and right tags of a horizontal sum.
atlasBraiderHom
  :: AtlasConfederation leftScope leftIndex
  -> AtlasConfederation rightScope rightIndex
  -> AtlasConfederationHom
       (HorizontalSumObject leftScope leftIndex rightScope rightIndex)
       (HorizontalSumObject rightScope rightIndex leftScope leftIndex)
atlasBraiderHom left right =
  reindexingHom
    (atlasHorizontalSum left right)
    (atlasHorizontalSum right left)
    swapEither
  where
    swapEither (Left index) = Right index
    swapEither (Right index) = Left index

-- | The symmetric braider and its inverse.
atlasBraider
  :: AtlasConfederation leftScope leftIndex
  -> AtlasConfederation rightScope rightIndex
  -> AtlasConfederationIsomorphism
       (HorizontalSumObject leftScope leftIndex rightScope rightIndex)
       (HorizontalSumObject rightScope rightIndex leftScope leftIndex)
atlasBraider left right =
  (atlasBraiderHom left right, atlasBraiderHom right left)

-- | Reassociate tags from @((left + middle) + right)@ to
-- @(left + (middle + right))@.
atlasAssociatorHom
  :: AtlasConfederation leftScope leftIndex
  -> AtlasConfederation middleScope middleIndex
  -> AtlasConfederation rightScope rightIndex
  -> AtlasConfederationHom
       (LeftAssociatedObject
         leftScope leftIndex middleScope middleIndex rightScope rightIndex)
       (RightAssociatedObject
         leftScope leftIndex middleScope middleIndex rightScope rightIndex)
atlasAssociatorHom left middle right =
  reindexingHom source target associate
  where
    source = atlasHorizontalSum (atlasHorizontalSum left middle) right
    target = atlasHorizontalSum left (atlasHorizontalSum middle right)

    associate (Left (Left index)) = Left index
    associate (Left (Right index)) = Right (Left index)
    associate (Right index) = Right (Right index)

-- | Inverse reassociation of three horizontal-sum tag families.
atlasAssociatorInv
  :: AtlasConfederation leftScope leftIndex
  -> AtlasConfederation middleScope middleIndex
  -> AtlasConfederation rightScope rightIndex
  -> AtlasConfederationHom
       (RightAssociatedObject
         leftScope leftIndex middleScope middleIndex rightScope rightIndex)
       (LeftAssociatedObject
         leftScope leftIndex middleScope middleIndex rightScope rightIndex)
atlasAssociatorInv left middle right =
  reindexingHom source target unassociate
  where
    source = atlasHorizontalSum left (atlasHorizontalSum middle right)
    target = atlasHorizontalSum (atlasHorizontalSum left middle) right

    unassociate (Left index) = Left (Left index)
    unassociate (Right (Left index)) = Left (Right index)
    unassociate (Right (Right index)) = Right index

-- | The horizontal-sum associator and its inverse.
atlasAssociator
  :: AtlasConfederation leftScope leftIndex
  -> AtlasConfederation middleScope middleIndex
  -> AtlasConfederation rightScope rightIndex
  -> AtlasConfederationIsomorphism
       (LeftAssociatedObject
         leftScope leftIndex middleScope middleIndex rightScope rightIndex)
       (RightAssociatedObject
         leftScope leftIndex middleScope middleIndex rightScope rightIndex)
atlasAssociator left middle right =
  ( atlasAssociatorHom left middle right
  , atlasAssociatorInv left middle right
  )

-- | Delete the impossible left tag of @empty + value@.
atlasLeftUnitorHom
  :: AtlasConfederation scope index
  -> AtlasConfederationHom
       (HorizontalSumObject
         EmptyAtlasConfederationScope Void scope index)
       (AtlasConfederationObject scope index)
atlasLeftUnitorHom value =
  reindexingHom
    (atlasHorizontalSum emptyAtlasConfederation value)
    value
    (either absurd id)

-- | Insert a value tag into the right side of @empty + value@.
atlasLeftUnitorInv
  :: AtlasConfederation scope index
  -> AtlasConfederationHom
       (AtlasConfederationObject scope index)
       (HorizontalSumObject
         EmptyAtlasConfederationScope Void scope index)
atlasLeftUnitorInv value =
  reindexingHom
    value
    (atlasHorizontalSum emptyAtlasConfederation value)
    Right

-- | The left unitor and its inverse.
atlasLeftUnitor
  :: AtlasConfederation scope index
  -> AtlasConfederationIsomorphism
       (HorizontalSumObject
         EmptyAtlasConfederationScope Void scope index)
       (AtlasConfederationObject scope index)
atlasLeftUnitor value =
  (atlasLeftUnitorHom value, atlasLeftUnitorInv value)

-- | Delete the impossible right tag of @value + empty@.
atlasRightUnitorHom
  :: AtlasConfederation scope index
  -> AtlasConfederationHom
       (HorizontalSumObject
         scope index EmptyAtlasConfederationScope Void)
       (AtlasConfederationObject scope index)
atlasRightUnitorHom value =
  reindexingHom
    (atlasHorizontalSum value emptyAtlasConfederation)
    value
    (either id absurd)

-- | Insert a value tag into the left side of @value + empty@.
atlasRightUnitorInv
  :: AtlasConfederation scope index
  -> AtlasConfederationHom
       (AtlasConfederationObject scope index)
       (HorizontalSumObject
         scope index EmptyAtlasConfederationScope Void)
atlasRightUnitorInv value =
  reindexingHom
    value
    (atlasHorizontalSum value emptyAtlasConfederation)
    Left

-- | The right unitor and its inverse.
atlasRightUnitor
  :: AtlasConfederation scope index
  -> AtlasConfederationIsomorphism
       (HorizontalSumObject
         scope index EmptyAtlasConfederationScope Void)
       (AtlasConfederationObject scope index)
atlasRightUnitor value =
  (atlasRightUnitorHom value, atlasRightUnitorInv value)
