{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE RoleAnnotations #-}
{-# LANGUAGE TypeFamilies #-}

-- | Hidden representation of Atlas confederations and their morphisms.
module AtlasConfederation.Internal
  ( AtlasMergePresentation (..)
  , atlasMergePresentationSize
  , withAtlasMergePresentationAtlas
  , AtlasConfederationComponent
  , atlasConfederationComponentWitness
  , withAtlasConfederationComponent
  , AtlasConfederation (..)
  , EmptyAtlasConfederationScope
  , emptyAtlasConfederation
  , atlasConfederation
  , atlasConfederationIndexDominion
  , atlasConfederationComponent
  , atlasConfederationPresentation
  , withAtlasConfederationResultingAtlas
  , forgetAtlasConfederationTags
  , AtlasConfederationObject
  , AtlasConfederationObjectIndex
  , AtlasConfederationWitness
  , atlasConfederationWitness
  , AtlasConfederationComponentHom
  , atlasConfederationComponentHom
  , identityAtlasConfederationComponentHom
  , composeAtlasConfederationComponentHoms
  , foldAtlasConfederationComponentHom
  , atlasConfederationComponentHomStable
  , AtlasConfederationHom
  , atlasConfederationHom
  , identityAtlasConfederationHom
  , composeAtlasConfederationHoms
  , mapAtlasConfederationIndex
  , mapAtlasConfederationComponent
  , targetAtlasConfederationWitness
  , SingletonAtlasConfederationScope
  , MergedAtlasConfederationScope
  , singletonAtlasConfederation
  , singletonAtlasConfederationHom
  , mergeAtlasConfederations
  , leftAtlasConfederationInclusion
  , rightAtlasConfederationInclusion
  , mergeAtlasConfederationHoms
  ) where

import Atlas
  ( Atlas
  , AtlasObject
  , AtlasWitness
  , atlasWitness
  )
import Atlas.Morphism.Internal (AtlasWitness (..))
import AtlasMerge (atlasMerge)
import Control.Category (Category (..))
import Data.Kind (Type)
import Data.Type.Equality ((:~:) (Refl))
import Data.Void (Void, absurd)
import Dominion (Dominion, dominion, rank, unrank)
import EmptyAtlas (emptyAtlas)
import Numeric.Natural (Natural)
import Prelude hiding ((.), id)
import StableAtlasTransversal
  ( StableAtlasTransversal
  , stableAtlasTransversalPreservesExtent
  )

-- | A syntax tree recording how the resulting Atlas of a confederation was
-- assembled.  Atlas objects are existential because different atoms may use
-- unrelated pagination scopes and dependent data families.
data AtlasMergePresentation where
  EmptyAtlasMergePresentation :: AtlasMergePresentation
  AtlasMergeAtom
    :: AtlasWitness atlasObject
    -> AtlasMergePresentation
  AtlasMergeNode
    :: AtlasMergePresentation
    -> AtlasMergePresentation
    -> AtlasMergePresentation

-- | Number of Atlas atoms retained by a merge presentation.
atlasMergePresentationSize :: AtlasMergePresentation -> Natural
atlasMergePresentationSize EmptyAtlasMergePresentation = 0
atlasMergePresentationSize (AtlasMergeAtom _) = 1
atlasMergePresentationSize (AtlasMergeNode left right) =
  atlasMergePresentationSize left + atlasMergePresentationSize right

-- | Evaluate a presentation to its concrete Atlas.  The rank-polymorphic
-- continuation hides the different dependent data family introduced by each
-- node of the tree.
withAtlasMergePresentationAtlas
  :: AtlasMergePresentation
  -> (forall atlasScope paginationScope cellData origin final.
       Atlas atlasScope paginationScope cellData origin final
       -> result)
  -> result
withAtlasMergePresentationAtlas EmptyAtlasMergePresentation useAtlas =
  emptyAtlas useAtlas
withAtlasMergePresentationAtlas
  (AtlasMergeAtom (AtlasWitness valueAtlas)) useAtlas =
    useAtlas valueAtlas
withAtlasMergePresentationAtlas (AtlasMergeNode left right) useAtlas =
  withAtlasMergePresentationAtlas left $ \leftAtlas ->
    withAtlasMergePresentationAtlas right $ \rightAtlas ->
      atlasMerge leftAtlas rightAtlas useAtlas

-- | One existentially named stable-Atlas object in a confederation.
data AtlasConfederationComponent where
  AtlasConfederationComponent
    :: AtlasWitness atlasObject
    -> AtlasConfederationComponent

atlasConfederationComponentWitness
  :: AtlasWitness atlasObject
  -> AtlasConfederationComponent
atlasConfederationComponentWitness = AtlasConfederationComponent

withAtlasConfederationComponent
  :: AtlasConfederationComponent
  -> (forall atlasObject. AtlasWitness atlasObject -> result)
  -> result
withAtlasConfederationComponent
  (AtlasConfederationComponent witness) useComponent =
    useComponent witness

-- | A countably tagged family of stable Atlas objects together with the merge
-- presentation producing its resulting Atlas.  @confederationScope@ is a
-- nominal token naming this category object independently of its index carrier.
type role AtlasConfederation nominal nominal
data AtlasConfederation (confederationScope :: Type) index = AtlasConfederation
  (Dominion index)
  (index -> AtlasConfederationComponent)
  AtlasMergePresentation

-- | Type-level name for the canonical empty confederation.
data EmptyAtlasConfederationScope

emptyDominion :: Dominion Void
emptyDominion = dominion absurd (const Nothing) absurd

-- | The confederation with no tagged components and an 'EmptyAtlas' result.
emptyAtlasConfederation
  :: AtlasConfederation EmptyAtlasConfederationScope Void
emptyAtlasConfederation =
  AtlasConfederation
    emptyDominion
    absurd
    EmptyAtlasMergePresentation

-- | Introduce an Atlas confederation with a fresh object identity.
atlasConfederation
  :: Dominion index
  -> (index -> AtlasConfederationComponent)
  -> AtlasMergePresentation
  -> (forall confederationScope.
       AtlasConfederation confederationScope index -> result)
  -> result
atlasConfederation indexDominion components presentation useConfederation =
  useConfederation
    (AtlasConfederation indexDominion components presentation)

atlasConfederationIndexDominion
  :: AtlasConfederation confederationScope index
  -> Dominion index
atlasConfederationIndexDominion
  (AtlasConfederation indexDominion _ _) = indexDominion

atlasConfederationComponent
  :: AtlasConfederation confederationScope index
  -> index
  -> AtlasConfederationComponent
atlasConfederationComponent (AtlasConfederation _ components _) = components

atlasConfederationPresentation
  :: AtlasConfederation confederationScope index
  -> AtlasMergePresentation
atlasConfederationPresentation
  (AtlasConfederation _ _ presentation) = presentation

-- | Evaluate the stored presentation and forget the component tags.
withAtlasConfederationResultingAtlas
  :: AtlasConfederation confederationScope index
  -> (forall atlasScope paginationScope cellData origin final.
       Atlas atlasScope paginationScope cellData origin final
       -> result)
  -> result
withAtlasConfederationResultingAtlas confederation =
  withAtlasMergePresentationAtlas
    (atlasConfederationPresentation confederation)

-- | Semantic alias emphasizing that presentation evaluation discards tags.
forgetAtlasConfederationTags
  :: AtlasConfederation confederationScope index
  -> (forall atlasScope paginationScope cellData origin final.
       Atlas atlasScope paginationScope cellData origin final
       -> result)
  -> result
forgetAtlasConfederationTags = withAtlasConfederationResultingAtlas

-- | Type-level name of an Atlas-confederation category object.
data AtlasConfederationObject (confederationScope :: Type) index

type family AtlasConfederationObjectIndex object :: Type where
  AtlasConfederationObjectIndex
    (AtlasConfederationObject confederationScope index) = index

type role AtlasConfederationWitness nominal
data AtlasConfederationWitness object where
  AtlasConfederationWitness
    :: AtlasConfederation confederationScope index
    -> AtlasConfederationWitness
         (AtlasConfederationObject confederationScope index)

atlasConfederationWitness
  :: AtlasConfederation confederationScope index
  -> AtlasConfederationWitness
       (AtlasConfederationObject confederationScope index)
atlasConfederationWitness = AtlasConfederationWitness

-- | An existential stable component arrow.  Composition is retained as
-- syntax because its intermediate Atlas identity depends on a runtime tag;
-- every primitive leaf nevertheless remains a fully typed stable transversal.
data AtlasConfederationComponentHom where
  PrimitiveAtlasConfederationComponentHom
    :: AtlasWitness source
    -> AtlasWitness target
    -> StableAtlasTransversal source target
    -> AtlasConfederationComponentHom
  IdentityAtlasConfederationComponentHom
    :: AtlasWitness object
    -> AtlasConfederationComponentHom
  CompositeAtlasConfederationComponentHom
    :: AtlasConfederationComponentHom
    -> AtlasConfederationComponentHom
    -> AtlasConfederationComponentHom

atlasConfederationComponentHom
  :: AtlasWitness source
  -> AtlasWitness target
  -> StableAtlasTransversal source target
  -> AtlasConfederationComponentHom
atlasConfederationComponentHom =
  PrimitiveAtlasConfederationComponentHom

identityAtlasConfederationComponentHom
  :: AtlasConfederationComponent
  -> AtlasConfederationComponentHom
identityAtlasConfederationComponentHom
  (AtlasConfederationComponent witness) =
    IdentityAtlasConfederationComponentHom witness

composeAtlasConfederationComponentHoms
  :: AtlasConfederationComponentHom
  -> AtlasConfederationComponentHom
  -> AtlasConfederationComponentHom
composeAtlasConfederationComponentHoms
  (IdentityAtlasConfederationComponentHom _) first = first
composeAtlasConfederationComponentHoms
  second (IdentityAtlasConfederationComponentHom _) = second
composeAtlasConfederationComponentHoms second first =
  CompositeAtlasConfederationComponentHom second first

-- | Eliminate identity, primitive, and composition nodes without exposing the
-- private representation.
foldAtlasConfederationComponentHom
  :: (forall object. AtlasWitness object -> result)
  -> (forall source target.
       AtlasWitness source
       -> AtlasWitness target
       -> StableAtlasTransversal source target
       -> result)
  -> (result -> result -> result)
  -> AtlasConfederationComponentHom
  -> result
foldAtlasConfederationComponentHom onIdentity _ _
  (IdentityAtlasConfederationComponentHom witness) =
    onIdentity witness
foldAtlasConfederationComponentHom _ onPrimitive _
  (PrimitiveAtlasConfederationComponentHom source target transversal) =
    onPrimitive source target transversal
foldAtlasConfederationComponentHom onIdentity onPrimitive onComposition
  (CompositeAtlasConfederationComponentHom second first) =
    onComposition
      (foldAtlasConfederationComponentHom
        onIdentity onPrimitive onComposition second)
      (foldAtlasConfederationComponentHom
        onIdentity onPrimitive onComposition first)

-- | Invoke the extent-preservation evidence at every primitive component.
atlasConfederationComponentHomStable
  :: AtlasConfederationComponentHom
  -> ()
atlasConfederationComponentHomStable =
  foldAtlasConfederationComponentHom
    (const ())
    (\_ _ transversal -> stableAtlasTransversalPreservesExtent transversal)
    seq

-- | Morphisms of Atlas confederations.  A primitive carries a tag map and one
-- stable component arrow per source tag.  Identity and composition are syntax
-- nodes, matching the coherent representation used by 'AtlasHom'.
type role AtlasConfederationHom nominal nominal
data AtlasConfederationHom source target
  = forall sourceFamily targetFamily sourceIndex targetIndex.
    PrimitiveAtlasConfederationHom
      (source :~:
        AtlasConfederationObject sourceFamily sourceIndex)
      (target :~:
        AtlasConfederationObject targetFamily targetIndex)
      (AtlasConfederation sourceFamily sourceIndex)
      (AtlasConfederation targetFamily targetIndex)
      (sourceIndex -> targetIndex)
      (sourceIndex -> AtlasConfederationComponentHom)
  | IdentityAtlasConfederationHom (source :~: target)
  | forall middle.
    CompositeAtlasConfederationHom
      (AtlasConfederationHom middle target)
      (AtlasConfederationHom source middle)

atlasConfederationHom
  :: AtlasConfederation sourceFamily sourceIndex
  -> AtlasConfederation targetFamily targetIndex
  -> (sourceIndex -> targetIndex)
  -> (sourceIndex -> AtlasConfederationComponentHom)
  -> AtlasConfederationHom
       (AtlasConfederationObject sourceFamily sourceIndex)
       (AtlasConfederationObject targetFamily targetIndex)
atlasConfederationHom = PrimitiveAtlasConfederationHom
    Refl Refl

identityAtlasConfederationHom :: AtlasConfederationHom object object
identityAtlasConfederationHom = IdentityAtlasConfederationHom Refl

composeAtlasConfederationHoms
  :: AtlasConfederationHom middle target
  -> AtlasConfederationHom source middle
  -> AtlasConfederationHom source target
composeAtlasConfederationHoms
  (IdentityAtlasConfederationHom Refl) first = first
composeAtlasConfederationHoms
  second (IdentityAtlasConfederationHom Refl) = second
composeAtlasConfederationHoms second
  (CompositeAtlasConfederationHom middle first) =
    CompositeAtlasConfederationHom
      (composeAtlasConfederationHoms second middle)
      first
composeAtlasConfederationHoms second first =
  CompositeAtlasConfederationHom second first

instance Category AtlasConfederationHom where
  id = identityAtlasConfederationHom
  (.) = composeAtlasConfederationHoms

targetAtlasConfederationWitness
  :: AtlasConfederationWitness source
  -> AtlasConfederationHom source target
  -> AtlasConfederationWitness target
targetAtlasConfederationWitness sourceWitness
  (IdentityAtlasConfederationHom Refl) = sourceWitness
targetAtlasConfederationWitness _
  (PrimitiveAtlasConfederationHom Refl Refl _ target _ _) =
    AtlasConfederationWitness target
targetAtlasConfederationWitness sourceWitness
  (CompositeAtlasConfederationHom second first) =
    targetAtlasConfederationWitness
      (targetAtlasConfederationWitness sourceWitness first)
      second

mapAtlasConfederationIndex
  :: AtlasConfederationWitness source
  -> AtlasConfederationHom source target
  -> AtlasConfederationObjectIndex source
  -> AtlasConfederationObjectIndex target
mapAtlasConfederationIndex _ (IdentityAtlasConfederationHom Refl) = id
mapAtlasConfederationIndex _
  (PrimitiveAtlasConfederationHom Refl Refl _ _ indexMap _) = indexMap
mapAtlasConfederationIndex sourceWitness
  (CompositeAtlasConfederationHom second first) =
    mapAtlasConfederationIndex
      (targetAtlasConfederationWitness sourceWitness first)
      second
      . mapAtlasConfederationIndex sourceWitness first

mapAtlasConfederationComponent
  :: AtlasConfederationWitness source
  -> AtlasConfederationHom source target
  -> AtlasConfederationObjectIndex source
  -> AtlasConfederationComponentHom
mapAtlasConfederationComponent
  (AtlasConfederationWitness source)
  (IdentityAtlasConfederationHom Refl) index =
    identityAtlasConfederationComponentHom
      (atlasConfederationComponent source index)
mapAtlasConfederationComponent _
  (PrimitiveAtlasConfederationHom Refl Refl _ _ _ componentMap) index =
    componentMap index
mapAtlasConfederationComponent sourceWitness
  (CompositeAtlasConfederationHom second first) index =
    composeAtlasConfederationComponentHoms
      (mapAtlasConfederationComponent
        (targetAtlasConfederationWitness sourceWitness first)
        second
        (mapAtlasConfederationIndex sourceWitness first index))
      (mapAtlasConfederationComponent sourceWitness first index)

unitDominion :: Dominion ()
unitDominion =
  dominion
    (const 0)
    (\valueRank -> if valueRank == 0 then Just () else Nothing)
    (const ())

sumDominions
  :: Dominion left
  -> Dominion right
  -> Dominion (Either left right)
sumDominions left right =
  dominion sumRank sumUnrank (const ())
  where
    sumRank (Left value) = 2 * rank left value
    sumRank (Right value) = 2 * rank right value + 1

    sumUnrank valueRank
      | even valueRank = Left <$> unrank left (valueRank `div` 2)
      | otherwise = Right <$> unrank right (valueRank `div` 2)

-- | Type-level names for the canonical confederation constructors.
data SingletonAtlasConfederationScope atlasObject
data MergedAtlasConfederationScope leftScope rightScope

-- | Regard one Atlas as a singleton confederation.
singletonAtlasConfederation
  :: Atlas atlasScope paginationScope cellData origin final
  -> AtlasConfederation
       (SingletonAtlasConfederationScope
         (AtlasObject atlasScope paginationScope cellData))
       ()
singletonAtlasConfederation valueAtlas =
  let witness = atlasWitness valueAtlas
  in AtlasConfederation
      unitDominion
      (const (AtlasConfederationComponent witness))
      (AtlasMergeAtom witness)

-- | The arrow action of the singleton-confederation embedding.
singletonAtlasConfederationHom
  :: Atlas
       sourceAtlasScope sourcePaginationScope sourceCellData
       sourceOrigin sourceFinal
  -> Atlas
       targetAtlasScope targetPaginationScope targetCellData
       targetOrigin targetFinal
  -> StableAtlasTransversal
       (AtlasObject
         sourceAtlasScope sourcePaginationScope sourceCellData)
       (AtlasObject
         targetAtlasScope targetPaginationScope targetCellData)
  -> AtlasConfederationHom
       (AtlasConfederationObject
         (SingletonAtlasConfederationScope
           (AtlasObject
             sourceAtlasScope sourcePaginationScope sourceCellData))
         ())
       (AtlasConfederationObject
         (SingletonAtlasConfederationScope
           (AtlasObject
             targetAtlasScope targetPaginationScope targetCellData))
         ())
singletonAtlasConfederationHom sourceAtlas targetAtlas transversal =
  atlasConfederationHom
    (singletonAtlasConfederation sourceAtlas)
    (singletonAtlasConfederation targetAtlas)
    id
    (const (atlasConfederationComponentHom
      (atlasWitness sourceAtlas)
      (atlasWitness targetAtlas)
      transversal))

-- | Retain the disjoint tags of two confederations and merge their stored
-- presentations.  This is an object operation, not a categorical coproduct.
mergeAtlasConfederations
  :: AtlasConfederation leftFamily leftIndex
  -> AtlasConfederation rightFamily rightIndex
  -> AtlasConfederation
       (MergedAtlasConfederationScope leftFamily rightFamily)
       (Either leftIndex rightIndex)
mergeAtlasConfederations left right =
  AtlasConfederation
    (sumDominions
      (atlasConfederationIndexDominion left)
      (atlasConfederationIndexDominion right))
    (either
      (atlasConfederationComponent left)
      (atlasConfederationComponent right))
    (AtlasMergeNode
      (atlasConfederationPresentation left)
      (atlasConfederationPresentation right))

-- | Include the left family into a tagged merge using identity component
-- arrows.
leftAtlasConfederationInclusion
  :: AtlasConfederation leftScope leftIndex
  -> AtlasConfederation rightScope rightIndex
  -> AtlasConfederationHom
       (AtlasConfederationObject leftScope leftIndex)
       (AtlasConfederationObject
         (MergedAtlasConfederationScope leftScope rightScope)
         (Either leftIndex rightIndex))
leftAtlasConfederationInclusion left right =
  atlasConfederationHom
    left
    (mergeAtlasConfederations left right)
    Left
    (identityAtlasConfederationComponentHom
      . atlasConfederationComponent left)

-- | Include the right family into a tagged merge using identity component
-- arrows.
rightAtlasConfederationInclusion
  :: AtlasConfederation leftScope leftIndex
  -> AtlasConfederation rightScope rightIndex
  -> AtlasConfederationHom
       (AtlasConfederationObject rightScope rightIndex)
       (AtlasConfederationObject
         (MergedAtlasConfederationScope leftScope rightScope)
         (Either leftIndex rightIndex))
rightAtlasConfederationInclusion left right =
  atlasConfederationHom
    right
    (mergeAtlasConfederations left right)
    Right
    (identityAtlasConfederationComponentHom
      . atlasConfederationComponent right)

-- | Apply two confederation morphisms componentwise to merged
-- confederations.  The tag map is 'Either'-functorial and each branch retains
-- the corresponding stable component path.
mergeAtlasConfederationHoms
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
mergeAtlasConfederationHoms
  leftSource rightSource leftTarget rightTarget leftHom rightHom =
    atlasConfederationHom
      (mergeAtlasConfederations leftSource rightSource)
      (mergeAtlasConfederations leftTarget rightTarget)
      (either
        (Left . mapAtlasConfederationIndex leftSourceWitness leftHom)
        (Right . mapAtlasConfederationIndex rightSourceWitness rightHom))
      (either
        (mapAtlasConfederationComponent leftSourceWitness leftHom)
        (mapAtlasConfederationComponent rightSourceWitness rightHom))
  where
    leftSourceWitness = atlasConfederationWitness leftSource
    rightSourceWitness = atlasConfederationWitness rightSource
