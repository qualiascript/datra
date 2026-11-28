{-# LANGUAGE CPP #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE RoleAnnotations #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
#include "../../../../LiquidPlugin.h"
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}
{-@ LIQUID "--higherorder" @-}
{-@ embed AtlasEquality * as TypeEquality @-}

-- | Symbolic Atlas syntax, materialization, and checked endpoint retention.
module Atlas.Morphism.Internal
  ( AtlasMorphism (..), AtlasMorphismImage (..), AtlasHom (..), AtlasEquality (..)
  , atlasMorphism, withAtlasMorphismImage, identityAtlasMorphism, composeAtlasMorphisms
  , identityAtlasHom, composeAtlasHoms, atlasHom, atlasHomTargetObjectEquality
  , materializeAtlasHom, atlasMorphismTargetWitness, targetAtlasWitness
  , morphismSourceOwner, morphismTargetOwner, homSourceOwner, homTargetOwner
  ) where
import Atlas.Internal (Atlas)
import Atlas.Morphism (AtlasMorphismAction, atlasMorphismSource, atlasMorphismTarget)
import Atlas.Witness.Internal
  (AtlasObjectEquality (..), withAtlasWitness, AtlasObject, AtlasObjectAtlasScope,
   AtlasObjectPaginationScope, AtlasObjectCellData, AtlasWitness, AtlasWitnessData (..),
   AtlasOwner, atlasOwner, atlasWitnessOwner, atlasWitness, atlasWitnessData)
import Data.Kind (Type)
import DomanialInsertion (DomanialInsertion)
import PageElements.Structure (PageElement)
import Atlas.Morphism.Equality.Internal (AtlasEquality (..))
import Data.Type.Equality ((:~:) (Refl))
import Control.Category (Category (..))
import Prelude hiding ((.), id)

-- | The observable image of one source cell. Its target identity remains
-- existential, keeping the target cell and its correctly indexed data
-- insertion together.
type role AtlasMorphismImage nominal nominal nominal nominal
data AtlasMorphismImage
  (targetScope :: Type)
  (sourceCellData :: Type -> Type)
  (targetCellData :: Type -> Type)
  (sourceObject :: Type) where
  AtlasMorphismImage
    :: forall targetScope sourceCellData targetCellData sourceObject targetObject.
       { materializedImageTarget :: PageElement targetScope targetObject
       , materializedImageInsertion :: DomanialInsertion
           (sourceCellData sourceObject) (targetCellData targetObject)
       } -> AtlasMorphismImage targetScope sourceCellData targetCellData sourceObject

-- | Eliminate the hidden target-cell identity of a mapped Atlas cell.
withAtlasMorphismImage
  :: AtlasMorphismImage
       targetScope sourceCellData targetCellData sourceObject
  -> (forall targetObject.
        PageElement targetScope targetObject
        -> DomanialInsertion
             (sourceCellData sourceObject)
             (targetCellData targetObject)
        -> result)
  -> result
withAtlasMorphismImage (AtlasMorphismImage target insertion) useImage =
  useImage target insertion

type role AtlasMorphism nominal nominal nominal nominal nominal nominal
data AtlasMorphism
  (sa :: Type)
  (ta :: Type)
  (ss :: Type)
  (ts :: Type)
  (sd :: Type -> Type)
  (td :: Type -> Type) where
  PrimitiveAtlasMorphism
    :: forall sa ta ss ts sd td m so sf to tf. AtlasMorphismAction
         m sa ta ss ts
         sd td
         so sf to tf
    -> AtlasMorphism
         sa ta
         ss ts sd td
  IdentityAtlasMorphism
    :: Atlas a s d o f
    -> AtlasMorphism a a s s d d
  CompositeAtlasMorphism
    :: AtlasMorphism
         ma ta
         ms ts md td
    -> AtlasMorphism
         sa ma
         ss ms sd md
    -> AtlasMorphism
         sa ta
         ss ts sd td

-- | Promote a checked primitive action to an Atlas morphism.
{-@ reflect atlasMorphism @-}
atlasMorphism
  :: AtlasMorphismAction
       m sa ta ss ts
       sd td
       so sf to tf
  -> AtlasMorphism
       sa ta
       ss ts sd td
atlasMorphism = PrimitiveAtlasMorphism

-- | The coherent identity of a particular Atlas. Its page action is the
-- normalization idempotent, not the raw full-spine identity.
-- ALIGN: ATLAS-IDENTITY-COHERENCE.
-- ALIGN: ATLAS-MATERIALIZED-IDENTITY.
-- ALIGN: ATLAS-MATERIALIZED-IDENTITY-OWNERS.
{-@ identityAtlasMorphism :: owner:Atlas a s d o f
      -> {result:AtlasMorphism a a s s d d |
           morphismSourceOwner result == atlasOwner owner
           && morphismTargetOwner result == atlasOwner owner} @-}
identityAtlasMorphism
  :: Atlas a s d o f
  -> AtlasMorphism a a s s d d
identityAtlasMorphism = IdentityAtlasMorphism

-- | Compose in categorical order. Recursive evaluation explicitly retains
-- the middle Atlas coherence, giving Karoubi composition @g . eMiddle . f@.
-- ALIGN: ATLAS-COMPOSE-COHERENCE.
-- ALIGN: ATLAS-MATERIALIZED-COMPOSITION.
-- ALIGN: ATLAS-MATERIALIZED-COMPOSITION-OWNERS.
{-@ composeAtlasMorphisms :: second:AtlasMorphism ma ta ms ts md td
      -> first:AtlasMorphism sa ma ss ms sd md
      -> {result:AtlasMorphism sa ta ss ts sd td |
           morphismSourceOwner result == morphismSourceOwner first
           && morphismTargetOwner result == morphismTargetOwner second} @-}
composeAtlasMorphisms
  :: AtlasMorphism
       ma ta
       ms ts md td
  -> AtlasMorphism
       sa ma
       ss ms sd md
  -> AtlasMorphism
       sa ta
       ss ts sd td
composeAtlasMorphisms = CompositeAtlasMorphism

-- | A genuine 'Control.Category' arrow over type-level Atlas objects.
--
-- Identity is symbolic because 'Category.id' has no value argument. It is
-- interpreted as the witnessed object's coherence morphism by
-- 'materializeAtlasHom'. Primitive arrows retain their checked
-- 'AtlasMorphism'; composition is an indexed syntax node.
type role AtlasHom nominal nominal
data AtlasHom source target
  = forall sa ta
      ss ts sd td.
    PrimitiveAtlasHom
      (source :~:
        AtlasObject sa ss sd)
      (target :~:
        AtlasObject ta ts td)
      (AtlasMorphism
        sa ta
        ss ts sd td)
  | IdentityAtlasHom (AtlasEquality source target)
  | forall middle.
    CompositeAtlasHom
      (AtlasHom middle target)
      (AtlasHom source middle)

-- | The symbolic identity used by the ordinary Atlas category.
identityAtlasHom :: AtlasHom object object
identityAtlasHom = IdentityAtlasHom (AtlasEquality Refl)

-- | Compose symbolic Atlas arrows, simplifying identity nodes eagerly.
composeAtlasHoms
  :: AtlasHom middle target
  -> AtlasHom source middle
  -> AtlasHom source target
composeAtlasHoms (IdentityAtlasHom (AtlasEquality Refl)) first = first
composeAtlasHoms second (IdentityAtlasHom (AtlasEquality Refl)) = second
composeAtlasHoms second (CompositeAtlasHom middle first) =
  CompositeAtlasHom (composeAtlasHoms second middle) first
composeAtlasHoms second first = CompositeAtlasHom second first

-- | Lift a checked semantic morphism into the ordinary category wrapper.
{-@ reflect atlasHom @-}
atlasHom
  :: AtlasMorphism
       sa ta
       ss ts sd td
  -> AtlasHom
       (AtlasObject sa ss sd)
       (AtlasObject ta ts td)
atlasHom = PrimitiveAtlasHom Refl Refl

-- | Recover the target's type indexing without materializing either owner.
atlasHomTargetObjectEquality :: AtlasWitness source -> AtlasHom source target
  -> AtlasObjectEquality target (AtlasObjectAtlasScope target) (AtlasObjectPaginationScope target) (AtlasObjectCellData target)
atlasHomTargetObjectEquality witness hom =
  withAtlasWitness witness $ \equality _ -> targetAtlasObjectEquality equality hom

-- ALIGN: ATLASHOM-TARGET-OBJECT-EQUALITY.
targetAtlasObjectEquality :: AtlasObjectEquality source a s d -> AtlasHom source target
  -> AtlasObjectEquality target (AtlasObjectAtlasScope target) (AtlasObjectPaginationScope target) (AtlasObjectCellData target)
targetAtlasObjectEquality AtlasObjectEquality (IdentityAtlasHom (AtlasEquality Refl)) = AtlasObjectEquality
targetAtlasObjectEquality _ (PrimitiveAtlasHom _ Refl _) = AtlasObjectEquality
targetAtlasObjectEquality equality (CompositeAtlasHom second first) =
  targetAtlasObjectEquality (targetAtlasObjectEquality equality first) second

-- | The target object carried by an already materialized morphism.
-- ALIGN: ATLAS-MORPHISM-TARGET-WITNESS.
{-@ atlasMorphismTargetWitness :: morphism:AtlasMorphism sa ta ss ts sd td
      -> {witness:AtlasWitness (AtlasObject ta ts td) |
           atlasWitnessOwner witness == morphismTargetOwner morphism} @-}
atlasMorphismTargetWitness
  :: forall sa ta ss ts sd td. AtlasMorphism
       sa ta
       ss ts sd td
  -> AtlasWitness
       (AtlasObject ta ts td)
atlasMorphismTargetWitness (PrimitiveAtlasMorphism action) =
  atlasWitness (atlasMorphismTarget action)
atlasMorphismTargetWitness (IdentityAtlasMorphism valueAtlas) =
  (atlasWitnessData valueAtlas :: AtlasWitnessData (AtlasObject sa ss sd) sa ss sd)
atlasMorphismTargetWitness (CompositeAtlasMorphism second _) =
  atlasMorphismTargetWitness second

-- | Recover the target witness of a symbolic arrow from its source witness.
-- Identity returns its input witness; primitive arrows recover the target
-- Atlas stored by their checked action; composition follows the two stages.
-- ALIGN: ATLASHOM-RETAINED-TARGET-WITNESS.
{-@ targetAtlasWitness :: witness:AtlasWitness source -> hom:AtlasHom source target
      -> {result:AtlasWitness target | atlasWitnessOwner result == homTargetOwner witness hom} @-}
targetAtlasWitness
  :: AtlasWitness source
  -> AtlasHom source target
  -> AtlasWitness target
targetAtlasWitness sourceWitness (IdentityAtlasHom (AtlasEquality Refl)) = sourceWitness
targetAtlasWitness _ (PrimitiveAtlasHom Refl Refl morphism) =
  atlasMorphismTargetWitness morphism
targetAtlasWitness sourceWitness (CompositeAtlasHom second first) =
  targetAtlasWitness
    (targetAtlasWitness sourceWitness first)
    second

-- | Interpret a symbolic category arrow as the checked semantic morphism for
-- a particular source object. This is where symbolic 'Category.id' becomes
-- 'identityAtlasMorphism', hence the source Atlas's coherence idempotent.
-- ALIGN: ATLAS-FINITE-NORMALIZED-EQUIVALENCE.
-- ALIGN: ATLASHOM-MATERIALIZE-COMPOSE.
-- ALIGN: ATLASHOM-MATERIALIZE.
-- ALIGN: ATLAS-RESTRICT-TALL.
-- ALIGN: ATLAS-TALL-RESTRICT.
-- ALIGN: ATLAS-CONCRETE-IDENTITY.
-- ALIGN: ATLAS-CONCRETE-COMPOSITION.
{-@ opaque-reflect materializeAtlasHom @-}
-- ALIGN: ATLASHOM-MATERIALIZED-OWNERS.
{-@ materializeAtlasHom :: witness:AtlasWitness source -> hom:AtlasHom source target
      -> {morphism:AtlasMorphism (AtlasObjectAtlasScope source) (AtlasObjectAtlasScope target)
           (AtlasObjectPaginationScope source) (AtlasObjectPaginationScope target)
           (AtlasObjectCellData source) (AtlasObjectCellData target) |
           morphismSourceOwner morphism == homSourceOwner witness hom
           && morphismTargetOwner morphism == homTargetOwner witness hom} @-}
materializeAtlasHom
  :: AtlasWitness source
  -> AtlasHom source target
  -> AtlasMorphism
       (AtlasObjectAtlasScope source)
       (AtlasObjectAtlasScope target)
       (AtlasObjectPaginationScope source)
       (AtlasObjectPaginationScope target)
       (AtlasObjectCellData source)
       (AtlasObjectCellData target)
materializeAtlasHom (AtlasWitness _ valueAtlas) (IdentityAtlasHom (AtlasEquality Refl)) =
  identityAtlasMorphism valueAtlas
materializeAtlasHom _ (PrimitiveAtlasHom Refl Refl morphism) = morphism
materializeAtlasHom sourceWitness (CompositeAtlasHom second first) =
  composeAtlasMorphisms
    (materializeAtlasHom
      (targetAtlasWitness sourceWitness first)
      second)
    (materializeAtlasHom sourceWitness first)

-- | Symbolic Atlas arrows form an ordinary Haskell category. Simplifying the
-- two identity cases is sound because primitive actions are already
-- coherence-sandwiched; a standalone identity is still materialized as the
-- object's actual coherence morphism.
instance Category AtlasHom where
  id = identityAtlasHom
  (.) = composeAtlasHoms


-- ALIGN: ATLAS-MORPHISM-SOURCE-OWNER.
{-@ reflect morphismSourceOwner @-}
morphismSourceOwner :: AtlasMorphism sa ta ss ts sd td -> AtlasOwner
morphismSourceOwner (PrimitiveAtlasMorphism action) = atlasOwner (atlasMorphismSource action)
morphismSourceOwner (IdentityAtlasMorphism owner) = atlasOwner owner
morphismSourceOwner (CompositeAtlasMorphism _ first) = morphismSourceOwner first

-- ALIGN: ATLAS-MORPHISM-TARGET-OWNER.
{-@ reflect morphismTargetOwner @-}
morphismTargetOwner :: AtlasMorphism sa ta ss ts sd td -> AtlasOwner
morphismTargetOwner (PrimitiveAtlasMorphism action) = atlasOwner (atlasMorphismTarget action)
morphismTargetOwner (IdentityAtlasMorphism owner) = atlasOwner owner
morphismTargetOwner (CompositeAtlasMorphism second _) = morphismTargetOwner second

-- ALIGN: ATLASHOM-SOURCE-OWNER.
{-@ reflect homSourceOwner @-}
homSourceOwner :: AtlasWitness source -> AtlasHom source target -> AtlasOwner
homSourceOwner _ (PrimitiveAtlasHom _ _ morphism) = morphismSourceOwner morphism
homSourceOwner witness (IdentityAtlasHom _) = atlasWitnessOwner witness
homSourceOwner witness (CompositeAtlasHom _ first) = homSourceOwner witness first

-- ALIGN: ATLASHOM-TARGET-OWNER.
{-@ reflect homTargetOwner @-}
homTargetOwner :: AtlasWitness source -> AtlasHom source target -> AtlasOwner
homTargetOwner _ (PrimitiveAtlasHom _ _ morphism) = morphismTargetOwner morphism
homTargetOwner witness (IdentityAtlasHom _) = atlasWitnessOwner witness
homTargetOwner witness (CompositeAtlasHom second first) =
  homTargetOwner (targetAtlasWitness witness first) second
