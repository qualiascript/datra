{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE RoleAnnotations #-}

-- | Hidden implementation of Data Transformation Maps and their full
-- subcategory of DaTra sets.
module DataTransformationMap.Internal
  ( DataTransformationMap
  , dataTransformationMap
  , dataTransformationMapDataTransformation
  , dataTransformationMapAtlasMap
  , dataTransformationMapExpedition
  , DataTransformationMapHom
  , dataTransformationMapHom
  , identityDataTransformationMapHom
  , composeDataTransformationMapHoms
  , mapDataTransformationMapHom
  , dataTransformationMapHomNaturality
  , DataTransformationMapInclusionFunctor
  , dataTransformationMapInclusionFunctor
  , dataTransformationMapInclusionObject
  , dataTransformationMapInclusionHom
  ) where

import Atlas (AtlasHom)
import AtlasMap (AtlasMap)
import Control.Category (Category (..))
import Data.Kind (Type)
import DataTransformation
  ( DataTransformation
  , DataTransformationHom
  , DataTransformationValue
  , dataTransformationHomNaturality
  , mapDataTransformationHom
  )
import Expedition (Expedition, expeditionFromNavigation)
import Navigation (Navigation)
import Prelude hiding ((.), id)

-- | An object of the full subcategory of Data Transformation Maps.
--
-- The second field is the executable form of Lean's
--
-- @
-- IsDaTraMap D := forall nav : Navigation D, IsAtlasMap nav.A
-- @
--
-- It turns the representing object of every navigation into an 'AtlasMap'.
-- Combined with that same navigation this produces an 'Expedition'.
type role DataTransformationMap nominal
data DataTransformationMap (values :: Type) = DataTransformationMap
  (DataTransformation values)
  (forall atlas. Navigation atlas values -> AtlasMap atlas)

-- | Restrict a DaTra set to a Data Transformation Map by showing that every
-- navigation into it is represented by an Atlas map.
dataTransformationMap
  :: DataTransformation values
  -> (forall atlas. Navigation atlas values -> AtlasMap atlas)
  -> DataTransformationMap values
dataTransformationMap = DataTransformationMap

-- | Forget the object restriction and recover the underlying DaTra set.
dataTransformationMapDataTransformation
  :: DataTransformationMap values
  -> DataTransformation values
dataTransformationMapDataTransformation
  (DataTransformationMap transformation _) = transformation

-- | Apply the defining @IsDaTraMap@ witness to a navigation.
dataTransformationMapAtlasMap
  :: DataTransformationMap values
  -> Navigation atlas values
  -> AtlasMap atlas
dataTransformationMapAtlasMap
  (DataTransformationMap _ atlasMapForNavigation) = atlasMapForNavigation

-- | Every navigation of a Data Transformation Map is canonically an
-- expedition, as stated immediately after Lean's definition.
dataTransformationMapExpedition
  :: DataTransformationMap values
  -> Navigation atlas values
  -> Expedition atlas values
dataTransformationMapExpedition valueMap valueNavigation =
  expeditionFromNavigation
    (dataTransformationMapAtlasMap valueMap valueNavigation)
    valueNavigation

-- | An arrow in the full subcategory of Data Transformation Maps.
--
-- Fullness means there is no additional arrow property: the hom-set is the
-- corresponding hom-set of natural transformations between the underlying
-- DaTra sets.
type role DataTransformationMapHom nominal nominal
newtype DataTransformationMapHom source target = DataTransformationMapHom
  { getDataTransformationMapHom :: DataTransformationHom source target
  }

-- | Regard any natural transformation between restricted objects as a
-- morphism in the full subcategory.
dataTransformationMapHom
  :: DataTransformationHom source target
  -> DataTransformationMapHom source target
dataTransformationMapHom = DataTransformationMapHom

-- | Identity in the category of Data Transformation Maps.
identityDataTransformationMapHom
  :: DataTransformationMapHom object object
identityDataTransformationMapHom = DataTransformationMapHom id

-- | Compose Data Transformation Map morphisms in categorical order.
composeDataTransformationMapHoms
  :: DataTransformationMapHom middle target
  -> DataTransformationMapHom source middle
  -> DataTransformationMapHom source target
composeDataTransformationMapHoms
  (DataTransformationMapHom second)
  (DataTransformationMapHom first) =
    DataTransformationMapHom (second . first)

-- | The full subcategory inherits identity and composition from DaTra.
instance Category DataTransformationMapHom where
  id = identityDataTransformationMapHom
  (.) = composeDataTransformationMapHoms

-- | Evaluate one component of a Data Transformation Map morphism.
mapDataTransformationMapHom
  :: DataTransformationMapHom source target
  -> DataTransformationValue source atlas
  -> DataTransformationValue target atlas
mapDataTransformationMapHom (DataTransformationMapHom hom) =
  mapDataTransformationHom hom

-- | Invoke the inherited naturality witness.
dataTransformationMapHomNaturality
  :: DataTransformationMapHom source target
  -> AtlasHom sourceAtlas targetAtlas
  -> DataTransformationValue source targetAtlas
  -> ()
dataTransformationMapHomNaturality (DataTransformationMapHom hom) =
  dataTransformationHomNaturality hom

-- | The canonical inclusion of the full subcategory into DaTra. Its object
-- action forgets the navigation restriction and its arrow action unwraps the
-- unchanged natural transformation.
data DataTransformationMapInclusionFunctor =
  DataTransformationMapInclusionFunctor
    { dataTransformationMapInclusionObject
        :: forall values.
           DataTransformationMap values -> DataTransformation values
    , dataTransformationMapInclusionHom
        :: forall source target.
           DataTransformationMapHom source target
           -> DataTransformationHom source target
    }

-- | The canonical full-subcategory inclusion @DaTraMap -> DaTra@.
dataTransformationMapInclusionFunctor
  :: DataTransformationMapInclusionFunctor
dataTransformationMapInclusionFunctor =
  DataTransformationMapInclusionFunctor
    { dataTransformationMapInclusionObject =
        dataTransformationMapDataTransformation
    , dataTransformationMapInclusionHom = getDataTransformationMapHom
    }
