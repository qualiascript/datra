-- | The full subcategory of DaTra sets whose navigations are expeditions.
--
-- 'DataTransformationMap' implements Lean's @IsDaTraMap@ object property,
-- while 'DataTransformationMapHom' inherits every natural transformation
-- between restricted objects, together with the ordinary category laws.
module DataTransformationMap
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

import DataTransformationMap.Internal
  ( DataTransformationMap
  , DataTransformationMapHom
  , DataTransformationMapInclusionFunctor
  , composeDataTransformationMapHoms
  , dataTransformationMap
  , dataTransformationMapAtlasMap
  , dataTransformationMapDataTransformation
  , dataTransformationMapExpedition
  , dataTransformationMapHom
  , dataTransformationMapHomNaturality
  , dataTransformationMapInclusionFunctor
  , dataTransformationMapInclusionHom
  , dataTransformationMapInclusionObject
  , identityDataTransformationMapHom
  , mapDataTransformationMapHom
  )
