-- | Atlas maps and their full subcategory of atlases.
--
-- An Atlas map is an 'Atlas' whose entire extent is covered by final-region
-- data. 'AtlasMapHom' leaves the ordinary Atlas hom-sets unchanged, and
-- 'atlasMapInclusionFunctor' forgets the object restriction canonically.
module AtlasMap
  ( AtlasMap
  , atlasMap
  , atlasMapAtlas
  , withAtlasMapExtent
  , AtlasMapHom
  , atlasMapHom
  , identityAtlasMapHom
  , composeAtlasMapHoms
  , materializeAtlasMapHom
  , atlasMapHomPagination
  , mapAtlasMapHomElement
  , mapAtlasMapHomArrow
  , mapAtlasMapHomData
  , AtlasMapInclusionFunctor
  , atlasMapInclusionFunctor
  , atlasMapInclusionObject
  , atlasMapInclusionHom
  ) where

import AtlasMap.Internal
  ( AtlasMap
  , AtlasMapHom
  , AtlasMapInclusionFunctor
  , atlasMap
  , atlasMapAtlas
  , atlasMapHom
  , atlasMapHomPagination
  , atlasMapInclusionFunctor
  , atlasMapInclusionHom
  , atlasMapInclusionObject
  , composeAtlasMapHoms
  , identityAtlasMapHom
  , mapAtlasMapHomArrow
  , mapAtlasMapHomData
  , mapAtlasMapHomElement
  , materializeAtlasMapHom
  , withAtlasMapExtent
  )
