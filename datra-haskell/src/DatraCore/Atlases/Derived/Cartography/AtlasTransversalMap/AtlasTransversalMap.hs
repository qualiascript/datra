-- | Atlas transversal maps and their canonical inclusion into Atlas
-- transversals.
--
-- The objects are 'AtlasMap' values and the arrows are all
-- 'AtlasTransversal' arrows between their underlying atlases, matching Lean's
-- full-subcategory definition of @AtlTravMap@.
module AtlasTransversalMap
  ( AtlasTransversalMap
  , atlasTransversalMap
  , atlasTransversalMapTransversal
  , atlasTransversalMapAtlasMapHom
  , identityAtlasTransversalMap
  , composeAtlasTransversalMaps
  , atlasTransversalMapOrderedTransposal
  , atlasTransversalMapTransposal
  , atlasTransversalMapHom
  , atlasTransversalMapPreservesCoverage
  , mapAtlasTransversalMapCoveredDatum
  , mapAtlasTransversalMapObject
  , atlasTransversalMapPreimage
  , atlasTransversalMapLeftInverse
  , atlasTransversalMapPreservesOrder
  , atlasTransversalMapPagination
  , mapAtlasTransversalMapElement
  , mapAtlasTransversalMapArrow
  , mapAtlasTransversalMapData
  , AtlasTransversalMapInclusionFunctor
  , atlasTransversalMapInclusionFunctor
  , atlasTransversalMapInclusionObject
  , atlasTransversalMapInclusionHom
  ) where

import AtlasTransversalMap.Internal
  ( AtlasTransversalMap
  , AtlasTransversalMapInclusionFunctor
  , atlasTransversalMap
  , atlasTransversalMapAtlasMapHom
  , atlasTransversalMapHom
  , atlasTransversalMapInclusionFunctor
  , atlasTransversalMapInclusionHom
  , atlasTransversalMapInclusionObject
  , atlasTransversalMapLeftInverse
  , atlasTransversalMapOrderedTransposal
  , atlasTransversalMapPagination
  , atlasTransversalMapPreimage
  , atlasTransversalMapPreservesCoverage
  , atlasTransversalMapPreservesOrder
  , atlasTransversalMapTransposal
  , atlasTransversalMapTransversal
  , composeAtlasTransversalMaps
  , identityAtlasTransversalMap
  , mapAtlasTransversalMapArrow
  , mapAtlasTransversalMapCoveredDatum
  , mapAtlasTransversalMapData
  , mapAtlasTransversalMapElement
  , mapAtlasTransversalMapObject
  )
