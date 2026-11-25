{-# LANGUAGE CPP #-}
{-# LANGUAGE RankNTypes #-}
#include "../../../../LiquidPlugin.h"
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}
{-@ LIQUID "--higherorder" @-}

-- | Atlas maps and their full subcategory of atlases.
--
-- An Atlas map is an 'Atlas' whose entire extent is covered by final-region
-- data. 'AtlasMapHom' leaves the ordinary Atlas hom-sets unchanged, and
-- 'atlasMapInclusionFunctor' forgets the object restriction canonically.
module AtlasMap
  ( AtlasMap
  , atlasMap
  , atlasMapAtlas
  , atlasMapCoversDatum
  , atlasMapAcceptsDatum
  , atlasMapCellValid
  , atlasMapWitnessCovers
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
  , atlasMapAtlas
  , atlasMapCoversDatum
  , atlasMapAcceptsDatum
  , atlasMapCellValid
  , atlasMapWitnessCovers
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

import qualified AtlasMap.Internal as Internal (atlasMap)
import Atlas (Atlas, AtlasObject, atlasPageElements, atlasAcceptsDatum)
import AtlasCoveredPageElement (CoverageWitness, coverageWitnessCovers)
import AtlasExtent (cellTraceValid)
import PageElements (originPageElement)
import PageElements.Structure (PageElement, SomePageElement (..))

-- | Preserve the origin and accepted-datum conditions through the exposed API.
-- ALIGN: ATLAS-MAP-PUBLIC-CONSTRUCTION.
{-@ atlasMap :: owner:Atlas a s d o f
      -> (forall object. source:{PageElement s object | cellTraceValid owner source
             && SomePageElement source == originPageElement (atlasPageElements owner)}
           -> datum:{d object | atlasAcceptsDatum owner source datum}
           -> {witness:CoverageWitness a s d | coverageWitnessCovers owner source datum witness})
      -> AtlasMap (AtlasObject a s d) @-}
atlasMap :: Atlas a s d o f
  -> (forall object. PageElement s object -> d object -> CoverageWitness a s d)
  -> AtlasMap (AtlasObject a s d)
atlasMap = Internal.atlasMap
