-- | Atlases and their morphisms, built over finite paginations with an
-- explicitly stable infinite padded spine.
--
-- Atlas object laws are checked by LiquidHaskell.  Atlas morphism laws are
-- documented by the unchecked constructor for now and will be imposed in a
-- subsequent verification pass.
module Atlas
  ( Atlas
  , AtlasDataAction
  , AtlasMorphism
  , AtlasMorphismImage
  , atlasDataAction
  , atlas
  , atlasPagination
  , atlasFolio
  , atlasPageElements
  , atlasCardinality
  , normalizeAtlasElement
  , normalizeAtlasArrow
  , atlasCoherence
  , atlasDataAt
  , mapAtlasData
  , atlasDataCoherence
  , normalizeAtlasDatum
  , atlasMorphismImage
  , withAtlasMorphismImage
  , atlasMorphism
  , atlasMorphismPagination
  , mapAtlasMorphismElement
  , mapAtlasMorphismArrow
  , mapAtlasMorphismData
  , identityAtlasMorphism
  , composeAtlasMorphisms
  ) where

import Atlas.Internal
  ( Atlas
  , AtlasDataAction
  , atlas
  , atlasDataAction
  , atlasCardinality
  , atlasCoherence
  , atlasDataAt
  , atlasDataCoherence
  , atlasFolio
  , atlasPageElements
  , atlasPagination
  , mapAtlasData
  , normalizeAtlasArrow
  , normalizeAtlasDatum
  , normalizeAtlasElement
  )
import Atlas.Morphism.Internal
  ( AtlasMorphism
  , AtlasMorphismImage
  , atlasMorphism
  , atlasMorphismImage
  , atlasMorphismPagination
  , composeAtlasMorphisms
  , identityAtlasMorphism
  , mapAtlasMorphismArrow
  , mapAtlasMorphismData
  , mapAtlasMorphismElement
  , withAtlasMorphismImage
  )
