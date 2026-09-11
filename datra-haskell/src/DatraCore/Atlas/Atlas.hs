-- | Atlas objects built over finite paginations with an explicitly stable
-- infinite padded spine.
--
-- This first version exposes objects and their data assignments only.  Atlas
-- morphisms will be added separately after the object representation has
-- settled.  Atlas object laws are checked by LiquidHaskell.
module Atlas
  ( Atlas
  , AtlasDataAction
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
