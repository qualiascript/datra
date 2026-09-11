-- | Atlas objects built over finite paginations with an explicitly stable
-- infinite padded spine.
--
-- This first version exposes objects and their data assignments only.  Atlas
-- morphisms and machine-checked Atlas coherence laws will be added separately
-- after the object representation has settled.
module Atlas
  ( Atlas
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
  , atlas
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
