-- | Navigations represented by Atlas maps.
--
-- This module implements Lean's @Expedition D extends Navigation D@ by
-- pairing a navigation with the @IsAtlasMap@ witness for its representing
-- Atlas.
module Expedition
  ( Expedition
  , expedition
  , expeditionFromNavigation
  , expeditionAtlasMap
  , expeditionNavigation
  , expeditionAtlas
  , expeditionHom
  , mapExpedition
  , expeditionPreimage
  , expeditionLeftInverse
  ) where

import Expedition.Internal
  ( Expedition
  , expedition
  , expeditionAtlas
  , expeditionAtlasMap
  , expeditionFromNavigation
  , expeditionHom
  , expeditionLeftInverse
  , expeditionNavigation
  , expeditionPreimage
  , mapExpedition
  )
