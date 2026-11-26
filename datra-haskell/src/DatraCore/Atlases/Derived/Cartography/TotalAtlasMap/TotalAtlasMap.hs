{-# LANGUAGE CPP #-}
#include "../../../../LiquidPlugin.h"
{-@ LIQUID "--reflection" @-}

-- | Atlas maps whose final-page regions are singleton sets.
module TotalAtlasMap
  ( SingletonDominion
  , singletonDominion
  , singletonDominionValue
  , singletonDominionUnique
  , TotalAtlasMap
  , totalAtlasMap
  , totalAtlasMapUnderlying
  , withTotalAtlasMap
  ) where

import TotalAtlasMap.Internal
  ( SingletonDominion
  , singletonDominion
  , singletonDominionValue
  , singletonDominionUnique
  , TotalAtlasMap
  , totalAtlasMap
  , totalAtlasMapUnderlying
  , withTotalAtlasMap
  )

