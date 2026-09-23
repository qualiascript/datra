{-# LANGUAGE CPP #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE RoleAnnotations #-}
{-# LANGUAGE TypeFamilies #-}
{-# OPTIONS_GHC -Wno-unused-imports #-}
#include "../../../../LiquidPlugin.h"
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}

-- | Hidden proof-bearing representation of total Atlas maps.
module TotalAtlasMap.Internal
  ( SingletonDominion
  , singletonDominion
  , singletonDominionValue
  , singletonDominionUnique
  , FinalAtlasRegion
  , finalAtlasRegionDominion
  , TotalAtlasMap
  , totalAtlasMap
  , totalAtlasMapUnderlying
  , totalAtlasMapRegionSingleton
  ) where

import Atlas
  ( AtlasObject
  , AtlasObjectCellData
  )
import AtlasMap (AtlasMap)
import Dominion (Dominion)

-- | Constructive evidence that a type, and therefore any dominion over that
-- type, has exactly one inhabitant.  LiquidHaskell checks that every proposed
-- inhabitant is equal to the selected value.
{-@
data SingletonDominion value = SingletonDominion
  { singletonDominionValue :: value
  , singletonDominionUnique :: candidate:value
      -> { proof:() | candidate == singletonDominionValue }
  }
@-}
data SingletonDominion value = SingletonDominion
  { singletonDominionValue :: value
  , singletonDominionUnique :: value -> ()
  }

{-@
singletonDominion
  :: selected:value
  -> (candidate:value -> { proof:() | candidate == selected })
  -> SingletonDominion value
@-}
singletonDominion
  :: value
  -> (value -> ())
  -> SingletonDominion value
singletonDominion = SingletonDominion

-- | One genuine final-page region of an Atlas.  The constructor stays hidden
-- so clients can only be asked to prove singletonhood for regions produced by
-- the Atlas implementation itself.
type role FinalAtlasRegion nominal nominal
data FinalAtlasRegion atlasObject object where
  FinalAtlasRegion
    :: Dominion (cellData object)
    -> FinalAtlasRegion
         (AtlasObject atlasScope paginationScope cellData)
         object

finalAtlasRegionDominion
  :: FinalAtlasRegion atlasObject object
  -> Dominion (AtlasObjectCellData atlasObject object)
finalAtlasRegionDominion (FinalAtlasRegion valueDominion) = valueDominion

-- | An individual Atlas map with a proof that every region on its final page
-- is a singleton.  This refinement is intentionally independent from
-- Atlas-map federations: some federation kinds, including NaturalRange, have
-- only total members, but that is not true of federations in general.
type role TotalAtlasMap nominal
data TotalAtlasMap atlasObject = TotalAtlasMap
  (AtlasMap atlasObject)
  (forall object.
     FinalAtlasRegion atlasObject object
     -> SingletonDominion (AtlasObjectCellData atlasObject object))

{-@
totalAtlasMap
  :: valueMap:AtlasMap atlasObject
  -> (forall object.
       region:FinalAtlasRegion atlasObject object
       -> SingletonDominion (AtlasObjectCellData atlasObject object))
  -> TotalAtlasMap atlasObject
@-}
totalAtlasMap
  :: AtlasMap atlasObject
  -> (forall object.
       FinalAtlasRegion atlasObject object
       -> SingletonDominion (AtlasObjectCellData atlasObject object))
  -> TotalAtlasMap atlasObject
totalAtlasMap = TotalAtlasMap

totalAtlasMapUnderlying
  :: TotalAtlasMap atlasObject
  -> AtlasMap atlasObject
totalAtlasMapUnderlying (TotalAtlasMap valueMap _) = valueMap

totalAtlasMapRegionSingleton
  :: TotalAtlasMap atlasObject
  -> FinalAtlasRegion atlasObject object
  -> SingletonDominion (AtlasObjectCellData atlasObject object)
totalAtlasMapRegionSingleton (TotalAtlasMap _ proveSingleton) =
  proveSingleton
