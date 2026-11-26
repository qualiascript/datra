{-# LANGUAGE CPP #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE RoleAnnotations #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# OPTIONS_GHC -Wno-unused-imports #-}
#include "../../../../LiquidPlugin.h"
{-@ LIQUID "--reflection" @-}

-- | Hidden proof-bearing representation of total Atlas maps.
module TotalAtlasMap.Internal
  ( SingletonDominion
  , singletonDominion
  , singletonDominionValue
  , singletonDominionUnique
  , TotalAtlasMap
  , totalAtlasMap
  , totalAtlasMapUnderlying
  , withTotalAtlasMap
  ) where

import Atlas (AtlasObject)
import AtlasMap (AtlasMap, atlasMapRegionValid, atlasMapAcceptsDatum)
import PageElements.Structure (PageElement)

-- | Constructive evidence that a type, and therefore any dominion over that
-- type, has exactly one inhabitant.  LiquidHaskell checks that every proposed
-- inhabitant is equal to the selected value.
{-@
data SingletonDominion value = SingletonDominion
  { singletonSelected :: value
  , singletonEquality :: candidate:value
      -> { proof:() | candidate == singletonSelected }
  }
@-}
data SingletonDominion value = SingletonDominion
  { singletonSelected :: value
  , singletonEquality :: value -> ()
  }

-- | A named measure keeps the selected value available through the abstract
-- public interface, independently of record-selector inlining.
{-@ measure singletonDominionValue @-}
singletonDominionValue :: SingletonDominion value -> value
singletonDominionValue (SingletonDominion selected _) = selected

{-@ singletonDominionUnique :: certificate:SingletonDominion value
      -> candidate:value -> {candidate == singletonDominionValue certificate} @-}
-- ALIGN: SINGLETON-DOMINION-UNIQUENESS.
singletonDominionUnique :: SingletonDominion value -> value -> ()
singletonDominionUnique (SingletonDominion _ unique) candidate = unique candidate

{-@
singletonDominion
  :: selected:value
  -> (candidate:value -> { proof:() | candidate == selected })
  -> {result:SingletonDominion value | singletonDominionValue result == selected}
@-}
-- ALIGN: SINGLETON-DOMINION-CONSTRUCTION.
singletonDominion
  :: value
  -> (value -> ())
  -> SingletonDominion value
singletonDominion selected unique = SingletonDominion selected unique

-- | An individual Atlas map with a proof that every region on its final page
-- is a singleton.  This refinement is intentionally independent from
-- Atlas-map federations: some federation kinds, including NaturalRange, have
-- only total members, but that is not true of federations in general.
type role TotalAtlasMap nominal
data TotalAtlasMap atlasObject where
  TotalAtlasMap :: TotalAtlasMapData a s d -> TotalAtlasMap (AtlasObject a s d)

-- | The actual region and accepted carrier stay tied to the stored map.
type role TotalAtlasMapData nominal nominal nominal
{-@ data TotalAtlasMapData a s d = TotalAtlasMapData
      { totalMapOwner :: AtlasMap (AtlasObject a s d)
      , totalMapSingleton :: forall object.
          region:{PageElement s object | atlasMapRegionValid totalMapOwner region}
          -> SingletonDominion ({datum:d object | atlasMapAcceptsDatum totalMapOwner region datum})
      } @-}
data TotalAtlasMapData a s d = TotalAtlasMapData
  { totalMapOwner :: AtlasMap (AtlasObject a s d)
  , totalMapSingleton :: forall object. PageElement s object -> SingletonDominion (d object)
  }

{-@
totalAtlasMap
  :: valueMap:AtlasMap (AtlasObject a s d)
  -> (forall object.
       region:{PageElement s object | atlasMapRegionValid valueMap region}
       -> SingletonDominion ({datum:d object | atlasMapAcceptsDatum valueMap region datum}))
  -> TotalAtlasMap (AtlasObject a s d)
@-}
-- ALIGN: TOTAL-ATLAS-MAP-CONSTRUCTION.
-- ALIGN: TOTAL-ATLAS-MAP-INTERPRETATION.
-- ALIGN: TOTAL-ATLAS-MAP-RAW-INTERPRETATION.
totalAtlasMap
  :: AtlasMap (AtlasObject a s d)
  -> (forall object. PageElement s object -> SingletonDominion (d object))
  -> TotalAtlasMap (AtlasObject a s d)
totalAtlasMap valueMap proveSingleton = TotalAtlasMap (TotalAtlasMapData valueMap proveSingleton)

-- | Forget singletonhood while retaining the underlying Atlas map.
totalAtlasMapUnderlying
  :: TotalAtlasMap atlasObject
  -> AtlasMap atlasObject
totalAtlasMapUnderlying (TotalAtlasMap value) = totalMapOwner value

-- | Eliminate the map together with its dependent singleton certificates.
-- The callback receives the actual stored owner, so its final-region and
-- membership conditions cannot accidentally refer to another Atlas map.
-- ALIGN: TOTAL-ATLAS-MAP-ELIMINATION.
{-@ withTotalAtlasMap :: TotalAtlasMap (AtlasObject a s d)
      -> (owner:AtlasMap (AtlasObject a s d)
           -> (forall object.
                 region:{PageElement s object | atlasMapRegionValid owner region}
                 -> SingletonDominion ({datum:d object | atlasMapAcceptsDatum owner region datum}))
           -> result)
      -> result @-}
withTotalAtlasMap
  :: forall a s d result. TotalAtlasMap (AtlasObject a s d)
  -> (AtlasMap (AtlasObject a s d)
      -> (forall object. PageElement s object -> SingletonDominion (d object))
      -> result)
  -> result
withTotalAtlasMap (TotalAtlasMap (value :: TotalAtlasMapData a s d)) useMap =
  useMap (totalMapOwner value) (totalMapSingleton value)
