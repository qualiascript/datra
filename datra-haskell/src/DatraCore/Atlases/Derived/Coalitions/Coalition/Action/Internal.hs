{-# LANGUAGE CPP #-}
{-# OPTIONS_GHC -Wno-unused-imports #-}
#include "../../../../../LiquidPlugin.h"
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--higherorder" @-}

-- | Erase the retained owner for the object-indexed coalition carrier API.
module Coalition.Action.Internal (mapCoalitionElement) where

import Atlas (Atlas, AtlasObject, atlasPageElements)
import AtlasTransversal (AtlasTransversal)
import Coalition.Action (withMappedCoalitionElement)
import Coalition.Element.Data (CoalitionData, coalitionElementValid, coalitionElementSource)
import PageElements (originPageElement)

-- | The checked worker obtains the target owner from the transversal itself.
-- ALIGN: COALITION-FORWARD-CARRIER.
-- ALIGN: COALITION-FORWARD-INTERPRETATION.
{-@ reflect mapCoalitionElement @-}
{-@ mapCoalitionElement :: owner:Atlas sa ss sd so sf
      -> AtlasTransversal (AtlasObject sa ss sd) (AtlasObject ta ts td)
      -> source:{CoalitionData sa ss sd | coalitionElementValid owner source
           && coalitionElementSource source == originPageElement (atlasPageElements owner)}
      -> CoalitionData ta ts td @-}
mapCoalitionElement
  :: Atlas sa ss sd so sf
  -> AtlasTransversal (AtlasObject sa ss sd) (AtlasObject ta ts td)
  -> CoalitionData sa ss sd -> CoalitionData ta ts td
mapCoalitionElement sourceOwner transversal source =
  withMappedCoalitionElement sourceOwner transversal source (\_ element -> element)
