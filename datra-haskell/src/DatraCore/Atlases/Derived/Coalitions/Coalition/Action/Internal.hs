-- | Erase the retained owner for the object-indexed coalition carrier API.
module Coalition.Action.Internal (mapCoalitionElement) where

import Atlas (Atlas, AtlasObject)
import AtlasTransversal (AtlasTransversal)
import Coalition.Action (withMappedCoalitionElement)
import Coalition.Element.Data (CoalitionData)

-- | The checked worker obtains the target owner from the transversal itself.
-- ALIGN: COALITION-FORWARD-CARRIER.
-- ALIGN: COALITION-FORWARD-INTERPRETATION.
mapCoalitionElement
  :: Atlas sa ss sd so sf
  -> AtlasTransversal (AtlasObject sa ss sd) (AtlasObject ta ts td)
  -> CoalitionData sa ss sd -> CoalitionData ta ts td
mapCoalitionElement sourceOwner transversal source =
  withMappedCoalitionElement sourceOwner transversal source (\_ element -> element)
