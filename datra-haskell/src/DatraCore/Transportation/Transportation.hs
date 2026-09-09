-- | Public transportation-functor API backed by the hidden implementation.
module Transportation
  ( Transportation
  , runTransportation
  , transportation
  , transportationIdentity
  , transportationComposition
  , transportCoconsolidation
  ) where

import Transportation.Internal
  ( Transportation
  , runTransportation
  , transportCoconsolidation
  , transportation
  , transportationComposition
  , transportationIdentity
  )
