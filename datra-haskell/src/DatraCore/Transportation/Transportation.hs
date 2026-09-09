-- | Public transportation-functor API backed by the hidden implementation.
module Transportation
  ( Transportation
  , runTransportation
  , transportation
  , transportCoconsolidation
  ) where

import Transportation.Internal
  ( Transportation
  , runTransportation
  , transportCoconsolidation
  , transportation
  )
