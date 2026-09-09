-- | Public consolidation-transport functor API backed by the hidden implementation.
module ConsolidationTransport
  ( ConsolidationTransport
  , runConsolidationTransport
  , consolidationTransport
  , consolidationTransportIdentity
  , consolidationTransportComposition
  , transportCoconsolidation
  ) where

import ConsolidationTransport.Internal
  ( ConsolidationTransport
  , runConsolidationTransport
  , transportCoconsolidation
  , consolidationTransport
  , consolidationTransportComposition
  , consolidationTransportIdentity
  )
