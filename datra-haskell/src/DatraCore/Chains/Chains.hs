-- | Public chain API backed by the hidden chain implementation.
module Chains
  ( Chain
  , chainOrdinalLT
  , positionMatches
  , chainOrderType
  , chainPosition
  , chainObjectAt
  , chainPositionBelow
  , chainPositionInjective
  , chainPositionSurjective
  , chain
  , compareInChain
  , hasArrow
  , sumChains
  , spine
  ) where

import Chains.Internal
  ( Chain
  , chain
  , chainObjectAt
  , chainOrderType
  , chainOrdinalLT
  , chainPosition
  , chainPositionBelow
  , chainPositionInjective
  , chainPositionSurjective
  , compareInChain
  , hasArrow
  , positionMatches
  , spine
  , sumChains
  )
