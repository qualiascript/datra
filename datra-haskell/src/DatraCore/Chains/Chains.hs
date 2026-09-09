-- | Public chain API. Chain proofs share a hidden kernel with the ordinal
-- representation so LiquidHaskell never has to reflect across that boundary.
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

import OrdinalChain.Internal
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
