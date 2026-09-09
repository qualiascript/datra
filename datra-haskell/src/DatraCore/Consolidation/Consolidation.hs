-- | Public consolidation API backed by the hidden implementation.
module Consolidation
  ( Consolidation
  , applyConsolidation
  , consolidationPreimage
  , consolidationMonotone
  , consolidationPointSurjective
  , consolidation
  , identityConsolidation
  , composeConsolidations
  , sumConsolidations
  , Coconsolidation
  , composeCoconsolidations
  , op
  , unop
  ) where

import Consolidation.Internal
  ( Coconsolidation
  , Consolidation
  , applyConsolidation
  , composeConsolidations
  , composeCoconsolidations
  , consolidation
  , consolidationMonotone
  , consolidationPointSurjective
  , consolidationPreimage
  , identityConsolidation
  , op
  , sumConsolidations
  , unop
  )
