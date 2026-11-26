{-# OPTIONS_GHC -Wno-orphans #-}

-- | Hidden consolidation and carrier-transport implementation.
module Consolidation.Internal
  ( Consolidation (..)
  , consolidationMonotone
  , consolidation
  , identityConsolidation
  , composeConsolidations
  , sumConsolidations
  , Coconsolidation (..)
  , composeCoconsolidations
  , op
  , unop
  , ConsolidationTransport (..)
  , consolidationTransport
  , consolidationTransportIdentity
  , consolidationTransportComposition
  , transportCoconsolidation
  , transportCoconsolidationPreimage
  ) where

import Control.Category (Category (..))
import Consolidation.Core
  ( Coconsolidation (..)
  , Consolidation (..)
  , ConsolidationTransport (..)
  , composeCoconsolidations
  , composeConsolidations
  , consolidation
  , consolidationMonotone
  , consolidationTransport
  , consolidationTransportComposition
  , consolidationTransportIdentity
  , identityConsolidation
  , transportCoconsolidation
  , transportCoconsolidationPreimage
  , op
  , unop
  )
import Consolidation.Sum (sumConsolidations)
import Prelude hiding ((.), id)

-- The Category instances expose the checked operations in Consolidation.Core.
instance Category Consolidation where
  id = identityConsolidation
  (.) = composeConsolidations

instance Category Coconsolidation where
  id = op identityConsolidation
  (.) = composeCoconsolidations

instance Category ConsolidationTransport where
  id = ConsolidationTransport id
  ConsolidationTransport second . ConsolidationTransport first =
    ConsolidationTransport (second . first)
