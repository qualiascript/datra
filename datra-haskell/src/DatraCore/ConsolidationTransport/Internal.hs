{-# OPTIONS_GHC -Wno-orphans #-}

-- | Hidden implementation of the consolidation-transport functor.
module ConsolidationTransport.Internal
  ( ConsolidationTransport (..)
  , consolidationTransport
  , consolidationTransportIdentity
  , consolidationTransportComposition
  , transportCoconsolidation
  ) where

import Control.Category (Category (..))
import Consolidation
  ( Coconsolidation
  )
import ConsolidationTransport.LiquidInternal
  ( ConsolidationTransport (..)
  , consolidationTransport
  , consolidationTransportComposition
  , consolidationTransportIdentity
  )

import qualified Consolidation
import Prelude hiding ((.), id)

instance Category ConsolidationTransport where
  id = ConsolidationTransport id
  ConsolidationTransport second . ConsolidationTransport first =
    ConsolidationTransport (second . first)

-- | Apply consolidation transport to a morphism in @CoCon@. Its underlying
-- consolidation, and hence its function, runs in the opposite direction.
transportCoconsolidation
  :: Coconsolidation source target
  -> ConsolidationTransport target source
transportCoconsolidation =
  consolidationTransport . Consolidation.unop
