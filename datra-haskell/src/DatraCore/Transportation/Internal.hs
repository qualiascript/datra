{-# OPTIONS_GHC -Wno-orphans #-}

-- | Hidden implementation of the transportation functor.
module Transportation.Internal
  ( Transportation (..)
  , transportation
  , transportationIdentity
  , transportationComposition
  , transportCoconsolidation
  ) where

import Control.Category (Category (..))
import Consolidation
  ( Coconsolidation
  )
import Transportation.LiquidInternal
  ( Transportation (..)
  , transportation
  , transportationComposition
  , transportationIdentity
  )

import qualified Consolidation
import Prelude hiding ((.), id)

instance Category Transportation where
  id = Transportation id
  Transportation second . Transportation first =
    Transportation (second . first)

-- | Apply transportation to a morphism in @CoCon@. Its underlying
-- consolidation, and hence its function, runs in the opposite direction.
transportCoconsolidation
  :: Coconsolidation source target
  -> Transportation target source
transportCoconsolidation =
  transportation . Consolidation.unop
