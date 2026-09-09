-- | Hidden implementation of the transportation functor.
module Transportation.Internal
  ( Transportation (..)
  , transportation
  , transportCoconsolidation
  ) where

import Control.Category (Category (..))
import Consolidation
  ( Coconsolidation
  , Consolidation
  , applyConsolidation
  )

import qualified Consolidation
import Prelude hiding ((.), id)

-- | A morphism in the target of the transportation functor.
--
-- Haskell already represents the object part of @Tra : Con -> Type@ with the
-- carrier type parameters @source@ and @target@. This wrapper makes its
-- morphism part explicit without discarding those types.
newtype Transportation source target = Transportation
  { runTransportation :: source -> target
  }

instance Category Transportation where
  id = Transportation id
  Transportation second . Transportation first =
    Transportation (second . first)

-- | The morphism action of the transportation functor.
transportation
  :: Consolidation source target
  -> Transportation source target
transportation = Transportation . applyConsolidation

-- Transportation coherence conditions:
--
-- * @transportation identityConsolidation@ is extensionally the identity.
-- * @transportation (composeConsolidations second first)@ is extensionally
--   @transportation second . transportation first@.
--
-- These laws are immediate from the executable definitions. They are kept as
-- comments until this module acquires LiquidHaskell specifications.

-- | Apply transportation to a morphism in @CoCon@. Its underlying
-- consolidation, and hence its function, runs in the opposite direction.
transportCoconsolidation
  :: Coconsolidation source target
  -> Transportation target source
transportCoconsolidation =
  transportation . Consolidation.unop
