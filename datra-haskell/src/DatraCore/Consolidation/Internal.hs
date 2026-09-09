{-# OPTIONS_GHC -Wno-orphans #-}

-- | Hidden consolidation implementation.
module Consolidation.Internal
  ( Consolidation (..)
  , consolidationMonotone
  , consolidation
  , identityConsolidation
  , composeConsolidations
  , sumConsolidations
  , Coconsolidation (..)
  , op
  , unop
  ) where

import Control.Category (Category (..))
import Consolidation.LiquidInternal
  ( Consolidation (..)
  , composeConsolidations
  , consolidation
  , consolidationMonotone
  , identityConsolidation
  )
import Prelude hiding ((.), id)

-- | The horizontal sum of two consolidations, corresponding to
-- @ConHom.sum@ in @datra.lean@.
--
-- Its full abstract-refinement proof is not yet discharged; the implementation
-- combines the already law-carrying component witnesses branch by branch.
sumConsolidations
  :: Consolidation leftSource leftTarget
  -> Consolidation rightSource rightTarget
  -> Consolidation
       (Either leftSource rightSource)
       (Either leftTarget rightTarget)
sumConsolidations left right =
  Consolidation
    { applyConsolidation = mapSum
    , consolidationPreimage = preimageInSum
    , consolidationMonotoneProof = \sumLeft _ sumRight ->
        monotoneInSum sumLeft sumRight
    , consolidationPointSurjective = pointSurjectiveInSum
    }
  where
    mapSum (Left value) = Left (applyConsolidation left value)
    mapSum (Right value) = Right (applyConsolidation right value)

    preimageInSum (Left value) =
      Left (consolidationPreimage left value)
    preimageInSum (Right value) =
      Right (consolidationPreimage right value)

    monotoneInSum (Left first) (Left second) =
      Left (consolidationMonotone left first second)
    monotoneInSum (Right first) (Right second) =
      Right (consolidationMonotone right first second)
    monotoneInSum (Left _) (Right second) = mapSum (Right second)
    monotoneInSum (Right _) (Left second) = mapSum (Left second)

    pointSurjectiveInSum (Left value) =
      consolidationPointSurjective left value
    pointSurjectiveInSum (Right value) =
      consolidationPointSurjective right value

-- LiquidHaskell 0.9.4 cannot parse declarations for the symbolic Category
-- method `(.)`. The law-carrying representation, smart constructor, identity,
-- and composition are specified in Consolidation.LiquidInternal. These
-- instances merely expose those operations through Control.Category.
instance Category Consolidation where
  id = identityConsolidation
  (.) = composeConsolidations

-- | The opposite category of consolidations (@CoCon@ in @datra.lean@).
--
-- A morphism from @a@ to @b@ here is a consolidation from @b@ to @a@.
newtype Coconsolidation a b = Coconsolidation
  { getOppositeConsolidation :: Consolidation b a
  }

-- | Reverse the categorical direction of a consolidation.
op :: Consolidation a b -> Coconsolidation b a
op = Coconsolidation

-- | Recover the underlying consolidation.
unop :: Coconsolidation b a -> Consolidation a b
unop = getOppositeConsolidation

instance Category Coconsolidation where
  id = Coconsolidation id

  Coconsolidation second . Coconsolidation first =
    Coconsolidation (first . second)
