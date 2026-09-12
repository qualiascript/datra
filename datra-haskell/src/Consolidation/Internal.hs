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
  ) where

import Control.Category (Category (..))
import Consolidation.LiquidInternal
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
  , op
  , unop
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

instance Category Coconsolidation where
  id = op identityConsolidation
  (.) = composeCoconsolidations

instance Category ConsolidationTransport where
  id = ConsolidationTransport id
  ConsolidationTransport second . ConsolidationTransport first =
    ConsolidationTransport (second . first)

-- | Apply consolidation transport to a morphism in @CoCon@. Its underlying
-- consolidation, and hence its function, runs in the opposite direction.
transportCoconsolidation
  :: Coconsolidation source target
  -> ConsolidationTransport target source
transportCoconsolidation = consolidationTransport . unop
