-- | Hidden consolidation implementation.
module Consolidation.Internal
  ( Consolidation (..)
  , consolidation
  , identityConsolidation
  , composeConsolidations
  , sumConsolidations
  , Coconsolidation (..)
  , op
  , unop
  ) where

import Control.Category (Category (..))
import Prelude hiding ((.), id)

-- | A monotone, point-surjective map between chain carriers.
--
-- A value is used together with a source @Chain source@ and a target
-- @Chain target@. Until these obligations are encoded in LiquidHaskell, the
-- constructor and its proof callbacks are required to obey these laws:
--
-- * Monotonicity: if @hasArrow sourceChain x y@, then
--   @hasArrow targetChain (applyConsolidation value x)
--                         (applyConsolidation value y)@.
-- * Point-surjectivity: for every @y@,
--   @applyConsolidation value (consolidationPreimage value y) == y@.
--
-- The chosen preimage is executable evidence for Lean's existential
-- @Function.Surjective@ field. It is stronger data, but expresses the same
-- point-surjectivity property.
data Consolidation source target = Consolidation
  { applyConsolidation :: source -> target
  , consolidationPreimage :: target -> source
  , consolidationMonotone :: source -> source -> ()
  , consolidationPointSurjective :: target -> ()
  }

-- | Construct a consolidation from its object map, a chosen preimage for each
-- target object, and witnesses of the laws documented on 'Consolidation'.
--
-- The laws are currently an unchecked caller obligation. The witness
-- callbacks reserve the proof-bearing API shape for a later LiquidHaskell
-- refinement without adding runtime validation now.
consolidation
  :: (source -> target)
  -> (target -> source)
  -> (source -> source -> ())
  -> (target -> ())
  -> Consolidation source target
consolidation = Consolidation

-- | The identity consolidation.
identityConsolidation :: Consolidation object object
identityConsolidation =
  Consolidation id id (\_ _ -> ()) (const ())

-- | Compose consolidations in categorical order.
--
-- @composeConsolidations second first@ first applies @first@, then @second@.
-- The chosen preimages compose in the reverse order. Assuming the input laws,
-- the result is monotone and its chosen preimage remains a right inverse.
composeConsolidations
  :: Consolidation middle target
  -> Consolidation source middle
  -> Consolidation source target
composeConsolidations second first =
  Consolidation
    { applyConsolidation =
        applyConsolidation second . applyConsolidation first
    , consolidationPreimage =
        consolidationPreimage first . consolidationPreimage second
    , consolidationMonotone = \left right ->
        consolidationMonotone first left right
          `seq` consolidationMonotone second
            (applyConsolidation first left)
            (applyConsolidation first right)
    , consolidationPointSurjective = \target ->
        consolidationPointSurjective second target
          `seq` consolidationPointSurjective first
            (consolidationPreimage second target)
    }

-- | The horizontal sum of two consolidations, corresponding to
-- @ConHom.sum@ in @datra.lean@.
--
-- It maps and chooses preimages independently in the two summands. The
-- cross-summand monotonicity case follows from every left object preceding
-- every right object in @sumChains@.
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
    , consolidationMonotone = monotoneInSum
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
      consolidationMonotone left first second
    monotoneInSum (Right first) (Right second) =
      consolidationMonotone right first second
    monotoneInSum (Left _) (Right _) = ()
    -- A right object never precedes a left object in the chain sum, so the
    -- premise of the monotonicity law is false in this case.
    monotoneInSum (Right _) (Left _) = ()

    pointSurjectiveInSum (Left value) =
      consolidationPointSurjective left value
    pointSurjectiveInSum (Right value) =
      consolidationPointSurjective right value

-- The category coherence laws are extensional laws on the object maps:
--
-- * @applyConsolidation (id . f) x == applyConsolidation f x@,
-- * @applyConsolidation (f . id) x == applyConsolidation f x@, and
-- * @applyConsolidation ((h . g) . f) x ==
--      applyConsolidation (h . (g . f)) x@.
--
-- The chosen preimages satisfy the dual equations because composition reverses
-- their order. These laws follow from function composition, but are documented
-- rather than checked by LiquidHaskell at this stage.
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
