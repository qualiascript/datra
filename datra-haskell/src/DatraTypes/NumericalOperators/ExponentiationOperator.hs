{-# LANGUAGE RankNTypes #-}

-- | Exponentiation of singleton ellipsis naturals.
module NumericalOperators.ExponentiationOperator
  ( exponentiationOperator
  ) where

import EllipsisNatural (EllipsisNatural)
import NumericalOperators.Internal (applyNaturalOperator)
import Prelude (Maybe)

import qualified Prelude

-- | Raise the first ellipsis natural to the power of the second and introduce
-- the result with a fresh scope. As for 'Prelude.^', @0 ^ 0@ is @1@.
exponentiationOperator
  :: EllipsisNatural baseScope
  -> EllipsisNatural exponentScope
  -> (forall resultScope. EllipsisNatural resultScope -> result)
  -> Maybe result
exponentiationOperator = applyNaturalOperator (Prelude.^)
