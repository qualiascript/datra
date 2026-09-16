{-# LANGUAGE RankNTypes #-}

-- | Addition of singleton ellipsis naturals.
module NumericalOperators.AdditionOperator
  ( additionOperator
  ) where

import EllipsisNatural (EllipsisNatural)
import NumericalOperators.Internal (applyNaturalOperator)
import Prelude (Maybe)

import qualified Prelude

-- | Add two ellipsis naturals and introduce the result with a fresh scope.
additionOperator
  :: EllipsisNatural leftScope
  -> EllipsisNatural rightScope
  -> (forall resultScope. EllipsisNatural resultScope -> result)
  -> Maybe result
additionOperator = applyNaturalOperator (Prelude.+)
