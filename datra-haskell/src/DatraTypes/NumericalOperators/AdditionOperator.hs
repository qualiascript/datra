{-# LANGUAGE RankNTypes #-}

-- | Addition of singleton natural values.
module NumericalOperators.AdditionOperator
  ( additionOperator
  ) where

import EllipsisNatural qualified as Datra
import NumericalOperators.Internal (applyNaturalOperator)
import Prelude (Maybe)

import qualified Prelude

-- | Add two naturals and introduce the result with a fresh scope.
additionOperator
  :: Datra.EllipsisNatural leftScope
  -> Datra.EllipsisNatural rightScope
  -> (forall resultScope. Datra.EllipsisNatural resultScope -> result)
  -> Maybe result
additionOperator = applyNaturalOperator (Prelude.+)
