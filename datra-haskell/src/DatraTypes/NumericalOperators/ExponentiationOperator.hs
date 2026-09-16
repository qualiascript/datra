{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}

-- | Finite exponentiation of ordinal values and super-ellipsis formulations.
module NumericalOperators.ExponentiationOperator
  ( ExponentiationOperand (ExponentiationOutput)
  , exponentiationOperator
  ) where

import DatraOrdinal (naturalAtOrdinal, powerOrdinal)
import EllipsisNatural (EllipsisNatural)
import NumericalOperators.Internal (applyOrdinalExponentOperator)
import NumericalOperators.NumericalOperand
  ( KnownSuperEllipsisLevel
  , NumericalOperandLevel
  , NumericalOperandTarget
  , SomeSuperEllipsis
  , SuperEllipsisCarrier
  , someSuperEllipsis
  , superEllipsisCarrierLevelNatural
  )
import Prelude (Maybe (..), (*), (>>=))
import StableConfederalData (StableConfederalData)
import SuperEllipsisRange (SuperEllipsisRange)
import SuperEllipsisValue
  ( SuperEllipsisValue
  , superEllipsisValueOrdinal
  )

class ExponentiationOperand base where
  type ExponentiationOutput base scope
  applyExponentiationOperand
    :: base
    -> EllipsisNatural exponentScope
    -> (forall resultScope.
          ExponentiationOutput base resultScope -> result)
    -> Maybe result

instance
    ( SuperEllipsisCarrier target
    , KnownSuperEllipsisLevel
        (NumericalOperandLevel (SuperEllipsisRange target scope))
    ) =>
    ExponentiationOperand (SuperEllipsisRange target scope) where
  type ExponentiationOutput
      (SuperEllipsisRange target scope) resultScope =
    SuperEllipsisValue
      (NumericalOperandTarget (SuperEllipsisRange target scope))
      resultScope
  applyExponentiationOperand =
    applyOrdinalExponentOperator powerOrdinal

instance forall target.
    SuperEllipsisCarrier target =>
    ExponentiationOperand (StableConfederalData target) where
  type ExponentiationOutput (StableConfederalData target) scope =
    SomeSuperEllipsis
  applyExponentiationOperand _ exponentValue useResult =
    superEllipsisValueOrdinal exponentValue
      >>= naturalAtOrdinal
      >>= (\power ->
        Just (useResult (someSuperEllipsis
          (superEllipsisCarrierLevelNatural @target * power))))

-- | Raise a base to an Ellipsis-natural exponent.  Explicit bases produce
-- explicit ordinal values.  Formulation bases produce formulations, with the
-- precise finite level hidden existentially because the exponent is runtime.
exponentiationOperator
  :: ExponentiationOperand base
  => base
  -> EllipsisNatural exponentScope
  -> (forall resultScope.
        ExponentiationOutput base resultScope -> result)
  -> Maybe result
exponentiationOperator = applyExponentiationOperand
