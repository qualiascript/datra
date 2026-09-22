{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
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
  , NumericalForm (..)
  , NumericalOperand
  , NumericalOperandForm
  , NumericalOperandLevel
  , NumericalOperandTarget
  , PreviousSuperEllipsisLevel
  , SomeSuperEllipsis
  , knownSuperEllipsisLevelNatural
  , someSuperEllipsis
  )
import Prelude (Maybe (..), (*), (>>=))
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

type family ExponentiationOutputFor
    (form :: NumericalForm)
    base
    scope where
  ExponentiationOutputFor 'ExplicitNumerical base scope =
    SuperEllipsisValue
      (NumericalOperandTarget base)
      scope
  ExponentiationOutputFor 'FormulationNumerical _base _scope =
    SomeSuperEllipsis

class ApplyExponentiation (form :: NumericalForm) base where
  applyExponentiation
    :: base
    -> EllipsisNatural exponentScope
    -> (forall resultScope.
          ExponentiationOutputFor form base resultScope -> result)
    -> Maybe result

instance
    ( NumericalOperand base
    , KnownSuperEllipsisLevel (NumericalOperandLevel base)
    ) =>
    ApplyExponentiation 'ExplicitNumerical base where
  applyExponentiation = applyOrdinalExponentOperator powerOrdinal

instance
    ( NumericalOperand base
    , KnownSuperEllipsisLevel
        (PreviousSuperEllipsisLevel (NumericalOperandLevel base))
    ) =>
    ApplyExponentiation 'FormulationNumerical base where
  applyExponentiation _ exponentValue useResult =
    naturalAtOrdinal (superEllipsisValueOrdinal exponentValue)
      >>= (\power ->
        Just (useResult (someSuperEllipsis
          (knownSuperEllipsisLevelNatural
            @(PreviousSuperEllipsisLevel (NumericalOperandLevel base))
            * power))))

instance
    ( NumericalOperand base
    , ApplyExponentiation (NumericalOperandForm base) base
    ) =>
    ExponentiationOperand base where
  type ExponentiationOutput base scope =
    ExponentiationOutputFor (NumericalOperandForm base) base scope
  applyExponentiationOperand =
    applyExponentiation @(NumericalOperandForm base)

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
