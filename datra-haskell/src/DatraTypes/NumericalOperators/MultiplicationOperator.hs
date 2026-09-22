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

-- | Multiplication of ordinal values and super-ellipsis formulations.
module NumericalOperators.MultiplicationOperator
  ( MultiplicationOperands (MultiplicationOutput)
  , multiplicationOperator
  ) where

import DatraOrdinal (multiplyOrdinals)
import NumericalOperators.Internal (applyOrdinalMultiplication)
import NumericalOperators.NumericalOperand
  ( KnownSuperEllipsisData
  , KnownSuperEllipsisLevel
  , MultiplicationNumericalLevel
  , MultiplicationResult
  , NumericalForm (..)
  , NumericalOperand
  , NumericalOperandForm
  , PreviousSuperEllipsisLevel
  , SuperEllipsisAt
  , knownSuperEllipsisData
  )
import Prelude (Maybe (..))
import StableConfederalData (StableConfederalData)

class MultiplicationOperands left right where
  type MultiplicationOutput left right scope
  applyMultiplicationOperands
    :: left
    -> right
    -> (forall resultScope.
          MultiplicationOutput left right resultScope -> result)
    -> Maybe result

type family MultiplicationOutputFor
    (leftForm :: NumericalForm)
    (rightForm :: NumericalForm)
    left
    right
    scope where
  MultiplicationOutputFor
      'FormulationNumerical 'FormulationNumerical left right _scope =
    StableConfederalData
      (SuperEllipsisAt
        (PreviousSuperEllipsisLevel
          (MultiplicationNumericalLevel left right)))
  MultiplicationOutputFor _leftForm _rightForm left right scope =
    MultiplicationResult left right scope

class ApplyMultiplication
    (leftForm :: NumericalForm)
    (rightForm :: NumericalForm)
    left
    right where
  applyMultiplication
    :: left
    -> right
    -> (forall resultScope.
          MultiplicationOutputFor
            leftForm rightForm left right resultScope -> result)
    -> Maybe result

instance
    ( NumericalOperand left
    , NumericalOperand right
    , KnownSuperEllipsisLevel (MultiplicationNumericalLevel left right)
    ) =>
    ApplyMultiplication 'ExplicitNumerical rightForm left right where
  applyMultiplication = applyOrdinalMultiplication multiplyOrdinals

instance
    ( NumericalOperand left
    , NumericalOperand right
    , KnownSuperEllipsisLevel (MultiplicationNumericalLevel left right)
    ) =>
    ApplyMultiplication
      'FormulationNumerical 'ExplicitNumerical left right where
  applyMultiplication = applyOrdinalMultiplication multiplyOrdinals

instance
    ( NumericalOperand left
    , NumericalOperand right
    , KnownSuperEllipsisData
        (PreviousSuperEllipsisLevel
          (MultiplicationNumericalLevel left right))
    ) =>
    ApplyMultiplication
      'FormulationNumerical 'FormulationNumerical left right where
  applyMultiplication _ _ useResult =
    Just (useResult (knownSuperEllipsisData
      @(PreviousSuperEllipsisLevel
        (MultiplicationNumericalLevel left right))))

instance
    ( NumericalOperand left
    , NumericalOperand right
    , ApplyMultiplication
        (NumericalOperandForm left)
        (NumericalOperandForm right)
        left
        right
    ) =>
    MultiplicationOperands left right where
  type MultiplicationOutput left right scope =
    MultiplicationOutputFor
      (NumericalOperandForm left)
      (NumericalOperandForm right)
      left
      right
      scope
  applyMultiplicationOperands =
    applyMultiplication
      @(NumericalOperandForm left)
      @(NumericalOperandForm right)

multiplicationOperator
  :: MultiplicationOperands left right
  => left
  -> right
  -> (forall resultScope.
        MultiplicationOutput left right resultScope -> result)
  -> Maybe result
multiplicationOperator = applyMultiplicationOperands
