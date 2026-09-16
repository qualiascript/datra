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
  ( AddSuperEllipsisLevels
  , KnownSuperEllipsisData
  , KnownSuperEllipsisLevel
  , MultiplicationNumericalLevel
  , MultiplicationResult
  , SuperEllipsisAt
  , SuperEllipsisCarrier
  , SuperEllipsisCarrierLevel
  , knownSuperEllipsisData
  )
import Prelude (Maybe (..))
import StableConfederalData (StableConfederalData)
import SuperEllipsisRange (SuperEllipsisRange)

class MultiplicationOperands left right where
  type MultiplicationOutput left right scope
  applyMultiplicationOperands
    :: left
    -> right
    -> (forall resultScope.
          MultiplicationOutput left right resultScope -> result)
    -> Maybe result

instance
    ( SuperEllipsisCarrier leftTarget
    , SuperEllipsisCarrier rightTarget
    , KnownSuperEllipsisLevel
        (MultiplicationNumericalLevel
          (SuperEllipsisRange leftTarget leftScope)
          (SuperEllipsisRange rightTarget rightScope))
    ) =>
    MultiplicationOperands
      (SuperEllipsisRange leftTarget leftScope)
      (SuperEllipsisRange rightTarget rightScope) where
  type MultiplicationOutput
      (SuperEllipsisRange leftTarget leftScope)
      (SuperEllipsisRange rightTarget rightScope)
      resultScope =
    MultiplicationResult
      (SuperEllipsisRange leftTarget leftScope)
      (SuperEllipsisRange rightTarget rightScope)
      resultScope
  applyMultiplicationOperands =
    applyOrdinalMultiplication multiplyOrdinals

instance
    ( SuperEllipsisCarrier formulationTarget
    , SuperEllipsisCarrier valueTarget
    , KnownSuperEllipsisLevel
        (MultiplicationNumericalLevel
          (StableConfederalData formulationTarget)
          (SuperEllipsisRange valueTarget valueScope))
    ) =>
    MultiplicationOperands
      (StableConfederalData formulationTarget)
      (SuperEllipsisRange valueTarget valueScope) where
  type MultiplicationOutput
      (StableConfederalData formulationTarget)
      (SuperEllipsisRange valueTarget valueScope)
      resultScope =
    MultiplicationResult
      (StableConfederalData formulationTarget)
      (SuperEllipsisRange valueTarget valueScope)
      resultScope
  applyMultiplicationOperands =
    applyOrdinalMultiplication multiplyOrdinals

instance
    ( SuperEllipsisCarrier valueTarget
    , SuperEllipsisCarrier formulationTarget
    , KnownSuperEllipsisLevel
        (MultiplicationNumericalLevel
          (SuperEllipsisRange valueTarget valueScope)
          (StableConfederalData formulationTarget))
    ) =>
    MultiplicationOperands
      (SuperEllipsisRange valueTarget valueScope)
      (StableConfederalData formulationTarget) where
  type MultiplicationOutput
      (SuperEllipsisRange valueTarget valueScope)
      (StableConfederalData formulationTarget)
      resultScope =
    MultiplicationResult
      (SuperEllipsisRange valueTarget valueScope)
      (StableConfederalData formulationTarget)
      resultScope
  applyMultiplicationOperands =
    applyOrdinalMultiplication multiplyOrdinals

instance
    forall leftTarget rightTarget.
    ( SuperEllipsisCarrier leftTarget
    , SuperEllipsisCarrier rightTarget
    , KnownSuperEllipsisData
        (AddSuperEllipsisLevels
          (SuperEllipsisCarrierLevel leftTarget)
          (SuperEllipsisCarrierLevel rightTarget))
    ) =>
    MultiplicationOperands
      (StableConfederalData leftTarget)
      (StableConfederalData rightTarget) where
  type MultiplicationOutput
      (StableConfederalData leftTarget)
      (StableConfederalData rightTarget)
      _resultScope =
    StableConfederalData
      (SuperEllipsisAt
        (AddSuperEllipsisLevels
          (SuperEllipsisCarrierLevel leftTarget)
          (SuperEllipsisCarrierLevel rightTarget)))
  applyMultiplicationOperands _ _ useResult =
    Just (useResult (knownSuperEllipsisData
      @(AddSuperEllipsisLevels
        (SuperEllipsisCarrierLevel leftTarget)
        (SuperEllipsisCarrierLevel rightTarget))))

multiplicationOperator
  :: MultiplicationOperands left right
  => left
  -> right
  -> (forall resultScope.
        MultiplicationOutput left right resultScope -> result)
  -> Maybe result
multiplicationOperator = applyMultiplicationOperands
