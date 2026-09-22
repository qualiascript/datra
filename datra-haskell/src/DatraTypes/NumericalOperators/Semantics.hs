-- | Erased numerical policy shared by typed operators and the evaluator.
module NumericalOperators.Semantics
  ( NumericalDenotation (..)
  , numericalDenotationOrdinal
  , addNumericalDenotations
  , multiplyNumericalDenotations
  , exponentiateNumericalDenotation
  ) where

import DatraOrdinal
  ( Ordinal
  , addOrdinals
  , multiplyOrdinals
  , omegaPower
  , powerOrdinal
  )
import Numeric.Natural (Natural)

data NumericalDenotation
  = ExplicitDenotation Ordinal
  | FormulationDenotation Natural

numericalDenotationOrdinal :: NumericalDenotation -> Ordinal
numericalDenotationOrdinal (ExplicitDenotation value) = value
numericalDenotationOrdinal (FormulationDenotation level) = omegaPower level

addNumericalDenotations
  :: NumericalDenotation
  -> NumericalDenotation
  -> NumericalDenotation
addNumericalDenotations left right =
  ExplicitDenotation
    (addOrdinals
      (numericalDenotationOrdinal left)
      (numericalDenotationOrdinal right))

multiplyNumericalDenotations
  :: NumericalDenotation
  -> NumericalDenotation
  -> NumericalDenotation
multiplyNumericalDenotations
    (FormulationDenotation leftLevel)
    (FormulationDenotation rightLevel) =
  FormulationDenotation (leftLevel + rightLevel)
multiplyNumericalDenotations left right =
  ExplicitDenotation
    (multiplyOrdinals
      (numericalDenotationOrdinal left)
      (numericalDenotationOrdinal right))

exponentiateNumericalDenotation
  :: NumericalDenotation
  -> Natural
  -> NumericalDenotation
exponentiateNumericalDenotation
    (FormulationDenotation level) power =
  FormulationDenotation (level * power)
exponentiateNumericalDenotation (ExplicitDenotation value) power =
  ExplicitDenotation (powerOrdinal value power)
