-- | Optional federation construction for Datra's postfix @?@ operator.
module Evaluation.Optional
  ( makeNothing
  , makeOptionalValue
  ) where

import Evaluation.Either (makeEitherValue)
import Evaluation.Map (makeAtlasMap)
import Evaluation.Value

-- | The distinguished absent value, rendered canonically as @Nothing : ()@.
makeNothing :: InterpretedValue
makeNothing = value
  where
    unit = makeAtlasMap 0 []
    semantics =
      IdentifierTypeSemantics
        (SimpleIdentifierDependency "Nothing")
        (interpretedSemantics unit)
        True
    value =
      makeSingletonInterpretedValue
        NothingForm
        NoInsertion
        (interpretedMap unit)
        TotalInterpretedMap
        semantics

-- | @T?@ is definitionally @T | Nothing := ()@.
makeOptionalValue :: InterpretedValue -> InterpretedValue
makeOptionalValue value = makeEitherValue value makeNothing
