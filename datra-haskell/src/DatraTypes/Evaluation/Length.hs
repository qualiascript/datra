-- | Exact final-page lengths for evaluated Datra objects.
module Evaluation.Length (mapLengthValue) where

import DatraOrdinal (naturalAtOrdinal, omega)
import Evaluation.Construction (makeNatural)
import Evaluation.Error
  ( InterpretingError (MapLengthFailed)
  , MapLengthFailure (..)
  )
import Evaluation.Numerical
  ( IntegerLimit (PositiveInfinity)
  , makeIntegerLimit
  )
import Evaluation.Value
  ( InterpretedValue
  , ValueForm (..)
  , interpretedForm
  , interpretedMap
  , interpretedMapFinalOrderType
  )

-- | Return the exact ordered length of an object's final Atlas page whenever
-- that length is representable by @NatLimit@. Host meta-types, functions, and
-- other values without a meaningful final-page extent are not empty maps.
mapLengthValue
  :: InterpretedValue
  -> Either InterpretingError InterpretedValue
mapLengthValue value
  | not (hasDeterminateMapLength (interpretedForm value)) =
      Left (MapLengthFailed IndeterminateMapLength)
  | Just finite <- naturalAtOrdinal orderType = Right (makeNatural finite)
  | orderType == omega = Right (makeIntegerLimit PositiveInfinity)
  | otherwise =
      Left (MapLengthFailed (MapLengthExceedsNaturalLimit orderType))
  where
    orderType = interpretedMapFinalOrderType (interpretedMap value)

-- Forms whose map field is an implementation placeholder do not denote an
-- Atlas object with an observable final-page length. The remaining forms are
-- constructed with an exact finite or ordinal-indexed final-page extent.
hasDeterminateMapLength :: ValueForm -> Bool
hasDeterminateMapLength form =
  case form of
    BuiltinMetaTypeForm {} -> False
    FunctionForm {} -> False
    IdentifierValueTypeForm -> False
    ToStringForm -> False
    TemplateForm {} -> False
    DependentSumForm {} -> False
    IdentifierStringProjectionForm {} -> False
    _ -> True
