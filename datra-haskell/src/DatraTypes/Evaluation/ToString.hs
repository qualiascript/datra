-- | Internal pointwise conversion used by string-template interpolation.
-- There is deliberately no surface-language name for this operation.
module Evaluation.ToString
  ( toStringValue
  , stringTemplateValue
  ) where

import AtlasMapFederationExpression
  ( AtlasMapFederationExpression (PrimitiveAtlasMapFederation) )
import Evaluation.Construction (makeAsciiString)
import Evaluation.Error (InterpretingError (AmbiguousStringTemplate))
import Evaluation.Value

-- | Convert a total value to its canonical source spelling, or retain a
-- pointwise string-federation map for a non-total value. Strings are identity
-- values so their source delimiters never become data.
toStringValue
  :: (CanonicalResult -> String)
  -> InterpretedValue
  -> Either InterpretingError InterpretedValue
toStringValue renderCanonical source =
  case interpretedForm source of
    AsciiStringForm _ -> Right source
    StringTypeForm -> Right source
    ToStringForm _ -> Right source
    StringTemplateForm _ -> Right source
    _
      | interpretedValueHasTotalMap source ->
          Right
            (makeAsciiString
              (renderCanonical (interpretedCanonicalResult source)))
      | toStringConversionIsInjective (interpretedSemantics source) ->
          Right pointwiseFederation
      | otherwise -> Left AmbiguousStringTemplate
  where
    pointwiseFederation =
      makeInterpretedValue
        (ToStringForm source)
        NoInsertion
        emptyInterpretedMap
        (PrimitiveAtlasMapFederation
          (ToStringAtlasMapFederation source))
        NonTotalInterpretedMap
        (ToStringSemantics (interpretedSemantics source))

toStringConversionIsInjective :: ValueSemantics -> Bool
toStringConversionIsInjective semantics =
  case semantics of
    NaturalRangeSemantics {} -> True
    ValuedNaturalRangeSemantics {} -> True
    NaturalTypeSemantics -> True
    IntegerRangeSemantics {} -> True
    ValuedIntegerRangeSemantics {} -> True
    IntegerTypeSemantics -> True
    StringTypeSemantics -> True
    EitherSemantics left right -> isBooleanPair left right
    IdentifierTypeSemantics _ underlying _ ->
      toStringConversionIsInjective underlying
    IdentifierStringProjectionSemantics _ underlying _ ->
      toStringConversionIsInjective underlying
    ToStringSemantics source -> toStringConversionIsInjective source
    _ -> False
  where
    isBooleanPair (BooleanSemantics leftFlag _) (BooleanSemantics rightFlag _) =
      leftFlag /= rightFlag
    isBooleanPair _ _ = False

-- | Retain the ordinary concatenation result while recording that its members
-- are the pointwise outputs of one string template.
stringTemplateValue :: InterpretedValue -> InterpretedValue
stringTemplateValue value =
  case interpretedForm value of
    AsciiStringForm _ -> value
    StringTypeForm -> value
    ToStringForm _ -> value
    StringTemplateForm _ -> value
    _ ->
      makeInterpretedValue
        (StringTemplateForm value)
        (interpretedInsertionCapability value)
        (interpretedMap value)
        (interpretedAtlasMapFederation value)
        (if interpretedValueHasTotalMap value
          then TotalInterpretedMap
          else NonTotalInterpretedMap)
        (interpretedSemantics value)
