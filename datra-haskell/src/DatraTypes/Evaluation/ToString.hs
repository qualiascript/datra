-- | Internal pointwise conversion used by string-template interpolation.
-- There is deliberately no surface-language name for this operation.
module Evaluation.ToString
  ( toStringValue
  , templateValue
  , stringConversionIsIdentity
  ) where

import Evaluation.Construction (makeAsciiString)
import Evaluation.Error
  ( InterpretingError (InjectiveValueConstructionNotImplemented) )
import Evaluation.Specification.String (valueProducesStrings)
import Evaluation.Value

-- | Conversion of a concrete value remains safe. Pointwise conversion of a
-- federation used to manufacture alleged injectivity evidence from rendered
-- strings; it is intentionally unavailable until the structural insertion
-- design is implemented.
toStringValue
  :: (InterpretedValue -> String)
  -> InterpretedValue
  -> Either InterpretingError InterpretedValue
toStringValue render source
  | stringConversionIsIdentity source = Right source
  | interpretedTypeIsTotal source =
      Right (makeAsciiString (render source))
  | otherwise = Left InjectiveValueConstructionNotImplemented

-- | Retain the ordinary concatenation result while recording that its members
-- are the pointwise outputs of one string template. A concrete string is
-- already its own canonical template result; a string federation still needs
-- the wrapper so its components render as interpolations rather than ordinary
-- map concatenation.
templateValue :: InterpretedValue -> InterpretedValue
templateValue value =
  case interpretedForm value of
    AsciiStringForm _ -> value
    _ ->
      makeInterpretedValue
        (interpretedDatraType value)
        (TemplateForm value)
        (interpretedInsertionCapability value)
        (interpretedMap value)
        (interpretedAtlasMapFederation value)
        (if interpretedValueHasTotalMap value
          then TotalInterpretedMap
          else NonTotalInterpretedMap)
        (TemplateSemantics (interpretedSemantics value))

stringConversionIsIdentity :: InterpretedValue -> Bool
stringConversionIsIdentity = valueProducesStrings
