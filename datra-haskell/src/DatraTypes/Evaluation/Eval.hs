-- | Typed decoding shared by surface eval and template-backed syntax.
module Evaluation.Eval
  ( evalValues
  ) where

import Evaluation.Access (accessValues)
import Evaluation.Construction (makeNatural)
import Evaluation.Error (InterpretingError)
import Evaluation.Specification (specifyValues)
import Evaluation.ToString
  ( CanonicalStringCodec
  , stringConversionIsIdentity
  , stringTemplateValue
  , toStringValue
  )
import Evaluation.Value
import Extract (extractValue)

evalValues
  :: CanonicalStringCodec
  -> InterpretedValue
  -> InterpretedValue
  -> Either InterpretingError InterpretedValue
evalValues codec source target
  -- A string federation already describes the input text. Keep its entire
  -- specification, including every template capture, for subsequent extract.
  | stringConversionIsIdentity (interpretedForm target) =
      specifyValues source target
  | otherwise = do
      renderedTarget <- toStringValue codec target
      matched <- specifyValues source (stringTemplateValue renderedTarget)
      captured <- extractValue matched
      accessValues captured (makeNatural 1)
