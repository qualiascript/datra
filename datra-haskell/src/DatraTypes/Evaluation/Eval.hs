-- | Typed decoding shared by surface eval and template-backed syntax.
module Evaluation.Eval
  ( evalValues
  ) where

import Evaluation.Access (accessValues)
import Evaluation.Construction (makeNatural)
import Evaluation.Error (InterpretingError)
import Evaluation.Specification (specifyValues)
import Evaluation.ToString
  ( stringConversionIsIdentity
  , templateValue
  , toStringValue
  )
import Evaluation.Value

evalValues
  :: (InterpretedValue -> String)
  -> InterpretedValue
  -> InterpretedValue
  -> Either InterpretingError InterpretedValue
evalValues render source target
  -- A string federation already describes the input text. Keep its entire
  -- specification, including every retained template selection.
  | stringConversionIsIdentity target =
      specifyValues source target
  | otherwise = do
      renderedTarget <- toStringValue render target
      matched <- specifyValues source (templateValue renderedTarget)
      accessValues matched (makeNatural 1)
