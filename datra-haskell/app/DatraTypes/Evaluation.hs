module DatraTypes.Evaluation
  ( Interpreter
  ) where

import DatraLanguage.AST (Expression)
import DatraTypes (InterpretedValue, InterpretingError)

type Interpreter = Expression -> Either InterpretingError InterpretedValue
