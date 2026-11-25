module DatraTypes.Contextual
  ( ContextualLevel
  , ContextualMap (..)
  , RecursivePrefix (..)
  , RecursiveCollection (..)
  ) where

import DatraLanguage.AST (Expression)
import DatraLanguage.ContextualDeclaration (ContextualRole)
import DatraTypes

type ContextualLevel =
  (Bool, ReductionContext -> Either InterpretingError InterpretedValue)

data ContextualMap = ContextualMap ContextualRole [ContextualLevel]

data RecursivePrefix
  = RecursiveConcatenation Expression
  | RecursiveAtlasSequence [Expression]
  | RecursiveMapSequence [Expression]

data RecursiveCollection
  = RecursiveList Expression
  | RecursiveStream Expression
