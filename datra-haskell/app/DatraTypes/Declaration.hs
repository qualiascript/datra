module DatraTypes.Declaration
  ( PreparedDependentDeclaration (..)
  , EvaluatedDeclarationCapture (..)
  , PreparedDependentDeclarationSelection (..)
  ) where

import DatraTypes

data PreparedDependentDeclaration = PreparedDependentDeclaration
  { preparedDeclarationCaptures :: [EvaluatedDeclarationCapture]
  , preparedDeclarationTemplate :: EvaluatedStringTemplate
  }

data EvaluatedDeclarationCapture = EvaluatedDeclarationCapture
  { evaluatedDeclarationCaptureName :: Maybe String
  , evaluatedDeclarationCaptureSchema :: InterpretedValue
  , evaluatedDeclarationCaptureBound :: InterpretedValue
  , evaluatedDeclarationCapturePresentation :: InterpretedValue
  }

data PreparedDependentDeclarationSelection
  = PreparedDeclarationDescriptor PreparedDependentDeclaration
  | PreparedDeclarationConcrete
      PreparedDependentDeclaration
      [InterpretedValue]
