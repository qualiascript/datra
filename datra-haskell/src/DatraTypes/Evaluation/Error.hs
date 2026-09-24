-- | Domain failures produced while evaluating Datra values. Rendering and
-- locale selection deliberately live outside this module.
module Evaluation.Error
  ( InterpretedValueKind (..)
  , InterpretingError (..)
  , OverloadFailure (..)
  , overloadFailureIsAmbiguous
  , OperandSide (..)
  , AtlasMapFederationOperation (..)
  , AtlasMapFederationRefutation (..)
  , AtlasMapFederationUncertainty (..)
  ) where

import MapOperators.AccessOperator (AccessError)
import SuperEllipsisRange
  ( SuperEllipsisRangeConcatError
  , SuperEllipsisRangeError
  )

data OperandSide = LeftOperand | RightOperand
  deriving (Eq, Show)

data InterpretedValueKind
  = FunctionValueKind
  | NaturalValueKind
  | IntegerValueKind
  | BooleanValueKind
  | EitherValueKind
  | ExplicitOrdinalValueKind
  | FormulationValueKind
  | RangeValueKind
  | RangeConcatenationValueKind
  | AsciiStringValueKind
  | DependentIdentifierTypeValueKind
  | MapValueKind
  | SpecificationValueKind
  deriving (Eq, Show)

data AtlasMapFederationOperation
  = AtlasMapFederationConcatenation
  | AtlasMapFederationAccess
  | AtlasMapFederationSpecification
  | AtlasMapFederationSubfederation
  deriving (Eq, Show)

data AtlasMapFederationRefutation
  = AtlasMapFederationConcatenationCollision Integer
  | AtlasMapFederationAccessHasEmptyCounterexample
  | AtlasMapFederationSpecificationHasNoMatchingMember
  | AtlasMapFederationSubfederationHasMissingMember
  deriving (Eq, Show)

data AtlasMapFederationUncertainty
  = NoAtlasMapFederationDecisionProcedure AtlasMapFederationOperation
  deriving (Eq, Show)

-- | Semantic overload failures. These constructors are used for evaluator
-- control flow; localized prose belongs exclusively to diagnostics modules.
data OverloadFailure
  = OverloadNoMatch
  | OverloadAmbiguousWithoutWrittenOrder
  | OverloadAmbiguousWrittenOrder
  | OverloadMissingRequiredSlot
  | OverloadSkippedRequiredSlot
  | OverloadChangedDefault
  deriving (Eq, Show)

overloadFailureIsAmbiguous :: OverloadFailure -> Bool
overloadFailureIsAmbiguous failure =
  case failure of
    OverloadAmbiguousWithoutWrittenOrder -> True
    OverloadAmbiguousWrittenOrder -> True
    _ -> False

data InterpretingError
  = NamedAccessError String
  | FunctionError String
  | OverloadError OverloadFailure
  | AssertionFailed
  | IdentifierStringOverlap String
  | UnknownIdentifier String
  | PrivateParameterCannotBeOptional String
  | CyclicIdentifierReference [String]
  | LetOutsideBegin
  | ExpectedNumericalOperand OperandSide InterpretedValueKind
  | ExpectedFiniteIntegerOperand OperandSide InterpretedValueKind
  | ExpectedBooleanOperand OperandSide InterpretedValueKind
  | ExpectedBooleanCondition InterpretedValueKind
  | ExpectedNaturalExponent InterpretedValueKind
  | ExpectedInsertionOperand InterpretedValueKind
  | ExpectedTotalAtlasMap InterpretedValueKind
  | RangeConstructionRejected SuperEllipsisRangeError
  | RangeConcatenationRejected SuperEllipsisRangeConcatError
  | AccessRejected AccessError
  | GivenValueOutsideTypeAnnotation
      { expectedTypeAnnotation :: String
      , givenValue :: String
      }
  | IdentifierStringMismatch
      { expectedIdentifierString :: String
      , givenIdentifierString :: String
      }
  | IntermediateTypeAnnotationOutsideTarget
      { expectedTargetTypeAnnotation :: String
      , givenIntermediateTypeAnnotation :: String
      }
  | AtlasMapFederationOperationRefuted AtlasMapFederationRefutation
  | AtlasMapFederationOperationUndecidable AtlasMapFederationUncertainty
  | NonInjectiveStringInterpolation
  | NoCanonicalStringConversion
  | ExpectedStringTemplateSpecification InterpretedValueKind
  | EitherAlternativesNotDistinct
  | AmbiguousStringTemplate
  | InvalidAsciiStringCharacter Char
  deriving (Eq, Show)
