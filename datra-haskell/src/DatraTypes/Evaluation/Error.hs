-- | Domain failures produced while evaluating Datra values. Rendering and
-- locale selection deliberately live outside this module.
module Evaluation.Error
  ( InterpretedValueKind (..)
  , InterpretingError (..)
  , OperandSide (..)
  , AtlasMapFederationOperation (..)
  , AtlasMapFederationRefutation (..)
  , AtlasMapFederationUncertainty (..)
  ) where

import MapOperators.AccessOperator (AccessError)
import Numeric.Natural (Natural)
import SuperEllipsisRange
  ( SuperEllipsisRangeConcatError
  , SuperEllipsisRangeError
  )

data OperandSide = LeftOperand | RightOperand
  deriving (Eq, Show)

data InterpretedValueKind
  = NaturalValueKind
  | ExplicitOrdinalValueKind
  | FormulationValueKind
  | RangeValueKind
  | RangeConcatenationValueKind
  | AsciiStringValueKind
  | IdentifierTypeValueKind
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
  = AtlasMapFederationConcatenationCollision Natural
  | AtlasMapFederationAccessHasEmptyCounterexample
  | AtlasMapFederationSpecificationHasNoMatchingMember
  | AtlasMapFederationSubfederationHasMissingMember
  deriving (Eq, Show)

data AtlasMapFederationUncertainty
  = NoAtlasMapFederationDecisionProcedure AtlasMapFederationOperation
  deriving (Eq, Show)

data InterpretingError
  = ExpectedNumericalOperand OperandSide InterpretedValueKind
  | ExpectedNaturalExponent InterpretedValueKind
  | ExpectedInsertionOperand InterpretedValueKind
  | ExpectedTotalAtlasMap InterpretedValueKind
  | RangeConstructionRejected SuperEllipsisRangeError
  | RangeConcatenationRejected SuperEllipsisRangeConcatError
  | AccessRejected AccessError
  | AtlasMapFederationOperationRefuted AtlasMapFederationRefutation
  | AtlasMapFederationOperationUndecidable AtlasMapFederationUncertainty
  | InvalidAsciiStringCharacter Char
  deriving (Eq, Show)
