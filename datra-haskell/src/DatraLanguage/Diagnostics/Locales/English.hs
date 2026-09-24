-- | English presentation text for typed Datra diagnostics.
--
-- This display-stage module translates strongly typed domain errors into
-- prose. Domain modules do not depend on it.
module DatraLanguage.Diagnostics.Locales.English
  ( localizeAccessError
  , localizeInterpretingError
  , localizeSuperEllipsisRangeError
  , localizeSuperEllipsisRangeConcatError
  , englishOrdinal
  ) where

import DatraLanguage.Diagnostics (LocalizedMessage (LocalizedMessage))
import Evaluation.Error
  ( InterpretedValueKind (..)
  , InterpretingError (..)
  , OverloadFailure (..)
  , OperandSide (..)
  , AtlasMapFederationOperation (..)
  , AtlasMapFederationRefutation (..)
  , AtlasMapFederationUncertainty (..)
  )
import DatraLanguage.Diagnostics.Locales.Rendering
  ( renderOrdinal
  , renderRangeBounds
  , renderRangeDescription
  )
import DatraOrdinal (Ordinal)
import MapOperators.AccessOperator
  ( AccessError
      ( AccessInsertionRankExceedsMap
      , AccessPositionOutOfBounds
      )
  )
import SuperEllipsisRange
  ( SuperEllipsisRangeConcatError (SuperEllipsisRangesOverlap)
  , SuperEllipsisRangeDescription
  , SuperEllipsisRangeError
      ( SuperEllipsisRangeInvalidDescendingBounds
      , SuperEllipsisRangeStartOutsideRank
      , SuperEllipsisRangeTargetOutsideRank
      )
  )

localizeAccessError :: AccessError -> LocalizedMessage
localizeAccessError reason =
  case reason of
    AccessInsertionRankExceedsMap insertionRank mapOrderType ->
      LocalizedMessage
        "the access insertion has a larger rank than the map"
        [ "insertion rank limit: " <> englishOrdinal insertionRank
        , "map final-page order type: " <> englishOrdinal mapOrderType
        ]
    AccessPositionOutOfBounds position mapOrderType ->
      LocalizedMessage
        "the access insertion selects a position outside the map"
        [ "selected position: " <> englishOrdinal position
        , "map final-page order type: " <> englishOrdinal mapOrderType
        ]

localizeInterpretingError :: InterpretingError -> LocalizedMessage
localizeInterpretingError reason =
  case reason of
    NamedAccessError message -> LocalizedMessage "named access failed" [message]
    FunctionError message -> LocalizedMessage "function evaluation failed" [message]
    OverloadError failure ->
      LocalizedMessage "overloading failed" [overloadFailure failure]
    AssertionFailed -> LocalizedMessage "assertion failed" []
    IdentifierStringOverlap name ->
      LocalizedMessage "identifier strings overlap in begin scope" ["identifier: " <> name]
    UnknownIdentifier name ->
      LocalizedMessage "identifier is not imported in this scope" ["identifier: " <> name]
    CyclicIdentifierReference names ->
      LocalizedMessage "cyclic identifier dependency" ["identifiers: " <> show names]
    LetOutsideBegin ->
      LocalizedMessage "let requires an enclosing begin block" []
    ExpectedNumericalOperand side actual ->
      LocalizedMessage
        (operandSide side <> " operand must be numerical")
        ["actual value kind: " <> valueKind actual]
    ExpectedFiniteIntegerOperand side actual ->
      LocalizedMessage
        (operandSide side <> " operand must be a finite integer")
        ["actual value kind: " <> valueKind actual]
    ExpectedBooleanOperand side actual ->
      LocalizedMessage
        (operandSide side <> " operand must be Boolean")
        ["actual value kind: " <> valueKind actual]
    ExpectedBooleanCondition actual ->
      LocalizedMessage
        "if condition must be Boolean"
        ["actual value kind: " <> valueKind actual]
    ExpectedNaturalExponent actual ->
      LocalizedMessage
        "exponent must be a natural value"
        ["actual value kind: " <> valueKind actual]
    ExpectedInsertionOperand actual ->
      LocalizedMessage
        "right operand of map access must define a super-ellipsis insertion"
        ["actual value kind: " <> valueKind actual]
    ExpectedTotalAtlasMap actual ->
      LocalizedMessage
        "left operand of specification must be a total Atlas map"
        ["actual value kind: " <> valueKind actual]
    RangeConstructionRejected rejection ->
      localizeSuperEllipsisRangeError rejection
    RangeConcatenationRejected rejection ->
      localizeSuperEllipsisRangeConcatError rejection
    AccessRejected rejection -> localizeAccessError rejection
    GivenValueOutsideTypeAnnotation expected given ->
      LocalizedMessage
        "the given value is outside the type annotation"
        [ "expected: " <> expected
        , "given: " <> given
        ]
    IdentifierStringMismatch expected given ->
      LocalizedMessage
        "the identifier string does not match"
        [ "expected: " <> expected
        , "given: " <> given
        ]
    IntermediateTypeAnnotationOutsideTarget expected given ->
      LocalizedMessage
        "the intermediate type annotation does not fit in the target type annotation"
        [ "expected: " <> expected
        , "given: " <> given
        ]
    AtlasMapFederationOperationRefuted refutation ->
      case refutation of
        AtlasMapFederationConcatenationCollision value ->
          LocalizedMessage
            "concatenation does not produce an Atlas-map federation"
            [ "the value " <> show value
                <> " occurs on both sides and has two configurations"
            ]
        AtlasMapFederationAccessHasEmptyCounterexample ->
          LocalizedMessage
            "access fails for a member of the left Atlas-map federation"
            ["the empty map is a counterexample for the nonempty selection"]
        AtlasMapFederationSpecificationHasNoMatchingMember ->
          LocalizedMessage
            "specification has no matching Atlas map in the target federation"
            [ "the source total Atlas map is a counterexample: no target "
                <> "member admits the required identity-pagination morphism"
            ]
        AtlasMapFederationSubfederationHasMissingMember ->
          LocalizedMessage
            "the intermediate federation is not an Atlas subfederation of the target"
            [ "an Atlas map in the intermediate federation is absent from "
                <> "the final federation"
            ]
    AtlasMapFederationOperationUndecidable
        (NoAtlasMapFederationDecisionProcedure operation) ->
      LocalizedMessage
        "the compiler cannot decide this Atlas-map federation operation"
        ["operation: " <> federationOperation operation]
    NonInjectiveStringInterpolation ->
      LocalizedMessage
        "non-injective string interpolation"
        ["distinct values in the interpolation can have the same string form"]
    NoCanonicalStringConversion ->
      LocalizedMessage
        "value does not have a canonical string conversion"
        [ "weakToString can render the value, but specification requires "
            <> "an injective canonical conversion"
        ]
    ExpectedStringTemplateSpecification kind ->
      LocalizedMessage
        "extract expects a concrete string-template specification"
        ["given value kind: " <> valueKind kind]
    EitherAlternativesNotDistinct ->
      LocalizedMessage
        "Either alternatives are not distinguishable Atlas maps"
        ["the alternatives cannot be distinct members of one Atlas federation"]
    AmbiguousStringTemplate ->
      LocalizedMessage
        "ambiguous string template"
        ["the template does not map each source configuration to a unique string"]
    InvalidAsciiStringCharacter character ->
      LocalizedMessage
        "string contains a character outside the ASCII map"
        ["character: " <> show character]

overloadFailure :: OverloadFailure -> String
overloadFailure failure =
  case failure of
    OverloadNoMatch ->
      "the right operand does not match the left operand without its defaults"
    OverloadAmbiguousWithoutWrittenOrder ->
      "ambiguous overload; no order-preserving match exists"
    OverloadAmbiguousWrittenOrder ->
      "ambiguous overload; multiple order-preserving matches exist"
    OverloadMissingRequiredSlot ->
      "overload leaves a required slot without a value"
    OverloadChangedDefault ->
      "safe overload cannot change an existing default value"

federationOperation :: AtlasMapFederationOperation -> String
federationOperation AtlasMapFederationConcatenation = "concatenation"
federationOperation AtlasMapFederationAccess = "access"
federationOperation AtlasMapFederationSpecification = "specification"
federationOperation AtlasMapFederationSubfederation = "subfederation"

operandSide :: OperandSide -> String
operandSide LeftOperand = "left"
operandSide RightOperand = "right"

valueKind :: InterpretedValueKind -> String
valueKind FunctionValueKind = "function"
valueKind NaturalValueKind = "natural"
valueKind IntegerValueKind = "integer"
valueKind BooleanValueKind = "Boolean"
valueKind EitherValueKind = "Either federation"
valueKind ExplicitOrdinalValueKind = "explicit ordinal"
valueKind FormulationValueKind = "super-ellipsis formulation"
valueKind RangeValueKind = "range"
valueKind RangeConcatenationValueKind = "range concatenation"
valueKind AsciiStringValueKind = "ASCII string"
valueKind DependentIdentifierTypeValueKind = "identifier type"
valueKind MapValueKind = "map"
valueKind SpecificationValueKind = "specification morphism"

localizeSuperEllipsisRangeError
  :: SuperEllipsisRangeError
  -> LocalizedMessage
localizeSuperEllipsisRangeError reason =
  case reason of
    SuperEllipsisRangeStartOutsideRank start rankLimit ->
      LocalizedMessage
        ( "range start " <> englishOrdinal start
            <> " is not below the rank limit " <> englishOrdinal rankLimit
        )
        []
    SuperEllipsisRangeTargetOutsideRank target rankLimit ->
      LocalizedMessage
        ( "range target " <> englishOrdinal target
            <> " is above the rank limit " <> englishOrdinal rankLimit
        )
        []
    SuperEllipsisRangeInvalidDescendingBounds start target ->
      LocalizedMessage
        ( "descending range from " <> englishOrdinal start
            <> " to " <> englishOrdinal target
            <> " crosses an ordinal limit"
        )
        []

localizeSuperEllipsisRangeConcatError
  :: SuperEllipsisRangeConcatError
  -> LocalizedMessage
localizeSuperEllipsisRangeConcatError
    (SuperEllipsisRangesOverlap first second lower upper) =
  LocalizedMessage
    "cannot use overlapping ranges to access a map"
    [ "first range: " <> englishRangeDescription first
    , "second range: " <> englishRangeDescription second
    , "overlap: " <> renderRangeBounds lower upper
        <> " (upper bound excluded)"
    ]

englishRangeDescription :: SuperEllipsisRangeDescription -> String
englishRangeDescription = renderRangeDescription

englishOrdinal :: Ordinal -> String
englishOrdinal = renderOrdinal
