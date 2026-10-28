-- | English presentation text for typed Datra diagnostics.
--
-- This display-stage module translates strongly typed domain errors into
-- prose. Domain modules do not depend on it.
module DatraLanguage.Diagnostics.Locales.English
  ( localizeAccessError
  , localizeParseFailure
  , localizeModuleLoadFailure
  , localizeCommandLineOptionFailure
  , localizeInterpretingError
  , localizeSuperEllipsisRangeError
  , localizeSuperEllipsisRangeConcatError
  , englishOrdinal
  ) where

import DatraLanguage.Diagnostics (LocalizedMessage (LocalizedMessage))
import DatraLanguage.Diagnostics.Application
  ( CommandLineOptionFailure (..)
  , ModuleLoadFailure (..)
  , ParseFailure (..)
  , SyntaxTemplateAdmissibilityFailure (..)
  )
import Evaluation.Error
  ( InterpretedValueKind (..)
  , InterpretingError (..)
  , FunctionFailure (..)
  , ModuleEvaluationFailure (..)
  , NamedAccessFailure (..)
  , MapLengthFailure (..)
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

localizeParseFailure :: ParseFailure -> LocalizedMessage
localizeParseFailure (ParseFailure message) =
  LocalizedMessage "source could not be parsed" [message]

localizeModuleLoadFailure :: ModuleLoadFailure -> LocalizedMessage
localizeModuleLoadFailure failure =
  case failure of
    ImportScanFailed path parseFailure ->
      LocalizedMessage "module imports could not be scanned"
        ["module: " <> path, parseFailureMessage parseFailure]
    ImportPathResolutionFailed requested location reason ->
      LocalizedMessage "module path could not be resolved"
        [ "module: " <> requested
        , "location: " <> location
        , "reason: " <> reason
        ]
    CyclicModuleImport path ->
      LocalizedMessage "cyclic module import" ["module: " <> path]
    ModuleReadFailed requested path reason ->
      LocalizedMessage "module could not be read"
        [ "module: " <> requested
        , "path: " <> path
        , "reason: " <> reason
        ]
    ImportedModuleParseFailed path parseFailure ->
      LocalizedMessage "imported module could not be parsed"
        ["module: " <> path, parseFailureMessage parseFailure]

localizeCommandLineOptionFailure
  :: CommandLineOptionFailure
  -> LocalizedMessage
localizeCommandLineOptionFailure failure =
  case failure of
    UnsupportedDiagnosticLocale value ->
      LocalizedMessage "diagnostic locale is not supported"
        [ "given locale: " <> value
        , "expected english, en, romana, romanian, or ro"
        ]

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
    NamedAccessFailed failure -> localizeNamedAccessFailure failure
    MapLengthFailed failure -> localizeMapLengthFailure failure
    FunctionEvaluationFailed failure -> localizeFunctionFailure failure
    ModuleEvaluationFailed failure -> localizeModuleFailure failure
    ExpectedBuiltinType name ->
      LocalizedMessage "value does not belong to the required built-in type"
        ["expected type: " <> name]
    OverloadError failure ->
      LocalizedMessage "overloading failed" [overloadFailure failure]
    OperationHasNoEffect ->
      LocalizedMessage "operation has no effect" []
    OverlappingBindings name ->
      LocalizedMessage "bindings overlap in the same scope" ["binding: " <> name]
    InconsistentShadowing name ->
      LocalizedMessage
        "identifier shadowing is inconsistent with its existing binding"
        ["identifier: " <> name]
    LetBindingCannotShadowConsistentIdentifier name ->
      LocalizedMessage
        "let binding cannot shadow a shadowing-consistent identifier"
        ["identifier: " <> name]
    UnknownIdentifier name ->
      LocalizedMessage "identifier is not imported in this scope" ["identifier: " <> name]
    PrivateParameterCannotBeOptional name ->
      LocalizedMessage
        "private function parameter cannot be optional"
        ["identifier: " <> name]
    InvalidDependentDeclarationModifiers written correct ->
      LocalizedMessage
        "declaration modifiers must occur at most once in let def val order"
        [ "written modifiers: " <> written
        , "correct modifiers: " <> correct
        ]
    GenericIntroductionOutsideFunctionType binder ->
      LocalizedMessage
        "generic introduction requires an enclosing function type"
        ["generic operator: " <> binder]
    DuplicateGenericIdentifier name ->
      LocalizedMessage
        "generic identifier is introduced more than once in one function domain"
        ["identifier: " <> name]
    ForwardGenericBoundReference owner referenced ->
      LocalizedMessage
        "generic bound refers to a binder that is not yet available"
        [ "generic identifier: " <> owner
        , "unavailable identifier: " <> referenced
        ]
    GenericIdentifierOverlap name ->
      LocalizedMessage
        "generic identifier overlaps another identifier in its function type"
        ["identifier: " <> name]
    GenericIdentifierDisjointnessUndecidable name ->
      LocalizedMessage
        "generic identifier cannot be proven disjoint from a dependent argument"
        ["identifier: " <> name]
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
    IndeterminateInfinityOperation operator ->
      LocalizedMessage
        "operation is indeterminate for these infinity operands"
        ["operator: " <> operator]
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
    RedundantConcatenation ->
      LocalizedMessage
        "concatenation does not change the meaning of this expression"
        ["use ; between operands or remove the trailing comma"]
    RedundantAssignment ->
      LocalizedMessage
        "inferred assignment is redundant for a total value"
        ["use : instead of :="]
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
        ["only injective, round-trippable string conversions are accepted"]
    InvalidSyntaxTemplate template failure ->
      LocalizedMessage
        (syntaxTemplateFailureSummary template failure)
        [ "pattern: " <> show template
        , syntaxTemplateFailureDetail failure
        ]
    EitherAlternativesNotDistinct ->
      LocalizedMessage
        "Either alternatives are not distinguishable Atlas maps"
        ["the alternatives cannot be distinct members of one Atlas federation"]
    AmbiguousStringTemplate ->
      LocalizedMessage
        "ambiguous string template"
        ["the template does not map each source configuration to a unique string"]
    LookupRequiresString kind ->
      LocalizedMessage
        "lookup operator expects a string expression"
        ["operand kind: " <> show kind]
    LookupCaptureHasNoGenericMapView index capture ->
      LocalizedMessage
        "lookup capture has no generic map view"
        [ "capture index: " <> show index
        , "capture: " <> capture
        ]
    InvalidAsciiStringCharacter character ->
      LocalizedMessage
        "string contains a character outside the ASCII map"
        ["character: " <> show character]

syntaxTemplateFailureSummary
  :: String
  -> SyntaxTemplateAdmissibilityFailure
  -> String
syntaxTemplateFailureSummary _ NeutralSyntaxTemplateParseFailure =
  "syntax pattern cannot be read by the neutral source parser"
syntaxTemplateFailureSummary _ (IncompleteCoreSyntaxOperator operator) =
  "syntax pattern ends with the incomplete core operator " <> operator
syntaxTemplateFailureSummary _ SyntaxTemplateProjectionLoss =
  "syntax pattern loses a literal or hole during matching"
syntaxTemplateFailureSummary _ UnstableSyntaxTemplateProjection =
  "syntax pattern changes when rendered and parsed again"

syntaxTemplateFailureDetail :: SyntaxTemplateAdmissibilityFailure -> String
syntaxTemplateFailureDetail NeutralSyntaxTemplateParseFailure =
  "the complete pattern must be parseable before declared syntax is installed"
syntaxTemplateFailureDetail (IncompleteCoreSyntaxOperator _) =
  "the complete pattern must supply the operator's required operand"
syntaxTemplateFailureDetail SyntaxTemplateProjectionLoss =
  "the matcher cannot recover every pattern boundary from the neutral AST"
syntaxTemplateFailureDetail UnstableSyntaxTemplateProjection =
  "the recovered neutral form must survive a canonical round trip"

localizeFunctionFailure :: FunctionFailure -> LocalizedMessage
localizeFunctionFailure failure =
  case failure of
    HostSyntaxHookRequiresAstCaptures ->
      LocalizedMessage "host syntax hook requires unevaluated AST captures" []
    MissingNativeArgument name ->
      LocalizedMessage "native function did not receive a required argument"
        ["argument: " <> name]
    AmbiguousFunctionSumApplication ->
      LocalizedMessage "function sum application is ambiguous" []
    AmbiguousFunctionArgumentBindings ->
      LocalizedMessage "function argument bindings are ambiguous"
        ["supply identifiers to select the intended slots"]
    NoApplicableFunctionAlternative ->
      LocalizedMessage "no function alternative accepts the arguments"
        ["syntax-only alternatives require their AST pattern"]
    FunctionSignatureVarianceViolation ->
      LocalizedMessage "function signature violates variance"
        ["input must be contravariant and output must be covariant"]
    FunctionSpecificationUndecidable source target ->
      LocalizedMessage "function specification cannot be decided"
        ["source: " <> source, "target: " <> target]
    ExpectedFunctionValue ->
      LocalizedMessage "expected a function value" []
    EmptyFunctionSum ->
      LocalizedMessage "function sum has no alternatives" []
    NoMatchingFunctionSpecificationAlternative ->
      LocalizedMessage "function specification has no matching alternative" []
    AmbiguousFunctionSpecification ->
      LocalizedMessage "function specification is ambiguous" []
    FunctionArgumentPageUnavailable position ->
      LocalizedMessage "function argument page is unavailable"
        ["position: " <> show position]
    ExpectedFunctionType ->
      LocalizedMessage "expected a function type" []

localizeNamedAccessFailure :: NamedAccessFailure -> LocalizedMessage
localizeNamedAccessFailure failure =
  case failure of
    NamedFieldNotFound name ->
      LocalizedMessage "named field does not exist" ["field: " <> name]
    NamedFieldAmbiguous name ->
      LocalizedMessage "named field is ambiguous" ["field: " <> name]
    NamedFieldMapNotInspectable ->
      LocalizedMessage "field map cannot be inspected" []
    NamedAccessRequiresFiniteMap ->
      LocalizedMessage "named access requires a finite map" []

localizeMapLengthFailure :: MapLengthFailure -> LocalizedMessage
localizeMapLengthFailure failure =
  case failure of
    IndeterminateMapLength ->
      LocalizedMessage "object does not have a determinate final-page length" []
    MapLengthExceedsNaturalLimit orderType ->
      LocalizedMessage
        "object's final-page length is not representable by NatLimit"
        ["final-page order type: " <> renderOrdinal orderType]

localizeModuleFailure :: ModuleEvaluationFailure -> LocalizedMessage
localizeModuleFailure failure =
  case failure of
    StandardLibraryParseFailure path message ->
      LocalizedMessage "standard library failed to parse"
        ["path: " <> path, message]
    StandardLibraryRequiresDeclarationBlock path ->
      LocalizedMessage "standard library must contain a declaration block"
        ["path: " <> path]
    ImportedModuleRequiresBlock ->
      LocalizedMessage "imported file must reduce to a block" []
    ImportedModuleRequiresIdentifierBinderFederation ->
      LocalizedMessage "imported file must yield an identifier-binder federation"
        ["use yield Name : value or a federation of identifier binders"]
    ModuleScopeRequiresTotalMapOfSimpleIdentifierTypes ->
      LocalizedMessage
        "module scope requires a total map of simple identifier types" []
    ImportedModuleRequiresNamedExports ->
      LocalizedMessage "imported module must yield a scope or named map"
        ["use yield this to export its scope"]
    ModuleExportRequiresIdentifier ->
      LocalizedMessage "module export must have an identifier" []
    ModuleNotLoaded path ->
      LocalizedMessage "module was not loaded" ["module: " <> path]

overloadFailure :: OverloadFailure -> String
overloadFailure failure =
  case failure of
    OverloadNoMatch ->
      "the right operand does not match the left operand without its defaults"
    OverloadNamedPrivateSlot ->
      "a private parameter accepts only positional input"
    OverloadAmbiguousWithoutWrittenOrder ->
      "ambiguous overload; no order-preserving match exists"
    OverloadAmbiguousWrittenOrder ->
      "ambiguous overload; multiple order-preserving matches exist"
    OverloadMissingRequiredSlot ->
      "overload leaves a required slot without a value"
    OverloadSkippedRequiredSlot ->
      "a required argument without a default value cannot be skipped"
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
valueKind DependentArgumentTypeValueKind = "dependent argument type"
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
