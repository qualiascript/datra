-- | English presentation text for typed Datra diagnostics.
--
-- This display-stage module translates strongly typed domain errors into
-- prose. Domain modules do not depend on it.
module DatraLanguage.Diagnostics.Locales.English
  ( localizeAccessError
  , localizeParseFailure
  , localizeModuleLoadFailure
  , localizeSyntaxExpansionFailure
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
  , SyntaxExpansionFailure (..)
  )
import Evaluation.Error
  ( InterpretedValueKind (..)
  , InterpretingError (..)
  , ExternalFailure (..)
  , FunctionFailure (..)
  , ModuleEvaluationFailure (..)
  , NamedAccessFailure (..)
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

localizeSyntaxExpansionFailure
  :: SyntaxExpansionFailure
  -> LocalizedMessage
localizeSyntaxExpansionFailure failure =
  case failure of
    UnknownSyntaxControlAdapter name ->
      LocalizedMessage "syntax control adapter is not registered"
        ["adapter: " <> name]
    InvalidSyntaxControlCaptures name expected given ->
      LocalizedMessage "syntax control adapter received invalid captures"
        [ "adapter: " <> name
        , "expected captures: " <> show expected
        , "given captures: " <> show given
        ]

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
    UnsupportedEvaluationMode value ->
      LocalizedMessage "evaluation mode is not supported"
        [ "given mode: " <> value
        , "expected dev, development, prod, or production"
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
    FunctionEvaluationFailed failure -> localizeFunctionFailure failure
    ExternalEvaluationFailed failure -> localizeExternalFailure failure
    ModuleEvaluationFailed failure -> localizeModuleFailure failure
    ExpectedBuiltinType name ->
      LocalizedMessage "value does not belong to the required built-in type"
        ["expected type: " <> name]
    NonCanonicalIdentifierTypeAnnotation ->
      LocalizedMessage "identifier type annotation is not canonical"
        ["identifier type annotations must implement canonical toString"]
    OverloadError failure ->
      LocalizedMessage "overloading failed" [overloadFailure failure]
    AssertionFailed -> LocalizedMessage "assertion failed" []
    IdentifierStringOverlap name ->
      LocalizedMessage "identifier strings overlap in begin scope" ["identifier: " <> name]
    UnknownIdentifier name ->
      LocalizedMessage "identifier is not imported in this scope" ["identifier: " <> name]
    PrivateParameterCannotBeOptional name ->
      LocalizedMessage
        "private function parameter cannot be optional"
        ["identifier: " <> name]
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

localizeFunctionFailure :: FunctionFailure -> LocalizedMessage
localizeFunctionFailure failure =
  case failure of
    UnconstrainedInferredParameter name ->
      LocalizedMessage "cannot infer an unconstrained function parameter"
        ["parameter: " <> name, "provide an explicit input type"]
    IncompatibleInferredParameterConstraints name ->
      LocalizedMessage "function parameter has incompatible inferred constraints"
        ["parameter: " <> name]
    InferredApplicationRequiresFunction ->
      LocalizedMessage "function inference found an application of a non-function" []
    UnsupportedInferredExpression ->
      LocalizedMessage "function result type cannot be inferred for this expression"
        ["add a supported explicit specification"]
    InferredTypeOutsideRequirement actual expected ->
      LocalizedMessage "inferred type is outside the required type"
        ["inferred: " <> actual, "required: " <> expected]
    AstPatternRequiresFunctionSignature ->
      LocalizedMessage "an AST pattern requires a function signature" []
    AstPatternRequiresFunctionImplementation ->
      LocalizedMessage "an AST pattern requires a function implementation" []
    FunctionBodyOutsideDeclaredResult ->
      LocalizedMessage "function body does not satisfy its declared output type" []
    ExternalAdapterRequiresAstCaptures ->
      LocalizedMessage "external syntax adapter requires unevaluated AST captures" []
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
    FunctionArgumentsRequireFinitePages ->
      LocalizedMessage "function arguments require finitely many pages" []
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

localizeExternalFailure :: ExternalFailure -> LocalizedMessage
localizeExternalFailure failure =
  case failure of
    DuplicateExternalDescriptorField ->
      LocalizedMessage "external descriptor contains a duplicate field" []
    UnknownExternalDescriptorFields names ->
      LocalizedMessage "external descriptor contains unknown fields"
        ["fields: " <> show names]
    UnsupportedExternalBackend backend ->
      LocalizedMessage "external backend is not supported"
        ["backend: " <> backend]
    MissingExternalDescriptorField name ->
      LocalizedMessage "external descriptor is missing a required field"
        ["field: " <> name]
    ExternalDescriptorRequiresStringMap ->
      LocalizedMessage "external descriptor must be a map of string fields" []
    UnknownExternalSymbol symbol ->
      LocalizedMessage "external symbol is not registered"
        ["symbol: " <> symbol]
    MissingNativeArgument name ->
      LocalizedMessage "native function did not receive a required argument"
        ["argument: " <> name]

localizeModuleFailure :: ModuleEvaluationFailure -> LocalizedMessage
localizeModuleFailure failure =
  case failure of
    StandardLibraryParseFailure path message ->
      LocalizedMessage "standard library failed to parse"
        ["path: " <> path, message]
    StandardLibraryRequiresDeclarationBlock path ->
      LocalizedMessage "standard library must contain a declaration block"
        ["path: " <> path]
    ImportOutsideScope ->
      LocalizedMessage "import must be a scope entry" []
    ImportedModuleRequiresSimpleIdentifierType ->
      LocalizedMessage "imported file must yield a simple identifier type"
        ["use yield Name := value"]
    ImportedModuleRequiresTotalValue ->
      LocalizedMessage "imported identifier must have a total value" []
    ImportAllRequiresTotalMapOfSimpleIdentifierTypes ->
      LocalizedMessage
        "import all requires a total map of simple identifier types" []
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
