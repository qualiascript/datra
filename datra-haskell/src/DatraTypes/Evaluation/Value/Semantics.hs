-- | Source-independent semantic identity and canonical presentation.
--
-- Runtime representations may retain evaluators, maps, and source provenance;
-- this module deliberately contains none of those.  It is the stable meaning
-- used by equality, specification, and rendering.
module Evaluation.Value.Semantics
  ( IdentifierDependency (..)
  , identifierDependencyStringFor
  , identifierDependencyRepresentativeString
  , identifierDependenciesCompatible
  , PresentationDependency (..)
  , ValuePresentation (..)
  , ValueSemantics (..)
  , CanonicalResult (..)
  , canonicalResult
  , semanticCanonicalResult
  , canonicalPresentation
  , presentationForSemantics
  , semanticValueSemantics
  , mapValueSemanticsChildren
  , stripPresentedDependencies
  ) where

import DatraOrdinal (Ordinal)
import Evaluation.DatraType (BuiltinMetaType)
import IntegerRange qualified
import NaturalRange qualified
import Numeric.Natural (Natural)
import SuperEllipsisRange qualified as Range

-- | Runtime string rule for an identifier type. The stable key makes two
-- dependent rules comparable for subfederation decisions; simple identifiers
-- additionally retain their literal string for source rendering.
data IdentifierDependency
  = SimpleIdentifierDependency
      { simpleIdentifierString :: String
      }
  | DependentIdentifierDependency
      { dependentIdentifierFamilyKey :: String
      , dependentIdentifierStringFor :: CanonicalResult -> String
      }

identifierDependencyStringFor
  :: IdentifierDependency
  -> CanonicalResult
  -> String
identifierDependencyStringFor dependency value =
  case dependency of
    SimpleIdentifierDependency identifierString -> identifierString
    DependentIdentifierDependency _ identifierStringFor ->
      identifierStringFor value

-- | Choose the string that can represent an identifier before a particular
-- federation member is known. A total underlying value supplies that member;
-- otherwise dependent identifiers retain their stable family key.
identifierDependencyRepresentativeString
  :: IdentifierDependency
  -> Maybe CanonicalResult
  -> String
identifierDependencyRepresentativeString dependency selectedValue =
  case dependency of
    SimpleIdentifierDependency identifierString -> identifierString
    DependentIdentifierDependency familyKey identifierStringFor ->
      case selectedValue of
        Just value -> identifierStringFor value
        Nothing -> familyKey

-- | Constant dependencies agree by identifier string. Dependent dependencies
-- are comparable when they carry the same stable family key.
identifierDependenciesCompatible
  :: IdentifierDependency
  -> IdentifierDependency
  -> Bool
identifierDependenciesCompatible left right =
  case (left, right) of
    (SimpleIdentifierDependency leftString,
      SimpleIdentifierDependency rightString) ->
        leftString == rightString
    (DependentIdentifierDependency leftKey _,
      DependentIdentifierDependency rightKey _) ->
        leftKey == rightKey
    _ -> False

-- | Opaque identity of a lexical scope required by a retained presentation.
newtype PresentationDependency = PresentationDependency String
  deriving (Eq, Ord, Show)

-- | Semantic provenance retained after existential Atlas witnesses have been
-- erased. Evaluation modules inspect this structure; presentation is derived
-- separately as 'CanonicalResult'.
data ValueSemantics
  = PresentedSemantics
      [PresentationDependency] ValuePresentation ValueSemantics
  | NeverSemantics
  | BuiltinMetaTypeSemantics BuiltinMetaType
  | FunctionSemantics
      ValueSemantics ValueSemantics (Maybe String)
  | FunctionBodySemantics String
  | ExplicitSemantics Natural Ordinal
  | IntegerSemantics Integer
  | FormulationSemantics Natural
  | RangeSemantics Range.SuperEllipsisRangeDescription
  | NaturalRangeSemantics Natural NaturalRange.NaturalRangeTarget
  | ValuedNaturalRangeSemantics Natural NaturalRange.NaturalRangeTarget
  | NaturalTypeSemantics
  | IntegerRangeSemantics Integer IntegerRange.IntegerRangeTarget
  | ValuedIntegerRangeSemantics Integer IntegerRange.IntegerRangeTarget
  | IntegerTypeSemantics
  | EitherSemantics ValueSemantics ValueSemantics
  | SkipSemantics ValueSemantics
  | RangeConcatenationSemantics [Range.SuperEllipsisRangeDescription]
  | ConcatenationSemantics [ValueSemantics]
  | AsciiStringSemantics String
  | IdentifierValueTypeSemantics
  | ToStringSemantics ValueSemantics
  | TemplateSemantics ValueSemantics
  | DependentSumSemantics String
  | DependentIdentifierTypeSemantics
      IdentifierDependency
      ValueSemantics
      Bool
      Bool
  | IdentifierStringProjectionSemantics
      IdentifierDependency
      ValueSemantics
      Bool
  | AssignmentSemantics
      { assignmentIdentifierString :: String
      , assignmentTypeAnnotation :: ValueSemantics
      , assignmentGivenValue :: ValueSemantics
      }
  | CoalizationSemantics ValueSemantics
  | MapSemantics Natural [ValueSemantics]
  | ArgumentMapSemantics Bool [ValueSemantics]
  | SpecificationSemantics ValueSemantics ValueSemantics

-- | A canonical spelling whose dependencies remain local to its leaves.
-- Applications compose operand presentations directly, so lexical fallback
-- never requires enumerating their Cartesian product.
data ValuePresentation
  = AtomicPresentation CanonicalResult
  | SemanticPresentation ValueSemantics
  | ApplicationPresentation ValuePresentation ValuePresentation

-- | A normalized, source-independent presentation of an evaluated value.
data CanonicalResult
  = CanonicalReference String
  | CanonicalNever
  | CanonicalNamedAccess CanonicalResult String
  | CanonicalApplication CanonicalResult CanonicalResult
  | CanonicalBuiltinMetaType BuiltinMetaType
  | CanonicalFunction
      CanonicalResult CanonicalResult (Maybe String)
  | CanonicalExplicit Natural Ordinal
  | CanonicalInteger Integer
  | CanonicalFormulation Natural
  | CanonicalRange Range.SuperEllipsisRangeDescription
  | CanonicalNaturalRange Natural NaturalRange.NaturalRangeTarget
  | CanonicalValuedNaturalRange Natural NaturalRange.NaturalRangeTarget
  | CanonicalNaturalType
  | CanonicalIntegerRange Integer IntegerRange.IntegerRangeTarget
  | CanonicalValuedIntegerRange Integer IntegerRange.IntegerRangeTarget
  | CanonicalIntegerType
  | CanonicalEither CanonicalResult CanonicalResult
  | CanonicalSkip CanonicalResult
  | CanonicalRangeConcatenation [Range.SuperEllipsisRangeDescription]
  | CanonicalConcatenation [CanonicalResult]
  | CanonicalAsciiString String
  | CanonicalIdentifierValueType
  | CanonicalToString CanonicalResult
  | CanonicalTemplate CanonicalResult
  | CanonicalDependentSum String
  | CanonicalSimpleIdentifierType
      { canonicalIdentifierString :: String
      , canonicalSimpleIdentifierTypeAnnotation :: CanonicalResult
      }
  | CanonicalDependentIdentifierType String CanonicalResult
  | CanonicalIdentifierStringProjection String CanonicalResult
  | CanonicalAssignment
      { canonicalAssignmentIdentifierString :: String
      , canonicalAssignmentTypeAnnotation :: CanonicalResult
      , canonicalAssignmentGivenValue :: CanonicalResult
      }
  | CanonicalCoalization CanonicalResult
  | CanonicalMap Natural [CanonicalResult]
  | CanonicalArgumentMap Bool [CanonicalResult]
  | CanonicalSpecification CanonicalResult CanonicalResult
  deriving (Eq, Show)

canonicalResult :: ValueSemantics -> CanonicalResult
canonicalResult = canonicalResultWith True

-- | The presentation-free normal form used for semantic comparisons. Named
-- references never replace the value they denote; this view recursively
-- discards presentation wrappers and exposes that underlying value.
semanticCanonicalResult :: ValueSemantics -> CanonicalResult
semanticCanonicalResult = canonicalResultWith False

-- | Read only an explicitly retained presentation. Derived values without a
-- binding or named application deliberately return 'Nothing'.
canonicalPresentation
  :: ValueSemantics
  -> Maybe ([PresentationDependency], CanonicalResult)
canonicalPresentation (PresentedSemantics dependencies presentation _) =
  Just
    ( dependencies <> presentationDependencies presentation
    , presentationResult presentation
    )
canonicalPresentation _ = Nothing

-- | Remove presentation at an operation boundary while retaining the full
-- underlying semantic structure.
semanticValueSemantics :: ValueSemantics -> ValueSemantics
semanticValueSemantics (PresentedSemantics _ _ semantics) =
  semanticValueSemantics semantics
semanticValueSemantics semantics = semantics

-- | Apply one transformation to every immediate recursive semantic child.
-- Scope cleanup and future semantic rewrites share this constructor knowledge
-- instead of each maintaining their own traversal.
mapValueSemanticsChildren
  :: (ValueSemantics -> ValueSemantics)
  -> ValueSemantics
  -> ValueSemantics
mapValueSemanticsChildren recur semantics =
  case semantics of
    PresentedSemantics dependencies presentation underlying ->
      PresentedSemantics dependencies presentation (recur underlying)
    FunctionSemantics input output body ->
      FunctionSemantics (recur input) (recur output) body
    EitherSemantics left right -> EitherSemantics (recur left) (recur right)
    SkipSemantics payload -> SkipSemantics (recur payload)
    ConcatenationSemantics members -> ConcatenationSemantics (map recur members)
    ToStringSemantics source -> ToStringSemantics (recur source)
    TemplateSemantics source -> TemplateSemantics (recur source)
    DependentIdentifierTypeSemantics
        dependency underlying isTotal isCanonical ->
      DependentIdentifierTypeSemantics
        dependency (recur underlying) isTotal isCanonical
    IdentifierStringProjectionSemantics dependency underlying isTotal ->
      IdentifierStringProjectionSemantics dependency (recur underlying) isTotal
    AssignmentSemantics identifierString typeAnnotation givenValue ->
      AssignmentSemantics
        identifierString (recur typeAnnotation) (recur givenValue)
    CoalizationSemantics operand -> CoalizationSemantics (recur operand)
    MapSemantics cardinality members -> MapSemantics cardinality (map recur members)
    ArgumentMapSemantics total members ->
      ArgumentMapSemantics total (map recur members)
    SpecificationSemantics source target ->
      SpecificationSemantics (recur source) (recur target)
    _ -> semantics

-- | Remove presentations owned by lexical scopes that have just expired.
-- The denoted semantic value and presentations owned by enclosing scopes are
-- retained unchanged.
stripPresentedDependencies
  :: [PresentationDependency]
  -> ValueSemantics
  -> ValueSemantics
stripPresentedDependencies expired semantics =
  case semantics of
    PresentedSemantics
        dependencies presentation@(ApplicationPresentation _ _) underlying
      | any (`elem` expired) dependencies -> recur underlying
      | otherwise ->
          let stripped = stripPresentationDependencies expired presentation
          in if presentationRetainsName stripped
            then PresentedSemantics dependencies stripped (recur underlying)
            else recur underlying
    PresentedSemantics dependencies presentation underlying
      | any (`elem` expired)
          (dependencies <> presentationDependencies presentation) ->
            recur underlying
    PresentedSemantics dependencies presentation underlying ->
      PresentedSemantics
        dependencies
        (stripPresentationDependencies expired presentation)
        (recur underlying)
    _ -> mapValueSemanticsChildren recur semantics
  where
    recur = stripPresentedDependencies expired

presentationRetainsName :: ValuePresentation -> Bool
presentationRetainsName presentation =
  case presentation of
    AtomicPresentation _ -> True
    SemanticPresentation semantics ->
      case canonicalPresentation semantics of
        Just _ -> True
        Nothing -> False
    ApplicationPresentation function argument ->
      presentationRetainsName function || presentationRetainsName argument

canonicalResultWith :: Bool -> ValueSemantics -> CanonicalResult
canonicalResultWith retainPresentation semantics =
  case semantics of
    PresentedSemantics _ presentation underlying
      | retainPresentation -> presentationResult presentation
      | otherwise -> canonicalResultWith False underlying
    NeverSemantics -> CanonicalNever
    BuiltinMetaTypeSemantics kind -> CanonicalBuiltinMetaType kind
    FunctionSemantics input output body ->
      CanonicalFunction
        (recur input) (recur output) body
    FunctionBodySemantics source -> CanonicalReference source
    ExplicitSemantics level value -> CanonicalExplicit level value
    IntegerSemantics value -> CanonicalInteger value
    FormulationSemantics level -> CanonicalFormulation level
    RangeSemantics description -> CanonicalRange description
    NaturalRangeSemantics start target -> CanonicalNaturalRange start target
    ValuedNaturalRangeSemantics start target ->
      CanonicalValuedNaturalRange start target
    NaturalTypeSemantics -> CanonicalNaturalType
    IntegerRangeSemantics start target -> CanonicalIntegerRange start target
    ValuedIntegerRangeSemantics start target ->
      CanonicalValuedIntegerRange start target
    IntegerTypeSemantics -> CanonicalIntegerType
    EitherSemantics left right ->
      CanonicalEither (recur left) (recur right)
    SkipSemantics payload -> CanonicalSkip (recur payload)
    RangeConcatenationSemantics descriptions ->
      CanonicalRangeConcatenation descriptions
    ConcatenationSemantics members ->
      CanonicalConcatenation (map recur members)
    AsciiStringSemantics characters -> CanonicalAsciiString characters
    IdentifierValueTypeSemantics -> CanonicalIdentifierValueType
    ToStringSemantics source -> CanonicalToString (recur source)
    TemplateSemantics source ->
      CanonicalTemplate (recur source)
    DependentSumSemantics source -> CanonicalDependentSum source
    DependentIdentifierTypeSemantics dependency underlying isTotal _ ->
      let underlyingResult = recur underlying
      in case dependency of
        SimpleIdentifierDependency identifierString
          | isTotal ->
              CanonicalAssignment
                identifierString underlyingResult underlyingResult
          | otherwise ->
              CanonicalSimpleIdentifierType identifierString underlyingResult
        DependentIdentifierDependency familyKey _ ->
          CanonicalDependentIdentifierType familyKey underlyingResult
    IdentifierStringProjectionSemantics dependency underlying isTotal ->
      let underlyingResult = recur underlying
      in if isTotal
        then CanonicalAsciiString
          (identifierDependencyRepresentativeString
            dependency (Just underlyingResult))
        else CanonicalIdentifierStringProjection
          (identifierDependencyRepresentativeString dependency Nothing)
          underlyingResult
    AssignmentSemantics identifierString typeAnnotation givenValue ->
      CanonicalAssignment
        identifierString
        (recur typeAnnotation)
        (recur givenValue)
    CoalizationSemantics operand ->
      CanonicalCoalization (recur operand)
    MapSemantics cardinality components ->
      CanonicalMap cardinality (map recur components)
    ArgumentMapSemantics totalPages members ->
      CanonicalArgumentMap totalPages (map recur members)
    SpecificationSemantics source target ->
      canonicalSpecificationResult
        (recur source)
        (recur target)
  where
    recur = canonicalResultWith retainPresentation

presentationForSemantics :: ValueSemantics -> ValuePresentation
presentationForSemantics = SemanticPresentation

presentationResult :: ValuePresentation -> CanonicalResult
presentationResult presentation =
  case presentation of
    AtomicPresentation result -> result
    SemanticPresentation semantics -> canonicalResult semantics
    ApplicationPresentation function argument ->
      CanonicalApplication
        (presentationResult function)
        (presentationResult argument)

presentationDependencies :: ValuePresentation -> [PresentationDependency]
presentationDependencies presentation =
  case presentation of
    AtomicPresentation _ -> []
    SemanticPresentation semantics ->
      maybe [] fst (canonicalPresentation semantics)
    ApplicationPresentation function argument ->
      presentationDependencies function <> presentationDependencies argument

stripPresentationDependencies
  :: [PresentationDependency]
  -> ValuePresentation
  -> ValuePresentation
stripPresentationDependencies expired presentation =
  case presentation of
    AtomicPresentation _ -> presentation
    SemanticPresentation semantics ->
      SemanticPresentation (stripPresentedDependencies expired semantics)
    ApplicationPresentation function argument ->
      ApplicationPresentation
        (stripPresentationDependencies expired function)
        (stripPresentationDependencies expired argument)

-- Specifications into optional identifier slots have an assignment
-- presentation that carries the selected source values directly. This is the
-- canonical value, not merely a renderer shorthand.
canonicalSpecificationResult
  :: CanonicalResult
  -> CanonicalResult
  -> CanonicalResult
canonicalSpecificationResult source target =
  case optionalAssignment source target of
    Just assignment -> assignment
    Nothing ->
      case (canonicalComponents source, canonicalComponents target) of
        (Just sourceMembers, Just targetMembers)
          | length sourceMembers == length targetMembers ->
              case sequence
                  (zipWith optionalAssignment sourceMembers targetMembers) of
                Just assignments -> CanonicalConcatenation assignments
                Nothing -> CanonicalSpecification source target
        _ -> CanonicalSpecification source target

canonicalComponents :: CanonicalResult -> Maybe [CanonicalResult]
canonicalComponents (CanonicalConcatenation members) = Just members
canonicalComponents (CanonicalMap _ members) = Just members
canonicalComponents _ = Nothing

optionalAssignment
  :: CanonicalResult
  -> CanonicalResult
  -> Maybe CanonicalResult
optionalAssignment source (CanonicalEither present missing) =
  case present of
    CanonicalSimpleIdentifierType identifierString typeAnnotation
      | typeAnnotation == missing ->
          Just (CanonicalEither
            (CanonicalAssignment
              identifierString
              typeAnnotation
              (optionalAssignmentValue
                identifierString typeAnnotation source))
            missing)
    CanonicalAssignment identifierString typeAnnotation _
      | typeAnnotation == missing ->
          Just (CanonicalEither
            (CanonicalAssignment
              identifierString
              typeAnnotation
              (optionalAssignmentValue
                identifierString typeAnnotation source))
            missing)
    _ -> Nothing
optionalAssignment _ _ = Nothing

optionalAssignmentValue
  :: String
  -> CanonicalResult
  -> CanonicalResult
  -> CanonicalResult
optionalAssignmentValue identifierString _typeAnnotation source =
  case source of
    CanonicalAssignment sourceString _ givenValue
      | sourceString == identifierString -> givenValue
    CanonicalEither
        (CanonicalAssignment sourceString sourceType givenValue)
        sourceMissing
      | sourceString == identifierString
      , sourceType == sourceMissing -> givenValue
    _ -> source
