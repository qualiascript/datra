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
  , ValueSemantics (..)
  , CanonicalResult (..)
  , canonicalResult
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

-- | Semantic provenance retained after existential Atlas witnesses have been
-- erased. Evaluation modules inspect this structure; presentation is derived
-- separately as 'CanonicalResult'.
data ValueSemantics
  = BuiltinMetaTypeSemantics BuiltinMetaType
  | FunctionSemantics
      ValueSemantics ValueSemantics (Maybe (String, Bool)) (Maybe String)
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
  | StringTypeSemantics
  | IdentifierValueTypeSemantics
  | ToStringSemantics ValueSemantics
  | WeakToStringSemantics ValueSemantics
  | StringTemplateSemantics ValueSemantics
  | DependentIdentifierTypeSemantics
      IdentifierDependency
      ValueSemantics
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
  | MapSemantics Natural [ValueSemantics]
  | ArgumentMapSemantics Bool [ValueSemantics]
  | SpecificationSemantics ValueSemantics ValueSemantics

-- | A normalized, source-independent presentation of an evaluated value.
data CanonicalResult
  = CanonicalBuiltinMetaType BuiltinMetaType
  | CanonicalFunction
      CanonicalResult CanonicalResult (Maybe (String, Bool)) (Maybe String)
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
  | CanonicalStringType
  | CanonicalIdentifierValueType
  | CanonicalToString CanonicalResult
  | CanonicalWeakToString CanonicalResult
  | CanonicalStringTemplate CanonicalResult
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
  | CanonicalMap Natural [CanonicalResult]
  | CanonicalArgumentMap Bool [CanonicalResult]
  | CanonicalSpecification CanonicalResult CanonicalResult
  deriving (Eq, Show)

canonicalResult :: ValueSemantics -> CanonicalResult
canonicalResult semantics =
  case semantics of
    BuiltinMetaTypeSemantics kind -> CanonicalBuiltinMetaType kind
    FunctionSemantics input output patternInfo body ->
      CanonicalFunction
        (canonicalResult input) (canonicalResult output) patternInfo body
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
      CanonicalEither (canonicalResult left) (canonicalResult right)
    SkipSemantics payload -> CanonicalSkip (canonicalResult payload)
    RangeConcatenationSemantics descriptions ->
      CanonicalRangeConcatenation descriptions
    ConcatenationSemantics members ->
      CanonicalConcatenation (map canonicalResult members)
    AsciiStringSemantics characters -> CanonicalAsciiString characters
    StringTypeSemantics -> CanonicalStringType
    IdentifierValueTypeSemantics -> CanonicalIdentifierValueType
    ToStringSemantics source -> CanonicalToString (canonicalResult source)
    WeakToStringSemantics source ->
      CanonicalWeakToString (canonicalResult source)
    StringTemplateSemantics source ->
      CanonicalStringTemplate (canonicalResult source)
    DependentIdentifierTypeSemantics dependency underlying isTotal ->
      let underlyingResult = canonicalResult underlying
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
      let underlyingResult = canonicalResult underlying
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
        (canonicalResult typeAnnotation)
        (canonicalResult givenValue)
    MapSemantics cardinality components ->
      CanonicalMap cardinality (map canonicalResult components)
    ArgumentMapSemantics totalPages members ->
      CanonicalArgumentMap totalPages (map canonicalResult members)
    SpecificationSemantics source target ->
      canonicalSpecificationResult
        (canonicalResult source)
        (canonicalResult target)

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
