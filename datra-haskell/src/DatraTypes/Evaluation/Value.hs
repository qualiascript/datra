{-# LANGUAGE GADTs #-}

-- | Internal runtime representation shared by DatraTypes evaluation modules.
-- Constructors stay internal; the public 'DatraTypes' module exposes only the
-- observations and checked operations needed by the AST interpreter.
module Evaluation.Value
  ( ExplicitOrigin (..)
  , EvaluatedExplicit (..)
  , EvaluatedRange (..)
  , EvaluatedNaturalRange (..)
  , EvaluatedValuedNaturalRange (..)
  , EvaluatedIntegerRange (..)
  , EvaluatedValuedIntegerRange (..)
  , EvaluatedEither (..)
  , IdentifierDependency (..)
  , identifierDependencyStringFor
  , identifierDependencyRepresentativeString
  , identifierDependenciesCompatible
  , EvaluatedIdentifierType (..)
  , InterpretedTotalAtlasMap (..)
  , EvaluatedAtlasMapFederationMember (..)
  , EvaluatedSpecification (..)
  , ValueForm (..)
  , SomeSuperEllipsisInsertion
  , InsertionCapability (..)
  , OrdinalOrderedValues (..)
  , InterpretedMap (..)
  , interpretedMapCardinality
  , ToStringInverseDecision (..)
  , ProvenInjectiveToString (..)
  , InterpretedAtlasMapFederationPrimitive (..)
  , InterpretedAtlasMapFederation
  , ValueSemantics (..)
  , CanonicalResult (..)
  , InterpretedValue
  , InterpretedValueTotality (..)
  , makeInterpretedValue
  , makeSingletonInterpretedValue
  , interpretedForm
  , interpretedInsertionCapability
  , interpretedMap
  , interpretedAtlasMapFederation
  , interpretedTotalAtlasMap
  , interpretedSemantics
  , interpretedValueHasTotalMap
  , implicitCoercionSemantics
  , interpretedCanonicalResult
  , interpretedValueKind
  , interpretedExplicitOrdinal
  , interpretedInteger
  , interpretedFormulationLevel
  , interpretedRangeDescription
  , interpretedMapFinalOrderType
  , interpretedMapValueAt
  , asciiStringFromInterpretedMap
  , explicitOrdinal
  , explicitInsertion
  , rangeDescription
  , evaluatedRangeLevel
  , rangeInsertion
  , naturalRangeAsEvaluatedRange
  , valueRanges
  , emptyInterpretedMap
  , singletonMap
  , emptyOrdinalOrderedValues
  , singletonOrdinalOrderedValues
  , appendOrdinalOrderedValues
  , appendSomeSuperEllipsisInsertion
  ) where

import Control.Monad (guard)
import BooleanType (DatraBoolean)
import AtlasMapFederationExpression
  ( AtlasMapFederationExpression (SingletonAtlasMapFederation) )
import Data.Char (chr)
import DatraOrdinal (Ordinal, finiteOrdinal, naturalAtOrdinal)
import Evaluation.Error (InterpretedValueKind (..))
import MapOperators.OrderedAtlasMap
  ( OrdinalOrderedValues (..)
  , appendOrdinalOrderedValues
  , emptyOrdinalOrderedValues
  , singletonOrdinalOrderedValues
  )
import Numeric.Natural (Natural)
import NaturalRange qualified
import ValuedNaturalRange qualified
import IntegerRange qualified
import ValuedIntegerRange qualified
import NumericalOperators.NumericalOperand
  ( SomeSuperEllipsis
  , someSuperEllipsisLevel
  )
import SuperEllipsisInsertion
  ( SomeSuperEllipsisInsertion
  , appendSomeSuperEllipsisInsertion
  , eraseSuperEllipsisInsertion
  )
import SuperEllipsisRange qualified as Range
import SuperEllipsisValue
  ( SuperEllipsisValue
  , superEllipsisValueInsertion
  , superEllipsisValueOrdinal
  )

data ExplicitOrigin = NaturalOrigin | ComputedOrigin

data EvaluatedExplicit where
  EvaluatedExplicit
    :: Natural
    -> ExplicitOrigin
    -> SuperEllipsisValue target scope
    -> EvaluatedExplicit

data EvaluatedRange where
  EvaluatedRange
    :: Natural
    -> Range.SuperEllipsisRange target scope
    -> EvaluatedRange

data EvaluatedNaturalRange where
  EvaluatedNaturalRange
    :: NaturalRange.NaturalRange rangeScope federationScope
    -> EvaluatedNaturalRange

data EvaluatedValuedNaturalRange where
  EvaluatedValuedNaturalRange
    :: ValuedNaturalRange.ValuedNaturalRange rangeScope federationScope
    -> EvaluatedValuedNaturalRange

data EvaluatedIntegerRange where
  EvaluatedIntegerRange
    :: IntegerRange.IntegerRange rangeScope federationScope
    -> EvaluatedIntegerRange

data EvaluatedValuedIntegerRange where
  EvaluatedValuedIntegerRange
    :: ValuedIntegerRange.ValuedIntegerRange rangeScope federationScope
    -> EvaluatedValuedIntegerRange

-- | A proven-disjoint federation union. The alternatives remain separate so
-- selection can record its route, but that internal route does not make equal
-- or overlapping Atlas maps distinct.
data EvaluatedEither = EvaluatedEither
  { evaluatedEitherLeft :: InterpretedValue
  , evaluatedEitherRight :: InterpretedValue
  }

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

data EvaluatedIdentifierType = EvaluatedIdentifierType
  { evaluatedIdentifierDependency :: IdentifierDependency
  , evaluatedIdentifierUnderlying :: InterpretedValue
  }

-- | Runtime erasure of the proof-bearing 'TotalAtlasMap'.  This certificate
-- is attached only by constructors known to give every final-page region a
-- singleton value; being a singleton federation is not sufficient by itself.
newtype InterpretedTotalAtlasMap = InterpretedTotalAtlasMap
  { interpretedTotalAtlasMapUnderlying :: InterpretedMap
  }

-- | The selected member stays tagged by federation family. Primitive range
-- members remain distinct even when they carry the same natural; a singleton
-- federation records the canonical identity of its sole total-map member.
data EvaluatedAtlasMapFederationMember
  = EvaluatedNaturalRangeMember NaturalRange.NaturalSubrangeDescription
  | EvaluatedValuedNaturalRangeMember Natural
  | EvaluatedIntegerRangeMember IntegerRange.IntegerSubrangeDescription
  | EvaluatedValuedIntegerRangeMember Integer
  | EvaluatedAsciiStringMember String
  | EvaluatedEitherMember
      DatraBoolean
      EvaluatedAtlasMapFederationMember
  | EvaluatedIdentifierTypeMember EvaluatedAtlasMapFederationMember
  | EvaluatedToStringMember EvaluatedAtlasMapFederationMember
  | EvaluatedSingletonAtlasMapMember CanonicalResult
  | EvaluatedSequentialAtlasMapMember [EvaluatedAtlasMapFederationMember]
  | EvaluatedExpansionAtlasMapMember
      EvaluatedAtlasMapFederationMember
      EvaluatedAtlasMapFederationMember
  | EvaluatedConcatenatedAtlasMapMember [EvaluatedAtlasMapFederationMember]

-- | Erased semantic witness for a successful specification.  The core
-- 'SpecificationOperator' module carries the non-erased categorical form used
-- when concrete Atlas witnesses remain available.
data EvaluatedSpecification = EvaluatedSpecification
  { evaluatedSpecificationSourceValue :: InterpretedValue
  , evaluatedSpecificationSource :: InterpretedTotalAtlasMap
  , evaluatedSpecificationTarget :: InterpretedValue
  , evaluatedSpecificationMember :: EvaluatedAtlasMapFederationMember
  }

data ValueForm
  = ExplicitForm EvaluatedExplicit
  | IntegerForm Integer
  | BooleanForm DatraBoolean
  | NothingForm
  | FormulationForm SomeSuperEllipsis
  | RangeForm EvaluatedRange
  | NaturalRangeForm EvaluatedNaturalRange
  | ValuedNaturalRangeForm EvaluatedValuedNaturalRange
  | IntegerRangeForm EvaluatedIntegerRange
  | ValuedIntegerRangeForm EvaluatedValuedIntegerRange
  | EitherForm EvaluatedEither
  | RangeConcatenationForm
      [EvaluatedRange]
      (Maybe (InterpretedValue, InterpretedValue))
  | AsciiStringForm String
  | StringTypeForm
  | IdentifierValueTypeForm
  | ToStringForm
  | WeakToStringForm
  | StringTemplateForm InterpretedValue
  | SpecificationForm EvaluatedSpecification
  | AssignmentForm EvaluatedSpecification
  | IdentifierTypeForm EvaluatedIdentifierType
  | IdentifierStringProjectionForm EvaluatedIdentifierType
  | SequentialMapForm
  | ExpansionMapForm InterpretedValue InterpretedValue
  | ConcatenatedMapForm InterpretedValue InterpretedValue
  | MapForm

data InsertionCapability
  = NoInsertion
  | ValidInsertion SomeSuperEllipsisInsertion
  | RejectedInsertion Range.SuperEllipsisRangeConcatError

data InterpretedMap = InterpretedMap
  { interpretedMapPageCardinality :: Natural
  , interpretedMapFinalValues :: OrdinalOrderedValues InterpretedValue
  , interpretedMapComponents :: [ValueSemantics]
  }

-- | Compatibility name for the number of Atlas pages represented by a map.
-- This is distinct from the final page's possibly-transfinite order type.
interpretedMapCardinality :: InterpretedMap -> Natural
interpretedMapCardinality = interpretedMapPageCardinality

-- | The partial inverse carried by a proven pointwise string conversion.
data ToStringInverseDecision
  = ToStringInverseMatched InterpretedValue
  | ToStringInverseRejected
  | ToStringInverseUndecidable

data ProvenInjectiveToString = ProvenInjectiveToString
  { injectiveToStringCharacterAlphabet :: Maybe String
  , injectiveToStringExactStrings :: Maybe [String]
  , invertInjectiveToString :: String -> ToStringInverseDecision
  }

-- | Primitive Atlas-map federation kinds understood by the interpreter.
-- The injective string primitive carries the language facts and inverse that
-- justified its construction; the explicitly weak primitive does not.
data InterpretedAtlasMapFederationPrimitive
  = NaturalRangeAtlasMapFederation EvaluatedNaturalRange
  | ValuedNaturalRangeAtlasMapFederation EvaluatedValuedNaturalRange
  | IntegerRangeAtlasMapFederation EvaluatedIntegerRange
  | ValuedIntegerRangeAtlasMapFederation EvaluatedValuedIntegerRange
  | EitherAtlasMapFederation EvaluatedEither
  | IdentifierTypeAtlasMapFederation EvaluatedIdentifierType
  | IdentifierStringProjectionAtlasMapFederation EvaluatedIdentifierType
  | StringTypeAtlasMapFederation
  | IdentifierValueTypeAtlasMapFederation
  | ToStringAtlasMapFederation
      InterpretedValue
      ProvenInjectiveToString
  | WeakToStringAtlasMapFederation InterpretedValue

type InterpretedAtlasMapFederation =
  AtlasMapFederationExpression
    InterpretedAtlasMapFederationPrimitive
    InterpretedMap

-- | Semantic provenance retained after existential Atlas witnesses have been
-- erased. Evaluation modules inspect this structure; presentation is derived
-- separately as 'CanonicalResult'.
data ValueSemantics
  = ExplicitSemantics Natural Ordinal
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
  | RangeConcatenationSemantics [Range.SuperEllipsisRangeDescription]
  | ConcatenationSemantics [ValueSemantics]
  | AsciiStringSemantics String
  | StringTypeSemantics
  | IdentifierValueTypeSemantics
  | ToStringSemantics ValueSemantics
  | WeakToStringSemantics ValueSemantics
  | StringTemplateSemantics ValueSemantics
  | IdentifierTypeSemantics
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
  | SpecificationSemantics ValueSemantics ValueSemantics

-- | A normalized, source-independent presentation of an evaluated value.
data CanonicalResult
  = CanonicalExplicit Natural Ordinal
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
  | CanonicalRangeConcatenation [Range.SuperEllipsisRangeDescription]
  | CanonicalConcatenation [CanonicalResult]
  | CanonicalAsciiString String
  | CanonicalStringType
  | CanonicalIdentifierValueType
  | CanonicalToString CanonicalResult
  | CanonicalWeakToString CanonicalResult
  | CanonicalStringTemplate CanonicalResult
  | CanonicalIdentifierType
      { canonicalIdentifierString :: String
      , canonicalIdentifierTypeAnnotation :: CanonicalResult
      }
  | CanonicalDependentIdentifierType String CanonicalResult
  | CanonicalIdentifierStringProjection String CanonicalResult
  | CanonicalAssignment
      { canonicalAssignmentIdentifierString :: String
      , canonicalAssignmentTypeAnnotation :: CanonicalResult
      , canonicalAssignmentGivenValue :: CanonicalResult
      }
  | CanonicalMap Natural [CanonicalResult]
  | CanonicalSpecification CanonicalResult CanonicalResult
  deriving (Eq, Show)

data InterpretedValue = InterpretedValue
  { interpretedForm :: ValueForm
  , interpretedInsertionCapability :: InsertionCapability
  , interpretedMap :: InterpretedMap
  , interpretedAtlasMapFederation :: InterpretedAtlasMapFederation
  , interpretedTotalAtlasMap :: Maybe InterpretedTotalAtlasMap
  , interpretedSemantics :: ValueSemantics
  }

data InterpretedValueTotality = TotalInterpretedMap | NonTotalInterpretedMap

makeInterpretedValue
  :: ValueForm
  -> InsertionCapability
  -> InterpretedMap
  -> InterpretedAtlasMapFederation
  -> InterpretedValueTotality
  -> ValueSemantics
  -> InterpretedValue
makeInterpretedValue form capability valueMap federation totality semantics =
  InterpretedValue
    { interpretedForm = form
    , interpretedInsertionCapability = capability
    , interpretedMap = valueMap
    , interpretedAtlasMapFederation = federation
    , interpretedTotalAtlasMap =
        case totality of
          TotalInterpretedMap -> Just (InterpretedTotalAtlasMap valueMap)
          NonTotalInterpretedMap -> Nothing
    , interpretedSemantics = semantics
    }

makeSingletonInterpretedValue
  :: ValueForm
  -> InsertionCapability
  -> InterpretedMap
  -> InterpretedValueTotality
  -> ValueSemantics
  -> InterpretedValue
makeSingletonInterpretedValue form capability valueMap totality =
  makeInterpretedValue
    form
    capability
    valueMap
    (SingletonAtlasMapFederation valueMap)
    totality

interpretedValueHasTotalMap :: InterpretedValue -> Bool
interpretedValueHasTotalMap = maybe False (const True) . interpretedTotalAtlasMap

-- | One implicit coercion step through a total identifier binding. Consumers
-- can follow the chain without knowing whether a binding came from user code,
-- an interpreter bootstrap, or a future standard-library definition.
implicitCoercionSemantics :: ValueSemantics -> Maybe ValueSemantics
implicitCoercionSemantics semantics =
  case semantics of
    IdentifierTypeSemantics _ underlying True -> Just underlying
    _ -> Nothing

interpretedCanonicalResult :: InterpretedValue -> CanonicalResult
interpretedCanonicalResult = canonicalResult . interpretedSemantics

canonicalResult :: ValueSemantics -> CanonicalResult
canonicalResult semantics =
  case semantics of
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
    IdentifierTypeSemantics dependency underlying isTotal ->
      let underlyingResult = canonicalResult underlying
      in case dependency of
        SimpleIdentifierDependency identifierString
          | isTotal ->
              CanonicalAssignment
                identifierString underlyingResult underlyingResult
          | otherwise ->
              CanonicalIdentifierType identifierString underlyingResult
        DependentIdentifierDependency familyKey _ ->
          CanonicalDependentIdentifierType familyKey underlyingResult
    IdentifierStringProjectionSemantics dependency underlying isTotal ->
      let underlyingResult = canonicalResult underlying
      in if isTotal
        then
          CanonicalAsciiString
            (identifierDependencyRepresentativeString
              dependency (Just underlyingResult))
        else
          CanonicalIdentifierStringProjection
            (identifierDependencyRepresentativeString
              dependency Nothing)
            underlyingResult
    AssignmentSemantics identifierString typeAnnotation givenValue ->
      CanonicalAssignment
        identifierString
        (canonicalResult typeAnnotation)
        (canonicalResult givenValue)
    MapSemantics cardinality components ->
      CanonicalMap cardinality (map canonicalResult components)
    SpecificationSemantics source target ->
      canonicalSpecificationResult
        (canonicalResult source)
        (canonicalResult target)

-- Specifications into optional identifier slots have an assignment
-- presentation that carries the selected source values directly. This is the
-- canonical value, not merely a renderer shorthand: a pointwise specification
-- and its @:=@ federation therefore normalize identically.
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
    CanonicalIdentifierType identifierString typeAnnotation
      | typeAnnotation == missing ->
          Just
            (CanonicalEither
              (CanonicalAssignment
                identifierString
                typeAnnotation
                (optionalAssignmentValue
                  identifierString typeAnnotation source))
              missing)
    CanonicalAssignment identifierString typeAnnotation _
      | typeAnnotation == missing ->
          Just
            (CanonicalEither
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
optionalAssignmentValue identifierString typeAnnotation source =
  case source of
    CanonicalAssignment sourceString _ givenValue
      | sourceString == identifierString -> givenValue
    CanonicalEither
        (CanonicalAssignment sourceString sourceType givenValue)
        sourceMissing
      | sourceString == identifierString
      , sourceType == typeAnnotation
      , sourceMissing == typeAnnotation -> givenValue
    _ -> source

interpretedValueKind :: InterpretedValue -> InterpretedValueKind
interpretedValueKind value =
  case interpretedForm value of
    ExplicitForm (EvaluatedExplicit _ NaturalOrigin _) -> NaturalValueKind
    ExplicitForm _ -> ExplicitOrdinalValueKind
    IntegerForm _ -> IntegerValueKind
    BooleanForm _ -> BooleanValueKind
    NothingForm -> MapValueKind
    FormulationForm _ -> FormulationValueKind
    RangeForm _ -> RangeValueKind
    NaturalRangeForm _ -> RangeValueKind
    ValuedNaturalRangeForm _ -> RangeValueKind
    IntegerRangeForm _ -> RangeValueKind
    ValuedIntegerRangeForm _ -> RangeValueKind
    EitherForm _ -> EitherValueKind
    RangeConcatenationForm _ _ -> RangeConcatenationValueKind
    AsciiStringForm _ -> AsciiStringValueKind
    StringTypeForm -> AsciiStringValueKind
    IdentifierValueTypeForm -> AsciiStringValueKind
    ToStringForm -> AsciiStringValueKind
    WeakToStringForm -> AsciiStringValueKind
    StringTemplateForm _ -> AsciiStringValueKind
    SpecificationForm _ -> SpecificationValueKind
    AssignmentForm _ -> SpecificationValueKind
    IdentifierTypeForm _ -> IdentifierTypeValueKind
    IdentifierStringProjectionForm _ -> IdentifierTypeValueKind
    SequentialMapForm -> MapValueKind
    ExpansionMapForm _ _ -> MapValueKind
    ConcatenatedMapForm _ _ -> MapValueKind
    MapForm -> MapValueKind

interpretedExplicitOrdinal
  :: InterpretedValue
  -> Maybe (Natural, Ordinal)
interpretedExplicitOrdinal value =
  case interpretedForm value of
    ExplicitForm explicitValue -> Just (explicitOrdinal explicitValue)
    _ -> Nothing

interpretedInteger :: InterpretedValue -> Maybe Integer
interpretedInteger value =
  case interpretedForm value of
    IntegerForm integer -> Just integer
    ExplicitForm (EvaluatedExplicit 1 _ explicitValue) ->
      toInteger <$> naturalAtOrdinal (superEllipsisValueOrdinal explicitValue)
    _ -> Nothing

interpretedFormulationLevel :: InterpretedValue -> Maybe Natural
interpretedFormulationLevel value =
  case interpretedForm value of
    FormulationForm formulation ->
      Just (someSuperEllipsisLevel formulation)
    _ -> Nothing

interpretedRangeDescription
  :: InterpretedValue
  -> Maybe Range.SuperEllipsisRangeDescription
interpretedRangeDescription value =
  case interpretedForm value of
    RangeForm valueRange -> Just (rangeDescription valueRange)
    NaturalRangeForm valueRange ->
      Just (rangeDescription (naturalRangeAsEvaluatedRange valueRange))
    ValuedNaturalRangeForm valueRange ->
      Just (rangeDescription (valuedNaturalRangeAsEvaluatedRange valueRange))
    _ -> Nothing

interpretedMapFinalOrderType :: InterpretedMap -> Ordinal
interpretedMapFinalOrderType =
  ordinalOrderedValuesOrderType . interpretedMapFinalValues

interpretedMapValueAt
  :: InterpretedMap
  -> Ordinal
  -> Maybe InterpretedValue
interpretedMapValueAt = ordinalOrderedValueAt . interpretedMapFinalValues

-- | Recover ASCII characters from a finite interpreted map. String operators
-- use this after delegating their ordering to the ordinary map operations.
asciiStringFromInterpretedMap :: InterpretedMap -> Maybe String
asciiStringFromInterpretedMap valueMap = do
  cardinality <- naturalAtOrdinal (interpretedMapFinalOrderType valueMap)
  traverse characterAt (finitePositions cardinality)
  where
    characterAt position = do
      value <- interpretedMapValueAt valueMap position
      (_, ordinalValue) <- interpretedExplicitOrdinal value
      characterCode <- naturalAtOrdinal ordinalValue
      guard (characterCode < 256)
      pure (chr (fromIntegral characterCode))

    finitePositions 0 = []
    finitePositions cardinality =
      map finiteOrdinal [0 .. cardinality - 1]

explicitOrdinal :: EvaluatedExplicit -> (Natural, Ordinal)
explicitOrdinal (EvaluatedExplicit level _ value) =
  (level, superEllipsisValueOrdinal value)

explicitInsertion :: EvaluatedExplicit -> SomeSuperEllipsisInsertion
explicitInsertion (EvaluatedExplicit _ _ value) =
  eraseSuperEllipsisInsertion (superEllipsisValueInsertion value)

rangeDescription
  :: EvaluatedRange
  -> Range.SuperEllipsisRangeDescription
rangeDescription (EvaluatedRange _ valueRange) =
  Range.describeSuperEllipsisRange valueRange

evaluatedRangeLevel :: EvaluatedRange -> Natural
evaluatedRangeLevel (EvaluatedRange level _) = level

rangeInsertion :: EvaluatedRange -> SomeSuperEllipsisInsertion
rangeInsertion (EvaluatedRange _ valueRange) =
  eraseSuperEllipsisInsertion
    (Range.superEllipsisRangeInsertion valueRange)

naturalRangeAsEvaluatedRange :: EvaluatedNaturalRange -> EvaluatedRange
naturalRangeAsEvaluatedRange (EvaluatedNaturalRange valueRange) =
  EvaluatedRange 1 (NaturalRange.naturalRangeEllipsisRange valueRange)

valuedNaturalRangeAsEvaluatedRange
  :: EvaluatedValuedNaturalRange
  -> EvaluatedRange
valuedNaturalRangeAsEvaluatedRange
    (EvaluatedValuedNaturalRange valueRange) =
  EvaluatedRange
    1
    (ValuedNaturalRange.valuedNaturalRangeEllipsisRange valueRange)

valueRanges :: InterpretedValue -> Maybe [EvaluatedRange]
valueRanges value =
  case interpretedForm value of
    RangeForm valueRange -> Just [valueRange]
    NaturalRangeForm valueRange ->
      Just [naturalRangeAsEvaluatedRange valueRange]
    ValuedNaturalRangeForm valueRange ->
      Just [valuedNaturalRangeAsEvaluatedRange valueRange]
    RangeConcatenationForm ranges _ -> Just ranges
    _ -> Nothing

emptyInterpretedMap :: InterpretedMap
emptyInterpretedMap = InterpretedMap 0 emptyOrdinalOrderedValues []

singletonMap :: ValueSemantics -> InterpretedValue -> InterpretedMap
singletonMap semantics value =
  InterpretedMap
    1
    (singletonOrdinalOrderedValues value)
    [semantics]
