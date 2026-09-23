-- | Shared decision procedures for evaluated Atlas-map federations.
module Evaluation.Federation
  ( decideFederationConcatenation
  , decidePrimitiveSubfederation
  , requireFederationDecision
  , undecidableFederationOperation
  , selectNaturalRangeMember
  , selectValuedNaturalRangeMember
  , selectIntegerRangeMember
  , selectValuedIntegerRangeMember
  ) where

import AtlasMapFederationExpression
  ( AtlasMapFederationDecision (..)
  , AtlasMapFederationExpression (..)
  , atlasMapFederationExpressionIsSingleton
  )
import Evaluation.Error
import Evaluation.Value
import Data.List (isInfixOf)
import NaturalRange qualified
import IntegerRange qualified
import Numeric.Natural (Natural)
import ValuedNaturalRange qualified
import ValuedIntegerRange qualified
decideFederationConcatenation
  :: InterpretedAtlasMapFederation
  -> InterpretedAtlasMapFederation
  -> AtlasMapFederationDecision
       AtlasMapFederationRefutation
       AtlasMapFederationUncertainty
       ()
decideFederationConcatenation left right
  | atlasMapFederationExpressionIsSingleton left =
      AtlasMapFederationProved ()
  | atlasMapFederationExpressionIsSingleton right =
      AtlasMapFederationProved ()
  | Just (prefix, delimiter) <- trailingStringDelimiter left
  , not (null delimiter)
  , stringFederationExcludes delimiter prefix
      || stringFederationExcludes delimiter right =
      AtlasMapFederationProved ()
  | Just (delimiter, suffix) <- leadingStringDelimiter right
  , not (null delimiter)
  , stringFederationExcludes delimiter left
      || stringFederationExcludes delimiter suffix =
      AtlasMapFederationProved ()
decideFederationConcatenation
    (PrimitiveAtlasMapFederation (EitherAtlasMapFederation _)) _ =
  AtlasMapFederationProved ()
decideFederationConcatenation _
    (PrimitiveAtlasMapFederation (EitherAtlasMapFederation _)) =
  AtlasMapFederationProved ()
decideFederationConcatenation
    (PrimitiveAtlasMapFederation
      (NaturalRangeAtlasMapFederation
        (EvaluatedNaturalRange leftRange)))
    (PrimitiveAtlasMapFederation
      (NaturalRangeAtlasMapFederation
        (EvaluatedNaturalRange rightRange))) =
  overlapDecision
    (NaturalRange.naturalRangeOverlapWitness leftRange rightRange)
decideFederationConcatenation
    (PrimitiveAtlasMapFederation
      (ValuedNaturalRangeAtlasMapFederation
        (EvaluatedValuedNaturalRange leftRange)))
    (PrimitiveAtlasMapFederation
      (ValuedNaturalRangeAtlasMapFederation
        (EvaluatedValuedNaturalRange rightRange))) =
  overlapDecision
    (ValuedNaturalRange.valuedNaturalRangesOverlapWitness
      leftRange rightRange)
decideFederationConcatenation
    (PrimitiveAtlasMapFederation
      (NaturalRangeAtlasMapFederation
        (EvaluatedNaturalRange naturalRange)))
    (PrimitiveAtlasMapFederation
      (ValuedNaturalRangeAtlasMapFederation
        (EvaluatedValuedNaturalRange valuedRange))) =
  overlapDecision
    (ValuedNaturalRange.valuedNaturalRangeOverlapNaturalRange
      valuedRange naturalRange)
decideFederationConcatenation
    (PrimitiveAtlasMapFederation
      (IntegerRangeAtlasMapFederation
        (EvaluatedIntegerRange leftRange)))
    (PrimitiveAtlasMapFederation
      (IntegerRangeAtlasMapFederation
        (EvaluatedIntegerRange rightRange))) =
  integerOverlapDecision
    (IntegerRange.integerRangeOverlapWitness leftRange rightRange)
decideFederationConcatenation
    (PrimitiveAtlasMapFederation
      (ValuedIntegerRangeAtlasMapFederation
        (EvaluatedValuedIntegerRange leftRange)))
    (PrimitiveAtlasMapFederation
      (ValuedIntegerRangeAtlasMapFederation
        (EvaluatedValuedIntegerRange rightRange))) =
  integerOverlapDecision
    (ValuedIntegerRange.valuedIntegerRangesOverlapWitness
      leftRange rightRange)
decideFederationConcatenation
    (PrimitiveAtlasMapFederation
      (IntegerRangeAtlasMapFederation
        (EvaluatedIntegerRange integerRange)))
    (PrimitiveAtlasMapFederation
      (ValuedIntegerRangeAtlasMapFederation
        (EvaluatedValuedIntegerRange valuedRange))) =
  integerOverlapDecision
    (ValuedIntegerRange.valuedIntegerRangeOverlapIntegerRange
      valuedRange integerRange)
decideFederationConcatenation
    (PrimitiveAtlasMapFederation
      (ValuedIntegerRangeAtlasMapFederation
        (EvaluatedValuedIntegerRange valuedRange)))
    (PrimitiveAtlasMapFederation
      (IntegerRangeAtlasMapFederation
        (EvaluatedIntegerRange integerRange))) =
  integerOverlapDecision
    (ValuedIntegerRange.valuedIntegerRangeOverlapIntegerRange
      valuedRange integerRange)
decideFederationConcatenation
    (PrimitiveAtlasMapFederation
      (ValuedNaturalRangeAtlasMapFederation
        (EvaluatedValuedNaturalRange valuedRange)))
    (PrimitiveAtlasMapFederation
      (NaturalRangeAtlasMapFederation
        (EvaluatedNaturalRange naturalRange))) =
  overlapDecision
    (ValuedNaturalRange.valuedNaturalRangeOverlapNaturalRange
      valuedRange naturalRange)
decideFederationConcatenation _ _ =
  AtlasMapFederationUndecidable
    (NoAtlasMapFederationDecisionProcedure
      AtlasMapFederationConcatenation)

-- A fixed delimiter provides a unique split when it cannot occur in the
-- adjacent variable string language. A trailing delimiter can select its
-- first occurrence when excluded from the prefix or its final occurrence when
-- excluded from the suffix; the latter supports repeated separated fields.
trailingStringDelimiter
  :: InterpretedAtlasMapFederation
  -> Maybe (InterpretedAtlasMapFederation, String)
trailingStringDelimiter
    (ConcatenatedAtlasMapFederation left right) =
      (\delimiter -> (left, delimiter)) <$> singletonAsciiString right
trailingStringDelimiter _ = Nothing

leadingStringDelimiter
  :: InterpretedAtlasMapFederation
  -> Maybe (String, InterpretedAtlasMapFederation)
leadingStringDelimiter
    (ConcatenatedAtlasMapFederation left right) =
      (\delimiter -> (delimiter, right)) <$> singletonAsciiString left
leadingStringDelimiter _ = Nothing

singletonAsciiString
  :: InterpretedAtlasMapFederation
  -> Maybe String
singletonAsciiString (SingletonAtlasMapFederation valueMap) =
  case interpretedMapComponents valueMap of
    [AsciiStringSemantics characters] -> Just characters
    _ -> Nothing
singletonAsciiString _ = Nothing

stringFederationExcludes
  :: String
  -> InterpretedAtlasMapFederation
  -> Bool
stringFederationExcludes delimiter federation =
  case federation of
    SingletonAtlasMapFederation valueMap ->
      case interpretedMapComponents valueMap of
        [AsciiStringSemantics characters] ->
          not (delimiter `isInfixOf` characters)
        _ -> False
    PrimitiveAtlasMapFederation primitive ->
      case primitive of
        ToStringAtlasMapFederation source ->
          renderedSemanticsExclude
            delimiter (interpretedSemantics source)
        StringTypeAtlasMapFederation -> False
        _ -> False
    SequentialAtlasMapFederation members ->
      all (stringFederationExcludes delimiter) members
    ExpansionAtlasMapFederation left right ->
      stringFederationExcludes delimiter left
        && stringFederationExcludes delimiter right
    ConcatenatedAtlasMapFederation left right ->
      stringFederationExcludes delimiter left
        && stringFederationExcludes delimiter right

renderedSemanticsExclude :: String -> ValueSemantics -> Bool
renderedSemanticsExclude delimiter semantics =
  case semantics of
    ExplicitSemantics {} -> excludes "0123456789"
    IntegerSemantics {} -> excludes "-0123456789"
    BooleanSemantics {} -> excludes "falsetru"
    NaturalRangeSemantics {} -> excludes numericRangeCharacters
    ValuedNaturalRangeSemantics {} -> excludes numericRangeCharacters
    NaturalTypeSemantics -> excludes "0123456789"
    IntegerRangeSemantics {} -> excludes numericRangeCharacters
    ValuedIntegerRangeSemantics {} -> excludes numericRangeCharacters
    IntegerTypeSemantics -> excludes "-0123456789"
    ToStringSemantics source -> renderedSemanticsExclude delimiter source
    _ -> False
  where
    excludes alphabet = any (`notElem` alphabet) delimiter
    numericRangeCharacters = " -0123456789.rangeftoupwds"

decidePrimitiveSubfederation
  :: InterpretedAtlasMapFederationPrimitive
  -> InterpretedAtlasMapFederationPrimitive
  -> AtlasMapFederationDecision
       AtlasMapFederationRefutation
       AtlasMapFederationUncertainty
       ()
decidePrimitiveSubfederation
    StringTypeAtlasMapFederation
    StringTypeAtlasMapFederation =
  AtlasMapFederationProved ()
decidePrimitiveSubfederation
    (NaturalRangeAtlasMapFederation
      (EvaluatedNaturalRange sourceRange))
    (NaturalRangeAtlasMapFederation
      (EvaluatedNaturalRange targetRange))
  | NaturalRange.naturalRangeIsSubfederationOf sourceRange targetRange =
      AtlasMapFederationProved ()
  | otherwise = missingMember
decidePrimitiveSubfederation
    (IntegerRangeAtlasMapFederation
      (EvaluatedIntegerRange sourceRange))
    (IntegerRangeAtlasMapFederation
      (EvaluatedIntegerRange targetRange))
  | IntegerRange.integerRangeIsSubfederationOf sourceRange targetRange =
      AtlasMapFederationProved ()
  | otherwise = missingMember
decidePrimitiveSubfederation
    (ValuedIntegerRangeAtlasMapFederation
      (EvaluatedValuedIntegerRange sourceRange))
    (ValuedIntegerRangeAtlasMapFederation
      (EvaluatedValuedIntegerRange targetRange))
  | ValuedIntegerRange.valuedIntegerRangeIsSubfederationOf
      sourceRange targetRange = AtlasMapFederationProved ()
  | otherwise = missingMember
decidePrimitiveSubfederation
    (ValuedNaturalRangeAtlasMapFederation
      (EvaluatedValuedNaturalRange sourceRange))
    (ValuedIntegerRangeAtlasMapFederation
      (EvaluatedValuedIntegerRange targetRange))
  | valuedNaturalContainedInInteger sourceRange targetRange =
      AtlasMapFederationProved ()
  | otherwise = missingMember
decidePrimitiveSubfederation
    (ValuedIntegerRangeAtlasMapFederation
      (EvaluatedValuedIntegerRange sourceRange))
    (ValuedNaturalRangeAtlasMapFederation
      (EvaluatedValuedNaturalRange targetRange))
  | valuedIntegerContainedInNatural sourceRange targetRange =
      AtlasMapFederationProved ()
  | otherwise = missingMember
decidePrimitiveSubfederation
    (ValuedNaturalRangeAtlasMapFederation
      (EvaluatedValuedNaturalRange sourceRange))
    (ValuedNaturalRangeAtlasMapFederation
      (EvaluatedValuedNaturalRange targetRange))
  | ValuedNaturalRange.valuedNaturalRangeIsSubfederationOf
      sourceRange targetRange =
      AtlasMapFederationProved ()
  | otherwise = missingMember
decidePrimitiveSubfederation
    (IdentifierTypeAtlasMapFederation _)
    (IdentifierTypeAtlasMapFederation _) =
  AtlasMapFederationUndecidable
    (NoAtlasMapFederationDecisionProcedure
      AtlasMapFederationSubfederation)
decidePrimitiveSubfederation _ _ = missingMember

requireFederationDecision
  :: AtlasMapFederationDecision
       AtlasMapFederationRefutation
       AtlasMapFederationUncertainty
       ()
  -> Either InterpretingError ()
requireFederationDecision decision =
  case decision of
    AtlasMapFederationRefuted refutation ->
      Left (AtlasMapFederationOperationRefuted refutation)
    AtlasMapFederationUndecidable uncertainty ->
      Left (AtlasMapFederationOperationUndecidable uncertainty)
    AtlasMapFederationProved () -> Right ()

undecidableFederationOperation
  :: AtlasMapFederationOperation
  -> Either InterpretingError result
undecidableFederationOperation operation =
  Left
    (AtlasMapFederationOperationUndecidable
      (NoAtlasMapFederationDecisionProcedure operation))

selectNaturalRangeMember
  :: NaturalRange.NaturalRange rangeScope federationScope
  -> NaturalRange.NaturalSubrangeDescription
  -> Maybe NaturalRange.NaturalSubrangeDescription
selectNaturalRangeMember targetRange candidate =
  case candidate of
    NaturalRange.EmptyNaturalSubrange -> Just candidate
    NaturalRange.FiniteNaturalSubrange start final ->
      NaturalRange.naturalSubrangeDescription
        <$> NaturalRange.naturalRangeFiniteSubrange
              targetRange start final
    NaturalRange.UpwardsNaturalSubrange start ->
      NaturalRange.naturalSubrangeDescription
        <$> NaturalRange.naturalRangeUpwardsSubrange targetRange start

selectValuedNaturalRangeMember
  :: ValuedNaturalRange.ValuedNaturalRange rangeScope federationScope
  -> Natural
  -> Maybe Natural
selectValuedNaturalRangeMember targetRange candidate =
  candidate
    <$ ValuedNaturalRange.valuedNaturalRangeValue targetRange candidate

selectIntegerRangeMember
  :: IntegerRange.IntegerRange rangeScope federationScope
  -> IntegerRange.IntegerSubrangeDescription
  -> Maybe IntegerRange.IntegerSubrangeDescription
selectIntegerRangeMember targetRange candidate =
  case candidate of
    IntegerRange.EmptyIntegerSubrange -> Just candidate
    IntegerRange.FiniteIntegerSubrange start final ->
      IntegerRange.integerSubrangeDescription
        <$> IntegerRange.integerRangeFiniteSubrange targetRange start final
    IntegerRange.UpwardsIntegerSubrange start ->
      IntegerRange.integerSubrangeDescription
        <$> IntegerRange.integerRangeUpwardsSubrange targetRange start
    IntegerRange.DownwardsIntegerSubrange start ->
      IntegerRange.integerSubrangeDescription
        <$> IntegerRange.integerRangeDownwardsSubrange targetRange start

selectValuedIntegerRangeMember
  :: ValuedIntegerRange.ValuedIntegerRange rangeScope federationScope
  -> Integer
  -> Maybe Integer
selectValuedIntegerRangeMember targetRange candidate =
  candidate
    <$ ValuedIntegerRange.valuedIntegerRangeValue targetRange candidate

overlapDecision
  :: Maybe Natural
  -> AtlasMapFederationDecision
       AtlasMapFederationRefutation
       AtlasMapFederationUncertainty
       ()
overlapDecision Nothing = AtlasMapFederationProved ()
overlapDecision (Just witness) =
  AtlasMapFederationRefuted
    (AtlasMapFederationConcatenationCollision (toInteger witness))

integerOverlapDecision
  :: Maybe Integer
  -> AtlasMapFederationDecision
       AtlasMapFederationRefutation
       AtlasMapFederationUncertainty
       ()
integerOverlapDecision Nothing = AtlasMapFederationProved ()
integerOverlapDecision (Just witness) =
  AtlasMapFederationRefuted
    (AtlasMapFederationConcatenationCollision witness)

valuedNaturalContainedInInteger
  :: ValuedNaturalRange.ValuedNaturalRange sourceRange sourceFederation
  -> ValuedIntegerRange.ValuedIntegerRange targetRange targetFederation
  -> Bool
valuedNaturalContainedInInteger source target =
  case ValuedNaturalRange.valuedNaturalRangeTarget source of
    NaturalRange.FiniteNaturalTarget final ->
      contains (toInteger (ValuedNaturalRange.valuedNaturalRangeStart source))
        && contains (toInteger final)
    NaturalRange.UpwardsTarget ->
      contains (toInteger (ValuedNaturalRange.valuedNaturalRangeStart source))
        && ValuedIntegerRange.valuedIntegerRangeTarget target
          `elem` [ IntegerRange.UpwardsIntegerTarget
                 , IntegerRange.AllIntegersTarget
                 ]
  where
    contains = ValuedIntegerRange.valuedIntegerRangeContains target

valuedIntegerContainedInNatural
  :: ValuedIntegerRange.ValuedIntegerRange sourceRange sourceFederation
  -> ValuedNaturalRange.ValuedNaturalRange targetRange targetFederation
  -> Bool
valuedIntegerContainedInNatural source target =
  case ValuedIntegerRange.valuedIntegerRangeTarget source of
    IntegerRange.FiniteIntegerTarget final ->
      contains (ValuedIntegerRange.valuedIntegerRangeStart source)
        && contains final
    IntegerRange.UpwardsIntegerTarget ->
      contains (ValuedIntegerRange.valuedIntegerRangeStart source)
        && ValuedNaturalRange.valuedNaturalRangeTarget target
          == NaturalRange.UpwardsTarget
    IntegerRange.DownwardsIntegerTarget -> False
    IntegerRange.AllIntegersTarget -> False
  where
    contains value
      | value < 0 = False
      | otherwise =
          ValuedNaturalRange.valuedNaturalRangeContains
            target (fromInteger value)

missingMember
  :: AtlasMapFederationDecision
       AtlasMapFederationRefutation
       AtlasMapFederationUncertainty
       ()
missingMember =
  AtlasMapFederationRefuted
    AtlasMapFederationSubfederationHasMissingMember
