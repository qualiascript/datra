-- | Compile-time decision procedure for the specification operator.
module Evaluation.Specification
  ( validateFunctionInput
  , specifyValues
  , assignIdentifierValues
  ) where

import DatraLanguage.AST (renderAsciiStringLiteral)
import BooleanType (DatraBoolean (..))
import Evaluation.Boolean (makeBoolean)
import Evaluation.Construction (makeAsciiString)
import Evaluation.Optional (makeNothing)
import Evaluation.Error
  ( AtlasMapFederationOperation
      ( AtlasMapFederationSpecification
      , AtlasMapFederationSubfederation
      )
  , AtlasMapFederationRefutation
      ( AtlasMapFederationSpecificationHasNoMatchingMember
      , AtlasMapFederationSubfederationHasMissingMember
      )
  , AtlasMapFederationUncertainty
      (NoAtlasMapFederationDecisionProcedure)
  , InterpretedValueKind (MapValueKind, NaturalValueKind)
  , InterpretingError (..)
  )
import Evaluation.Specification.Composition (selectFederationMember)
import Evaluation.Identifier (simpleIdentifierTypeValue)
import Evaluation.Map (concatenateValues)
import Evaluation.Specification.Decision (Decision (..))
import Evaluation.Specification.String (federationUsesWeakToString)
import Evaluation.Specification.Subfederation
  ( decideValueSubfederation
  )
import Evaluation.Value
import Control.Monad (foldM)
import Evaluation.Either (makeEitherValue)
import Evaluation.Arguments (argumentAlternatives)

specifyValues
  :: InterpretedValue
  -> InterpretedValue
  -> Either InterpretingError InterpretedValue
specifyValues source target
  | EitherForm _ <- interpretedForm source
  , let alternatives = functionAlternatives source
  , not (null alternatives) = do
      specified <- traverse (`specifyValues` target) (argumentAlternatives source)
      case specified of
        first:rest -> foldM makeEitherValue first rest
        [] -> Left (FunctionError "empty function sum")
  | Just _ <- interpretedFunction source
  , EitherForm _ <- interpretedForm target =
      case [signature | signature <- functionAlternatives target
            , DecisionProved () <- [decideValueSubfederation source (makeFunctionValue signature)]] of
        [signature] -> specifyValues source (makeFunctionValue signature)
        [] -> Left (FunctionError "no matching alternative in function specification")
        _ -> Left (FunctionError "ambiguous function specification")
  | BuiltinMetaTypeForm kind <- interpretedForm target = case decideValueSubfederation source target of
      DecisionProved () -> Right source
      _ -> Left (FunctionError ("expected " <> builtinMetaTypeName kind))
  | Just original <- interpretedFunction source
  , Just signature <- interpretedFunction target =
      case decideValueSubfederation source target of
        DecisionProved () -> Right (makeFunctionValue signature
          { functionSource = functionSource original
          , functionInvoke = fmap (\invoke argument -> do
              validateFunctionInput argument (functionDomain signature)
              invoke argument) (functionInvoke original)
          })
        DecisionRefuted -> Left (FunctionError "function signature violates input contravariance or output covariance")
        DecisionUndecidable -> Left (FunctionError ("cannot decide function specification: " <> show (interpretedCanonicalResult source) <> " to " <> show (interpretedCanonicalResult target)))
  | Just _ <- interpretedFunction source = Left (FunctionError "expected a function type")
  | Just _ <- interpretedFunction target = Left (FunctionError "expected a function value")
  | federationUsesWeakToString (interpretedAtlasMapFederation target) =
      Left NoCanonicalStringConversion
  | interpretedCanonicalResult source == interpretedCanonicalResult target =
      Right source
  | otherwise = specifyValuesWithoutIdentity source target

specifyValuesWithoutIdentity
  :: InterpretedValue
  -> InterpretedValue
  -> Either InterpretingError InterpretedValue
specifyValuesWithoutIdentity source target =
  case identifierStringMismatch source target of
    Just (expected, given) ->
      Left
        (IdentifierStringMismatch
          { expectedIdentifierString = expected
          , givenIdentifierString = given
          })
    Nothing ->
      case interpretedForm source of
        ArgumentMapForm _ underlying ->
          specifyFamily source (argumentAlternatives underlying) target
        EitherForm _
          | Nothing <- concreteOptionalAssignmentSource source ->
              specifyFamily source (argumentAlternatives source) target
        FederationSpecificationForm originalSource previousTarget branches ->
          case decideValueSubfederation previousTarget target of
            DecisionProved () -> specifyFamily originalSource branches target
            DecisionRefuted ->
              Left (AtlasMapFederationOperationRefuted
                AtlasMapFederationSubfederationHasMissingMember)
            DecisionUndecidable ->
              Left (AtlasMapFederationOperationUndecidable
                (NoAtlasMapFederationDecisionProcedure
                  AtlasMapFederationSubfederation))
        SpecificationForm specification ->
          widenSpecification source specification target
        AssignmentForm specification ->
          widenSpecification source specification target
        ConcatenatedMapForm _ _ -> do
          presentations <- concatenatedSourcePresentations source
          case presentations of
            Just branches -> specifyFamily source branches target
            Nothing -> specifyTotalAtlasMap source target
        _ -> specifyTotalAtlasMap source target

-- Concatenation preserves each operand's family of presentations. Distribute
-- finite alternatives through its retained tree before requiring a total
-- source, then certify every resulting concatenation against the target.
-- Nothing means no distribution is needed, so ordinary non-total operands
-- still follow the existing total-source check rather than recurring here.
concatenatedSourcePresentations
  :: InterpretedValue
  -> Either InterpretingError (Maybe [InterpretedValue])
concatenatedSourcePresentations value =
  case interpretedForm value of
    ArgumentMapForm _ underlying ->
      Right (Just (argumentAlternatives underlying))
    EitherForm _
      | Nothing <- concreteOptionalAssignmentSource value ->
          Right (Just (argumentAlternatives value))
    ConcatenatedMapForm left right -> do
      leftPresentations <- concatenatedSourcePresentations left
      rightPresentations <- concatenatedSourcePresentations right
      case (leftPresentations, rightPresentations) of
        (Nothing, Nothing) -> Right Nothing
        _ -> Just <$> sequence
          [ concatenateValues leftSource rightSource
          | leftSource <- maybe [left] id leftPresentations
          , rightSource <- maybe [right] id rightPresentations
          ]
    _ -> Right Nothing

-- Lift specification over a finite family of concrete presentations. Every
-- source branch must select a target member; no order is silently discarded.
-- The displayed source stays intact, including its names and original order.
specifyFamily
  :: InterpretedValue
  -> [InterpretedValue]
  -> InterpretedValue
  -> Either InterpretingError InterpretedValue
specifyFamily source branches target = do
  specified <- traverse (`specifyValues` target) branches
  pure
    (makeInterpretedValue
      (FederationSpecificationForm source target specified)
      NoInsertion
      emptyInterpretedMap
      (interpretedAtlasMapFederation target)
      NonTotalInterpretedMap
      (SpecificationSemantics
        (interpretedSemantics source) (interpretedSemantics target)))

identifierStringMismatch
  :: InterpretedValue
  -> InterpretedValue
  -> Maybe (String, String)
identifierStringMismatch source target = do
  given <- simpleIdentifierStringFromSemantics (interpretedSemantics source)
  expected <- simpleIdentifierStringFromSemantics (interpretedSemantics target)
  if given == expected
    then Nothing
    else
      Just
        ( renderAsciiStringLiteral expected
        , renderAsciiStringLiteral given
        )

simpleIdentifierStringFromSemantics :: ValueSemantics -> Maybe String
simpleIdentifierStringFromSemantics semantics =
  case semantics of
    IdentifierTypeSemantics
        (SimpleIdentifierDependency identifierString) _ _ ->
          Just identifierString
    AssignmentSemantics identifierString _ _ -> Just identifierString
    SpecificationSemantics source target -> do
      sourceString <- simpleIdentifierStringFromSemantics source
      targetString <- simpleIdentifierStringFromSemantics target
      if sourceString == targetString then Just sourceString else Nothing
    _ -> Nothing

-- | Assignment is specification between two constant-string identifier types,
-- but remains marked for canonical assignment rendering even when its source
-- and target coincide. Pointwise specifications produced by access still use
-- 'specifyValues' and therefore obey the general identity coercion.
assignIdentifierValues
  :: String
  -> InterpretedValue
  -> InterpretedValue
  -> Either InterpretingError InterpretedValue
assignIdentifierValues identifierString typeAnnotation givenValue = do
  case distinguishedAssignment identifierString typeAnnotation givenValue of
    Just value -> Right value
    Nothing -> do
      let source = simpleIdentifierTypeValue identifierString givenValue
          target = simpleIdentifierTypeValue identifierString typeAnnotation
      specified <- specifyValuesWithoutIdentity source target
      case interpretedForm specified of
        SpecificationForm specification ->
          Right
            (makeInterpretedValue
              (AssignmentForm specification)
              NoInsertion
              (interpretedMap specified)
              (interpretedAtlasMapFederation specified)
              NonTotalInterpretedMap
              (AssignmentSemantics
                identifierString
                (interpretedSemantics typeAnnotation)
                (interpretedSemantics givenValue)))
        _ -> Right specified

-- These assignments are distinguished nullary constructors rather than
-- ordinary identifier specifications. Thus the expanded spellings of Bool
-- and optional absence are definitionally equal to their shorthand forms.
distinguishedAssignment
  :: String
  -> InterpretedValue
  -> InterpretedValue
  -> Maybe InterpretedValue
distinguishedAssignment identifierString typeAnnotation givenValue
  | interpretedCanonicalResult typeAnnotation
      /= interpretedCanonicalResult givenValue = Nothing
  | otherwise =
      case ( identifierString
           , interpretedValueKind givenValue
           , interpretedInteger givenValue
           , interpretedCanonicalResult givenValue
           ) of
        ("False", NaturalValueKind, Just 0, _) ->
          Just (makeBoolean DatraFalse)
        ("True", NaturalValueKind, Just 1, _) ->
          Just (makeBoolean DatraTrue)
        ("Nothing", MapValueKind, _, CanonicalMap 0 []) -> Just makeNothing
        (_, MapValueKind, _, CanonicalMap 0 []) ->
          Just (makeAsciiString identifierString)
        _ -> Nothing

specifyTotalAtlasMap
  :: InterpretedValue
  -> InterpretedValue
  -> Either InterpretingError InterpretedValue
specifyTotalAtlasMap source target = do
  (selectionSource, totalSource) <-
    case concreteOptionalAssignmentSource source of
      Just concreteSource -> Right concreteSource
      Nothing ->
        case interpretedTotalAtlasMap source of
          Just totalMap -> Right (source, totalMap)
          Nothing -> Left (ExpectedTotalAtlasMap (interpretedValueKind source))
  case selectFederationMember selectionSource target of
    DecisionProved member ->
      Right
        (specifiedValue
          source
          totalSource
          (interpretedSemantics source)
          target
          member)
    DecisionRefuted -> noMatchingMember
    DecisionUndecidable ->
      Left
        (AtlasMapFederationOperationUndecidable
          (NoAtlasMapFederationDecisionProcedure
            AtlasMapFederationSpecification))
  where
    noMatchingMember =
      Left
        (AtlasMapFederationOperationRefuted
          AtlasMapFederationSpecificationHasNoMatchingMember)

-- An optional assigned identifier is a federation union syntactically, but
-- its assignment branch retains the concrete total source that supplied the
-- value. As a specification source, it therefore selects the present branch
-- rather than being rejected merely because the surrounding Either is
-- non-total.
concreteOptionalAssignmentSource
  :: InterpretedValue
  -> Maybe (InterpretedValue, InterpretedTotalAtlasMap)
concreteOptionalAssignmentSource source = do
  alternatives <-
    case interpretedForm source of
      EitherForm value -> Just value
      _ -> Nothing
  let present = evaluatedEitherLeft alternatives
      missing = evaluatedEitherRight alternatives
  assignment <-
    case interpretedForm present of
      AssignmentForm value -> Just value
      _ -> Nothing
  case interpretedCanonicalResult present of
    CanonicalAssignment _ typeAnnotation _
      | typeAnnotation == interpretedCanonicalResult missing ->
          Just
            ( evaluatedSpecificationSourceValue assignment
            , evaluatedSpecificationSource assignment
            )
    _ -> Nothing

-- | Compose a prior specification with inclusion of its whole target
-- federation into a larger target. Checking only the previously selected
-- member would be weaker: the intermediate object itself must be an Atlas
-- subfederation of the final object.
widenSpecification
  :: InterpretedValue
  -> EvaluatedSpecification
  -> InterpretedValue
  -> Either InterpretingError InterpretedValue
widenSpecification source specification target =
  if interpretedCanonicalResult
      (evaluatedSpecificationTarget specification)
      == interpretedCanonicalResult target
    then Right source
    else
      case decideValueSubfederation
          (evaluatedSpecificationTarget specification)
          target of
        DecisionProved () ->
          -- Inclusion certifies widening, but the selection route can change
          -- when the new target lists argument permutations differently.
          case selectFederationMember
              (evaluatedSpecificationSourceValue specification) target of
            DecisionProved member ->
              Right
                (specifiedValue
                  (evaluatedSpecificationSourceValue specification)
                  (evaluatedSpecificationSource specification)
                  (originalSpecificationSourceSemantics source)
                  target
                  member)
            _ ->
              Left (AtlasMapFederationOperationUndecidable
                (NoAtlasMapFederationDecisionProcedure
                  AtlasMapFederationSpecification))
        DecisionRefuted ->
          Left
            (AtlasMapFederationOperationRefuted
              AtlasMapFederationSubfederationHasMissingMember)
        DecisionUndecidable ->
          Left
            (AtlasMapFederationOperationUndecidable
              (NoAtlasMapFederationDecisionProcedure
                AtlasMapFederationSubfederation))

specifiedValue
  :: InterpretedValue
  -> InterpretedTotalAtlasMap
  -> ValueSemantics
  -> InterpretedValue
  -> EvaluatedAtlasMapFederationMember
  -> InterpretedValue
specifiedValue sourceValue totalSource sourceCanonical target member =
  makeInterpretedValue
    (SpecificationForm
      EvaluatedSpecification
        { evaluatedSpecificationSourceValue = sourceValue
        , evaluatedSpecificationSource = totalSource
        , evaluatedSpecificationTarget = target
        , evaluatedSpecificationMember = member
        })
    NoInsertion
    (interpretedTotalAtlasMapUnderlying totalSource)
    (interpretedAtlasMapFederation target)
    NonTotalInterpretedMap
    (SpecificationSemantics sourceCanonical (interpretedSemantics target))

originalSpecificationSourceSemantics :: InterpretedValue -> ValueSemantics
originalSpecificationSourceSemantics value =
  case interpretedSemantics value of
    SpecificationSemantics source _ -> source
    AssignmentSemantics identifierString _ givenValueSemantics ->
      IdentifierTypeSemantics
        (SimpleIdentifierDependency identifierString)
        givenValueSemantics
        True
    semantics -> semantics


validateFunctionInput :: InterpretedValue -> InterpretedValue -> Either InterpretingError ()
validateFunctionInput input domain = case decideValueSubfederation input domain of
  DecisionProved () -> Right ()
  _ -> () <$ specifyValues input domain
