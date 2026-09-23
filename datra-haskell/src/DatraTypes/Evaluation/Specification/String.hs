-- | Finite membership decisions for total strings against string federations.
module Evaluation.Specification.String
  ( federationProducesStrings
  , federationUsesWeakToString
  , selectStringFederationMember
  ) where

import AtlasMapFederationExpression
  ( AtlasMapFederationExpression (..)
  )
import Evaluation.Specification.Decision
  ( Decision (..)
  , decideAny
  , mapDecision
  )
import Evaluation.Value
import IdentifierValueType (isIdentifierValue)

-- | Whether every member described by a federation is an ASCII string.
federationProducesStrings :: InterpretedAtlasMapFederation -> Bool
federationProducesStrings federation =
  case federation of
    SingletonAtlasMapFederation valueMap ->
      case interpretedMapComponents valueMap of
        [AsciiStringSemantics _] -> True
        _ -> False
    PrimitiveAtlasMapFederation primitive ->
      case primitive of
        StringTypeAtlasMapFederation -> True
        IdentifierValueTypeAtlasMapFederation -> True
        ToStringAtlasMapFederation _ _ -> True
        WeakToStringAtlasMapFederation _ -> True
        _ -> False
    ConcatenatedAtlasMapFederation left right ->
      federationProducesStrings left && federationProducesStrings right
    SequentialAtlasMapFederation _ -> False
    ExpansionAtlasMapFederation _ _ -> False

federationUsesWeakToString :: InterpretedAtlasMapFederation -> Bool
federationUsesWeakToString federation =
  case federation of
    SingletonAtlasMapFederation _ -> False
    PrimitiveAtlasMapFederation primitive ->
      case primitive of
        WeakToStringAtlasMapFederation _ -> True
        _ -> False
    ConcatenatedAtlasMapFederation left right ->
      federationUsesWeakToString left || federationUsesWeakToString right
    SequentialAtlasMapFederation members ->
      any federationUsesWeakToString members
    ExpansionAtlasMapFederation left right ->
      federationUsesWeakToString left || federationUsesWeakToString right

-- | Select a concrete string by traversing the retained string-federation
-- expression. Concatenations are split only at the finitely many character
-- boundaries of the source string.
selectStringFederationMember
  :: SelectMember
  -> InterpretedValue
  -> InterpretedValue
  -> Maybe (Decision EvaluatedAtlasMapFederationMember)
selectStringFederationMember selectMember source target = do
  characters <-
    case interpretedCanonicalResult source of
      CanonicalAsciiString value -> Just value
      _ -> Nothing
  selectCharacters
    selectMember characters (interpretedAtlasMapFederation target)

selectCharacters
  :: SelectMember
  -> String
  -> InterpretedAtlasMapFederation
  -> Maybe (Decision EvaluatedAtlasMapFederationMember)
selectCharacters selectMember characters federation =
  case federation of
    SingletonAtlasMapFederation valueMap ->
      case interpretedMapComponents valueMap of
        [AsciiStringSemantics expected] ->
          Just
            (if characters == expected
              then
                DecisionProved
                  (EvaluatedSingletonAtlasMapMember
                    (CanonicalAsciiString expected))
              else DecisionRefuted)
        _ -> Nothing
    PrimitiveAtlasMapFederation primitive ->
      case primitive of
        StringTypeAtlasMapFederation ->
          Just (DecisionProved (EvaluatedAsciiStringMember characters))
        IdentifierValueTypeAtlasMapFederation ->
          Just
            (if isIdentifierValue characters
              then DecisionProved (EvaluatedAsciiStringMember characters)
              else DecisionRefuted)
        ToStringAtlasMapFederation source proof ->
          Just
            (case invertInjectiveToString proof characters of
              ToStringInverseMatched candidates ->
                decideAny
                  [ mapDecision
                      (EvaluatedToStringMember candidate)
                      (selectMember candidate source)
                  | candidate <- candidates
                  ]
              ToStringInverseRejected -> DecisionRefuted)
        WeakToStringAtlasMapFederation _ -> Just DecisionUndecidable
        _ -> Nothing
    ConcatenatedAtlasMapFederation left right -> do
      decisions <-
        traverse
          (uncurry (selectConcatenatedCharacters selectMember left right))
          (characterSplits characters)
      pure (decideAny decisions)
    SequentialAtlasMapFederation _ -> Nothing
    ExpansionAtlasMapFederation _ _ -> Nothing

selectConcatenatedCharacters
  :: SelectMember
  -> InterpretedAtlasMapFederation
  -> InterpretedAtlasMapFederation
  -> String
  -> String
  -> Maybe (Decision EvaluatedAtlasMapFederationMember)
selectConcatenatedCharacters selectMember left right leftText rightText = do
  leftDecision <- selectCharacters selectMember leftText left
  rightDecision <- selectCharacters selectMember rightText right
  pure (combineConcatenatedDecisions leftDecision rightDecision)

combineConcatenatedDecisions
  :: Decision EvaluatedAtlasMapFederationMember
  -> Decision EvaluatedAtlasMapFederationMember
  -> Decision EvaluatedAtlasMapFederationMember
combineConcatenatedDecisions
    (DecisionProved left)
    (DecisionProved right) =
      DecisionProved (EvaluatedConcatenatedAtlasMapMember [left, right])
combineConcatenatedDecisions DecisionRefuted _ = DecisionRefuted
combineConcatenatedDecisions _ DecisionRefuted = DecisionRefuted
combineConcatenatedDecisions _ _ = DecisionUndecidable

type SelectMember =
  InterpretedValue
  -> InterpretedValue
  -> Decision EvaluatedAtlasMapFederationMember

characterSplits :: String -> [(String, String)]
characterSplits characters =
  [splitAt position characters | position <- [0 .. length characters]]
