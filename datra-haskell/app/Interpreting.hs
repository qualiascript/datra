-- | Recursive interpretation of the parsed Datra AST.
--
-- This module deliberately owns syntax traversal only. Checked semantic
-- operations and all type errors are provided by 'DatraTypes'.
module Interpreting
  ( InterpretedValue
  , CanonicalResult (..)
  , InterpretedValueKind (..)
  , InterpretedMap
  , InterpretingError (..)
  , OperandSide (..)
  , interpretExpression
  , interpretLocatedExpression
  , interpretExpressionReason
  , interpretedValueKind
  , interpretedValueHasTotalMap
  , interpretedCanonicalResult
  , interpretedExplicitOrdinal
  , interpretedInteger
  , interpretedFormulationLevel
  , interpretedRangeDescription
  , interpretedMap
  , interpretedMapCardinality
  , interpretedMapFinalOrderType
  , interpretedMapValueAt
  , canonicalStringCodec
  ) where

import Data.Bifunctor qualified as Bifunctor
import Control.Monad (foldM)
import DatraLanguage.AST
  ( Expression (..)
  , IdentifierString (IdentifierString)
  , StringTemplatePart (..)
  , normalizeExpression
  )
import DatraTypes
import Parsing (parseDatra)
import Rendering (renderCanonicalResult, renderInterpretedValue)
import DatraLanguage.Diagnostics
  ( DatraError
  , Located (Located)
  , atSourceSpan
  , withoutSourceSpan
  )
import Numeric.Natural (Natural)

interpretExpression
  :: Expression
  -> Either (DatraError InterpretingError) InterpretedValue
interpretExpression =
  Bifunctor.first withoutSourceSpan . interpretExpressionReason

interpretLocatedExpression
  :: Located Expression
  -> Either (DatraError InterpretingError) InterpretedValue
interpretLocatedExpression (Located sourceSpan expressionValue) =
  Bifunctor.first (atSourceSpan sourceSpan)
    (interpretExpressionReason expressionValue)

interpretExpressionReason
  :: Expression
  -> Either InterpretingError InterpretedValue
interpretExpressionReason = interpretNormalizedExpression . normalizeExpression

canonicalStringCodec :: CanonicalStringCodec
canonicalStringCodec =
  CanonicalStringCodec
    { renderCanonicalString = renderCanonicalResult
    , decodeCanonicalString = canonicalStringCandidates
    }

canonicalStringCandidates :: String -> [InterpretedValue]
canonicalStringCandidates characters =
  asciiCandidate <> parsedCanonicalCandidate
  where
    -- String-valued federations use their contents without source delimiters.
    asciiCandidate =
      case asciiStringValue characters of
        Right value -> [value]
        Left _ -> []
    -- Every other value must already use its canonical source spelling.
    parsedCanonicalCandidate =
      case parseDatra characters of
        Left _ -> []
        Right expressionValue ->
          case interpretExpressionReason expressionValue of
            Right value
              | canonicalSpelling characters
                  (renderInterpretedValue value) ->
                    [ candidate
                    | candidateExpression <-
                        canonicalExpressionCandidates expressionValue
                    , Right candidate <-
                        [interpretExpressionReason candidateExpression]
                    ]
            _ -> []

    -- Parentheses are canonical when a rendered value is embedded as one
    -- component of a larger expression. No other alternate spelling is
    -- accepted by the inverse.
    canonicalSpelling actual rendered =
      actual == rendered || actual == "(" <> rendered <> ")"

-- Canonical Either and map syntax can retain the unselected branches that
-- explain a value's type. Decode those contexts into their concrete member
-- expressions before asking the semantic federation to select one.
canonicalExpressionCandidates :: Expression -> [Expression]
canonicalExpressionCandidates expressionValue =
  case expressionValue of
    EitherType left right ->
      canonicalExpressionCandidates left
        <> canonicalExpressionCandidates right
    AtlasMap members ->
      AtlasMap <$> traverse canonicalExpressionCandidates members
    MapSequence members ->
      MapSequence <$> traverse canonicalExpressionCandidates members
    ArgumentMap members ->
      ArgumentMap <$> traverse canonicalExpressionCandidates members
    MapExpansion left right ->
      MapExpansion
        <$> canonicalExpressionCandidates left
        <*> canonicalExpressionCandidates right
    MapConcatenation left right ->
      MapConcatenation
        <$> canonicalExpressionCandidates left
        <*> canonicalExpressionCandidates right
    _ -> [expressionValue]

interpretNormalizedExpression
  :: Expression
  -> Either InterpretingError InterpretedValue
interpretNormalizedExpression expressionValue =
  case expressionValue of
    EllipsisNatural value -> Right (naturalValue value)
    EllipsisLiteral -> Right (formulationValue 1)
    AsciiStringLiteral value -> asciiStringValue value
    NothingLiteral -> Right nothingValue
    StringTemplate parts -> interpretStringTemplate parts
    StringType -> Right stringTypeValue
    IdentifierValueType -> Right identifierValueTypeValue
    AtlasMap expressions ->
      interpretAtlasMapWith interpretExpressionReason expressions
    ArgumentMap expressions ->
      traverse interpretExpressionReason expressions >>= makeArgumentMap
    MapSequence expressions ->
      interpretAtlasMapWith interpretExpressionReason expressions
    MapExpansion left right ->
      interpretAtlasMapWithBuilder
        makeAtlasExpansion
        interpretExpressionReason
        [ensureMapLevel left, ensureMapLevel right]
    SuperEllipsisRange lower upper -> do
      lowerValue <- interpretExpressionReason lower
      upperValue <- interpretExpressionReason upper
      boundedRangeValue lowerValue upperValue
    SuperEllipsisRangePlus lower ->
      interpretExpressionReason lower >>= openPlusRangeValue
    SuperEllipsisRangeMinus upper ->
      interpretExpressionReason upper >>= openMinusRangeValue
    NaturalRange origin target ->
      interpretBoundedKeyword "range" NaturalType (toInteger origin) (toInteger target)
        (\start end -> naturalRangeValue (fromInteger start) (fromInteger end))
    NaturalRangeUpwards origin ->
      interpretOpenKeyword "range" NaturalType (toInteger origin) "upwards"
        (naturalRangeUpwardsValue . fromInteger)
    ValuedNaturalRange origin target ->
      interpretBoundedKeyword "from" NaturalType (toInteger origin) (toInteger target)
        (\start end -> valuedNaturalRangeValue (fromInteger start) (fromInteger end))
    ValuedNaturalRangeUpwards origin ->
      interpretOpenKeyword "from" NaturalType (toInteger origin) "upwards"
        (valuedNaturalRangeUpwardsValue . fromInteger)
    NaturalType -> naturalTypeValue
    IntegerRange origin target ->
      interpretBoundedKeyword "range" IntegerType origin target integerRangeValue
    IntegerRangeUpwards origin ->
      interpretOpenKeyword "range" IntegerType origin "upwards" integerRangeUpwardsValue
    IntegerRangeDownwards origin ->
      interpretOpenKeyword "range" IntegerType origin "downwards" integerRangeDownwardsValue
    ValuedIntegerRange origin target ->
      interpretBoundedKeyword "from" IntegerType origin target valuedIntegerRangeValue
    ValuedIntegerRangeUpwards origin ->
      interpretOpenKeyword "from" IntegerType origin "upwards" valuedIntegerRangeUpwardsValue
    ValuedIntegerRangeDownwards origin ->
      interpretOpenKeyword "from" IntegerType origin "downwards" valuedIntegerRangeDownwardsValue
    IntegerType -> integerTypeValue
    BooleanLiteral value -> Right (booleanValue value)
    BooleanType -> booleanTypeValue
    EitherType left right ->
      interpretBinary eitherValue left right
    OptionalType operand ->
      interpretExpressionReason operand >>= optionalValue
    Conditional condition consequent alternative -> do
      conditionValue <- interpretExpressionReason condition
      conditionFlag <- booleanCondition conditionValue
      captured <- interpretKeywordTemplate
        ("if " <> renderInterpretedValue (booleanValue conditionFlag) <> " then")
        [ StringTemplateLiteral "if "
        , StringTemplateInterpolation BooleanType
        , StringTemplateLiteral " then"
        ]
      conditionResult <- accessValues captured (naturalValue 1) >>= booleanCondition
      -- Branch ASTs remain deferred: only the decoded condition selects which
      -- expression to interpret, including the implicit () alternative.
      interpretExpressionReason
        (if conditionResult then consequent else alternative)
    Addition left right ->
      interpretBinary addValues left right
    Subtraction left right ->
      interpretBinary subtractValues left right
    Minus operand -> interpretExpressionReason operand >>= minusValue
    Multiplication left right ->
      interpretBinary multiplyValues left right
    Exponentiation base exponentValue ->
      interpretBinary exponentiateValues base exponentValue
    Subfederation source target ->
      interpretBinary subfederationValues source target
    Equality left right ->
      interpretBinary equalValues left right
    BooleanAnd left right ->
      interpretBinary booleanAndValues left right
    BooleanOr left right ->
      interpretBinary booleanOrValues left right
    BooleanNot operand ->
      interpretExpressionReason operand >>= booleanNotValue
    Extract operand ->
      interpretExpressionReason operand >>= extractValue
    Eval source target ->
      interpretBinary (evalValues canonicalStringCodec) source target
    MapConcatenation left right ->
      interpretBinary concatenateValues left right
    MapAccess mapOperand insertionOperand ->
      interpretBinary accessValues mapOperand insertionOperand
    MapSpecification sourceOperand targetOperand ->
      interpretSpecification sourceOperand targetOperand
    IdentifierOperation
        (IdentifierString identifierString)
        typeAnnotationExpression
        maybeGivenValueExpression -> do
      typeAnnotation <- interpretExpressionReason typeAnnotationExpression
      case maybeGivenValueExpression of
        Nothing
          | identifierString == "False"
          , interpretedValueKind typeAnnotation == NaturalValueKind
          , interpretedInteger typeAnnotation == Just 0 ->
              Right (booleanValue False)
        Nothing
          | identifierString == "True"
          , interpretedValueKind typeAnnotation == NaturalValueKind
          , interpretedInteger typeAnnotation == Just 1 ->
              Right (booleanValue True)
        Nothing
          | identifierString == "Nothing"
          , interpretedCanonicalResult typeAnnotation == CanonicalMap 0 [] ->
              Right nothingValue
        Nothing ->
          Right (simpleIdentifierTypeValue identifierString typeAnnotation)
        Just givenValueExpression -> do
          givenValue <- interpretExpressionReason givenValueExpression
          case assignIdentifierValues
              identifierString typeAnnotation givenValue of
            Left
                (AtlasMapFederationOperationRefuted
                  AtlasMapFederationSpecificationHasNoMatchingMember) ->
              Left
                (GivenValueOutsideTypeAnnotation
                  { expectedTypeAnnotation =
                      renderInterpretedValue typeAnnotation
                  , givenValue = renderInterpretedValue givenValue
                  })
            result -> result

-- The parser retains structural boundaries and canonicalizes literal tokens;
-- eval matches the normalized keyword text and provides typed captures. The
-- range constructors below receive only those decoded bounds.
interpretKeywordTemplate
  :: String
  -> [StringTemplatePart Expression]
  -> Either InterpretingError InterpretedValue
interpretKeywordTemplate source parts =
  interpretExpressionReason
    (Eval (AsciiStringLiteral source) (StringTemplate parts)) >>= extractValue

interpretBoundedKeyword
  :: String
  -> Expression
  -> Integer
  -> Integer
  -> (Integer -> Integer -> Either InterpretingError InterpretedValue)
  -> Either InterpretingError InterpretedValue
interpretBoundedKeyword keyword boundType origin target construct = do
  captured <- interpretKeywordTemplate
    (keyword <> " " <> canonicalInteger origin <> " to " <> canonicalInteger target)
    [ StringTemplateLiteral (keyword <> " ")
    , StringTemplateInterpolation boundType
    , StringTemplateLiteral " to "
    , StringTemplateInterpolation boundType
    ]
  start <- accessValues captured (naturalValue 1) >>= requireFiniteInteger LeftOperand
  end <- accessValues captured (naturalValue 2) >>= requireFiniteInteger RightOperand
  construct start end

interpretOpenKeyword
  :: String
  -> Expression
  -> Integer
  -> String
  -> (Integer -> Either InterpretingError InterpretedValue)
  -> Either InterpretingError InterpretedValue
interpretOpenKeyword keyword boundType origin direction construct = do
  captured <- interpretKeywordTemplate
    (keyword <> " " <> canonicalInteger origin <> " " <> direction)
    [ StringTemplateLiteral (keyword <> " ")
    , StringTemplateInterpolation boundType
    , StringTemplateLiteral (" " <> direction)
    ]
  start <- accessValues captured (naturalValue 1) >>= requireFiniteInteger LeftOperand
  construct start

canonicalInteger :: Integer -> String
canonicalInteger = renderInterpretedValue . integerValue

interpretStringTemplate
  :: [StringTemplatePart Expression]
  -> Either InterpretingError InterpretedValue
interpretStringTemplate parts = do
  values <- traverse interpretPart parts
  case values of
    [] -> asciiStringValue ""
    firstValue : remaining -> do
      result <- foldM concatenateTemplateValues firstValue remaining
      pure (stringTemplateValue result)
  where
    interpretPart (StringTemplateLiteral value) = asciiStringValue value
    interpretPart (StringTemplateInterpolation expressionValue) = do
      value <- interpretExpressionReason expressionValue
      toStringValue canonicalStringCodec value
    interpretPart (StringTemplateWeakInterpolation expressionValue) = do
      value <- interpretExpressionReason expressionValue
      weakToStringValue canonicalStringCodec value

    concatenateTemplateValues left right =
      case concatenateValues left right of
        Right value -> Right value
        Left _ -> Left AmbiguousStringTemplate

interpretSpecification
  :: Expression
  -> Expression
  -> Either InterpretingError InterpretedValue
interpretSpecification sourceExpression targetExpression = do
  source <- interpretExpressionReason sourceExpression
  target <- interpretExpressionReason targetExpression
  case specifyValues source target of
    Left
        (AtlasMapFederationOperationRefuted
          AtlasMapFederationSpecificationHasNoMatchingMember)
      | Just (expected, given) <- identifierAnnotationMismatch source target ->
          Left
            (GivenValueOutsideTypeAnnotation
              { expectedTypeAnnotation = expected
              , givenValue = given
              })
    Left
        (AtlasMapFederationOperationRefuted
          AtlasMapFederationSubfederationHasMissingMember)
      | Just (expected, given) <-
          identifierIntermediateAnnotationMismatch source target ->
          Left
            (IntermediateTypeAnnotationOutsideTarget
              { expectedTargetTypeAnnotation = expected
              , givenIntermediateTypeAnnotation = given
              })
    result -> result

identifierAnnotationMismatch
  :: InterpretedValue
  -> InterpretedValue
  -> Maybe (String, String)
identifierAnnotationMismatch =
  identifierValueMismatch identifierGivenValue

identifierIntermediateAnnotationMismatch
  :: InterpretedValue
  -> InterpretedValue
  -> Maybe (String, String)
identifierIntermediateAnnotationMismatch =
  identifierValueMismatch identifierIntermediateValue

identifierValueMismatch
  :: (CanonicalResult -> Maybe (String, CanonicalResult))
  -> InterpretedValue
  -> InterpretedValue
  -> Maybe (String, String)
identifierValueMismatch givenValueFor source target = do
  (givenString, givenResult) <-
    givenValueFor (interpretedCanonicalResult source)
  (expectedString, expectedResult) <-
    identifierExpectedValue (interpretedCanonicalResult target)
  if givenString == expectedString
    then
      Just
        ( renderCanonicalResult expectedResult
        , renderCanonicalResult givenResult
        )
    else Nothing

identifierGivenValue
  :: CanonicalResult
  -> Maybe (String, CanonicalResult)
identifierGivenValue result =
  case result of
    CanonicalIdentifierType identifierString givenValue ->
      Just (identifierString, givenValue)
    CanonicalAssignment identifierString _ givenValue ->
      Just (identifierString, givenValue)
    CanonicalSpecification source _ -> identifierGivenValue source
    _ -> Nothing

identifierExpectedValue
  :: CanonicalResult
  -> Maybe (String, CanonicalResult)
identifierExpectedValue result =
  case result of
    CanonicalIdentifierType identifierString typeAnnotation ->
      Just (identifierString, typeAnnotation)
    CanonicalAssignment identifierString typeAnnotation _ ->
      Just (identifierString, typeAnnotation)
    CanonicalSpecification _ target -> identifierExpectedValue target
    _ -> Nothing

identifierIntermediateValue
  :: CanonicalResult
  -> Maybe (String, CanonicalResult)
identifierIntermediateValue result =
  case result of
    CanonicalAssignment identifierString typeAnnotation _ ->
      Just (identifierString, typeAnnotation)
    CanonicalSpecification _ intermediate ->
      identifierExpectedValue intermediate
    _ -> Nothing

interpretBinary
  :: ( InterpretedValue
       -> InterpretedValue
       -> Either InterpretingError InterpretedValue
     )
  -> Expression
  -> Expression
  -> Either InterpretingError InterpretedValue
interpretBinary operation left right = do
  leftValue <- interpretExpressionReason left
  rightValue <- interpretExpressionReason right
  operation leftValue rightValue

interpretAtlasMapWith
  :: (Expression -> Either InterpretingError InterpretedValue)
  -> [Expression]
  -> Either InterpretingError InterpretedValue
interpretAtlasMapWith interpret expressions = do
  interpretAtlasMapWithBuilder makeAtlasMap interpret expressions

interpretAtlasMapWithBuilder
  :: (Natural -> [InterpretedValue] -> InterpretedValue)
  -> (Expression -> Either InterpretingError InterpretedValue)
  -> [Expression]
  -> Either InterpretingError InterpretedValue
interpretAtlasMapWithBuilder buildMap interpret expressions = do
  values <- traverse interpret expressions
  let nestingDepths =
        zipWith expressionNestingDepth expressions values
      mapDepth
        | null expressions = 0
        | otherwise = 1 + maximum nestingDepths
      cardinality
        | mapDepth == 0 = 0
        | otherwise = mapDepth + 1
  pure (buildMap cardinality values)

expressionNestingDepth :: Expression -> InterpretedValue -> Natural
expressionNestingDepth expressionValue value =
  case expressionValue of
    AtlasMap _ -> mapNestingDepth
    MapSequence _ -> mapNestingDepth
    MapExpansion _ _ -> mapNestingDepth
    _ -> 0
  where
    mapNestingDepth =
      let cardinality = interpretedMapCardinality (interpretedMap value)
      in if cardinality == 0 then 0 else cardinality - 1

ensureMapLevel :: Expression -> Expression
ensureMapLevel expressionValue =
  case expressionValue of
    AtlasMap _ -> expressionValue
    MapSequence _ -> expressionValue
    MapExpansion _ _ -> expressionValue
    _ -> AtlasMap [expressionValue]
