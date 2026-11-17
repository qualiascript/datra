{-# LANGUAGE OverloadedStrings #-}

-- | Pretty-printing and canonical spelling for Datra syntax.
module DatraLanguage.Pretty
  ( renderExpression
  , renderOperatorExpression
  , renderAsciiStringLiteral
  , renderIdentifierString
  , renderStringTemplate
  , renderLiteralTemplate
  ) where

import Data.Char (ord, toUpper)
import Data.Foldable (toList)
import Data.List.NonEmpty (NonEmpty (..))
import DatraLanguage.AST
import DatraLanguage.AST.CanonicalForm
  ( CanonicalForm (..), canonicalFormName )
import DatraLanguage.AST.Operator
  ( Operator (..)
  , ellipsisSymbol
  , operatorCanonicalSymbol
  , operatorPreferredSymbol
  , SourceCharacterOperator
      ( EitherCharacterOperator
      , IdentifierExpressionCharacterOperator
      , OptionalCharacterOperator
      )
  , sourceOperatorCharacter
  , skipSourceSymbol
  )
import DatraLanguage.ConcreteSyntax
  ( StructuralDelimiter (..)
  , commentCharacter
  , delimiterCharacter
  , delimiterText
  , escapeCharacter
  , interpolationCharacter
  , literalTemplateDelimiterCharacter
  , sourceSpace
  , stringQuoteCharacter
  )
import DatraLanguage.AST.Reserved qualified as Reserved
import DatraLanguage.Identifier (isIdentifierCharacter, isIdentifierValue)
import Numeric (showHex)
import Numeric.Natural (Natural)
import Prettyprinter
  ( Doc
  , hsep
  , layoutCompact
  , parens
  , pretty
  )
import Prettyprinter.Render.String (renderString)

-- | Lower map notation and render an unevaluated expression in canonical AST
-- operator notation.
renderExpression :: Expression -> String
renderExpression =
  renderOperatorExpression . toOperatorExpression . normalizeExpression

renderOperatorExpression :: OperatorExpression -> String
renderOperatorExpression =
  renderString . layoutCompact . prettyOperator

prettyOperator :: OperatorExpression -> Doc annotation
prettyOperator (NaturalValue value) = pretty value
prettyOperator EllipsisValue = pretty ellipsisSymbol
prettyOperator SkipValue = pretty skipSourceSymbol
prettyOperator (AsciiStringValue value) =
  pretty (renderStandardStringLiteral value)
prettyOperator NothingValue =
  pretty (Reserved.reservedSymbolIdentifierString Reserved.NothingSymbol)
prettyOperator (StringTemplateValue parts) =
  pretty (renderOperatorStringTemplate parts)
prettyOperator (IdentifierExpressionValue operand) =
  prettyFormFor IdentifierExpressionOperator [prettyOperator operand]
prettyOperator (LiteralTemplateExpressionValue body) =
  pretty (literalTemplateDelimiterCharacter
    : renderLiteralTemplate body <> [literalTemplateDelimiterCharacter])
prettyOperator EmptyMap = pretty
  (delimiterText OpenParenthesis <> delimiterText CloseParenthesis)
prettyOperator (Sequential (expressionValue :| [])) =
  prettyOperator expressionValue
prettyOperator (Sequential expressions) =
  prettyFormFor SequentialOperator (map prettyOperator (toList expressions))
prettyOperator (ArgumentativeMapValue expressions) =
  prettyCanonicalForm ArgumentativeMapForm (map prettyOperator expressions)
prettyOperator (Expansion left right) =
  prettyBinary ExpansionOperator left right
prettyOperator (Range lowerBound upperBound) =
  prettyBinary RangeOperator lowerBound upperBound
prettyOperator (RangePlus lowerBound) =
  prettyUnary RangePlusOperator lowerBound
prettyOperator (RangeMinus upperBound) =
  prettyUnary RangeMinusOperator upperBound
prettyOperator (InclusiveNaturalRange origin target) =
  prettyForm (Reserved.reservedSymbolIdentifierString Reserved.RangeSymbol)
    [pretty origin, reservedWordDoc Reserved.ToWord, pretty target]
prettyOperator (InclusiveNaturalRangeUpwards origin) =
  prettyForm (Reserved.reservedSymbolIdentifierString Reserved.RangeSymbol)
    [pretty origin, reservedWordDoc Reserved.UpwardsWord]
prettyOperator (InclusiveValuedNaturalRange origin target) =
  prettyForm (Reserved.reservedSymbolIdentifierString Reserved.FromSymbol)
    [pretty origin, reservedWordDoc Reserved.ToWord, pretty target]
prettyOperator (InclusiveValuedNaturalRangeUpwards origin) =
  prettyForm (Reserved.reservedSymbolIdentifierString Reserved.FromSymbol)
    [pretty origin, reservedWordDoc Reserved.UpwardsWord]
prettyOperator AnyTypeValue = reservedSymbolDoc Reserved.AnyTypeSymbol
prettyOperator NaturalTypeValue = reservedSymbolDoc Reserved.NaturalTypeSymbol
prettyOperator (InclusiveIntegerRange origin target) =
  prettyForm (Reserved.reservedSymbolIdentifierString Reserved.RangeSymbol)
    [ prettyInteger origin
    , reservedWordDoc Reserved.ToWord
    , prettyInteger target
    ]
prettyOperator (InclusiveIntegerRangeUpwards origin) =
  prettyForm (Reserved.reservedSymbolIdentifierString Reserved.RangeSymbol)
    [prettyInteger origin, reservedWordDoc Reserved.UpwardsWord]
prettyOperator (InclusiveIntegerRangeDownwards origin) =
  prettyForm (Reserved.reservedSymbolIdentifierString Reserved.RangeSymbol)
    [prettyInteger origin, reservedWordDoc Reserved.DownwardsWord]
prettyOperator (InclusiveValuedIntegerRange origin target) =
  prettyForm (Reserved.reservedSymbolIdentifierString Reserved.FromSymbol)
    [ prettyInteger origin
    , reservedWordDoc Reserved.ToWord
    , prettyInteger target
    ]
prettyOperator (InclusiveValuedIntegerRangeUpwards origin) =
  prettyForm (Reserved.reservedSymbolIdentifierString Reserved.FromSymbol)
    [prettyInteger origin, reservedWordDoc Reserved.UpwardsWord]
prettyOperator (InclusiveValuedIntegerRangeDownwards origin) =
  prettyForm (Reserved.reservedSymbolIdentifierString Reserved.FromSymbol)
    [prettyInteger origin, reservedWordDoc Reserved.DownwardsWord]
prettyOperator IntegerTypeValue = reservedSymbolDoc Reserved.IntegerTypeSymbol
prettyOperator (BooleanValue False) =
  pretty (Reserved.reservedSymbolIdentifierString Reserved.FalseSymbol)
prettyOperator (BooleanValue True) =
  pretty (Reserved.reservedSymbolIdentifierString Reserved.TrueSymbol)
prettyOperator BooleanTypeValue = reservedSymbolDoc Reserved.BooleanTypeSymbol
prettyOperator (EitherValue left right) =
  prettyBinary EitherOperator left right
prettyOperator (OptionalValue operand) =
  prettyUnary OptionalOperator operand
prettyOperator (MaybeThenValue optional branch) =
  prettyForm (operatorCanonicalSymbol MaybeThenOperator)
    [prettyOperator optional, prettyOperator branch]
prettyOperator (ConditionalValue condition consequent alternative) =
  prettyForm
    (Reserved.reservedSymbolIdentifierString Reserved.IfSymbol)
    [ prettyOperator condition
    , prettyOperator consequent
    , prettyOperator alternative
    ]
prettyOperator (Add left right) =
  prettyBinary AdditionOperator left right
prettyOperator (Subtract left right) =
  prettyBinary SubtractionOperator left right
prettyOperator (Positive operand) =
  prettyUnary AdditionOperator operand
prettyOperator (Negate operand) =
  prettyUnary MinusOperator operand
prettyOperator (Less left right) =
  prettyBinary LessThanOperator left right
prettyOperator (LessOrEqual left right) =
  prettyBinary LessThanOrEqualOperator left right
prettyOperator (Greater left right) =
  prettyBinary GreaterThanOperator left right
prettyOperator (GreaterOrEqual left right) =
  prettyBinary GreaterThanOrEqualOperator left right
prettyOperator (Equal left right) =
  prettyBinary EqualityOperator left right
prettyOperator (NotEqual left right) =
  prettyBinary InequalityOperator left right
prettyOperator (CoalizationValue operand) =
  prettyUnary CoalizationOperator operand
prettyOperator (FunValue operand) =
  prettyCanonicalForm FunctionForm [prettyOperator operand]
prettyOperator (GenericIntroductionValue introduction) =
  prettyCanonicalForm GenericIntroductionForm
    (pretty (genericPolaritySymbol
      (genericArgumentPolarity introduction))
      : prettyGenericArgument introduction)
prettyOperator (InModuleValue path value) = prettyCanonicalForm InModuleForm
  [pretty (renderAsciiStringLiteral path), prettyOperator value]
prettyOperator (ImportValue paths body) = prettyCanonicalForm ImportForm
  [ prettyCanonicalForm ImportPathsForm
      (map (pretty . renderAsciiStringLiteral) paths)
  , prettyOperator body
  ]
prettyOperator (FunctionTypeValue generics input output) =
  prettyFormFor FunctionTypeOperator
    (genericPrefix <> [prettyOperator input, prettyOperator output])
  where
    genericPrefix
      | null generics = []
      | otherwise =
          [prettyCanonicalForm GenericPrefixForm (map prettyGenericBinder generics)]
prettyOperator (FunctionBodyValue bindings result) =
  prettyWordForm Reserved.DoWord
  [ prettyCanonicalForm BindingsForm (map prettyDeclaration bindings)
  , prettyOperator result
  ]
prettyOperator (FunctionApplicationValue function input) = prettyBinary ApplicationOperator function input
prettyOperator (DeclarationValue declaration) =
  prettyDeclaration declaration
prettyOperator (BeginValue bindings result) =
  prettyWordForm Reserved.BeginWord
    [ prettyCanonicalForm BindingsForm (map prettyDeclaration bindings)
    , prettyOperator result
    ]
prettyOperator (IdentifierReferenceValue (SimpleIdentifierString name)) =
  prettyCanonicalForm IdentifierReferenceForm
    [pretty (renderAsciiStringLiteral name)]
prettyOperator (UnresolvedSyntaxValue literal) =
  prettyCanonicalForm UnresolvedSyntaxForm
    [pretty (renderAsciiStringLiteral literal)]
prettyOperator ElidedSyntaxValue = prettyCanonicalForm ElidedSyntaxForm []
prettyOperator (SyntaxRemainderValue source) =
  prettyCanonicalForm SyntaxRemainderForm
    [pretty (renderAsciiStringLiteral source)]
prettyOperator (LookupValue operand) =
  prettyUnary LookupOperator operand
prettyOperator (Multiply left right) =
  prettyBinary MultiplicationOperator left right
prettyOperator (Power left right) =
  prettyBinary ExponentiationOperator left right
prettyOperator (Concatenate left right) =
  prettyBinary ConcatenationOperator left right
prettyOperator (ScopeAccessValue source body) =
  prettyForm (operatorCanonicalSymbol ScopeAccessOperator)
    [prettyOperator source, prettyOperator body]
prettyOperator (Access left right) =
  prettyBinary AccessOperator left right
prettyOperator
    (Specify given (DependentArgumentValue name typeAnnotation)) =
  prettyForm
    (operatorCanonicalSymbol AssignmentOperator)
    (prettyDependentArgumentName name :
      maybe [] ((: []) . prettyOperator) typeAnnotation
        <> [prettyOperator given])
prettyOperator (Specify left right) =
  prettyBinary SpecificationOperator left right
prettyOperator (OverloadValue left right) =
  prettyBinary OverloadOperator left right
prettyOperator (SafeOverloadValue left right) =
  prettyBinary SafeOverloadOperator left right
prettyOperator (DependentArgumentValue name (Just typeAnnotation)) =
  prettyForm
    (operatorCanonicalSymbol DependentArgumentTypeOperator)
    [prettyDependentArgumentName name, prettyOperator typeAnnotation]
prettyOperator (DependentArgumentValue name Nothing) =
  prettyDependentArgumentName name

prettyDependentArgumentName :: OperatorExpression -> Doc annotation
prettyDependentArgumentName name = case name of
  IdentifierReferenceValue (SimpleIdentifierString identifierString) ->
    pretty (renderIdentifierString identifierString)
  StringTemplateValue parts ->
    pretty (renderStringTemplate
      renderOperatorExpression operatorStringLiteral (const Nothing) parts)
  _ -> prettyOperator name

prettyDeclaration
  :: DependentDeclaration OperatorExpression
  -> Doc annotation
prettyDeclaration declaration =
  applyLet (applyDefinition (applyCanonical base))
  where
      implementation = dependentDeclarationImplementation declaration
      base = prettyForm
        (operatorCanonicalSymbol AssignmentOperator)
        [ prettyOperator (identifierHeadValue
            (dependentDeclarationHead declaration))
        , prettyOperator implementation
        ]
      applyCanonical
        | dependentDeclarationIsCanonicalValue declaration =
            prettyFormFor ValOperator . pure
        | otherwise = id
      applyDefinition
        | dependentDeclarationIsDefinition declaration =
            prettyFormFor DefOperator . pure
        | otherwise = id
      applyLet
        | dependentDeclarationIsLet declaration =
            prettyFormFor LetOperator . pure
        | otherwise = id

identifierHeadValue :: IdentifierExpression OperatorExpression -> OperatorExpression
identifierHeadValue headValue = case headValue of
  IdentifierExpressionBody body -> IdentifierExpressionValue body
  LiteralTemplateIdentifier body -> LiteralTemplateExpressionValue body

renderLiteralTemplate :: LiteralTemplate OperatorExpression -> String
renderLiteralTemplate (LiteralTemplate expressionValue) =
  renderTemplateExpression expressionValue
  where
    renderTemplateExpression composition = case composition of
      IdentifierComposition sequenceValue -> renderTemplateSequence sequenceValue
      EitherExpression left right ->
        renderTemplateExpression left
          <> sourceSpace
          <> operatorPreferredSymbol EitherOperator
          <> sourceSpace
          <> renderTemplateExpression right
      OptionalExpression value ->
        groupedExpression value <> operatorPreferredSymbol OptionalOperator

    renderTemplateSequence (LiteralTemplateSequence parts) =
      unwords (map renderTemplatePart (toList parts))

    renderTemplatePart composition = case composition of
      IdentifierComposition atom -> renderTemplateAtom atom
      OptionalExpression value ->
        renderPartOperand value <> operatorPreferredSymbol OptionalOperator
      EitherExpression {} -> groupedPart composition

    renderPartOperand composition = case composition of
      IdentifierComposition atom -> renderTemplateAtom atom
      _ -> groupedPart composition

    renderTemplateAtom (LiteralTemplateLiteralAtom literal) =
      renderTemplateLiteral literal
    renderTemplateAtom (LiteralTemplateCaptureAtom target) =
      interpolationCharacter : renderCapture target
    renderTemplateAtom (LiteralTemplateGroupAtom grouped) =
      delimiterText OpenParenthesis
        <> renderLiteralTemplate grouped
        <> delimiterText CloseParenthesis

    groupedExpression value =
      delimiterText OpenParenthesis
        <> renderTemplateExpression value
        <> delimiterText CloseParenthesis

    groupedPart value = delimiterText OpenParenthesis
      <> renderPartExpression value
      <> delimiterText CloseParenthesis

    renderPartExpression composition = case composition of
      IdentifierComposition atom -> renderTemplateAtom atom
      EitherExpression left right ->
        renderPartExpression left
          <> sourceSpace
          <> operatorPreferredSymbol EitherOperator
          <> sourceSpace
          <> renderPartExpression right
      OptionalExpression value ->
        renderPartOperand value <> operatorPreferredSymbol OptionalOperator

    renderCapture target@(IdentifierReferenceValue _) =
      renderOperatorExpression target
    renderCapture target =
      delimiterText OpenParenthesis
        <> renderOperatorExpression target
        <> delimiterText CloseParenthesis

renderTemplateLiteral :: LiteralTemplateLiteral -> String
renderTemplateLiteral literal = case literal of
  IdentifierTemplateLiteral (SimpleIdentifierString value) -> value
  SymbolTemplateLiteral (SymbolLiteral value) ->
    concatMap renderTemplateSymbol value
  where
    renderTemplateSymbol character
      | character `elem` templateStructuralCharacters =
          [escapeCharacter, character]
      | otherwise = [character]
    templateStructuralCharacters =
      [ interpolationCharacter
      , delimiterCharacter OpenParenthesis
      , delimiterCharacter CloseParenthesis
      , sourceOperatorCharacter OptionalCharacterOperator
      , sourceOperatorCharacter EitherCharacterOperator
      , literalTemplateDelimiterCharacter
      , escapeCharacter
      ]

prettyUnary
  :: Operator
  -> OperatorExpression
  -> Doc annotation
prettyUnary operator operand =
  prettyFormFor operator [prettyOperator operand]

prettyBinary
  :: Operator
  -> OperatorExpression
  -> OperatorExpression
  -> Doc annotation
prettyBinary operator left right =
  prettyFormFor operator [prettyOperator left, prettyOperator right]

prettyFormFor :: Operator -> [Doc annotation] -> Doc annotation
prettyFormFor operator = prettyForm (operatorCanonicalSymbol operator)

prettyWordForm :: Reserved.ReservedWord -> [Doc annotation] -> Doc annotation
prettyWordForm word = prettyForm (Reserved.reservedWordText word)

prettyCanonicalForm
  :: CanonicalForm
  -> [Doc annotation]
  -> Doc annotation
prettyCanonicalForm form = prettyForm (canonicalFormName form)

prettyForm :: String -> [Doc annotation] -> Doc annotation
prettyForm headName operands =
  parens (hsep (pretty headName : operands))

prettyGenericBinder
  :: GenericBinder OperatorExpression
  -> Doc annotation
prettyGenericBinder binder =
  prettyCanonicalForm GenericBinderForm
    ( [ pretty (genericBinderIdNatural (genericBinderId binder))
      , pretty (genericPolaritySymbol
          (genericArgumentPolarity (genericBinderArgument binder)))
      ] <> prettyGenericArgument (genericBinderArgument binder)
    )

prettyGenericArgument
  :: GenericArgument OperatorExpression
  -> [Doc annotation]
prettyGenericArgument argument =
  [ prettyOperator name
  , prettyOperator (genericArgumentBound argument)
  ]
  where
    reference = IdentifierReferenceValue (genericArgumentName argument)
    name
      | genericArgumentOptional argument = OptionalValue reference
      | otherwise = reference

genericBinderIdNatural :: GenericBinderId -> Natural
genericBinderIdNatural (GenericBinderId value) = value

genericPolaritySymbol :: GenericPolarity -> String
genericPolaritySymbol GenericProduct =
  operatorCanonicalSymbol GenericProductOperator
genericPolaritySymbol GenericSum =
  operatorCanonicalSymbol ExponentiationOperator

prettyInteger :: Integer -> Doc annotation
prettyInteger = pretty

reservedWordDoc :: Reserved.ReservedWord -> Doc annotation
reservedWordDoc = pretty . Reserved.reservedWordText

reservedSymbolDoc :: Reserved.ReservedSymbol -> Doc annotation
reservedSymbolDoc = pretty . Reserved.reservedSymbolIdentifierString

-- | Render an identifier string when possible, otherwise use the standard
-- quoted spelling. Standard strings leave the keyboard-visible ASCII range
-- literal and use hexadecimal escapes for every other byte except newline.
renderAsciiStringLiteral :: String -> String
renderAsciiStringLiteral value
  | isIdentifierValue value =
      sourceOperatorCharacter IdentifierExpressionCharacterOperator : value
renderAsciiStringLiteral value = renderStandardStringLiteral value

-- | Render a canonical identifier expression with its compact bare spelling.
renderIdentifierString :: String -> String
renderIdentifierString value
  | isIdentifierValue value = value
renderIdentifierString value = renderStandardStringLiteral value

renderStandardStringLiteral :: String -> String
renderStandardStringLiteral value =
  stringQuoteCharacter : renderStringLiteralContents value
    <> [stringQuoteCharacter]

renderStringLiteralContents :: String -> String
renderStringLiteralContents = foldr escape ""
  where
    escape '\n' rest = escapeCharacter : 'n' : rest
    escape character rest
      | character == stringQuoteCharacter =
          escapeCharacter : stringQuoteCharacter : rest
      | character == escapeCharacter =
          escapeCharacter : escapeCharacter : rest
      | character == commentCharacter =
          escapeCharacter : commentCharacter : rest
      | character == interpolationCharacter =
          escapeCharacter : interpolationCharacter : rest
    escape character rest
      | isAsciiByte character && not (isKeyboardCharacter character) =
          escapeCharacter : hexadecimalByte character <> rest
    escape character rest = character : rest

    hexadecimalByte character =
      case map toUpper (showHex (ord character) "") of
        [digit] -> ['0', digit]
        digits -> digits

    isAsciiByte character = ord character < 256
    isKeyboardCharacter character =
      0x20 <= ord character && ord character <= 0x7e

renderOperatorStringTemplate
  :: [StringTemplateInterpolation OperatorExpression]
  -> String
renderOperatorStringTemplate =
  renderStringTemplate
    renderOperatorExpression
    operatorStringLiteral
    compactOperatorStringInterpolation

renderStringTemplate
  :: (expression -> String)
  -> (expression -> Maybe String)
  -> (expression -> Maybe String)
  -> [StringTemplateInterpolation expression]
  -> String
renderStringTemplate renderExpressionValue literalInterpolation
    compactInterpolation parts =
  stringQuoteCharacter : foldr renderPart [stringQuoteCharacter] parts
  where
    renderPart (StringTemplateInterpolation expressionValue) rest =
      case literalInterpolation expressionValue of
        Just value -> renderStringLiteralContents value <> rest
        Nothing -> renderInterpolation [interpolationCharacter] expressionValue rest

    renderInterpolation prefix expressionValue rest =
      case compactInterpolation expressionValue of
        Just symbol
          | compactInterpolationBoundary rest ->
              prefix <> symbol <> rest
        Nothing ->
          prefix <> delimiterText OpenParenthesis <>
            renderExpressionValue expressionValue <>
            delimiterText CloseParenthesis <> rest
        Just _ ->
          prefix <> delimiterText OpenParenthesis <>
            renderExpressionValue expressionValue <>
            delimiterText CloseParenthesis <> rest

    compactInterpolationBoundary [] = True
    compactInterpolationBoundary (character : _) =
      not (isIdentifierCharacter character)

operatorStringLiteral :: OperatorExpression -> Maybe String
operatorStringLiteral (AsciiStringValue value) = Just value
operatorStringLiteral _ = Nothing

compactOperatorStringInterpolation
  :: OperatorExpression
  -> Maybe String
compactOperatorStringInterpolation expressionValue =
  case expressionValue of
    NothingValue -> reserved Reserved.NothingSymbol
    AnyTypeValue -> reserved Reserved.AnyTypeSymbol
    NaturalTypeValue -> reserved Reserved.NaturalTypeSymbol
    IntegerTypeValue -> reserved Reserved.IntegerTypeSymbol
    BooleanValue False -> reserved Reserved.FalseSymbol
    BooleanValue True -> reserved Reserved.TrueSymbol
    BooleanTypeValue -> reserved Reserved.BooleanTypeSymbol
    _ -> Nothing
  where
    reserved = Just . Reserved.reservedSymbolIdentifierString
