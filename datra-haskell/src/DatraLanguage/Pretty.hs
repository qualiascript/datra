{-# LANGUAGE OverloadedStrings #-}

-- | Pretty-printing and canonical spelling for Datra syntax.
module DatraLanguage.Pretty
  ( renderExpression
  , renderOperatorExpression
  , renderAsciiStringLiteral
  , renderIdentifierString
  , renderStringTemplate
  ) where

import Data.Char (ord, toUpper)
import Data.Foldable (toList)
import Data.List.NonEmpty (NonEmpty (..))
import DatraLanguage.AST
import DatraLanguage.AST.Operator
  ( Operator (..)
  , ellipsisSymbol
  , operatorCanonicalSymbol
  , skipSourceSymbol
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
prettyOperator (AsciiStringValue value) = pretty (renderAsciiStringLiteral value)
prettyOperator NothingValue =
  pretty (Reserved.reservedSymbolIdentifierString Reserved.NothingSymbol)
prettyOperator (StringTemplateValue parts) =
  pretty (renderOperatorStringTemplate parts)
prettyOperator (GreedyStringTemplateValue operand) =
  prettyUnary GreedyStringTemplateOperator operand
prettyOperator EmptyMap = "()"
prettyOperator (Sequential (expressionValue :| [])) =
  prettyOperator expressionValue
prettyOperator (Sequential expressions) =
  prettyFormFor SequentialOperator (map prettyOperator (toList expressions))
prettyOperator (ArgumentativeMapValue expressions) =
  prettyForm "argumentative-map" (map prettyOperator expressions)
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
prettyOperator (FunValue operand) = prettyForm "fun" [prettyOperator operand]
prettyOperator (GenericIntroductionValue introduction) =
  prettyForm "generic-introduction"
    [ pretty (genericPolaritySymbol
        (genericIntroductionPolarity introduction))
    , prettyGenericIdentifier
        (genericIntroductionIdentifier introduction)
    , prettyOperator (genericIntroductionBound introduction)
    ]
prettyOperator (InModuleValue path value) = prettyForm "in-module" [pretty (renderAsciiStringLiteral path), prettyOperator value]
prettyOperator (ImportValue paths body) = prettyForm "import"
  [ prettyForm "paths" (map (pretty . renderAsciiStringLiteral) paths)
  , prettyOperator body
  ]
prettyOperator (FunctionTypeValue generics input output) =
  prettyFormFor FunctionTypeOperator
    (genericPrefix <> [prettyOperator input, prettyOperator output])
  where
    genericPrefix
      | null generics = []
      | otherwise =
          [prettyForm "generic-prefix" (map prettyGenericBinder generics)]
prettyOperator (FunctionBodyValue bindings result) = prettyForm "do"
  [ prettyForm "bindings" (map prettyDeclaration bindings)
  , prettyOperator result
  ]
prettyOperator (FunctionApplicationValue function input) = prettyBinary ApplicationOperator function input
prettyOperator (DeclarationValue declaration) =
  prettyDeclaration declaration
prettyOperator (BeginValue bindings result) =
  prettyForm "begin"
    [prettyForm "bindings" (map prettyDeclaration bindings), prettyOperator result]
prettyOperator (IdentifierReferenceValue (IdentifierString name)) =
  prettyForm "ref" [pretty (renderAsciiStringLiteral name)]
prettyOperator (LookupValue operand) =
  prettyUnary LookupOperator operand
prettyOperator (Multiply left right) =
  prettyBinary MultiplicationOperator left right
prettyOperator (Power left right) =
  prettyBinary ExponentiationOperator left right
prettyOperator (Concatenate left right) =
  prettyBinary ConcatenationOperator left right
prettyOperator (ScopeAccessValue source body) =
  prettyForm "." [prettyOperator source, prettyOperator body]
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
  IdentifierReferenceValue (IdentifierString identifierString) ->
    pretty (renderIdentifierString identifierString)
  StringTemplateValue parts ->
    pretty (renderStringTemplate renderOperatorExpression (const Nothing) parts)
  _ -> prettyOperator name

prettyDeclaration
  :: DependentDeclaration OperatorExpression
  -> Doc annotation
prettyDeclaration declaration =
  applyLet (applyDefinition (applyCanonical base))
  where
      implementation = dependentDeclarationImplementation declaration
      base = case dependentDeclarationHead declaration of
        SimpleIdentifierDeclarationHead name -> prettyOperator
          (Specify implementation
            (DependentArgumentValue
              (IdentifierReferenceValue name)
              Nothing))
        StringTemplateDeclarationHead parts -> prettyOperator
          (Specify implementation
            (DependentArgumentValue
              (StringTemplateValue parts)
              Nothing))
        EvaluatedDeclarationHead expressionValue -> prettyForm
          (operatorCanonicalSymbol AssignmentOperator)
          [prettyOperator expressionValue, prettyOperator implementation]
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

prettyForm :: String -> [Doc annotation] -> Doc annotation
prettyForm headName operands =
  parens (hsep (pretty headName : operands))

prettyGenericBinder
  :: GenericBinder OperatorExpression
  -> Doc annotation
prettyGenericBinder binder =
  prettyForm "generic-binder"
    [ pretty (genericBinderIdNatural (genericBinderId binder))
    , pretty (genericPolaritySymbol (genericBinderPolarity binder))
    , prettyGenericIdentifier (genericBinderIdentifier binder)
    , prettyOperator (genericBinderBound binder)
    ]

prettyGenericIdentifier :: GenericIdentifier -> Doc annotation
prettyGenericIdentifier identifier =
  prettyOperator
    (if genericIdentifierNameOptional identifier
      then OptionalValue reference
      else reference)
  where
    reference = IdentifierReferenceValue (genericIdentifierName identifier)

genericBinderIdNatural :: GenericBinderId -> Natural
genericBinderIdNatural (GenericBinderId value) = value

genericPolaritySymbol :: GenericPolarity -> String
genericPolaritySymbol GenericProduct = "&"
genericPolaritySymbol GenericSum = "^"

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
  | isIdentifierValue value = '$' : value
renderAsciiStringLiteral value = renderStandardStringLiteral value

-- | Render a canonical identifier expression with its compact bare spelling.
renderIdentifierString :: String -> String
renderIdentifierString value
  | isIdentifierValue value = value
renderIdentifierString value = renderStandardStringLiteral value

renderStandardStringLiteral :: String -> String
renderStandardStringLiteral value =
  '"' : renderStringLiteralContents value <> "\""

renderStringLiteralContents :: String -> String
renderStringLiteralContents = foldr escape ""
  where
    escape '\n' rest = '\\' : 'n' : rest
    escape '"' rest = '\\' : '"' : rest
    escape '\\' rest = '\\' : '\\' : rest
    escape '#' rest = '\\' : '#' : rest
    escape '%' rest = '\\' : '%' : rest
    escape character rest
      | isAsciiByte character && not (isKeyboardCharacter character) =
          '\\' : hexadecimalByte character <> rest
    escape character rest = character : rest

    hexadecimalByte character =
      case map toUpper (showHex (ord character) "") of
        [digit] -> ['0', digit]
        digits -> digits

    isAsciiByte character = ord character < 256
    isKeyboardCharacter character =
      0x20 <= ord character && ord character <= 0x7e

renderOperatorStringTemplate
  :: [StringTemplatePart OperatorExpression]
  -> String
renderOperatorStringTemplate =
  renderStringTemplate
    renderOperatorExpression
    compactOperatorStringInterpolation

renderStringTemplate
  :: (expression -> String)
  -> (expression -> Maybe String)
  -> [StringTemplatePart expression]
  -> String
renderStringTemplate renderExpressionValue compactInterpolation parts =
  '"' : foldr renderPart "\"" parts
  where
    renderPart (StringTemplateLiteral value) rest =
      renderStringLiteralContents value <> rest
    renderPart (StringTemplateInterpolation expressionValue) rest =
      renderInterpolation "%" expressionValue rest

    renderInterpolation prefix expressionValue rest =
      case compactInterpolation expressionValue of
        Just symbol
          | compactInterpolationBoundary rest ->
              prefix <> symbol <> rest
        Nothing ->
          prefix <> "(" <> renderExpressionValue expressionValue <> ")" <> rest
        Just _ ->
          prefix <> "(" <> renderExpressionValue expressionValue <> ")" <> rest

    compactInterpolationBoundary [] = True
    compactInterpolationBoundary (character : _) =
      not (isIdentifierCharacter character)

compactOperatorStringInterpolation
  :: OperatorExpression
  -> Maybe String
compactOperatorStringInterpolation expressionValue =
  case expressionValue of
    NothingValue -> reserved Reserved.NothingSymbol
    NaturalTypeValue -> reserved Reserved.NaturalTypeSymbol
    IntegerTypeValue -> reserved Reserved.IntegerTypeSymbol
    BooleanValue False -> reserved Reserved.FalseSymbol
    BooleanValue True -> reserved Reserved.TrueSymbol
    BooleanTypeValue -> reserved Reserved.BooleanTypeSymbol
    _ -> Nothing
  where
    reserved = Just . Reserved.reservedSymbolIdentifierString
