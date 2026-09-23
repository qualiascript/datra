{-# LANGUAGE OverloadedStrings #-}

module DatraLanguage.AST
  ( IdentifierString (..)
  , StringTemplatePart (..)
  , Expression (..)
  , OperatorExpression (..)
  , toOperatorExpression
  , normalizeExpression
  , renderExpression
  , renderOperatorExpression
  , renderAsciiStringLiteral
  , renderStringTemplate
  , renderIdentifierString
  , isCompactStringLiteral
  , isReservedIdentifierString
  ) where

import Data.Char (ord, toUpper)
import DatraLanguage.AST.Operator
  ( Operator (..)
  , ellipsisSymbol
  , operatorCanonicalSymbol
  , operatorSourceSymbol
  )
import DatraLanguage.AST.Reserved (isReservedIdentifierString)
import DatraLanguage.AST.Reserved qualified as Reserved
import Numeric.Natural (Natural)
import Numeric (showHex)
import Prettyprinter
  ( Doc
  , hsep
  , layoutCompact
  , parens
  , pretty
  )
import Prettyprinter.Render.String (renderString)

-- | The identifier string used by identifier operations. It is deliberately
-- distinct from an expression: the parser is the boundary which validates
-- its spelling, and an arbitrary expression can never inhabit this field.
newtype IdentifierString = IdentifierString
  { identifierStringText :: String
  }
  deriving (Eq, Show)

-- | One source-order component of a quoted string template. Literal chunks
-- are already decoded by the parser; interpolations retain their unevaluated
-- expressions until the interpreter applies the internal @toString@ map.
data StringTemplatePart expression
  = StringTemplateLiteral String
  | StringTemplateInterpolation expression
  deriving (Eq, Show)

-- | Unevaluated Datra syntax. Capabilities and silent coercions are resolved
-- later by the type checker and interpreter, not while constructing the AST.
data Expression
  = EllipsisNatural Natural
  | EllipsisLiteral
  | AsciiStringLiteral String
  | NothingLiteral
  | StringTemplate [StringTemplatePart Expression]
  | StringType
  | AtlasMap [Expression]
  | MapSequence [Expression]
  | MapExpansion Expression Expression
  | SuperEllipsisRange Expression Expression
  | SuperEllipsisRangePlus Expression
  | SuperEllipsisRangeMinus Expression
  | NaturalRange Natural Natural
  | NaturalRangeUpwards Natural
  | ValuedNaturalRange Natural Natural
  | ValuedNaturalRangeUpwards Natural
  | NaturalType
  | IntegerRange Integer Integer
  | IntegerRangeUpwards Integer
  | IntegerRangeDownwards Integer
  | ValuedIntegerRange Integer Integer
  | ValuedIntegerRangeUpwards Integer
  | ValuedIntegerRangeDownwards Integer
  | IntegerType
  | BooleanLiteral Bool
  | BooleanType
  | EitherType Expression Expression
  | OptionalType Expression
  | Conditional Expression Expression Expression
  | Addition Expression Expression
  | Subtraction Expression Expression
  | Minus Expression
  | Subfederation Expression Expression
  | Equality Expression Expression
  | BooleanAnd Expression Expression
  | BooleanOr Expression Expression
  | BooleanNot Expression
  | Multiplication Expression Expression
  | Exponentiation Expression Expression
  | MapConcatenation Expression Expression
  | MapAccess Expression Expression
  | MapSpecification Expression Expression
  | IdentifierOperation
      { identifierOperationString :: IdentifierString
      , identifierOperationTypeAnnotation :: Expression
      , identifierOperationGivenValue :: Maybe Expression
      }
  deriving (Eq, Show)

-- | Lower map notation and render the unevaluated AST using canonical AST
-- operator notation.
renderExpression :: Expression -> String
renderExpression =
  renderOperatorExpression . toOperatorExpression . normalizeExpression

data OperatorExpression
  = NaturalValue Natural
  | EllipsisValue
  | AsciiStringValue String
  | NothingValue
  | StringTemplateValue [StringTemplatePart OperatorExpression]
  | StringTypeValue
  | EmptyMap
  | Sequential [OperatorExpression]
  | Expansion OperatorExpression OperatorExpression
  | Range OperatorExpression OperatorExpression
  | RangePlus OperatorExpression
  | RangeMinus OperatorExpression
  | InclusiveNaturalRange Natural Natural
  | InclusiveNaturalRangeUpwards Natural
  | InclusiveValuedNaturalRange Natural Natural
  | InclusiveValuedNaturalRangeUpwards Natural
  | NaturalTypeValue
  | InclusiveIntegerRange Integer Integer
  | InclusiveIntegerRangeUpwards Integer
  | InclusiveIntegerRangeDownwards Integer
  | InclusiveValuedIntegerRange Integer Integer
  | InclusiveValuedIntegerRangeUpwards Integer
  | InclusiveValuedIntegerRangeDownwards Integer
  | IntegerTypeValue
  | BooleanValue Bool
  | BooleanTypeValue
  | EitherValue OperatorExpression OperatorExpression
  | OptionalValue OperatorExpression
  | ConditionalValue
      OperatorExpression
      OperatorExpression
      OperatorExpression
  | Add OperatorExpression OperatorExpression
  | Subtract OperatorExpression OperatorExpression
  | Negate OperatorExpression
  | IsSubfederation OperatorExpression OperatorExpression
  | Equal OperatorExpression OperatorExpression
  | And OperatorExpression OperatorExpression
  | Or OperatorExpression OperatorExpression
  | Not OperatorExpression
  | Multiply OperatorExpression OperatorExpression
  | Power OperatorExpression OperatorExpression
  | Concatenate OperatorExpression OperatorExpression
  | Access OperatorExpression OperatorExpression
  | Specify OperatorExpression OperatorExpression
  | IdentifierOperationValue
      { operatorIdentifierString :: IdentifierString
      , operatorTypeAnnotation :: OperatorExpression
      , operatorGivenValue :: Maybe OperatorExpression
      }
  deriving (Eq, Show)

toOperatorExpression :: Expression -> OperatorExpression
toOperatorExpression = lower

renderOperatorExpression :: OperatorExpression -> String
renderOperatorExpression =
  renderString . layoutCompact . prettyOperator

normalizeExpression :: Expression -> Expression
normalizeExpression (EllipsisNatural value) = EllipsisNatural value
normalizeExpression EllipsisLiteral = EllipsisLiteral
normalizeExpression (AsciiStringLiteral value) = AsciiStringLiteral value
normalizeExpression NothingLiteral = NothingLiteral
normalizeExpression (StringTemplate parts) =
  StringTemplate (map normalizeStringTemplatePart parts)
normalizeExpression StringType = StringType
normalizeExpression (AtlasMap expressions) =
  normalizeSequence AtlasMap expressions
normalizeExpression (MapSequence expressions) =
  normalizeSequence MapSequence expressions
normalizeExpression (MapExpansion left right) =
  normalizeExpansion
    (normalizeExpression left)
    (normalizeExpression right)
normalizeExpression (SuperEllipsisRange lowerBound upperBound) =
  SuperEllipsisRange
    (normalizeExpression lowerBound)
    (normalizeExpression upperBound)
normalizeExpression (SuperEllipsisRangePlus lowerBound) =
  SuperEllipsisRangePlus (normalizeExpression lowerBound)
normalizeExpression (SuperEllipsisRangeMinus upperBound) =
  SuperEllipsisRangeMinus (normalizeExpression upperBound)
normalizeExpression (NaturalRange origin target) = NaturalRange origin target
normalizeExpression (NaturalRangeUpwards origin) = NaturalRangeUpwards origin
normalizeExpression (ValuedNaturalRange origin target) =
  ValuedNaturalRange origin target
normalizeExpression (ValuedNaturalRangeUpwards origin) =
  ValuedNaturalRangeUpwards origin
normalizeExpression NaturalType = NaturalType
normalizeExpression (IntegerRange origin target) = IntegerRange origin target
normalizeExpression (IntegerRangeUpwards origin) = IntegerRangeUpwards origin
normalizeExpression (IntegerRangeDownwards origin) = IntegerRangeDownwards origin
normalizeExpression (ValuedIntegerRange origin target) =
  ValuedIntegerRange origin target
normalizeExpression (ValuedIntegerRangeUpwards origin) =
  ValuedIntegerRangeUpwards origin
normalizeExpression (ValuedIntegerRangeDownwards origin) =
  ValuedIntegerRangeDownwards origin
normalizeExpression IntegerType = IntegerType
normalizeExpression (BooleanLiteral value) = BooleanLiteral value
normalizeExpression BooleanType = BooleanType
normalizeExpression (EitherType left right) =
  normalizeEither
    (normalizeExpression left)
    (normalizeExpression right)
normalizeExpression (OptionalType operand) =
  OptionalType (normalizeExpression operand)
normalizeExpression (Conditional condition consequent alternative) =
  Conditional
    (normalizeExpression condition)
    (normalizeExpression consequent)
    (normalizeExpression alternative)
normalizeExpression (Addition left right) =
  Addition (normalizeExpression left) (normalizeExpression right)
normalizeExpression (Subtraction left right) =
  Subtraction (normalizeExpression left) (normalizeExpression right)
normalizeExpression (Minus operand) = Minus (normalizeExpression operand)
normalizeExpression (Subfederation left right) =
  Subfederation (normalizeExpression left) (normalizeExpression right)
normalizeExpression (Equality left right) =
  Equality (normalizeExpression left) (normalizeExpression right)
normalizeExpression (BooleanAnd left right) =
  BooleanAnd (normalizeExpression left) (normalizeExpression right)
normalizeExpression (BooleanOr left right) =
  BooleanOr (normalizeExpression left) (normalizeExpression right)
normalizeExpression (BooleanNot operand) =
  BooleanNot (normalizeExpression operand)
normalizeExpression (Multiplication left right) =
  Multiplication (normalizeExpression left) (normalizeExpression right)
normalizeExpression (Exponentiation left right) =
  Exponentiation (normalizeExpression left) (normalizeExpression right)
normalizeExpression (MapConcatenation left right) =
  MapConcatenation (normalizeExpression left) (normalizeExpression right)
normalizeExpression (MapAccess left right) =
  MapAccess (normalizeExpression left) (normalizeExpression right)
normalizeExpression (MapSpecification left right) =
  MapSpecification (normalizeExpression left) (normalizeExpression right)
normalizeExpression
    (IdentifierOperation identifierString typeAnnotation givenValue) =
  IdentifierOperation
    identifierString
    (normalizeExpression typeAnnotation)
    (normalizeExpression <$> givenValue)

normalizeStringTemplatePart
  :: StringTemplatePart Expression
  -> StringTemplatePart Expression
normalizeStringTemplatePart (StringTemplateLiteral value) =
  StringTemplateLiteral value
normalizeStringTemplatePart (StringTemplateInterpolation expressionValue) =
  StringTemplateInterpolation (normalizeExpression expressionValue)

-- | Empty maps are neutral sequence members and a one-member sequence adds no
-- genuine Atlas page: beyond an Atlas's finite presentation its final page is
-- already repeated. Only a sequence with at least two members introduces a
-- structural boundary.
normalizeSequence
  :: ([Expression] -> Expression)
  -> [Expression]
  -> Expression
normalizeSequence constructor expressions =
  case filter (not . isEmptyMap) (map normalizeExpression expressions) of
    [] -> AtlasMap []
    [expressionValue] -> expressionValue
    normalized -> constructor normalized

normalizeExpansion :: Expression -> Expression -> Expression
normalizeExpansion left right
  | isEmptyMap left = right
  | isEmptyMap right = left
  | otherwise = MapExpansion left right

-- Either is associative. Flattening and rebuilding to the right gives every
-- source spelling one injection tree, so its Boolean tag paths are stable.
normalizeEither :: Expression -> Expression -> Expression
normalizeEither left right = buildEither (eitherMembers left <> eitherMembers right)
  where
    buildEither [member] = member
    buildEither (member : members) = EitherType member (buildEither members)
    buildEither [] = EitherType left right

eitherMembers :: Expression -> [Expression]
eitherMembers (EitherType left right) =
  eitherMembers left <> eitherMembers right
eitherMembers expressionValue = [expressionValue]

isEmptyMap :: Expression -> Bool
isEmptyMap (AtlasMap []) = True
isEmptyMap (MapSequence []) = True
isEmptyMap _ = False

lower :: Expression -> OperatorExpression
lower (EllipsisNatural value) = NaturalValue value
lower EllipsisLiteral = EllipsisValue
lower (AsciiStringLiteral value) = AsciiStringValue value
lower NothingLiteral = NothingValue
lower (StringTemplate parts) =
  StringTemplateValue (map lowerStringTemplatePart parts)
lower StringType = StringTypeValue
lower (AtlasMap []) = EmptyMap
lower (AtlasMap expressions) =
  combineExpansions (map lowerSegment (segments expressions))
lower (MapSequence expressions) = Sequential (map lower expressions)
lower (MapExpansion left right) = Expansion (lower left) (lower right)
lower (SuperEllipsisRange lowerBound upperBound) =
  Range (lower lowerBound) (lower upperBound)
lower (SuperEllipsisRangePlus lowerBound) = RangePlus (lower lowerBound)
lower (SuperEllipsisRangeMinus upperBound) = RangeMinus (lower upperBound)
lower (NaturalRange origin target) = InclusiveNaturalRange origin target
lower (NaturalRangeUpwards origin) = InclusiveNaturalRangeUpwards origin
lower (ValuedNaturalRange origin target) =
  InclusiveValuedNaturalRange origin target
lower (ValuedNaturalRangeUpwards origin) =
  InclusiveValuedNaturalRangeUpwards origin
lower NaturalType = NaturalTypeValue
lower (IntegerRange origin target) = InclusiveIntegerRange origin target
lower (IntegerRangeUpwards origin) = InclusiveIntegerRangeUpwards origin
lower (IntegerRangeDownwards origin) = InclusiveIntegerRangeDownwards origin
lower (ValuedIntegerRange origin target) =
  InclusiveValuedIntegerRange origin target
lower (ValuedIntegerRangeUpwards origin) =
  InclusiveValuedIntegerRangeUpwards origin
lower (ValuedIntegerRangeDownwards origin) =
  InclusiveValuedIntegerRangeDownwards origin
lower IntegerType = IntegerTypeValue
lower (BooleanLiteral value) = BooleanValue value
lower BooleanType = BooleanTypeValue
lower (EitherType left right) = EitherValue (lower left) (lower right)
lower (OptionalType operand) = OptionalValue (lower operand)
lower (Conditional condition consequent alternative) =
  ConditionalValue (lower condition) (lower consequent) (lower alternative)
lower (Addition left right) = Add (lower left) (lower right)
lower (Subtraction left right) = Subtract (lower left) (lower right)
lower (Minus operand) = Negate (lower operand)
lower (Subfederation left right) =
  IsSubfederation (lower left) (lower right)
lower (Equality left right) = Equal (lower left) (lower right)
lower (BooleanAnd left right) = And (lower left) (lower right)
lower (BooleanOr left right) = Or (lower left) (lower right)
lower (BooleanNot operand) = Not (lower operand)
lower (Multiplication left right) = Multiply (lower left) (lower right)
lower (Exponentiation left right) = Power (lower left) (lower right)
lower (MapConcatenation left right) =
  Concatenate (lower left) (lower right)
lower (MapAccess left right) = Access (lower left) (lower right)
lower (MapSpecification left right) = Specify (lower left) (lower right)
lower (IdentifierOperation identifierString typeAnnotation givenValue) =
  IdentifierOperationValue
    identifierString
    (lower typeAnnotation)
    (lower <$> givenValue)

lowerStringTemplatePart
  :: StringTemplatePart Expression
  -> StringTemplatePart OperatorExpression
lowerStringTemplatePart (StringTemplateLiteral value) =
  StringTemplateLiteral value
lowerStringTemplatePart (StringTemplateInterpolation expressionValue) =
  StringTemplateInterpolation (lower expressionValue)

data Segment
  = ExpressionSegment [Expression]
  | MapSegment Expression

-- Consecutive expressions occupy one level. Each directly nested map
-- delimits another level, even when that map contains only one expression.
segments :: [Expression] -> [Segment]
segments = go []
  where
    go expressions [] = finishExpressions expressions
    go expressions (nested@(AtlasMap _) : rest) =
      finishExpressions expressions <> (MapSegment nested : go [] rest)
    go expressions (next : rest) = go (next : expressions) rest

    finishExpressions [] = []
    finishExpressions values = [ExpressionSegment (reverse values)]

lowerSegment :: Segment -> OperatorExpression
lowerSegment (ExpressionSegment values) =
  case map lower values of
    [value] -> value
    expressions -> Sequential expressions
lowerSegment (MapSegment expressionValue) = lower expressionValue

combineExpansions :: [OperatorExpression] -> OperatorExpression
combineExpansions [] = EmptyMap
combineExpansions [expressionValue] = expressionValue
combineExpansions (firstExpression : rest) =
  Expansion firstExpression (combineExpansions rest)

prettyOperator :: OperatorExpression -> Doc annotation
prettyOperator (NaturalValue value) = pretty value
prettyOperator EllipsisValue = pretty ellipsisSymbol
prettyOperator (AsciiStringValue value) = pretty (renderAsciiStringLiteral value)
prettyOperator NothingValue =
  pretty (Reserved.reservedSymbolIdentifierString Reserved.NothingSymbol)
prettyOperator (StringTemplateValue parts) =
  pretty (renderOperatorStringTemplate parts)
prettyOperator StringTypeValue = reservedSymbolDoc Reserved.StringTypeSymbol
prettyOperator EmptyMap = "()"
prettyOperator (Sequential []) = "()"
prettyOperator (Sequential [expressionValue]) = prettyOperator expressionValue
prettyOperator (Sequential expressions) =
  prettyFormFor SequentialOperator (map prettyOperator expressions)
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
prettyOperator (Negate operand) =
  prettyUnary MinusOperator operand
prettyOperator (IsSubfederation left right) =
  prettyBinary SubfederationOperator left right
prettyOperator (Equal left right) =
  prettyBinary EqualityOperator left right
prettyOperator (And left right) =
  prettyBinary BooleanAndOperator left right
prettyOperator (Or left right) =
  prettyBinary BooleanOrOperator left right
prettyOperator (Not operand) =
  prettyUnary BooleanNotOperator operand
prettyOperator (Multiply left right) =
  prettyBinary MultiplicationOperator left right
prettyOperator (Power left right) =
  prettyBinary ExponentiationOperator left right
prettyOperator (Concatenate left right) =
  prettyBinary ConcatenationOperator left right
prettyOperator (Access left right) =
  prettyBinary AccessOperator left right
prettyOperator (Specify left right) =
  prettyBinary SpecificationOperator left right
prettyOperator
    (IdentifierOperationValue
      (IdentifierString identifierString)
      typeAnnotation
      givenValue) =
  case givenValue of
    Nothing ->
      prettyForm
        (operatorCanonicalSymbol IdentifierTypeOperator)
        [pretty (renderIdentifierString identifierString), prettyOperator typeAnnotation]
    Just givenValueExpression ->
      prettyForm
        (operatorCanonicalSymbol AssignmentOperator)
        (pretty (renderIdentifierString identifierString) :
          if givenValueExpression == typeAnnotation
            then [prettyOperator givenValueExpression]
            else
              [ prettyOperator typeAnnotation
              , prettyOperator givenValueExpression
              ])

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
  | isCompactStringLiteral value = '$' : value
renderAsciiStringLiteral value = renderStandardStringLiteral value

-- | Compact @$name@ strings permit an underscore in the leading position or
-- as a separator, but never doubled or trailing.
isCompactStringLiteral :: String -> Bool
isCompactStringLiteral [] = False
isCompactStringLiteral value@(first : rest) =
  isLeadingCanonicalCharacter first
    && all isCanonicalCharacter rest
    && last value /= '_'
    && not (hasDoubledUnderscore value)
  where
    hasDoubledUnderscore ('_' : '_' : _) = True
    hasDoubledUnderscore (_ : remaining) =
      hasDoubledUnderscore remaining
    hasDoubledUnderscore [] = False

-- | Render an identifier expression. Canonical non-reserved names use their
-- compact bare spelling; reserved or noncanonical names use a full string.
renderIdentifierString :: String -> String
renderIdentifierString value@(first : rest)
  | isLeadingCanonicalCharacter first
      && all isCanonicalCharacter rest
      && not (isReservedIdentifierString value) = value
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
    escape '$' rest = '\\' : '$' : rest
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
      case compactInterpolation expressionValue of
        Just symbol -> '$' : symbol <> escapeOptionalSuffix rest
        Nothing ->
          "$(" <> renderExpressionValue expressionValue <> ")" <> rest

    escapeOptionalSuffix ('?' : rest) = '\\' : '?' : rest
    escapeOptionalSuffix rest = rest

compactOperatorStringInterpolation
  :: OperatorExpression
  -> Maybe String
compactOperatorStringInterpolation expressionValue =
  case expressionValue of
    NothingValue -> reserved Reserved.NothingSymbol
    StringTypeValue -> reserved Reserved.StringTypeSymbol
    NaturalTypeValue -> reserved Reserved.NaturalTypeSymbol
    IntegerTypeValue -> reserved Reserved.IntegerTypeSymbol
    BooleanValue False -> reserved Reserved.FalseSymbol
    BooleanValue True -> reserved Reserved.TrueSymbol
    BooleanTypeValue -> reserved Reserved.BooleanTypeSymbol
    OptionalValue operand ->
      (<> optionalSourceSymbol)
        <$> compactOperatorStringInterpolation operand
    _ -> Nothing
  where
    reserved = Just . Reserved.reservedSymbolIdentifierString
    optionalSourceSymbol =
      case operatorSourceSymbol OptionalOperator of
        Just symbol -> symbol
        Nothing -> operatorCanonicalSymbol OptionalOperator

isLeadingCanonicalCharacter :: Char -> Bool
isLeadingCanonicalCharacter character =
  isAsciiLetter character || character == '_'

isCanonicalCharacter :: Char -> Bool
isCanonicalCharacter character =
  isLeadingCanonicalCharacter character
    || ('0' <= character && character <= '9')
    || character == '\''

isAsciiLetter :: Char -> Bool
isAsciiLetter character =
  ('a' <= character && character <= 'z')
    || ('A' <= character && character <= 'Z')
