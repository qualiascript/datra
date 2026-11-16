-- | Source rendering for retained, unevaluated block specifications.
module DatraLanguage.AST.Source
  ( renderSourceExpression
  ) where

import Data.List (intercalate)
import Data.List.NonEmpty qualified as NonEmpty
import DatraLanguage.AST
import DatraLanguage.AST.CanonicalForm
  ( CanonicalForm (FunctionForm, ImportForm), canonicalFormName )
import DatraLanguage.AST.Operator qualified as AST
import DatraLanguage.AST.Reserved qualified as Reserved
import DatraLanguage.ConcreteSyntax
  ( StructuralDelimiter (..)
  , delimiterText
  , isSourcePresentationCharacter
  , sourceSpace
  )
import DatraLanguage.ContextualRole
  ( ContextualRole (ContextualThis), contextualSurfaceName )
import DatraLanguage.Pretty
  ( renderAsciiStringLiteral
  , renderIdentifierString
  , renderOperatorExpression
  , renderStringTemplate
  )

renderSourceExpression :: Expression -> String
renderSourceExpression =
  source 0 . toOperatorExpression

syntaxWhitespaceSource :: String -> Bool
syntaxWhitespaceSource value =
  not (null value) && all isSourcePresentationCharacter value

-- Parenthesize nested operations conservatively, while leaving each block
-- entry and the yield expression readable at their own expression boundary.
source :: Int -> OperatorExpression -> String
source context expression =
  case expression of
    FunValue operand -> wrapped 0
      (canonicalFormName FunctionForm <> sourceSpace <> source 0 operand)
    GenericIntroductionValue introduction -> wrapped 0
      (genericPolarity introduction
        <> renderGenericArgument introduction)
    InModuleValue _ value -> source context value
    ImportValue paths body -> canonicalFormName ImportForm <> sourceSpace
      <> intercalate (spaced AST.SequentialOperator)
        (map renderAsciiStringLiteral paths)
      <> sourceSpace <> source 0 body
    FunctionTypeValue _ input output -> wrapped 11
      (source 12 input <> spaced AST.FunctionTypeOperator <> functionTypeOutput output)
    FunctionApplicationValue function (UnresolvedSyntaxValue literal) ->
      wrapped 11 (source 11 function <> literal)
    FunctionApplicationValue function input -> wrapped 11
      ( source 11 function
        <> applicationSeparator function
        <> applicationInput input
      )
    DeclarationValue declaration ->
      sourceDeclaration declaration
    FunctionBodyValue bindings result -> wrapped 0
      (block AST.DoOperator bindings result)
    BeginValue bindings result -> wrapped 0
      (block AST.BeginOperator bindings result)
    IdentifierReferenceValue (SimpleIdentifierString name)
      | renderIdentifierString name == name -> name
      | otherwise -> contextualSurfaceName ContextualThis
          <> op AST.ScopeAccessOperator <> renderIdentifierString name
    UnresolvedSyntaxValue literal -> literal
    ElidedSyntaxValue -> ""
    SyntaxRemainderValue sourceText -> sourceText
    LookupValue operand -> unary (op AST.LookupOperator) operand
    DependentArgumentValue name (Just annotation) ->
      let (writtenName, optionalName) = dependentArgumentNameSource name
      in dependentArgument writtenName optionalName (Just annotation) Nothing
    DependentArgumentValue name Nothing -> source 13 name
    Sequential members -> delimit OpenParenthesis CloseParenthesis
      (intercalate (spaced AST.SequentialOperator)
        (map (source 0) (NonEmpty.toList members)))
    ArgumentativeMapValue members ->
      delimit OpenBrace CloseBrace (argumentMembers members)
    Expansion left right -> delimit OpenParenthesis CloseParenthesis
      (source 0 left <> spaced AST.SequentialOperator <> source 0 right)
    Concatenate left EmptyMap -> wrapped 10
      (source 10 left <> op AST.ConcatenationOperator)
    Concatenate left right -> binary 2 (op AST.ConcatenationOperator) left right
    Specify given (DependentArgumentValue name annotation) ->
      let (writtenName, optionalName) = dependentArgumentNameSource name
      in dependentArgument writtenName optionalName annotation (Just given)
    Specify left right -> binary 1 (op AST.SpecificationOperator) left right
    OverloadValue left right -> binary 1 (op AST.OverloadOperator) left right
    SafeOverloadValue left right -> binary 1 (op AST.SafeOverloadOperator) left right
    ConditionalValue condition yes no -> wrapped 0
      ( reservedSymbol Reserved.IfSymbol <> sourceSpace <> source 0 condition
          <> sourceSpace <> reservedWord Reserved.ThenWord
          <> sourceSpace <> source 0 yes
          <> sourceSpace <> reservedWord Reserved.ElseWord
          <> sourceSpace <> source 0 no
      )
    MaybeThenValue optional branch -> binary 1 (op AST.MaybeThenOperator) optional branch
    EitherValue left right -> binary 3 (op AST.EitherOperator) left right
    Equal left right -> binary 6 (op AST.EqualityOperator) left right
    NotEqual left right -> binary 6 (op AST.InequalityOperator) left right
    Less left right -> binary 6 (op AST.LessThanOperator) left right
    LessOrEqual left right -> binary 6 (op AST.LessThanOrEqualOperator) left right
    Greater left right -> binary 6 (op AST.GreaterThanOperator) left right
    GreaterOrEqual left right -> binary 6 (op AST.GreaterThanOrEqualOperator) left right
    Add left right -> binary 7 (op AST.AdditionOperator) left right
    Subtract left right -> binary 7 (op AST.SubtractionOperator) left right
    Multiply left right -> wrapped 8
      (multiplicand left <> spaced AST.MultiplicationOperator <> multiplicand right)
    Power left right -> binary 9 (op AST.ExponentiationOperator) left right
    Positive operand -> unary (op AST.AdditionOperator) operand
    Negate operand -> unary (op AST.MinusOperator) operand
    CoalizationValue operand ->
      unary (op AST.CoalizationOperator <> sourceSpace) operand
    OptionalValue operand -> wrapped 10
      (source 10 operand <> op AST.OptionalOperator)
    ScopeAccessValue operand
        (IdentifierReferenceValue (SimpleIdentifierString name)) ->
      wrapped 12 (source 12 operand <> op AST.ScopeAccessOperator <> renderIdentifierString name)
    ScopeAccessValue operand body ->
      wrapped 12 (source 12 operand <> op AST.ScopeAccessOperator <> scopeBody body)
    -- Access associates to the left, so a second page selection can continue
    -- directly as @value[first][second]@.  Operands with genuinely looser
    -- precedence are still parenthesized by their own renderer.
    Access operand position -> wrapped 10
      (source 10 operand <> delimit OpenBracket CloseBracket (source 0 position))
    Range left right -> binary 9 (op AST.RangeOperator) left right
    RangePlus operand -> source 11 operand <> op AST.RangePlusOperator
    RangeMinus operand -> source 11 operand <> op AST.RangeMinusOperator
    InclusiveNaturalRange start end ->
      bounded Reserved.RangeSymbol start end
    InclusiveNaturalRangeUpwards start ->
      open Reserved.RangeSymbol start Reserved.UpwardsWord
    InclusiveValuedNaturalRange start end ->
      bounded Reserved.FromSymbol start end
    InclusiveValuedNaturalRangeUpwards start ->
      open Reserved.FromSymbol start Reserved.UpwardsWord
    InclusiveIntegerRange start end ->
      bounded Reserved.RangeSymbol start end
    InclusiveIntegerRangeUpwards start ->
      open Reserved.RangeSymbol start Reserved.UpwardsWord
    InclusiveIntegerRangeDownwards start ->
      open Reserved.RangeSymbol start Reserved.DownwardsWord
    InclusiveValuedIntegerRange start end ->
      bounded Reserved.FromSymbol start end
    InclusiveValuedIntegerRangeUpwards start ->
      open Reserved.FromSymbol start Reserved.UpwardsWord
    InclusiveValuedIntegerRangeDownwards start ->
      open Reserved.FromSymbol start Reserved.DownwardsWord
    StringTemplateValue parts -> renderStringTemplate
      (source 0) stringLiteral (const Nothing) parts
    IdentifierExpressionValue operand -> case operand of
      IdentifierReferenceValue (SimpleIdentifierString name) ->
        op AST.IdentifierExpressionOperator <> renderIdentifierString name
      AsciiStringValue value -> op AST.IdentifierExpressionOperator <> renderAsciiStringLiteral value
      _ -> op AST.IdentifierExpressionOperator <>
        delimit OpenParenthesis CloseParenthesis (source 0 operand)
    AtlasIdentifierExpressionValue operand -> case operand of
      Sequential {} -> op AST.AtlasIdentifierExpressionOperator <> source 0 operand
      Expansion {} -> op AST.AtlasIdentifierExpressionOperator <> source 0 operand
      EmptyMap -> op AST.AtlasIdentifierExpressionOperator <> source 0 operand
      _ -> op AST.AtlasIdentifierExpressionOperator <>
        delimit OpenParenthesis CloseParenthesis (source 0 operand)
    -- Atomic AST notation is also its source notation.
    NaturalValue _ -> atom
    EllipsisValue -> atom
    SkipValue -> atom
    AsciiStringValue _ -> atom
    NothingValue -> atom
    EmptyMap -> atom
    AnyTypeValue -> atom
    NaturalTypeValue -> atom
    IntegerTypeValue -> atom
    BooleanValue _ -> atom
    BooleanTypeValue -> atom
  where
    atom = renderOperatorExpression expression
    stringLiteral (AsciiStringValue value) = Just value
    stringLiteral _ = Nothing
    wrapped precedence text
      | context > precedence = delimit OpenParenthesis CloseParenthesis text
      | otherwise = text
    binary precedence operator left right = wrapped precedence
      ( source (precedence + 1) left <> sourceSpace <> operator
          <> sourceSpace <> source (precedence + 1) right
      )
    unary operator operand = wrapped 10 (operator <> source 11 operand)
    multiplicand SkipValue = delimit OpenParenthesis CloseParenthesis
      (op AST.MultiplicationOperator)
    multiplicand operand = source 9 operand
    applicationInput SkipValue = delimit OpenParenthesis CloseParenthesis
      (op AST.MultiplicationOperator)
    applicationInput operand@FunctionBodyValue {} = source 0 operand
    applicationInput operand = source 12 operand
    applicationSeparator
        (FunctionApplicationValue _ (UnresolvedSyntaxValue sourceText))
      | syntaxWhitespaceSource sourceText = ""
    applicationSeparator _ = sourceSpace
    functionTypeOutput output@FunctionTypeValue {} = source 11 output
    functionTypeOutput output = source 12 output
    bounded keyword start end =
      reservedSymbol keyword <> sourceSpace <> show start
        <> sourceSpace <> reservedWord Reserved.ToWord
        <> sourceSpace <> show end
    open keyword start direction =
      reservedSymbol keyword <> sourceSpace <> show start
        <> sourceSpace <> reservedWord direction
    binderName name optional =
      renderIdentifierString name <>
        if optional then op AST.OptionalOperator else ""
    renderGenericArgument argument =
      binderName
        (simpleIdentifierStringText (genericArgumentName argument))
        (genericArgumentOptional argument)
        <> renderGenericBound (genericArgumentBound argument)
    genericPolarity introduction =
      case genericArgumentPolarity introduction of
        GenericProduct -> op AST.GenericProductOperator
        GenericSum -> op AST.ExponentiationOperator
    renderGenericBound bound = case bound of
      AnyTypeValue -> ""
      _ -> spaced AST.GenericBoundOperator <> source 0 bound
    dependentArgument name optional annotation given = wrapped 1
      (name <> (if optional then op AST.OptionalOperator else "")
        <> maybe "" (\value -> spaced AST.DependentArgumentTypeOperator <> source 13 value) annotation
        <> maybe "" (\value -> spaced AST.AssignmentOperator <> assignedValue value) given)
    dependentArgumentNameSource name = case name of
      OptionalValue present -> (source 13 present, True)
      _ -> (source 13 name, False)
    -- Federation binds inside assignment. Other assignment operands retain
    -- their existing conservative grouping.
    assignedValue value@EitherValue {} = source 3 value
    assignedValue value = source 7 value
    block keyword bindings result = op keyword <> sourceSpace
      <> intercalate (spaced AST.SequentialOperator)
        ( map sourceDeclaration bindings
            <> [ reservedWord Reserved.YieldWord
                  <> sourceSpace <> source 0 result
               ]
        )
    sourceDeclaration declaration =
        modifier AST.LetOperator (dependentDeclarationIsLet declaration)
          <> modifier AST.DefOperator (dependentDeclarationIsDefinition declaration)
          <> modifier AST.ValOperator
            (dependentDeclarationIsCanonicalValue declaration)
          <> source 0 (identifierHeadValue
            (dependentDeclarationHead declaration))
          <> spaced AST.AssignmentOperator
          <> assignedValue (dependentDeclarationImplementation declaration)
    modifier operator present =
      if present then op operator <> sourceSpace else ""
    argumentMembers = intercalate (spaced AST.SequentialOperator) . map (source 0)

    op = AST.operatorPreferredSymbol
    spaced operator = sourceSpace <> op operator <> sourceSpace
    delimit opening closing body =
      delimiterText opening <> body <> delimiterText closing

    reservedWord = Reserved.reservedWordText
    reservedSymbol = Reserved.reservedSymbolIdentifierString

identifierHeadValue :: IdentifierExpression OperatorExpression -> OperatorExpression
identifierHeadValue headValue = case headValue of
  IdentifierExpressionBody body -> IdentifierExpressionValue body
  AtlasIdentifierExpressionBody body -> AtlasIdentifierExpressionValue body

scopeBody :: OperatorExpression -> String
scopeBody body = case body of
  Sequential {} -> source 0 body
  Expansion {} -> source 0 body
  EmptyMap -> source 0 body
  _ -> delimiterText OpenParenthesis <> source 0 body <>
    delimiterText CloseParenthesis
