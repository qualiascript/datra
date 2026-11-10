-- | Source rendering for retained, unevaluated block specifications.
module DatraLanguage.AST.Source (renderSourceExpression) where

import Data.List (intercalate)
import Data.List.NonEmpty qualified as NonEmpty
import DatraLanguage.AST
import DatraLanguage.NeutralLexer (isOpaqueSymbolicSyntaxLiteral)
import DatraLanguage.Pretty
  ( renderAsciiStringLiteral
  , renderIdentifierString
  , renderOperatorExpression
  , renderStringTemplate
  )

renderSourceExpression :: Expression -> String
renderSourceExpression =
  source 0 . toOperatorExpression

-- Parenthesize nested operations conservatively, while leaving each block
-- entry and the yield expression readable at their own expression boundary.
source :: Int -> OperatorExpression -> String
source context expression =
  case expression of
    FunValue operand -> wrapped 0 ("fun " <> source 0 operand)
    GenericIntroductionValue introduction -> wrapped 0
      (genericPolarity introduction
        <> renderGenericArgument introduction)
    InModuleValue _ value -> source context value
    ImportValue paths body -> "import "
      <> intercalate "; " (map renderAsciiStringLiteral paths)
      <> " " <> source 0 body
    FunctionTypeValue _ input output -> wrapped 11
      (source 12 input <> " -> " <> functionTypeOutput output)
    FunctionApplicationValue function input -> wrapped 11
      (source 11 function <> " " <> applicationInput input)
    DeclarationValue declaration ->
      sourceDeclaration declaration
    FunctionBodyValue bindings result -> wrapped 0 (block "do" bindings result)
    BeginValue bindings result -> wrapped 0 (block "begin" bindings result)
    IdentifierReferenceValue (SimpleIdentifierString name)
      | renderIdentifierString name == name -> name
      | isOpaqueSymbolicSyntaxLiteral name -> name
      | otherwise -> "this." <> renderIdentifierString name
    LookupValue operand -> unary "~" operand
    DependentArgumentValue name (Just annotation) ->
      dependentArgument (source 13 name) False (Just annotation) Nothing
    DependentArgumentValue name Nothing -> source 13 name
    Sequential members -> "(" <>
      intercalate "; " (map (source 0) (NonEmpty.toList members)) <> ")"
    ArgumentativeMapValue members ->
      "{" <> argumentMembers members <> "}"
    Expansion left right -> "(" <> source 0 left <> "; " <> source 0 right <> ")"
    Concatenate left EmptyMap -> wrapped 10 (source 10 left <> ",")
    Concatenate left right -> binary 2 "," left right
    Specify given (DependentArgumentValue name annotation) ->
      dependentArgument (source 13 name) False annotation (Just given)
    Specify left right -> binary 1 "~>" left right
    OverloadValue left right -> binary 1 "<<" left right
    SafeOverloadValue left right -> binary 1 "<<<" left right
    ConditionalValue condition yes no -> wrapped 0
      ("if " <> source 0 condition <> " then " <> source 0 yes <> " else " <> source 0 no)
    MaybeThenValue optional branch -> binary 1 "!?" optional branch
    EitherValue left right -> binary 3 "|" left right
    Equal left right -> binary 6 "=" left right
    NotEqual left right -> binary 6 "=/=" left right
    Less left right -> binary 6 "<" left right
    LessOrEqual left right -> binary 6 "<=" left right
    Greater left right -> binary 6 ">" left right
    GreaterOrEqual left right -> binary 6 ">=" left right
    Add left right -> binary 7 "+" left right
    Subtract left right -> binary 7 "-" left right
    Multiply left right -> wrapped 8
      (multiplicand left <> " * " <> multiplicand right)
    Power left right -> binary 9 "^" left right
    Positive operand -> unary "+" operand
    Negate operand -> unary "-" operand
    CoalizationValue operand -> unary ">< " operand
    OptionalValue (DependentArgumentValue name (Just annotation)) ->
      dependentArgument (source 13 name) True (Just annotation) Nothing
    OptionalValue
        (Specify given (DependentArgumentValue name annotation)) ->
      dependentArgument (source 13 name) True annotation (Just given)
    OptionalValue operand -> wrapped 10 (source 10 operand <> "?")
    ScopeAccessValue operand
        (IdentifierReferenceValue (SimpleIdentifierString name)) ->
      wrapped 12 (source 12 operand <> "." <> renderIdentifierString name)
    ScopeAccessValue operand body ->
      wrapped 12 (source 12 operand <> "." <> scopeBody body)
    -- Access associates to the left, so a second page selection can continue
    -- directly as @value[first][second]@.  Operands with genuinely looser
    -- precedence are still parenthesized by their own renderer.
    Access operand position -> wrapped 10 (source 10 operand <> "[" <> source 0 position <> "]")
    Range left right -> binary 9 ".." left right
    RangePlus operand -> source 11 operand <> ".."
    RangeMinus operand -> source 11 operand <> "..-"
    InclusiveNaturalRange start end -> bounded "range" start end
    InclusiveNaturalRangeUpwards start -> open "range" start "up"
    InclusiveValuedNaturalRange start end -> bounded "from" start end
    InclusiveValuedNaturalRangeUpwards start -> open "from" start "up"
    InclusiveIntegerRange start end -> bounded "range" start end
    InclusiveIntegerRangeUpwards start -> open "range" start "up"
    InclusiveIntegerRangeDownwards start -> open "range" start "down"
    InclusiveValuedIntegerRange start end -> bounded "from" start end
    InclusiveValuedIntegerRangeUpwards start -> open "from" start "up"
    InclusiveValuedIntegerRangeDownwards start -> open "from" start "down"
    StringTemplateValue parts -> renderStringTemplate
      (source 0) stringLiteral (const Nothing) parts
    IdentifierExpressionValue (IdentifierExpressionBody operand) -> case operand of
      IdentifierReferenceValue (SimpleIdentifierString name) ->
        "$" <> renderIdentifierString name
      AsciiStringValue value -> "$" <> renderAsciiStringLiteral value
      Sequential {} -> "$" <> source 0 operand
      _ -> "$(" <> source 0 operand <> ")"
    -- Atomic AST notation is also its source notation.
    NaturalValue _ -> atom
    EllipsisValue -> atom
    SkipValue -> atom
    AsciiStringValue _ -> atom
    NothingValue -> atom
    EmptyMap -> atom
    NaturalTypeValue -> atom
    IntegerTypeValue -> atom
    BooleanValue _ -> atom
    BooleanTypeValue -> atom
  where
    atom = renderOperatorExpression expression
    stringLiteral (AsciiStringValue value) = Just value
    stringLiteral _ = Nothing
    wrapped precedence text
      | context > precedence = "(" <> text <> ")"
      | otherwise = text
    binary precedence operator left right = wrapped precedence
      (source (precedence + 1) left <> " " <> operator <> " " <> source (precedence + 1) right)
    unary operator operand = wrapped 10 (operator <> source 11 operand)
    multiplicand SkipValue = "(*)"
    multiplicand operand = source 9 operand
    applicationInput SkipValue = "(*)"
    applicationInput operand@FunctionBodyValue {} = source 0 operand
    applicationInput operand = source 12 operand
    functionTypeOutput output@FunctionTypeValue {} = source 11 output
    functionTypeOutput output = source 12 output
    bounded keyword start end = keyword <> " " <> show start <> " to " <> show end
    open keyword start direction = keyword <> " " <> show start <> " " <> direction
    binderName name optional =
      renderIdentifierString name <> if optional then "?" else ""
    renderGenericArgument argument =
      binderName
        (simpleIdentifierStringText (genericArgumentName argument))
        (genericArgumentOptional argument)
        <> renderGenericBound (genericArgumentBound argument)
    genericPolarity introduction =
      case genericArgumentPolarity introduction of
        GenericProduct -> "&"
        GenericSum -> "^"
    renderGenericBound bound = case bound of
      IdentifierReferenceValue (SimpleIdentifierString "Any") -> ""
      _ -> " :: " <> source 0 bound
    dependentArgument name optional annotation given = wrapped 1
      (name <> (if optional then "?" else "")
        <> maybe "" (\value -> " : " <> source 13 value) annotation
        <> maybe "" (\value -> " := " <> assignedValue value) given)
    -- Federation binds inside assignment. Other assignment operands retain
    -- their existing conservative grouping.
    assignedValue value@EitherValue {} = source 3 value
    assignedValue value = source 7 value
    block keyword bindings result = keyword <> " "
      <> intercalate "; "
        (map sourceDeclaration bindings <> ["yield " <> source 0 result])
    sourceDeclaration declaration =
        modifier "let " (dependentDeclarationIsLet declaration)
          <> modifier "def " (dependentDeclarationIsDefinition declaration)
          <> modifier "val "
            (dependentDeclarationIsCanonicalValue declaration)
          <> source 0
            (IdentifierExpressionValue (dependentDeclarationHead declaration))
          <> " := "
          <> assignedValue (dependentDeclarationImplementation declaration)
    modifier written present = if present then written else ""
    argumentMembers = intercalate "; " . map (source 0)

scopeBody :: OperatorExpression -> String
scopeBody body = case body of
  Sequential {} -> source 0 body
  Expansion {} -> source 0 body
  EmptyMap -> source 0 body
  _ -> "(" <> source 0 body <> ")"
