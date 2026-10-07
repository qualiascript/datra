-- | Source rendering for retained, unevaluated block specifications.
module DatraLanguage.AST.Source (renderSourceExpression) where

import Data.List (intercalate)
import DatraLanguage.AST

renderSourceExpression :: Expression -> String
renderSourceExpression = source 0 . toOperatorExpression

-- Parenthesize nested operations conservatively, while leaving each block
-- entry and the yield expression readable at their own expression boundary.
source :: Int -> OperatorExpression -> String
source context expression =
  case expression of
    FunValue operand -> wrapped 0 ("fun " <> source 0 operand)
    WithBindingValue (IdentifierString name) optional bound -> wrapped 0
      ("with " <> binderName name optional <> " of " <> source 0 bound)
    ForBindingValue (IdentifierString name) optional bound -> wrapped 0
      ("for " <> binderName name optional <> " of " <> source 0 bound)
    InModuleValue _ value -> source context value
    ImportValue allNames path -> "import " <> (if allNames then "all " else "") <> renderAsciiStringLiteral path
    SyntaxTypeValue templates signature -> wrapped 1
      (source 2 templates <> " %% " <> source 0 signature)
    FunctionTypeValue input output -> wrapped 1 (source 2 input <> " -> " <> source 1 output)
    FunctionApplicationValue
        (IdentifierReferenceValue (IdentifierString "_this"))
        (NaturalValue 0) -> "this"
    FunctionApplicationValue
        (IdentifierReferenceValue (IdentifierString "_it"))
        (NaturalValue 0) -> "it"
    FunctionApplicationValue function input -> wrapped 11
      (source 11 function <> " " <> applicationInput input)
    FunctionBodyValue bindings result -> wrapped 0 (block "do" bindings result)
    ExternalValue descriptor -> wrapped 10 ("!~" <> source 12 descriptor)
    ProgramValue bindings result -> source context (BeginValue bindings result)
    BeginValue bindings result -> wrapped 0 (block "begin" bindings result)
    LetValue binding -> wrapped 0 ("let " <> source 0 binding)
    IdentifierReferenceValue (IdentifierString name)
      | renderIdentifierString name == name -> name
      | otherwise -> "~" <> renderIdentifierString name
    IdentifierOperationValue (IdentifierString name) annotation given ->
      identifierOperation
        (renderIdentifierString name) False annotation given
    IdentifierTemplateOperationValue parts annotation given ->
      identifierOperation
        (renderStringTemplate (source 0) (const Nothing) parts)
        False
        annotation
        given
    Sequential members -> "(" <> intercalate "; " (map (source 0) members) <> ")"
    Arguments members -> "{" <> argumentMembers members <> "}"
    Expansion left right -> "(" <> source 0 left <> "; " <> source 0 right <> ")"
    Concatenate left EmptyMap -> wrapped 10 (source 10 left <> ",")
    Concatenate left right -> binary 2 "," left right
    Specify left right -> binary 1 "~>" left right
    OverloadValue left right -> binary 1 "<<" left right
    SafeOverloadValue left right -> binary 1 "<<<" left right
    AssertValue hard condition -> wrapped 0
      ("assert " <> (if hard then "hard " else "") <> source 0 condition)
    ConditionalValue condition yes no -> wrapped 0
      ("if " <> source 0 condition <> " then " <> source 0 yes <> " else " <> source 0 no)
    MaybeThenValue
        (ListUnconsValue values)
        (FunctionApplicationValue function
          (FunctionApplicationValue
            (IdentifierReferenceValue (IdentifierString "_it"))
            (NaturalValue 0))) ->
      listMaybeThen values function
    MaybeThenValue optional branch -> binary 1 "??" optional branch
    EitherValue left right -> binary 3 "|" left right
    Or left right -> binary 4 "or" left right
    And left right -> binary 5 "and" left right
    Equal left right -> binary 6 "=" left right
    NotEqual left right -> binary 6 "=/=" left right
    Less left right -> binary 6 "<" left right
    LessOrEqual left right -> binary 6 "<=" left right
    Greater left right -> binary 6 ">" left right
    GreaterOrEqual left right -> binary 6 ">=" left right
    IsSubfederation left right -> binary 6 "of" left right
    Add left right -> binary 7 "+" left right
    Subtract left right -> binary 7 "-" left right
    Multiply left right -> wrapped 8
      (multiplicand left <> " * " <> multiplicand right)
    Power left right -> binary 9 "^" left right
    Positive operand -> unary "+" operand
    Negate operand -> unary "-" operand
    Not operand -> unary "not " operand
    CoalizationValue operand -> unary ">< " operand
    ModularValue operand -> wrapped 0 ("modular " <> source 0 operand)
    ExtractValue operand -> unary "%" operand
    OptionalValue
        (IdentifierOperationValue (IdentifierString name) annotation given) ->
      identifierOperation
        (renderIdentifierString name) True annotation given
    OptionalValue
        (IdentifierTemplateOperationValue parts annotation given) ->
      identifierOperation
        (renderStringTemplate (source 0) (const Nothing) parts)
        True
        annotation
        given
    OptionalValue operand -> wrapped 10 (source 10 operand <> "?")
    ListUnconsValue operand -> wrapped 10 (source 10 operand <> "!")
    NamedAccessValue operand (IdentifierString name) -> wrapped 12 (source 12 operand <> "." <> renderIdentifierString name)
    Access operand (NaturalValue 1)
      | Just names <- scopeNames operand ->
          "~" <> case names of
            [name] -> renderIdentifierString name
            _ -> "(" <> intercalate ", " (map renderIdentifierString names) <> ")"
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
    StringTemplateValue parts -> renderStringTemplate (source 0) (const Nothing) parts
    -- Atomic AST notation is also its source notation.
    NaturalValue _ -> atom
    EllipsisValue -> atom
    SkipValue -> atom
    AsciiStringValue _ -> atom
    NothingValue -> atom
    IdentifierValueTypeValue -> atom
    EmptyMap -> atom
    NaturalTypeValue -> atom
    IntegerTypeValue -> atom
    BooleanValue _ -> atom
    BooleanTypeValue -> atom
  where
    atom = renderOperatorExpression expression
    wrapped precedence text
      | context > precedence = "(" <> text <> ")"
      | otherwise = text
    binary precedence operator left right = wrapped precedence
      (source (precedence + 1) left <> " " <> operator <> " " <> source (precedence + 1) right)
    unary operator operand = wrapped 10 (operator <> source 11 operand)
    listMaybeThen values function = wrapped 1
      (listMaybeInput values <> " !? " <> listMaybeFunction function)
    listMaybeFunction function@FunValue {} = source 0 function
    listMaybeFunction function = source 2 function
    listMaybeInput operand = source 2 operand
    multiplicand SkipValue = "(*)"
    multiplicand operand = source 9 operand
    applicationInput SkipValue = "(*)"
    applicationInput operand
      | Just _ <- valueLookupNames operand = "(" <> source 0 operand <> ")"
    applicationInput operand = source 12 operand
    bounded keyword start end = keyword <> " " <> show start <> " to " <> show end
    open keyword start direction = keyword <> " " <> show start <> " " <> direction
    binderName name optional =
      renderIdentifierString name <> if optional then "?" else ""
    identifierOperation name optional annotation given = wrapped 1
      (name <> (if optional then "?" else "") <> case given of
        Just value | value == annotation -> " := " <> assignedValue value
        _ -> " : " <> source 13 annotation
          <> maybe "" (\value -> " := " <> assignedValue value) given)
    -- Federation binds inside assignment. Other assignment operands retain
    -- their existing conservative grouping.
    assignedValue value@EitherValue {} = source 3 value
    assignedValue value = source 7 value
    block keyword bindings result = keyword <> " "
      <> intercalate "; " (map (source 0) bindings <> ["yield " <> source 0 result])
    argumentMembers = intercalate "; " . map (source 0)

-- Preserve the exact expansion of @this.(a, b)[1]@ when rendering name lists.
scopeNames :: OperatorExpression -> Maybe [String]
scopeNames
    (NamedAccessValue
      (FunctionApplicationValue
        (IdentifierReferenceValue (IdentifierString "_this"))
        (NaturalValue 0))
      (IdentifierString name)) = Just [name]
scopeNames (Concatenate left EmptyMap) = scopeNames left
scopeNames (Concatenate left right) = (<>) <$> scopeNames left <*> scopeNames right
scopeNames _ = Nothing

valueLookupNames :: OperatorExpression -> Maybe [String]
valueLookupNames (Access operand (NaturalValue 1)) = scopeNames operand
valueLookupNames _ = Nothing
