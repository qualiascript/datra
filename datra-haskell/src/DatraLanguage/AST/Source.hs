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
    ProgramValue bindings result -> source context (BeginValue bindings result)
    BeginValue bindings result -> wrapped 0
      ("begin\n" <> concatMap (indent . source 0) bindings
        <> "yield " <> source 0 result)
    LetValue binding -> wrapped 0 ("let " <> source 0 binding)
    IdentifierReferenceValue (IdentifierString name) -> name
    IdentifierOperationValue (IdentifierString name) annotation given -> wrapped 1
      (renderIdentifierString name <> " : " <> source 0 annotation
        <> maybe "" (\value -> " := " <> source 0 value) given)
    Sequential members -> "(" <> intercalate "; " (map (source 0) members) <> ")"
    Arguments members -> "{" <> intercalate "; " (map (source 0) members) <> "}"
    Expansion left right -> "(" <> source 0 left <> "; " <> source 0 right <> ")"
    Concatenate left right -> binary 2 "," left right
    Specify left right -> binary 1 "~>" left right
    EvalValue text target -> wrapped 0 ("eval " <> source 3 text <> ", " <> source 0 target)
    ConditionalValue condition yes no -> wrapped 0
      ("if " <> source 0 condition <> " then " <> source 0 yes <> " else " <> source 0 no)
    EitherValue left right -> binary 3 "|" left right
    Or left right -> binary 4 "or" left right
    And left right -> binary 5 "and" left right
    Equal left right -> binary 6 "=" left right
    IsSubfederation left right -> binary 6 "of" left right
    Add left right -> binary 7 "+" left right
    Subtract left right -> binary 7 "-" left right
    Multiply left right -> binary 8 "*" left right
    Power left right -> binary 9 "^" left right
    Negate operand -> unary "-" operand
    Not operand -> unary "not " operand
    ExtractValue operand -> unary "%" operand
    OptionalValue operand -> wrapped 10 (source 11 operand <> "?")
    Access operand position -> wrapped 10 (source 11 operand <> "[" <> source 0 position <> "]")
    Range left right -> binary 9 ".." left right
    RangePlus operand -> source 11 operand <> ".."
    RangeMinus operand -> source 11 operand <> "..-"
    InclusiveNaturalRange start end -> bounded "range" start end
    InclusiveNaturalRangeUpwards start -> open "range" start "upwards"
    InclusiveValuedNaturalRange start end -> bounded "from" start end
    InclusiveValuedNaturalRangeUpwards start -> open "from" start "upwards"
    InclusiveIntegerRange start end -> bounded "range" start end
    InclusiveIntegerRangeUpwards start -> open "range" start "upwards"
    InclusiveIntegerRangeDownwards start -> open "range" start "downwards"
    InclusiveValuedIntegerRange start end -> bounded "from" start end
    InclusiveValuedIntegerRangeUpwards start -> open "from" start "upwards"
    InclusiveValuedIntegerRangeDownwards start -> open "from" start "downwards"
    StringTemplateValue parts -> renderStringTemplate (source 0) (const Nothing) parts
    -- Atomic AST notation is also its source notation.
    NaturalValue _ -> atom
    EllipsisValue -> atom
    AsciiStringValue _ -> atom
    NothingValue -> atom
    StringTypeValue -> atom
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
    bounded keyword start end = keyword <> " " <> show start <> " to " <> show end
    open keyword start direction = keyword <> " " <> show start <> " " <> direction
    indent = unlines . map (" " <>) . lines
