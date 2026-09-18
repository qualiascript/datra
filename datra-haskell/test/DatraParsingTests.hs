module DatraParsingTests (main) where

import Datra.AST
  ( Expression (..)
  , renderExpression
  )
import Datra.Parsing (parseDatra)

main :: IO ()
main = do
  assertAstOutput
    "flat map"
    "[1; 2; 10]"
    "1 <:> 2 <:> 10"
  assertAstOutput
    "nested map"
    "[[1; 2];[3;4]]"
    "1 <:> 2 <+> 3 <:> 4"
  assertAstOutput
    "comments and whitespace"
    "  [1; # retain the next value\n [2; 3]] # end\n"
    "1 <+> 2 <:> 3"
  assertAstOutput
    "empty nested maps are trimmed recursively"
    "[1; [[ ]  ]; 2]"
    "1 <:> 2"
  assertAstOutput
    "expansions are parenthesized at recursive depth"
    "[[[1;2];[3;4]];[5;6]]"
    "(1 <:> 2 <+> 3 <:> 4) <+> 5 <:> 6"
  assertAstOutput
    "the empty map is retained at the root"
    "[]"
    "[]"
  assertAstOutput
    "ellipsis literal"
    "[...]"
    "..."
  assertAstOutput
    "bounded super-ellipsis range"
    "[2..10]"
    "2 <..> 10"
  assertAstOutput
    "open super-ellipsis ranges"
    "[2..+; 10..-]"
    "(2 ..+) <:> (10 ..-)"
  assertAstOutput
    "Haskell arithmetic precedence"
    "[1 + 2 * 3 ^ 4]"
    "1 + 2 * 3 ^ 4"
  assertAstOutput
    "parentheses override arithmetic precedence"
    "[(1 + 2) * 3]"
    "(1 + 2) * 3"
  assertAstOutput
    "right-nested addition keeps necessary parentheses"
    "[1 + (2 + 3)]"
    "1 + (2 + 3)"
  assertAstOutput
    "redundant parentheses are omitted"
    "[((1 + (2 * (3 ^ 4))))]"
    "1 + 2 * 3 ^ 4"
  assertAstOutput
    "range endpoints accept arithmetic expressions"
    "[1 + 2..3 * 4]"
    "1 + 2 <..> 3 * 4"
  assertAstOutput
    "range concatenation"
    "[1..3, 5..7]"
    "(1 <..> 3) <.> (5 <..> 7)"
  assertAstOutput
    "access consumes a concatenated range insertion"
    "[... @ 1..3, 5..7]"
    "... <@> ((1 <..> 3) <.> (5 <..> 7))"
  assertAstOutput
    "parentheses can concatenate an access result"
    "[(... @ 1), 2]"
    "... <@> 1 <.> 2"
  assertAstOutput
    "map expressions are concatenation operands"
    "[[1; 2], [3; 4]]"
    "(1 <:> 2) <.> 3 <:> 4"
  assertAstOutput
    "arithmetic and map expansion fixity conflict is parenthesized"
    "[[1 + 2]; [3 * 4]]"
    "(1 + 2) <+> 3 * 4"
  assertParsed
    "exponentiation associates right"
    "[2 ^ 3 ^ 4]"
    (AtlasMap
      [ Exponentiation
          (EllipsisNatural 2)
          (Exponentiation (EllipsisNatural 3) (EllipsisNatural 4))
      ])
  assertParsed
    "addition associates left"
    "[1 + 2 + 3]"
    (AtlasMap
      [ Addition
          (Addition (EllipsisNatural 1) (EllipsisNatural 2))
          (EllipsisNatural 3)
      ])
  assertParsed
    "access associates left"
    "[... @ 1 @ 2]"
    (AtlasMap
      [ MapAccess
          (MapAccess EllipsisLiteral (EllipsisNatural 1))
          (EllipsisNatural 2)
      ])
  assertParsed
    "map is itself an expression"
    "[([1; 2], [3; 4]) @ 0]"
    (AtlasMap
      [ MapAccess
          (MapConcatenation
            (AtlasMap [EllipsisNatural 1, EllipsisNatural 2])
            (AtlasMap [EllipsisNatural 3, EllipsisNatural 4]))
          (EllipsisNatural 0)
      ])
  assertRejected "top-level expression must be a map" "10"
  assertAstOutput
    "trailing semicolons are ignored"
    "[1; 2; # trailing separators\n ; ; ]"
    "1 <:> 2"
  assertRejected "empty entries in the middle are rejected" "[1;;2]"
  assertRejected "bounded ranges are non-associative" "[1..2..3]"
  assertRejected "addition requires a right operand" "[1 +]"
  assertRejected "parentheses must be balanced" "[(1 + 2]"

assertAstOutput :: String -> String -> String -> IO ()
assertAstOutput label source expected =
  case renderExpression <$> parseDatra source of
    Left message -> fail (label <> ": unexpected parse failure: " <> message)
    Right actual
      | actual == expected -> pure ()
      | otherwise ->
          fail
            ( label
                <> ": expected "
                <> show expected
                <> ", got "
                <> show actual
            )

assertRejected :: String -> String -> IO ()
assertRejected label source =
  case parseDatra source of
    Left _ -> pure ()
    Right actual ->
      fail (label <> ": unexpectedly parsed as " <> show actual)

assertParsed :: String -> String -> Expression -> IO ()
assertParsed label source expected =
  case parseDatra source of
    Left message -> fail (label <> ": unexpected parse failure: " <> message)
    Right actual
      | actual == expected -> pure ()
      | otherwise ->
          fail
            ( label
                <> ": expected "
                <> show expected
                <> ", got "
                <> show actual
            )
