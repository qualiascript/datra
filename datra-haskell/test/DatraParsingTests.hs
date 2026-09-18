{-# LANGUAGE PostfixOperators #-}

module DatraParsingTests (main) where

import DatraLanguage.AST
  ( Expression (..)
  , renderExpression
  )
import DatraLanguage.AST.Syntax
  ( natural
  , (...)
  , (<:>)
  , (<+>)
  , (<..>)
  , (..+)
  , (..-)
  , (<.>)
  , (<@>)
  )
import DatraLanguage.AST.Syntax qualified as AST
import DatraLanguage.Diagnostics
  ( Located (Located)
  , SourcePosition (SourcePosition)
  , SourceSpan (SourceSpan)
  )
import Parsing (parseDatra, parseDatraAst, parseDatraLocated)

main :: IO ()
main = do
  assertLocatedParse
  assertAstSyntax
  assertAstOutput
    "flat map"
    "[1; 2; 10]"
    "(<:> 1 2 10)"
  assertAstOutput
    "nested map"
    "[[1; 2];[3;4]]"
    "(<+> (<:> 1 2) (<:> 3 4))"
  assertAstOutput
    "comments and whitespace"
    "  [1; # retain the next value\n [2; 3]] # end\n"
    "(<+> 1 (<:> 2 3))"
  assertAstOutput
    "empty nested maps are trimmed recursively"
    "[1; [[ ]  ]; 2]"
    "(<:> 1 2)"
  assertAstOutput
    "expansions are parenthesized at recursive depth"
    "[[[1;2];[3;4]];[5;6]]"
    "(<+> (<+> (<:> 1 2) (<:> 3 4)) (<:> 5 6))"
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
    "(<..> 2 10)"
  assertAstOutput
    "open super-ellipsis ranges"
    "[2..; 10..-]"
    "(<:> (..+ 2) (..- 10))"
  assertAstOutput
    "a prefix range starts at zero"
    "[..10]"
    "(<..> 0 10)"
  assertAstOutput
    "a prefix range greedily continues across a newline"
    "[..\n10]"
    "(<..> 0 10)"
  assertAstOutput
    "a postfix range can end before a closing delimiter"
    "[2..\n]"
    "(..+ 2)"
  assertAstOutput
    "a postfix range ends before lower-precedence access"
    "(...) .. @ 5"
    "(<@> (..+ ...) 5)"
  assertAstOutput
    "a postfix range ends before lower-precedence concatenation"
    "2.., 5"
    "(<.> (..+ 2) 5)"
  assertAstOutput
    "Haskell arithmetic precedence"
    "[1 + 2 * 3 ^ 4]"
    "(+ 1 (* 2 (^ 3 4)))"
  assertAstOutput
    "parentheses override arithmetic precedence"
    "[(1 + 2) * 3]"
    "(* (+ 1 2) 3)"
  assertAstOutput
    "right-nested addition keeps necessary parentheses"
    "[1 + (2 + 3)]"
    "(+ 1 (+ 2 3))"
  assertAstOutput
    "redundant parentheses are omitted"
    "[((1 + (2 * (3 ^ 4))))]"
    "(+ 1 (* 2 (^ 3 4)))"
  assertAstOutput
    "range endpoints accept arithmetic expressions"
    "[1 + 2..3 * 4]"
    "(<..> (+ 1 2) (* 3 4))"
  assertAstOutput
    "range concatenation"
    "[1..3, 5..7]"
    "(<.> (<..> 1 3) (<..> 5 7))"
  assertParsed
    "a trailing comma concatenates an empty map"
    "[1,]"
    (AtlasMap
      [ (<.>)
          (natural 1)
          (AtlasMap [])
      ])
  assertAstOutput
    "a trailing comma retains its semantic value"
    "[1,]"
    "(<.> 1 [])"
  assertAstOutput
    "a trailing comma works at the inferred map boundary"
    "1,"
    "(<.> 1 [])"
  assertAstOutput
    "a trailing comma can precede a newline and closing delimiter"
    "[1, # no right operand\n]"
    "(<.> 1 [])"
  assertAstOutput
    "a comma followed by an expression across a newline stays infix"
    "[1,\n2]"
    "(<.> 1 2)"
  assertParsed
    "a trailing comma is removed from an existing concatenation"
    "[1, 2,]"
    (AtlasMap
      [ (<.>)
          (natural 1)
          (natural 2)
      ])
  assertAstOutput
    "an existing concatenation does not gain an empty map"
    "[1, 2,]"
    "(<.> 1 2)"
  assertAstOutput
    "a trailing comma can precede a map separator"
    "[1,; 2]"
    "(<:> (<.> 1 []) 2)"
  assertAstOutput
    "access consumes a concatenated range insertion"
    "[... @ 1..3, 5..7]"
    "(<@> ... (<.> (<..> 1 3) (<..> 5 7)))"
  assertAstOutput
    "parentheses can concatenate an access result"
    "[(... @ 1), 2]"
    "(<.> (<@> ... 1) 2)"
  assertAstOutput
    "map expressions are concatenation operands"
    "[[1; 2], [3; 4]]"
    "(<.> (<:> 1 2) (<:> 3 4))"
  assertAstOutput
    "arithmetic and map expansion fixity conflict is parenthesized"
    "[[1 + 2]; [3 * 4]]"
    "(<+> (+ 1 2) (* 3 4))"
  assertAstOutput
    "outer map brackets are inferred"
    "2 + 3"
    "(+ 2 3)"
  assertAstOutput
    "completed lines become map elements"
    "2\n3"
    "(<:> 2 3)"
  assertAstOutput
    "a newline after an operator continues the expression"
    "2 +\n3\n4"
    "(<:> (+ 2 3) 4)"
  assertAstOutput
    "comments do not hide a required continuation"
    "2 + # continue addition\n3\n# blank comment line\n4"
    "(<:> (+ 2 3) 4)"
  assertAstOutput
    "blank lines do not create empty map elements"
    "\n# heading\n2\n\n# between values\n3\n"
    "(<:> 2 3)"
  assertAstOutput
    "a semicolon separates a postfix range from the next map line"
    "2..;\n3..-"
    "(<:> (..+ 2) (..- 3))"
  assertAstOutput
    "ellipsis is complete despite ending in dots"
    "...\n2"
    "(<:> ... 2)"
  assertAstOutput
    "bounded range and concatenation operators continue across lines"
    "2..\n4,\n5.."
    "(<.> (<..> 2 4) (..+ 5))"
  assertAstOutput
    "an ambiguous postfix range greedily consumes a following operand"
    "[2..\n4]"
    "(<..> 2 4)"
  assertAstOutput
    "exponentiation continues and remains right associative"
    "2 ^\n3 ^\n4"
    "(^ 2 (^ 3 4))"
  assertAstOutput
    "newlines separate expressions in an explicit map"
    "[2\n3]"
    "(<:> 2 3)"
  assertAstOutput
    "newline inference applies independently to nested maps"
    "[[1\n2]\n[3\n4]]"
    "(<+> (<:> 1 2) (<:> 3 4))"
  assertAstOutput
    "outer brackets are inferred unless both delimiters are present"
    "[1]\n2"
    "(<+> 1 2)"
  assertAstOutput
    "brackets inside comments do not affect outer bracket inference"
    "[1]\n2 # ] is only a comment"
    "(<+> 1 2)"
  assertAstOutput
    "operator continuation also applies in explicit maps"
    "[2 +\n3\n4]"
    "(<:> (+ 2 3) 4)"
  assertAstOutput
    "newlines inside unfinished expressions are ignored"
    "[2 + \n 3]"
    "(+ 2 3)"
  assertAstOutput
    "multiline parenthesized expressions remain one expression"
    "(2 +\n3)\n4"
    "(<:> (+ 2 3) 4)"
  assertParsed
    "exponentiation associates right"
    "[2 ^ 3 ^ 4]"
    (AtlasMap
      [ (AST.^)
          (natural 2)
          ((AST.^) (natural 3) (natural 4))
      ])
  assertParsed
    "addition associates left"
    "[1 + 2 + 3]"
    (AtlasMap
      [ (AST.+)
          ((AST.+) (natural 1) (natural 2))
          (natural 3)
      ])
  assertParsed
    "access associates left"
    "[... @ 1 @ 2]"
    (AtlasMap
      [ (<@>)
          ((<@>) (...) (natural 1))
          (natural 2)
      ])
  assertParsed
    "map is itself an expression"
    "[([1; 2], [3; 4]) @ 0]"
    (AtlasMap
      [ (<@>)
          ((<.>)
            (AtlasMap [natural 1, natural 2])
            (AtlasMap [natural 3, natural 4]))
          (natural 0)
      ])
  assertAstOutput
    "a single unbracketed expression becomes a singleton map"
    "10"
    "10"
  assertAstOutput
    "one trailing semicolon is ignored"
    "[1; 2; # trailing separator\n]"
    "(<:> 1 2)"
  assertRejected "multiple trailing semicolons are rejected" "[1; 2;;]"
  assertRejected "multiple trailing commas are rejected" "[1,,]"
  assertRejected
    "multiple trailing commas after concatenation are rejected"
    "[1, 2,,]"
  assertRejected "empty entries in the middle are rejected" "[1;;2]"
  assertRejected "bounded ranges are non-associative" "[1..2..3]"
  assertRejected "prefix and postfix ranges cannot be chained" "[..2..]"
  assertRejected "adjacent range markers cannot be chained" "[1....2]"
  assertRejected "the old explicit plus spelling is rejected" "[1..+]"
  assertAstOutput
    "parentheses permit an explicitly nested range"
    "[(1..2)..]"
    "(..+ (<..> 1 2))"
  assertParsed
    "a parenthesized Ellipsis can be a postfix range argument"
    "[(...)..]"
    (AtlasMap
      [(..+) (...)])
  assertAstOutput
    "a parenthesized Ellipsis can be a prefix range argument"
    "[..(...)]"
    "(<..> 0 ...)"
  assertAstOutput
    "a parenthesized Ellipsis can be a bounded range argument"
    "[(...)..2; 1..(...)]"
    "(<:> (<..> ... 2) (<..> 1 ...))"
  assertRejected
    "a bare Ellipsis cannot be a postfix range argument"
    "[... ..]"
  assertRejected
    "a bare Ellipsis cannot be a prefix range argument"
    "[.. ...]"
  assertRejected
    "a bare Ellipsis cannot be a bounded lower argument"
    "[... .. 2]"
  assertRejected
    "a bare Ellipsis cannot be a bounded upper argument"
    "[1.. ...]"
  assertRejected "addition requires a right operand" "[1 +]"
  assertRejected "parentheses must be balanced" "[(1 + 2]"
  assertRejected
    "an operator starting the next line is not retroactive continuation"
    "2\n+ 3"
  assertRejected
    "separate maps with both outer delimiter characters are not rewrapped"
    "[1]\n[2]"

assert :: String -> Bool -> IO ()
assert label condition
  | condition = pure ()
  | otherwise = fail ("test failed: " <> label)

assertLocatedParse :: IO ()
assertLocatedParse =
  case parseDatraLocated "[1; 2]" of
    Left message -> fail ("located parse unexpectedly failed: " <> message)
    Right
        (Located
          (SourceSpan source start end)
          (AtlasMap [EllipsisNatural 1, EllipsisNatural 2])) ->
      assert
        "located parsing uses an in-memory source span"
        ( source == "<input>"
          && start == SourcePosition 0 1 1
          && end == SourcePosition 6 1 7
        )
    Right actual ->
      fail ("located parse returned an unexpected value: " <> show actual)

assertAstSyntax :: IO ()
assertAstSyntax = do
  assert "sequential and expansion symbols construct canonical AST nodes"
    ( renderExpression
        ((natural 1 <:> natural 2) <+> (natural 3 <:> natural 4))
        == "(<+> (<:> 1 2) (<:> 3 4))"
    )
  assert "range, arithmetic, concatenation, and access symbols construct ASTs"
    ( renderExpression
        ( ((natural 1 AST.+ natural 2 AST.* natural 3) <..> (...))
            <.> ((natural 4 ..+) <@> (natural 5 ..-))
        )
        == "(<.> (<..> (+ 1 (* 2 3)) ...) (<@> (..+ 4) (..- 5)))"
    )

assertAstOutput :: String -> String -> String -> IO ()
assertAstOutput label source expected =
  case renderExpression <$> parseDatra source of
    Left message -> fail (label <> ": unexpected parse failure: " <> message)
    Right actual
      | actual == expected -> assertAstRoundTrip label actual
      | otherwise ->
          fail
            ( label
                <> ": expected "
                <> show expected
                <> ", got "
                <> show actual
            )

assertAstRoundTrip :: String -> String -> IO ()
assertAstRoundTrip label renderedAst =
  case renderExpression <$> parseDatraAst renderedAst of
    Left message ->
      fail (label <> ": emitted AST could not be parsed: " <> message)
    Right roundTripped
      | roundTripped == renderedAst -> pure ()
      | otherwise ->
          fail
            ( label
                <> ": AST round trip changed "
                <> show renderedAst
                <> " to "
                <> show roundTripped
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
