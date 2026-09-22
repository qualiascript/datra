{-# LANGUAGE PostfixOperators #-}

module DatraParsingTests (main) where

import Data.Char (chr, toUpper)
import DatraLanguage.AST
  ( Expression (..)
  , Identifier (Identifier)
  , normalizeExpression
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
  , (<~>)
  )
import DatraLanguage.AST.Syntax qualified as AST
import DatraLanguage.Diagnostics
  ( Located (Located)
  , SourcePosition (SourcePosition)
  , SourceSpan (SourceSpan)
  )
import Parsing
  ( ResourceEnvelope (..)
  , parseDatra
  , parseDatraAst
  , parseDatraLocated
  , parseDatraLocatedResourceWithSourceName
  )
import Numeric (showHex)
import Hedgehog qualified as H
import Hedgehog.Gen qualified as Gen
import Hedgehog.Range qualified as Range
import Test.Tasty (TestTree, defaultMain, testGroup)
import Test.Tasty.Hedgehog (testProperty)
import Test.Tasty.HUnit (assertBool, testCase)

main :: IO ()
main = defaultMain testTree

testTree :: TestTree
testTree =
  testGroup "Datra parser"
    [ testCase "syntax regressions" regressionTests
    , testGroup "properties"
        [ testProperty "rendered ASTs parse canonically" propAstRoundTrip
        , testProperty "natural maps parse in order" propNaturalMapParsing
        ]
    ]

regressionTests :: IO ()
regressionTests = do
  assertLocatedParse
  assertResourceEnvelopes
  assertAstSyntax
  assertAstOutput
    "flat map"
    "(1; 2; 10)"
    "(<:> 1 2 10)"
  assertAstOutput
    "nested map"
    "((1; 2);(3;4))"
    "(<+> (<:> 1 2) (<:> 3 4))"
  assertAstOutput
    "unary parentheses do not create map levels"
    "((Nat); (Nat))"
    "(<:> Nat Nat)"
  assertAstOutput
    "left-nested map structure remains explicit"
    "((Nat; Nat); Nat)"
    "(<+> (<:> Nat Nat) Nat)"
  assertAstOutput
    "right-nested map structure remains explicit"
    "(Nat; (Nat; Nat))"
    "(<+> Nat (<:> Nat Nat))"
  assertAstOutput
    "comments and whitespace"
    "  (1; # retain the next value\n (2; 3)) # end\n"
    "(<+> 1 (<:> 2 3))"
  assertAstOutput
    "empty nested maps are trimmed recursively"
    "(1; (( )  ); 2)"
    "(<:> 1 2)"
  assertAstOutput
    "expansions are parenthesized at recursive depth"
    "(((1;2);(3;4));(5;6))"
    "(<+> (<+> (<:> 1 2) (<:> 3 4)) (<:> 5 6))"
  assertAstOutput
    "the empty map is retained at the root"
    "()"
    "()"
  assertAstOutput
    "ellipsis literal"
    "(...)"
    "..."
  assertAstOutput
    "specification into a NaturalRange"
    "2..5 ~> from 0 upwards"
    "(<~> (<..> 2 5) (from 0 upwards))"
  assertAstOutput
    "bounded ValuedNaturalRange"
    "within 2 to 5"
    "(within 2 to 5)"
  assertAstOutput
    "upwards ValuedNaturalRange"
    "within 2 upwards"
    "(within 2 upwards)"
  assertAstOutput
    "NaturalType literal"
    "Nat"
    "Nat"
  assertAstOutput
    "EllipsisNatural specification into NaturalType"
    "2 ~> Nat"
    "(<~> 2 Nat)"
  assertRejected
    "shared bounded range suffix is not an expression"
    "2 to 5"
  assertRejected
    "shared upwards range suffix is not an expression"
    "2 upwards"
  assertAstOutput
    "specification binds after access and concatenation"
    "1, 2 @ from 0 upwards ~> from 0 to 10"
    "(<~> (<@> (<.> 1 2) (from 0 upwards)) (from 0 to 10))"
  assertAstOutput
    "access after a specification projects its fibers"
    "(2; 3) ~> (Nat; Nat) @ 0"
    "(<@> (<~> (<:> 2 3) (<:> Nat Nat)) 0)"
  assertAstOutput
    "specification chains associate through the intermediate federation"
    "2..3 ~> from 2 to 5 ~> from 2 to 8"
    "(<~> (<~> (<..> 2 3) (from 2 to 5)) (from 2 to 8))"
  assertAstOutput
    "reverse specification reverses its operands"
    "from 2 to 5 <~ 2..3"
    "(<~> (<..> 2 3) (from 2 to 5))"
  assertAstOutput
    "reverse specification accepts parenthesized composite operands"
    "($a; Nat) <~ ($a; 50)"
    "(<~> (<:> $a 50) (<:> $a Nat))"
  assertAstOutput
    "reverse specification accepts concatenated composite operands"
    "$a, from 1 to 10 <~ $a, 3, 4, 5"
    "(<~> (<.> $a (<.> 3 (<.> 4 5))) (<.> $a (from 1 to 10)))"
  assertAstOutput
    "reverse specification chains associate right"
    "from 2 to 8 <~ from 2 to 5 <~ 2..3"
    "(<~> (<~> (<..> 2 3) (from 2 to 5)) (from 2 to 8))"
  assertAstOutput
    "reverse specification binds after access and concatenation"
    "from 0 to 10 <~ 1, 2 @ from 0 upwards"
    "(<~> (<@> (<.> 1 2) (from 0 upwards)) (from 0 to 10))"
  assertAstOutput
    "a postfix range can precede reverse specification"
    "2.. <~ from 2 to 5"
    "(<~> (from 2 to 5) (..+ 2))"
  assertAstOutput
    "simple identifier type"
    "x : Nat"
    "(: x Nat)"
  assertAstOutput
    "full identifier assignment"
    "x : Nat := 5"
    "(:= x Nat 5)"
  assertAstOutput
    "assignment specified into its identifier target"
    "(a : Nat := 5) ~> (a : Nat)"
    "(<~> (:= a Nat 5) (: a Nat))"
  assertAstOutput
    "reverse specification between different identifier names"
    "(a : Nat) <~ (b := 10)"
    "(<~> (:= b 10) (: a Nat))"
  assertAstOutput
    "reverse assignment chain widens nested annotations"
    ( "(d : within 0 to 100) <~ "
        <> "(d : within 20 to 40 := 28) <~ "
        <> "(d : within 25 to 35 := 28) <~ (d := 28)"
    )
    ( "(<~> (<~> (<~> (:= d 28) "
        <> "(:= d (within 25 to 35) 28)) "
        <> "(:= d (within 20 to 40) 28)) "
        <> "(: d (within 0 to 100)))"
    )
  assertAstOutput
    "reverse assignment chain retains an incompatible intermediate annotation"
    ( "(x : within 1 to 10) <~ "
        <> "(x : within 5 to 20) <~ (x := 8)"
    )
    ( "(<~> (<~> (:= x 8) (: x (within 5 to 20))) "
        <> "(: x (within 1 to 10)))"
    )
  assertAstOutput
    "binary identifier assignment"
    "x := 5"
    "(:= x 5)"
  assertAstOutput
    "redundant assignment type canonicalizes to binary syntax"
    "x : 5 := 5"
    "(:= x 5)"
  assertAstOutput
    "access binds inside the assignment value"
    "x : Nat := (1; 2) @ 0"
    "(:= x Nat (<@> (<:> 1 2) 0))"
  assertAstOutput
    "accessing an identifier operation requires grouping"
    "(x : Nat) @ 0"
    "(<@> (: x Nat) 0)"
  assertAstOutput
    "bracket access uses the identifier map view"
    "(x : Nat)[0]"
    "(<@> (: x Nat) 0)"
  assertAstOutput
    "bracket access uses the assignment specification view"
    "(x : Nat := 5)[1]"
    "(<@> (:= x Nat 5) 1)"
  assertAstOutput
    "unparenthesized access belongs to the identifier type operand"
    "x : Nat @ 0"
    "(: x (<@> Nat 0))"
  assertAstOutput
    "identifier names share canonical continuation characters"
    "A_0'z : Nat"
    "(: A_0'z Nat)"
  assertRejected
    "identifier operations reject expression left sides"
    "(2 + 2) : Nat := 4"
  assertRejected
    "identifier operations reject dollar-prefixed left sides"
    "$x : Nat := 4"
  assertRejected
    "bare identifiers are not expressions"
    "x"
  assertParsed
    "IdentifierString produces an ASCII string literal"
    "$text"
    (AsciiStringLiteral "text")
  assertAstOutput
    "IdentifierString accepts all canonical continuation characters"
    "$A_0'z"
    "$A_0'z"
  assertAstOutput
    "StandardString canonicalizes to IdentifierString when possible"
    "\"text\""
    "$text"
  assertAstOutput
    "StandardString supports the empty string"
    "\"\""
    "\"\""
  assertAstOutput
    "StandardString escapes quote and backslash"
    "\"say \\\"hi\\\" and \\\\ path\""
    "\"say \\\"hi\\\" and \\\\ path\""
  assertAstOutput
    "StandardString decodes and canonicalizes escaped newlines"
    "\"first\\nsecond\""
    "\"first\\nsecond\""
  assertAstOutput
    "StandardString accepts and canonicalizes hexadecimal byte escapes"
    "\"\\0\\8\\08\\09\\1f\\7F\\ff\""
    "\"\\00\\08\\08\\09\\1F\\7F\\FF\""
  assertParsed
    "StandardString hexadecimal escapes select ASCII-map characters"
    "\"\\0\\8\\08\\09\\1f\\7F\\ff\""
    (AsciiStringLiteral ['\0', '\8', '\8', '\9', '\31', '\127', '\255'])
  assertAstOutput
    "StandardString canonicalizes a hexadecimal newline to its named escape"
    "\"\\0A\""
    "\"\\n\""
  assertAstOutput
    "StandardString leaves nonsyntactic keyboard-visible characters literal"
    "\" !%&'()*+,-./:;<=>?@^_`{|}~\""
    "\" !%&'()*+,-./:;<=>?@^_`{|}~\""
  assertAstOutput
    "StandardString line comments retain their terminating newline"
    "\"Comment test#this is a comment!\n\""
    "\"Comment test\\n\""
  assertParsed
    "StandardString comments may terminate at the closing quote"
    "\"Hello#, world!\""
    (AsciiStringLiteral "Hello")
  assertAstOutput
    "StandardString comments ending at a quote retain canonical rendering"
    "\"Hello#, world!\""
    "$Hello"
  assertAstOutput
    "StandardString escapes a literal hash"
    "\"literal \\# character\""
    "\"literal \\# character\""
  assertAllHexadecimalAsciiEscapes
  assertAstOutput
    "StandardString preserves multiline leading and trailing characters"
    "(\"  first\nsecond  \")"
    "\"  first\\nsecond  \""
  assertParsed
    "StandardString treats syntax and comments as literal contents"
    "(\"\\#;(value)\n$still_text\")"
    (AsciiStringLiteral "#;(value)\n$still_text")
  assertAstOutput
    "strings use the ordinary concatenation operator"
    "$ab, $cd"
    "(<.> $ab $cd)"
  assertAstOutput
    "strings use the ordinary access operator"
    "$abcd @ 1..3"
    "(<@> $abcd (<..> 1 3))"
  assertAstOutput
    "bounded super-ellipsis range"
    "(2..10)"
    "(<..> 2 10)"
  assertAstOutput
    "open super-ellipsis ranges"
    "(2..; 10..-)"
    "(<:> (..+ 2) (..- 10))"
  assertAstOutput
    "a prefix range starts at zero"
    "(..10)"
    "(<..> 0 10)"
  assertAstOutput
    "inclusive natural range"
    "from 2 to 5"
    "(from 2 to 5)"
  assertAstOutput
    "open inclusive natural range"
    "from 2 upwards"
    "(from 2 upwards)"
  assertAstOutput
    "natural range access"
    "1, 2, 3 @ from 1 upwards"
    "(<@> (<.> 1 (<.> 2 3)) (from 1 upwards))"
  assertAstOutput
    "bracket access binds before arithmetic"
    "$a + $b[$c]"
    "(+ $a (<@> $b $c))"
  assertAstOutput
    "grouping moves bracket access outside arithmetic"
    "($a + $b)[$c]"
    "(<@> (+ $a $b) $c)"
  assertAstOutput
    "bracket access chains associate left"
    "$a[$b][$c]"
    "(<@> (<@> $a $b) $c)"
  assertAstOutput
    "ordinary access sees a tightly bound insertion"
    "$a @ $b[$c]"
    "(<@> $a (<@> $b $c))"
  assertAstOutput
    "bracket insertion accepts ordinary access"
    "$a[$b @ $c]"
    "(<@> $a (<@> $b $c))"
  assertAstOutput
    "bracket insertion accepts a postfix range"
    "$a[1..]"
    "(<@> $a (..+ 1))"
  assertAstOutput
    "bracket insertion accepts an explicitly constructed map"
    "$a[(1; 2)]"
    "(<@> $a (<:> 1 2))"
  assertAstOutput
    "bracket access accepts an explicitly constructed map on the left"
    "(2; 3)[0]"
    "(<@> (<:> 2 3) 0)"
  assertAstOutput
    "grouping permits bracket access on a whole specification"
    "((2; 3) ~> (Nat; Nat))[0]"
    "(<@> (<~> (<:> 2 3) (<:> Nat Nat)) 0)"
  assertAstOutput
    "natural range keywords continue across lines"
    "from\n2\nto\n5"
    "(from 2 to 5)"
  assertAstOutput
    "a prefix range greedily continues across a newline"
    "(..\n10)"
    "(<..> 0 10)"
  assertAstOutput
    "a postfix range can end before a closing delimiter"
    "(2..\n)"
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
    "(1 + 2 * 3 ^ 4)"
    "(+ 1 (* 2 (^ 3 4)))"
  assertAstOutput
    "parentheses override arithmetic precedence"
    "((1 + 2) * 3)"
    "(* (+ 1 2) 3)"
  assertAstOutput
    "right-nested addition keeps necessary parentheses"
    "(1 + (2 + 3))"
    "(+ 1 (+ 2 3))"
  assertAstOutput
    "redundant parentheses are omitted"
    "(((1 + (2 * (3 ^ 4)))))"
    "(+ 1 (* 2 (^ 3 4)))"
  assertAstOutput
    "range endpoints accept arithmetic expressions"
    "(1 + 2..3 * 4)"
    "(<..> (+ 1 2) (* 3 4))"
  assertAstOutput
    "range concatenation"
    "(1..3, 5..7)"
    "(<.> (<..> 1 3) (<..> 5 7))"
  assertParsed
    "a trailing comma concatenates an empty map"
    "(1,)"
    ((<.>)
      (natural 1)
      (AtlasMap []))
  assertAstOutput
    "a trailing comma retains its semantic value"
    "(1,)"
    "(<.> 1 ())"
  assertAstOutput
    "a trailing comma works at the inferred map boundary"
    "1,"
    "(<.> 1 ())"
  assertAstOutput
    "a trailing comma can precede a newline and closing delimiter"
    "(1, # no right operand\n)"
    "(<.> 1 ())"
  assertAstOutput
    "a comma followed by an expression across a newline stays infix"
    "(1,\n2)"
    "(<.> 1 2)"
  assertParsed
    "a trailing comma is removed from an existing concatenation"
    "(1, 2,)"
    ((<.>)
      (natural 1)
      (natural 2))
  assertAstOutput
    "an existing concatenation does not gain an empty map"
    "(1, 2,)"
    "(<.> 1 2)"
  assertAstOutput
    "a trailing comma can precede a map separator"
    "(1,; 2)"
    "(<:> (<.> 1 ()) 2)"
  assertAstOutput
    "access consumes a concatenated range insertion"
    "(... @ 1..3, 5..7)"
    "(<@> ... (<.> (<..> 1 3) (<..> 5 7)))"
  assertAstOutput
    "parentheses can concatenate an access result"
    "((... @ 1), 2)"
    "(<.> (<@> ... 1) 2)"
  assertAstOutput
    "map expressions are concatenation operands"
    "((1; 2), (3; 4))"
    "(<.> (<:> 1 2) (<:> 3 4))"
  assertAstOutput
    "unary grouping does not manufacture map expansion"
    "((1 + 2); (3 * 4))"
    "(<:> (+ 1 2) (* 3 4))"
  assertAstOutput
    "outer map parentheses are inferred"
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
    "(2..\n4)"
    "(<..> 2 4)"
  assertAstOutput
    "exponentiation continues and remains right associative"
    "2 ^\n3 ^\n4"
    "(^ 2 (^ 3 4))"
  assertAstOutput
    "newlines separate expressions in an explicit map"
    "(2\n3)"
    "(<:> 2 3)"
  assertAstOutput
    "newline inference applies independently to nested maps"
    "((1\n2)\n(3\n4))"
    "(<+> (<:> 1 2) (<:> 3 4))"
  assertAstOutput
    "separately parenthesized expressions form an implicit outer map"
    "(1)\n2"
    "(<:> 1 2)"
  assertAstOutput
    "parentheses inside comments do not affect outer-map inference"
    "(1)\n2 # ) is only a comment"
    "(<:> 1 2)"
  assertAstOutput
    "operator continuation also applies in explicit maps"
    "(2 +\n3\n4)"
    "(<:> (+ 2 3) 4)"
  assertAstOutput
    "newlines inside unfinished expressions are ignored"
    "(2 + \n 3)"
    "(+ 2 3)"
  assertAstOutput
    "multiline parenthesized expressions remain one expression"
    "(2 +\n3)\n4"
    "(<:> (+ 2 3) 4)"
  assertParsed
    "exponentiation associates right"
    "(2 ^ 3 ^ 4)"
    ((AST.^)
      (natural 2)
      ((AST.^) (natural 3) (natural 4)))
  assertParsed
    "addition associates left"
    "(1 + 2 + 3)"
    ((AST.+)
      ((AST.+) (natural 1) (natural 2))
      (natural 3))
  assertParsed
    "access associates left"
    "(... @ 1 @ 2)"
    ((<@>)
      ((<@>) (...) (natural 1))
      (natural 2))
  assertParsed
    "map is itself an expression"
    "(((1; 2), (3; 4)) @ 0)"
    ((<@>)
      ((<.>)
        (AtlasMap [natural 1, natural 2])
        (AtlasMap [natural 3, natural 4]))
      (natural 0))
  assertAstOutput
    "a single unparenthesized expression stays itself"
    "10"
    "10"
  assertAstOutput
    "one trailing semicolon is ignored"
    "(1; 2; # trailing separator\n)"
    "(<:> 1 2)"
  assertRejected "multiple trailing semicolons are rejected" "(1; 2;;)"
  assertRejected "IdentifierString requires a leading canonical character" "$0bad"
  assertRejected "IdentifierString rejects a missing body" "$"
  assertRejected "IdentifierString rejects noncanonical continuation" "$bad-name"
  assertRejected "StandardString rejects unsupported escapes" "\"bad\\t\""
  assertRejected "StandardString rejects an unterminated literal" "\"bad"
  assertRejected "ASCII strings reject characters outside the ASCII map" "\"λ\""
  assertRejected "multiple trailing commas are rejected" "(1,,)"
  assertRejected "standalone brackets are not an empty map" "[]"
  assertRejected "bracket access requires an insertion" "$a[]"
  assertRejected
    "multiple trailing commas after concatenation are rejected"
    "(1, 2,,)"
  assertRejected "empty entries in the middle are rejected" "(1;;2)"
  assertRejected "bounded ranges are non-associative" "(1..2..3)"
  assertRejected "prefix and postfix ranges cannot be chained" "(..2..)"
  assertRejected "adjacent range markers cannot be chained" "(1....2)"
  assertRejected "the old explicit plus spelling is rejected" "(1..+)"
  assertRejected
    "natural range origins must be literal EllipsisNaturals"
    "from (1 + 2) to 5"
  assertRejected
    "natural range targets must be literal EllipsisNaturals"
    "from 1 to (2 + 3)"
  assertRejected "natural range keywords require separators" "from1to2"
  assertAstOutput
    "parentheses permit an explicitly nested range"
    "((1..2)..)"
    "(..+ (<..> 1 2))"
  assertParsed
    "a parenthesized Ellipsis can be a postfix range argument"
    "((...)..)"
    ((..+) (...))
  assertAstOutput
    "a parenthesized Ellipsis can be a prefix range argument"
    "(..(...))"
    "(<..> 0 ...)"
  assertAstOutput
    "a parenthesized Ellipsis can be a bounded range argument"
    "((...)..2; 1..(...))"
    "(<:> (<..> ... 2) (<..> 1 ...))"
  assertRejected
    "a bare Ellipsis cannot be a postfix range argument"
    "(... ..)"
  assertRejected
    "a bare Ellipsis cannot be a prefix range argument"
    "(.. ...)"
  assertRejected
    "a bare Ellipsis cannot be a bounded lower argument"
    "(... .. 2)"
  assertRejected
    "a bare Ellipsis cannot be a bounded upper argument"
    "(1.. ...)"
  assertRejected "addition requires a right operand" "(1 +)"
  assertRejected "parentheses must be balanced" "((1 + 2)"
  assertRejected
    "an operator starting the next line is not retroactive continuation"
    "2\n+ 3"
  assertAstOutput
    "separate parenthesized maps form an implicit outer map"
    "(1)\n(2)"
    "(<:> 1 2)"

assert :: String -> Bool -> IO ()
assert = assertBool

propAstRoundTrip :: H.Property
propAstRoundTrip = H.property $ do
  expressionValue <- H.forAll genExpression
  let rendered = renderExpression expressionValue
  case parseDatraAst rendered of
    Left message -> do
      H.footnote message
      H.failure
    Right roundTripped -> renderExpression roundTripped H.=== rendered

propNaturalMapParsing :: H.Property
propNaturalMapParsing = H.property $ do
  values <- H.forAll
    (Gen.list (Range.linear 0 40) (Gen.integral (Range.linear 0 100000)))
  let source = "(" <> joinWith "; " (map show values) <> ")"
      expected = normalizeExpression (AtlasMap (map EllipsisNatural values))
  parseDatra source H.=== Right expected

genExpression :: H.Gen Expression
genExpression =
  Gen.recursive Gen.choice
    [ EllipsisNatural <$> Gen.integral (Range.linear 0 1000)
    , pure EllipsisLiteral
    , AsciiStringLiteral
        <$> Gen.list (Range.linear 0 24) (Gen.enum '\0' '\255')
    , pure NaturalType
    , NaturalRange
        <$> Gen.integral (Range.linear 0 1000)
        <*> Gen.integral (Range.linear 0 1000)
    , NaturalRangeUpwards <$> Gen.integral (Range.linear 0 1000)
    , ValuedNaturalRange
        <$> Gen.integral (Range.linear 0 1000)
        <*> Gen.integral (Range.linear 0 1000)
    , ValuedNaturalRangeUpwards <$> Gen.integral (Range.linear 0 1000)
    ]
    [ AtlasMap <$> Gen.list (Range.linear 0 6) genExpression
    , MapSequence <$> Gen.list (Range.linear 0 6) genExpression
    , Gen.subterm2 genExpression genExpression MapExpansion
    , Gen.subterm2 genExpression genExpression SuperEllipsisRange
    , Gen.subterm genExpression SuperEllipsisRangePlus
    , Gen.subterm genExpression SuperEllipsisRangeMinus
    , Gen.subterm2 genExpression genExpression Addition
    , Gen.subterm2 genExpression genExpression Multiplication
    , Gen.subterm2 genExpression genExpression Exponentiation
    , Gen.subterm2 genExpression genExpression MapConcatenation
    , Gen.subterm2 genExpression genExpression MapAccess
    , Gen.subterm2 genExpression genExpression MapSpecification
    , IdentifierOperation
        <$> genIdentifier
        <*> genExpression
        <*> Gen.maybe genExpression
    ]

genIdentifier :: H.Gen Identifier
genIdentifier = do
  first <- Gen.element (['_'] <> ['a' .. 'z'] <> ['A' .. 'Z'])
  rest <-
    Gen.list
      (Range.linear 0 12)
      (Gen.element
        (['_', '\'']
          <> ['a' .. 'z']
          <> ['A' .. 'Z']
          <> ['0' .. '9']))
  pure (Identifier (first : rest))

joinWith :: String -> [String] -> String
joinWith _ [] = ""
joinWith _ [value] = value
joinWith separator (value : values) =
  value <> separator <> joinWith separator values

assertAllHexadecimalAsciiEscapes :: IO ()
assertAllHexadecimalAsciiEscapes = do
  mapM_ assertTwoDigitEscape [0 .. 255]
  mapM_ assertOneDigitEscape [0 .. 15]
  where
    assertTwoDigitEscape byteValue =
      assertHexadecimalEscape
        ("two-digit hexadecimal escape " <> hexadecimalByte byteValue)
        (hexadecimalByte byteValue)
        byteValue

    assertOneDigitEscape byteValue =
      assertHexadecimalEscape
        ("one-digit hexadecimal escape " <> hexadecimalDigit byteValue)
        (hexadecimalDigit byteValue)
        byteValue

    assertHexadecimalEscape label digits byteValue =
      assertParsed
        label
        ("\"\\" <> digits <> "\"")
        (AsciiStringLiteral [chr byteValue])

    hexadecimalByte byteValue =
      case hexadecimalDigit byteValue of
        [digit] -> ['0', digit]
        digits -> digits

    hexadecimalDigit byteValue =
      map toUpper (showHex byteValue "")

assertLocatedParse :: IO ()
assertLocatedParse =
  case parseDatraLocated "(1; 2)" of
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

assertResourceEnvelopes :: IO ()
assertResourceEnvelopes = do
  assertEnvelope
    "explicit outer map parentheses"
    "(1; 2)"
    ExplicitMapEnvelope
  assertEnvelope
    "implicit newline map"
    "1\n2"
    ImplicitMapEnvelope
  assertEnvelope
    "parenthesized operands are not an outer envelope"
    "(1) <~ (2)"
    ImplicitMapEnvelope
  where
    assertEnvelope label source expected =
      case parseDatraLocatedResourceWithSourceName "<input>" source of
        Left message -> fail (label <> ": unexpected failure: " <> message)
        Right (actual, _) -> assert label (actual == expected)

assertAstSyntax :: IO ()
assertAstSyntax = do
  assert "ASCII-string syntax chooses its canonical spelling"
    ( renderExpression (AST.asciiString "name_1") == "$name_1"
      && renderExpression (AST.asciiString "a\"b\\c\n")
        == "\"a\\\"b\\\\c\\n\""
    )
  assert "sequential and expansion symbols construct canonical AST nodes"
    ( renderExpression
        ((natural 1 <:> natural 2) <+> (natural 3 <:> natural 4))
        == "(<+> (<:> 1 2) (<:> 3 4))"
    )
  assert "empty and unary AST products normalize structurally"
    ( renderExpression (MapSequence [natural 1]) == "1"
      && renderExpression (MapExpansion (AtlasMap []) (natural 1)) == "1"
      && renderExpression (MapExpansion (natural 1) (AtlasMap [])) == "1"
    )
  assert "range, arithmetic, concatenation, and access symbols construct ASTs"
    ( renderExpression
        ( ((natural 1 AST.+ natural 2 AST.* natural 3) <..> (...))
            <.> ((natural 4 ..+) <@> (natural 5 ..-))
        )
        == "(<.> (<..> (+ 1 (* 2 3)) ...) (<@> (..+ 4) (..- 5)))"
    )
  assert "the specification symbol constructs its canonical AST node"
    ( renderExpression
        (((natural 2 <..> natural 5) <~> AST.fromUpwards 0))
        == "(<~> (<..> 2 5) (from 0 upwards))"
    )
  assert "valued natural range constructors retain their distinct prefix"
    ( renderExpression (AST.withinTo 2 5) == "(within 2 to 5)"
      && renderExpression (AST.withinUpwards 2)
        == "(within 2 upwards)"
      && renderExpression AST.naturalType == "Nat"
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
