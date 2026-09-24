{-# LANGUAGE PostfixOperators #-}

module DatraParsingTests (main) where

import Data.Char (chr, toUpper)
import DatraLanguage.AST
  ( Expression (..)
  , IdentifierString (IdentifierString)
  , StringTemplatePart (..)
  , normalizeExpression
  , renderExpression
  , toOperatorExpression
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
  , (~>)
  )
import DatraLanguage.AST.Syntax qualified as AST
import DatraLanguage.AST.Reserved qualified as Reserved
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
  assertAstOutput "eval consumes a semicolon-separated target"
    "eval \"x : 3, (b : 8; 2)\", x : 3; {a? : Nat := 2, b? : Nat}"
    (Eval (AsciiStringLiteral "x : 3, (b : 8; 2)")
      (AtlasMap
        [ AST.identifierType "x" (natural 3)
        , ArgumentMap
            [ EitherType (AST.assignment "a" NaturalType (natural 2)) NaturalType
            , EitherType (AST.identifierType "b" NaturalType) NaturalType
            ]
        ]))
  assertAstOutput "eval consumes newline-separated target components"
    "eval \"(1; 2)\", Nat\nNat"
    (Eval (AsciiStringLiteral "(1; 2)") (AtlasMap [NaturalType, NaturalType]))
  assertAstOutput "parentheses delimit eval before access and arithmetic"
    "(eval \"(b : 8; 2)\", {a? : Nat, b? : Nat})[1] * 5"
    (Multiplication
      (MapAccess
        (Eval (AsciiStringLiteral "(b : 8; 2)")
          (ArgumentMap
            [ EitherType (AST.identifierType "a" NaturalType) NaturalType
            , EitherType (AST.identifierType "b" NaturalType) NaturalType]))
        (natural 1)) (natural 5))
  assertAstOutput "eval accepts a computed parenthesized source"
    "eval (\"1\", \"2\"), Int"
    (Eval (MapConcatenation (AsciiStringLiteral "1") (AsciiStringLiteral "2")) IntegerType)
  assertRejected "eval requires its source-target comma" "eval \"2\" Nat"
  assertRejected "eval requires a target" "eval \"2\","
  assertRejected "eval requires a source" "eval , Nat"
  assertRejected "eval is reserved as a bare identifier" "eval : Nat"
  assertAstOutput "eval keyword respects identifier boundaries"
    "evaluate : Nat" (AST.identifierType "evaluate" NaturalType)
  assertAstOutput "argument map uses existing map arity"
    "{b := 8; 2}"
    (ArgumentMap [AST.assignment "b" (natural 8) (natural 8), natural 2])
  assertAstOutput "empty argument map" "{}" (AtlasMap [])
  assertAstOutput "comma argument map exposes both members"
    "{b := 8, 2}"
    (ArgumentMap [AST.assignment "b" (natural 8) (natural 8), natural 2])
  assertAstOutput "parenthesized concatenation remains one argument"
    "{(1, 2), 3}"
    (ArgumentMap [MapConcatenation (natural 1) (natural 2), natural 3])
  assertAstOutput "argument map permits a trailing comma"
    "{1, 2,}" (ArgumentMap [natural 1, natural 2])
  assertAstOutput "unary argument map" "{2}" (natural 2)
  assertAstOutput "argument map supports newline separators"
    "{1\n2}" (ArgumentMap [natural 1, natural 2])
  assertParsed "argument map AST round trip"
    "{a? : Nat; b? : String}"
    (ArgumentMap
      [EitherType (AST.identifierType "a" NaturalType) NaturalType
      ,EitherType (AST.identifierType "b" StringType) StringType])
  assert "reserved symbols have unique identifier strings"
    Reserved.reservedSymbolIdentifiersAreUnique
  assertAstOutput
    "extract applies to a parenthesized reverse specification"
    "%(\"%Iden %Int\" <~ \"alco 100\")"
    (Extract
      (MapSpecification
        (AsciiStringLiteral "alco 100")
        (StringTemplate
          [ StringTemplateInterpolation IdentifierValueType
          , StringTemplateLiteral " "
          , StringTemplateInterpolation IntegerType
          ])))
  assertParsed
    "extract binds before bracket access"
    "%String[0]"
    (MapAccess (Extract StringType) (natural 0))
  mapM_
    (\reservedSymbol ->
      assertRejected
        ("reserved symbol cannot be a bare identifier expression: "
          <> Reserved.reservedSymbolIdentifierString reservedSymbol)
        (Reserved.reservedSymbolIdentifierString reservedSymbol <> " : Nat"))
    Reserved.reservedSymbols
  assertLocatedParse
  assertResourceEnvelopes
  assertAstSyntax
  assertAstOutput
    "flat map"
    "(1; 2; 10)"
    (natural 1 <:> natural 2 <:> natural 10)
  assertAstOutput
    "nested map"
    "((1; 2);(3;4))"
    ((natural 1 <:> natural 2) <+> (natural 3 <:> natural 4))
  assertAstOutput
    "unary parentheses do not create map levels"
    "((Nat); (Nat))"
    (AST.naturalType <:> AST.naturalType)
  assertAstOutput
    "left-nested map structure remains explicit"
    "((Nat; Nat); Nat)"
    ((AST.naturalType <:> AST.naturalType) <+> AST.naturalType)
  assertAstOutput
    "right-nested map structure remains explicit"
    "(Nat; (Nat; Nat))"
    (AST.naturalType <+> (AST.naturalType <:> AST.naturalType))
  assertAstOutput
    "comments and whitespace"
    "  (1; # retain the next value\n (2; 3)) # end\n"
    (natural 1 <+> (natural 2 <:> natural 3))
  assertAstOutput
    "empty nested maps are trimmed recursively"
    "(1; (( )  ); 2)"
    (natural 1 <:> natural 2)
  assertAstOutput
    "expansions are parenthesized at recursive depth"
    "(((1;2);(3;4));(5;6))"
    ( ((natural 1 <:> natural 2) <+> (natural 3 <:> natural 4))
        <+> (natural 5 <:> natural 6)
    )
  assertAstOutput
    "the empty map is retained at the root"
    "()"
    AST.emptyMap
  assertAstOutput
    "ellipsis literal"
    "(...)"
    (...)
  assertAstOutput
    "specification into a NaturalRange"
    "2..5 ~> range 0 upwards"
    ((natural 2 <..> natural 5) ~> AST.fromUpwards 0)
  assertAstOutput
    "bounded ValuedNaturalRange"
    "from 2 to 5"
    (AST.withinTo 2 5)
  assertAstOutput
    "upwards ValuedNaturalRange"
    "from 2 upwards"
    (AST.withinUpwards 2)
  assertRejected
    "the old valued-range prefix is rejected"
    "within 2 to 5"
  assertRejected
    "the range prefix is reserved as an identifier expression"
    "range : Nat"
  assertAstOutput
    "the former valued-range prefix is available as an identifier"
    "within : Nat"
    (AST.identifierType "within" AST.naturalType)
  assertAstOutput
    "NaturalType literal"
    "Nat"
    AST.naturalType
  assertAstOutput
    "String type literal"
    "String"
    AST.stringType
  assertAstOutput
    "IntegerType literal"
    "Int"
    AST.integerType
  assertAstOutput
    "descending open integer range"
    "range -1 downwards"
    (AST.integerFromDownwards (-1))
  assertAstOutput
    "bounded valued integer range"
    "from -3 to 4"
    (AST.integerWithinTo (-3) 4)
  assertAstOutput
    "unary integer negation"
    "-6"
    (AST.minus (natural 6))
  assertAstOutput
    "integer subtraction"
    "5 - 8"
    ((AST.-) (natural 5) (natural 8))
  assertAstOutput
    "Boolean literal"
    "false"
    (AST.boolean False)
  assertAstOutput
    "Nothing literal"
    "nothing"
    AST.nothing
  assertAstOutput
    "Boolean type"
    "Bool"
    AST.booleanType
  assertAstOutput
    "Either surface operator"
    "False := 0 | True := 1"
    (AST.eitherType
      (AST.assignment "False" (natural 0) (natural 0))
      (AST.assignment "True" (natural 1) (natural 1)))
  assertAstOutput
    "Either is associative"
    "(0 | 1) | 2"
    (AST.eitherType
      (natural 0)
      (AST.eitherType (natural 1) (natural 2)))
  assertAstOutput
    "Boolean and, or, and not"
    "false and not true or true"
    (AST.or
      (AST.and (AST.boolean False) (AST.not (AST.boolean True)))
      (AST.boolean True))
  assertAstOutput
    "federation equality"
    "1 = 1"
    (AST.equal (natural 1) (natural 1))
  assertAstOutput
    "subfederation morphism check"
    "1 of Int"
    (AST.subfederation (natural 1) AST.integerType)
  assertAstOutput
    "subfederation check binds inside equality"
    "1 of Int = true"
    (AST.equal
      (AST.subfederation (natural 1) AST.integerType)
      (AST.boolean True))
  assertAstOutput
    "optional type suffix"
    "Nat?"
    (AST.optional AST.naturalType)
  assertAstOutput
    "optional suffix applies to a complete type expression"
    "(Nat | Int)?"
    (AST.optional (AST.eitherType AST.naturalType AST.integerType))
  assertAstOutput
    "optional identifier slot"
    "a? : Nat"
    (AST.eitherType
      (AST.identifierType "a" AST.naturalType)
      AST.naturalType)
  assertRejected
    "reserved names cannot be bare identifier expressions"
    "String : Nat"
  assertAstOutput
    "reserved names can be full-string identifier expressions"
    "\"String\" : Nat"
    (AST.identifierType "String" AST.naturalType)
  assertAstOutput
    "contextual range words remain bare identifier expressions"
    "to : Nat"
    (AST.identifierType "to" AST.naturalType)
  assertAstOutput
    "contextual range directions remain bare identifier expressions"
    "(upwards : Nat; downwards : Nat)"
    (AST.identifierType "upwards" AST.naturalType
      <:> AST.identifierType "downwards" AST.naturalType)
  assertAstOutput
    "uppercase built-in names remain bare identifier expressions"
    "False : Nat"
    (AST.identifierType "False" AST.naturalType)
  assertAstOutput
    "full-string identifier expressions compose with optional syntax"
    "\"Abc\"? : Nat"
    (AST.eitherType
      (AST.identifierType "Abc" AST.naturalType)
      AST.naturalType)
  assertAstOutput
    "optional assigned identifier slot"
    "a? : Nat := 5"
    (AST.eitherType
      (AST.assignment "a" AST.naturalType (natural 5))
      AST.naturalType)
  let optionalIntegerSlots =
        MapConcatenation
          (AST.eitherType
            (AST.identifierType "a" AST.integerType)
            AST.integerType)
          (AST.eitherType
            (AST.identifierType "b" AST.integerType)
            AST.integerType)
      integerPair = MapConcatenation (natural 12) (natural 23)
  assertAstOutput
    "optional identifier slots are concatenation operands"
    "(a? : Int, b? : Int)"
    optionalIntegerSlots
  assertAstOutput
    "parenthesized optional identifier target preserves precedence"
    "12, 23 ~> (a? : Int, b? : Int)"
    (integerPair ~> optionalIntegerSlots)
  assertAstOutput
    "unparenthesized optional identifier target preserves precedence"
    "12, 23 ~> a? : Int, b? : Int"
    (integerPair ~> optionalIntegerSlots)
  assertAstOutput
    "named source member precedes an optional identifier target"
    "12, b := 23 ~> a? : Int, b? : Int"
    ( MapConcatenation
        (natural 12)
        (AST.assignment "b" (natural 23) (natural 23))
        ~> optionalIntegerSlots
    )
  assertAstOutput
    "optional identifier range subfederation check"
    "(2, b := 5) of (a? : Int, b? : from 3 to 8)"
    (AST.subfederation
      (MapConcatenation
        (natural 2)
        (AST.assignment "b" (natural 5) (natural 5)))
      (MapConcatenation
        (AST.eitherType
          (AST.identifierType "a" AST.integerType)
          AST.integerType)
        (AST.eitherType
          (AST.identifierType "b" (AST.withinTo 3 8))
          (AST.withinTo 3 8))))
  let optionalAssigned identifierString value =
        AST.eitherType
          (AST.assignment
            identifierString AST.integerType (natural value))
          AST.integerType
      optionalIdentifier identifierString =
        AST.eitherType
          (AST.identifierType identifierString AST.integerType)
          AST.integerType
  assertAstOutput
    "parenthesized reverse specification stays in its concatenation slot"
    "a? : Int := 12, (b? : Int) <~ (b? : Int := 23)"
    (MapConcatenation
      (optionalAssigned "a" 12)
      (optionalAssigned "b" 23 ~> optionalIdentifier "b"))
  assertAstOutput
    "optional assignment sequence equals its canonical concatenation"
    ( "(a? : Int := 12; b? : Int := 23) = "
        <> "(a? : Int := 12, b? : Int := 23)"
    )
    (AST.equal
      (optionalAssigned "a" 12 <:> optionalAssigned "b" 23)
      (MapConcatenation
        (optionalAssigned "a" 12)
        (optionalAssigned "b" 23)))
  assertAstOutput
    "ternary conditional"
    "if true then 1 else -2"
    (AST.conditional
      (AST.boolean True)
      (natural 1)
      (AST.minus (natural 2)))
  assertAstOutput
    "binary conditional defaults to unit"
    "if false then 1"
    (AST.conditionalWithoutElse (AST.boolean False) (natural 1))
  assertAstOutput
    "conditional combines optionals, equality, logic, and identifiers"
    ( "if (Nat? = (Nat | Nothing := ())) and not false "
        <> "then (a? : Nat := 5) else (Nothing := ())"
    )
    (AST.conditional
      (AST.and
        (AST.equal
          (AST.optional AST.naturalType)
          (AST.eitherType
            AST.naturalType
            (AST.assignment "Nothing" AST.emptyMap AST.emptyMap)))
        (AST.not (AST.boolean False)))
      (AST.eitherType
        (AST.assignment "a" AST.naturalType (natural 5))
        AST.naturalType)
      (AST.assignment "Nothing" AST.emptyMap AST.emptyMap))
  assertAstOutput
    "EllipsisNatural specification into NaturalType"
    "2 ~> Nat"
    (natural 2 ~> AST.naturalType)
  assertRejected
    "shared bounded range suffix is not an expression"
    "2 to 5"
  assertRejected
    "shared upwards range suffix is not an expression"
    "2 upwards"
  assertAstOutput
    "specification binds after access and concatenation"
    "1, 2 @ range 0 upwards ~> range 0 to 10"
    (((natural 1 <.> natural 2) <@> AST.fromUpwards 0) ~> AST.fromTo 0 10)
  assertAstOutput
    "access after a specification projects its fibers"
    "(2; 3) ~> (Nat; Nat) @ 0"
    ( ((natural 2 <:> natural 3)
        ~> (AST.naturalType <:> AST.naturalType))
        <@> natural 0
    )
  assertAstOutput
    "specification chains associate through the intermediate federation"
    "2..3 ~> range 2 to 5 ~> range 2 to 8"
    ((natural 2 <..> natural 3) ~> AST.fromTo 2 5 ~> AST.fromTo 2 8)
  assertAstOutput
    "reverse specification reverses its operands"
    "range 2 to 5 <~ 2..3"
    ((natural 2 <..> natural 3) ~> AST.fromTo 2 5)
  assertAstOutput
    "reverse specification accepts parenthesized composite operands"
    "($a; Nat) <~ ($a; 50)"
    ( (AST.asciiString "a" <:> natural 50)
        ~> (AST.asciiString "a" <:> AST.naturalType)
    )
  assertAstOutput
    "reverse specification accepts concatenated composite operands"
    "$a, range 1 to 10 <~ $a, 3, 4, 5"
    ( (AST.asciiString "a" <.> natural 3 <.> natural 4 <.> natural 5)
        ~> (AST.asciiString "a" <.> AST.fromTo 1 10)
    )
  assertAstOutput
    "reverse specification chains associate right"
    "range 2 to 8 <~ range 2 to 5 <~ 2..3"
    ((natural 2 <..> natural 3) ~> AST.fromTo 2 5 ~> AST.fromTo 2 8)
  assertAstOutput
    "reverse specification binds after access and concatenation"
    "range 0 to 10 <~ 1, 2 @ range 0 upwards"
    (((natural 1 <.> natural 2) <@> AST.fromUpwards 0) ~> AST.fromTo 0 10)
  assertAstOutput
    "a postfix range can precede reverse specification"
    "2.. <~ range 2 to 5"
    (AST.fromTo 2 5 ~> (natural 2 ..+))
  assertAstOutput
    "simple identifier type"
    "x : Nat"
    (AST.identifierType "x" AST.naturalType)
  assertAstOutput
    "unit identifier equals its identifier string"
    "$Value = (Value : ())"
    (AST.equal
      (AST.asciiString "Value")
      (AST.identifierType "Value" AST.emptyMap))
  assertAstOutput
    "full identifier assignment"
    "x : Nat := 5"
    (AST.assignment "x" AST.naturalType (natural 5))
  assertAstOutput
    "assignment specified into its identifier target"
    "(a : Nat := 5) ~> (a : Nat)"
    ( AST.assignment "a" AST.naturalType (natural 5)
        ~> AST.identifierType "a" AST.naturalType
    )
  assertAstOutput
    "reverse specification between different identifier strings"
    "(a : Nat) <~ (b := 10)"
    ( AST.assignment "b" (natural 10) (natural 10)
        ~> AST.identifierType "a" AST.naturalType
    )
  assertAstOutput
    "reverse assignment chain widens nested annotations"
    ( "(d : from 0 to 100) <~ "
        <> "(d : from 20 to 40 := 28) <~ "
        <> "(d : from 25 to 35 := 28) <~ (d := 28)"
    )
    ( AST.assignment "d" (natural 28) (natural 28)
        ~> AST.assignment "d" (AST.withinTo 25 35) (natural 28)
        ~> AST.assignment "d" (AST.withinTo 20 40) (natural 28)
        ~> AST.identifierType "d" (AST.withinTo 0 100)
    )
  assertAstOutput
    "reverse assignment chain accepts unparenthesized multiline operands"
    ( "d : range 10 to 100 <~\n"
        <> "    d : range 12 to 85 := 23..66 <~\n"
        <> "    d := 23..66"
    )
    ( AST.assignment
        "d"
        (natural 23 <..> natural 66)
        (natural 23 <..> natural 66)
        ~> AST.assignment
          "d"
          (AST.fromTo 12 85)
          (natural 23 <..> natural 66)
        ~> AST.identifierType "d" (AST.fromTo 10 100)
    )
  assertAstOutput
    "reverse assignment chain retains an incompatible intermediate annotation"
    ( "(x : from 1 to 10) <~ "
        <> "(x : from 5 to 20) <~ (x := 8)"
    )
    ( AST.assignment "x" (natural 8) (natural 8)
        ~> AST.identifierType "x" (AST.withinTo 5 20)
        ~> AST.identifierType "x" (AST.withinTo 1 10)
    )
  assertAstOutput
    "binary identifier assignment"
    "x := 5"
    (AST.assignment "x" (natural 5) (natural 5))
  assertAstOutput
    "redundant assignment type canonicalizes to binary syntax"
    "x : 5 := 5"
    (AST.assignment "x" (natural 5) (natural 5))
  assertAstOutput
    "access binds inside the assignment value"
    "x : Nat := (1; 2) @ 0"
    ( AST.assignment
        "x"
        AST.naturalType
        ((natural 1 <:> natural 2) <@> natural 0)
    )
  assertAstOutput
    "accessing an identifier operation requires grouping"
    "(x : Nat) @ 0"
    (AST.identifierType "x" AST.naturalType <@> natural 0)
  assertAstOutput
    "bracket access uses the identifier map view"
    "(x : Nat)[0]"
    (AST.identifierType "x" AST.naturalType <@> natural 0)
  assertAstOutput
    "bracket access uses the assignment specification view"
    "(x : Nat := 5)[1]"
    (AST.assignment "x" AST.naturalType (natural 5) <@> natural 1)
  assertAstOutput
    "unparenthesized access belongs to the identifier type operand"
    "x : Nat @ 0"
    (AST.identifierType "x" (AST.naturalType <@> natural 0))
  assertAstOutput
    "identifier arithmetic operands compose without grouping"
    "x : 5 + y : 10 = 15"
    (AST.equal
      ((AST.+)
        (AST.identifierType "x" (natural 5))
        (AST.identifierType "y" (natural 10)))
      (natural 15))
  assertAstOutput
    "transfinite identifier arithmetic preserves precedence"
    "x : ...^2 + y : 1 = ...^2 + 1"
    (AST.equal
      ((AST.+)
        (AST.identifierType "x" ((AST.^) (...) (natural 2)))
        (AST.identifierType "y" (natural 1)))
      ((AST.+) ((AST.^) (...) (natural 2)) (natural 1)))
  assertAstOutput
    "identifier strings share canonical continuation characters"
    "A_0'z : Nat"
    (AST.identifierType "A_0'z" AST.naturalType)
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
  assertRejected
    "compact strings cannot be entirely numeric"
    "$12"
  assertAstOutput
    "compact strings consume a digit-leading alphanumeric token whole"
    "$345abc"
    (AsciiStringLiteral "345abc")
  assertAstOutput
    "IdentifierString accepts all canonical continuation characters"
    "$A_0'z"
    (AST.asciiString "A_0'z")
  assertAstOutput
    "compact strings allow a leading underscore"
    "$_abc"
    (AST.asciiString "_abc")
  assertAstOutput
    "compact strings allow a single separating underscore"
    "$abc_def"
    (AST.asciiString "abc_def")
  assertRejected
    "compact strings reject consecutive underscores"
    "$abc__def"
  assertRejected
    "compact strings reject a trailing underscore"
    "$abc_"
  assertRejected
    "compact strings reject doubled leading underscores"
    "$__abc"
  assertRejected
    "a lone compact underscore is trailing and rejected"
    "$_"
  assertAstOutput
    "strings outside compact underscore syntax remain quoted"
    "\"abc_\""
    (AST.asciiString "abc_")
  assertAstOutput
    "StandardString canonicalizes to IdentifierString when possible"
    "\"text\""
    (AST.asciiString "text")
  assertAstOutput
    "StandardString supports the empty string"
    "\"\""
    (AST.asciiString "")
  assertAstOutput
    "StandardString escapes quote and backslash"
    "\"say \\\"hi\\\" and \\\\ path\""
    (AST.asciiString "say \"hi\" and \\ path")
  assertAstOutput
    "StandardString decodes and canonicalizes escaped newlines"
    "\"first\\nsecond\""
    (AST.asciiString "first\nsecond")
  assertAstOutput
    "StandardString accepts and canonicalizes hexadecimal byte escapes"
    "\"\\0\\8\\08\\09\\1f\\7F\\ff\""
    (AST.asciiString ['\0', '\8', '\8', '\9', '\31', '\127', '\255'])
  assertParsed
    "StandardString hexadecimal escapes select ASCII-map characters"
    "\"\\0\\8\\08\\09\\1f\\7F\\ff\""
    (AsciiStringLiteral ['\0', '\8', '\8', '\9', '\31', '\127', '\255'])
  assertAstOutput
    "StandardString canonicalizes a hexadecimal newline to its named escape"
    "\"\\0A\""
    (AST.asciiString "\n")
  assertAstOutput
    "StandardString leaves nonsyntactic keyboard-visible characters literal"
    "\" !\\%&'()*+,-./:;<=>?@^_`{|}~\""
    (AST.asciiString " !%&'()*+,-./:;<=>?@^_`{|}~")
  assertAstOutput
    "StandardString line comments retain their terminating newline"
    "\"Comment test#this is a comment!\n\""
    (AST.asciiString "Comment test\n")
  assertParsed
    "StandardString comments may terminate at the closing quote"
    "\"Hello#, world!\""
    (AsciiStringLiteral "Hello")
  assertAstOutput
    "StandardString comments ending at a quote retain canonical rendering"
    "\"Hello#, world!\""
    (AST.asciiString "Hello")
  assertAstOutput
    "StandardString escapes a literal hash"
    "\"literal \\# character\""
    (AST.asciiString "literal # character")
  assertAstOutput
    "StandardString leaves a literal dollar sign unescaped"
    "\"literal $ character\""
    (AST.asciiString "literal $ character")
  assertAstOutput
    "StandardString escapes a literal percent sign"
    "\"literal \\% character\""
    (AST.asciiString "literal % character")
  assertAstOutput
    "string template interpolates a compound expression"
    "\"example%(2 + 2)\""
    (StringTemplate
      [ StringTemplateLiteral "example"
      , StringTemplateInterpolation
          (Addition (natural 2) (natural 2))
      ])
  assertParsed
    "simple numeric interpolation has string-template syntax"
    "\"%4\""
    (StringTemplate [StringTemplateInterpolation (natural 4)])
  assertParsed
    "reserved atomic symbols may be simple interpolations"
    "\"%String\""
    (StringTemplate [StringTemplateInterpolation StringType])
  assertParsed
    "Iden is available to string templates"
    "\"%Iden\""
    (StringTemplate [StringTemplateInterpolation IdentifierValueType])
  assertAstOutput
    "digit-leading compact strings retain an apostrophe before an operator"
    "$12' of \"%(Nat)'\""
    (AST.subfederation
      (AsciiStringLiteral "12'")
      (StringTemplate
        [ StringTemplateInterpolation NaturalType
        , StringTemplateLiteral "'"
        ]))
  assertParsed
    "weak interpolation has explicit compact syntax"
    "\"%!String\""
    (StringTemplate [StringTemplateWeakInterpolation StringType])
  assertParsed
    "weak interpolation supports compound expressions"
    "\"%!(Nat | Nat)\""
    (StringTemplate
      [StringTemplateWeakInterpolation
        (EitherType NaturalType NaturalType)])
  assertParsed
    "postfix optional composes with a simple interpolation"
    "\"%Int?\""
    (StringTemplate
      [StringTemplateInterpolation (OptionalType IntegerType)])
  assertParsed
    "an escaped question mark remains text after a simple interpolation"
    "\"%Int\\?\""
    (StringTemplate
      [ StringTemplateInterpolation IntegerType
      , StringTemplateLiteral "?"
      ])
  assertParsed
    "an escaped question mark is accepted as ordinary string text"
    "\"\\?\""
    (AsciiStringLiteral "?")
  assertRejected
    "unreserved alphabetic names are not simple interpolations"
    "\"%abc\""
  assertParsed
    "a compact string can itself be interpolated"
    "\"%$abc\""
    (StringTemplate
      [StringTemplateInterpolation (AsciiStringLiteral "abc")])
  assertParsed
    "signed interpolation requires the compound form"
    "\"%(-10)\""
    (StringTemplate
      [StringTemplateInterpolation (Minus (natural 10))])
  assertRejected
    "signed interpolation rejects the simple form"
    "\"%-10\""
  assertParsed
    "a nested quoted string is one simple interpolation"
    "\"hello, %\"world\"!\""
    (StringTemplate
      [ StringTemplateLiteral "hello, "
      , StringTemplateInterpolation (AsciiStringLiteral "world")
      , StringTemplateLiteral "!"
      ])
  assertParsed
    "operators outside parentheses remain template text"
    "\"%2 + 2\""
    (StringTemplate
      [ StringTemplateInterpolation (natural 2)
      , StringTemplateLiteral " + 2"
      ])
  assertParsed
    "interpolation comments terminate at the closing parenthesis"
    "\"a%(2 # ignored)b\""
    (StringTemplate
      [ StringTemplateLiteral "a"
      , StringTemplateInterpolation (natural 2)
      , StringTemplateLiteral "b"
      ])
  assertParsed
    "interpolation comments terminate at newline without emitting it"
    "\"a%(2 # ignored\n)b\""
    (StringTemplate
      [ StringTemplateLiteral "a"
      , StringTemplateInterpolation (natural 2)
      , StringTemplateLiteral "b"
      ])
  assertParsed
    "template comments ignore interpolation and retain their newline"
    "\"a# ignored %4\nb\""
    (AsciiStringLiteral "a\nb")
  assertParsed
    "escaped hashes and percents remain literal template text"
    "\"\\#\\%%4\""
    (StringTemplate
      [ StringTemplateLiteral "#%"
      , StringTemplateInterpolation (natural 4)
      ])
  assertAstOutput
    "parentheses inside nested strings do not close interpolation"
    "\"x%(\"a)b\")y\""
    (StringTemplate
      [ StringTemplateLiteral "x"
      , StringTemplateInterpolation (AsciiStringLiteral "a)b")
      , StringTemplateLiteral "y"
      ])
  assertAstOutput
    "nested grouping composes inside interpolation"
    "\"x%((2 + 3) * 4)y\""
    (StringTemplate
      [ StringTemplateLiteral "x"
      , StringTemplateInterpolation
          (Multiplication
            (Addition (natural 2) (natural 3))
            (natural 4))
      , StringTemplateLiteral "y"
      ])
  assertRejected "an empty interpolation is rejected" "\"%()\""
  assertRejected
    "an unterminated interpolation is rejected"
    "\"%(2 + 2\""
  assertRejected
    "an unescaped percent without an interpolation is rejected"
    "\"literal % character\""
  assertAstOutput
    "string literals are members of String"
    "\"my_string\" of String = true"
    (AST.equal
      (AST.subfederation (AST.asciiString "my_string") AST.stringType)
      (AST.boolean True))
  assertAllHexadecimalAsciiEscapes
  assertAstOutput
    "StandardString preserves multiline leading and trailing characters"
    "(\"  first\nsecond  \")"
    (AST.asciiString "  first\nsecond  ")
  assertParsed
    "StandardString treats syntax and comments as literal contents"
    "(\"\\#;(value)\n$still_text\")"
    (AsciiStringLiteral "#;(value)\n$still_text")
  assertAstOutput
    "strings use the ordinary concatenation operator"
    "$ab, $cd"
    (AST.asciiString "ab" <.> AST.asciiString "cd")
  assertAstOutput
    "strings use the ordinary access operator"
    "$abcd @ 1..3"
    (AST.asciiString "abcd" <@> (natural 1 <..> natural 3))
  assertAstOutput
    "bounded super-ellipsis range"
    "(2..10)"
    (natural 2 <..> natural 10)
  assertAstOutput
    "open super-ellipsis ranges"
    "(2..; 10..-)"
    ((natural 2 ..+) <:> (natural 10 ..-))
  assertAstOutput
    "a prefix range starts at zero"
    "(..10)"
    (natural 0 <..> natural 10)
  assertAstOutput
    "inclusive natural range"
    "range 2 to 5"
    (AST.fromTo 2 5)
  assertAstOutput
    "open inclusive natural range"
    "range 2 upwards"
    (AST.fromUpwards 2)
  assertAstOutput
    "natural range access"
    "1, 2, 3 @ range 1 upwards"
    ((natural 1 <.> natural 2 <.> natural 3) <@> AST.fromUpwards 1)
  assertAstOutput
    "bracket access binds before arithmetic"
    "$a + $b[$c]"
    (AST.asciiString "a" AST.+ (AST.asciiString "b" <@> AST.asciiString "c"))
  assertAstOutput
    "grouping moves bracket access outside arithmetic"
    "($a + $b)[$c]"
    ((AST.asciiString "a" AST.+ AST.asciiString "b") <@> AST.asciiString "c")
  assertAstOutput
    "bracket access chains associate left"
    "$a[$b][$c]"
    ((AST.asciiString "a" <@> AST.asciiString "b") <@> AST.asciiString "c")
  assertAstOutput
    "ordinary access sees a tightly bound insertion"
    "$a @ $b[$c]"
    (AST.asciiString "a" <@> (AST.asciiString "b" <@> AST.asciiString "c"))
  assertAstOutput
    "bracket insertion accepts ordinary access"
    "$a[$b @ $c]"
    (AST.asciiString "a" <@> (AST.asciiString "b" <@> AST.asciiString "c"))
  assertAstOutput
    "bracket insertion accepts a postfix range"
    "$a[1..]"
    (AST.asciiString "a" <@> (natural 1 ..+))
  assertAstOutput
    "bracket insertion accepts an explicitly constructed map"
    "$a[(1; 2)]"
    (AST.asciiString "a" <@> (natural 1 <:> natural 2))
  assertAstOutput
    "bracket access accepts an explicitly constructed map on the left"
    "(2; 3)[0]"
    ((natural 2 <:> natural 3) <@> natural 0)
  assertAstOutput
    "grouping permits bracket access on a whole specification"
    "((2; 3) ~> (Nat; Nat))[0]"
    ( ((natural 2 <:> natural 3)
        ~> (AST.naturalType <:> AST.naturalType))
        <@> natural 0
    )
  assertAstOutput
    "natural range keywords continue across lines"
    "range\n2\nto\n5"
    (AST.fromTo 2 5)
  assertAstOutput
    "a prefix range greedily continues across a newline"
    "(..\n10)"
    (natural 0 <..> natural 10)
  assertAstOutput
    "a postfix range can end before a closing delimiter"
    "(2..\n)"
    (natural 2 ..+)
  assertAstOutput
    "a postfix range ends before lower-precedence access"
    "(...) .. @ 5"
    (((...) ..+) <@> natural 5)
  assertAstOutput
    "a postfix range ends before lower-precedence concatenation"
    "2.., 5"
    ((natural 2 ..+) <.> natural 5)
  assertAstOutput
    "Haskell arithmetic precedence"
    "(1 + 2 * 3 ^ 4)"
    (natural 1 AST.+ natural 2 AST.* natural 3 AST.^ natural 4)
  assertAstOutput
    "parentheses override arithmetic precedence"
    "((1 + 2) * 3)"
    ((natural 1 AST.+ natural 2) AST.* natural 3)
  assertAstOutput
    "right-nested addition keeps necessary parentheses"
    "(1 + (2 + 3))"
    (natural 1 AST.+ (natural 2 AST.+ natural 3))
  assertAstOutput
    "redundant parentheses are omitted"
    "(((1 + (2 * (3 ^ 4)))))"
    (natural 1 AST.+ natural 2 AST.* natural 3 AST.^ natural 4)
  assertAstOutput
    "range endpoints accept arithmetic expressions"
    "(1 + 2..3 * 4)"
    ((natural 1 AST.+ natural 2) <..> (natural 3 AST.* natural 4))
  assertAstOutput
    "range concatenation"
    "(1..3, 5..7)"
    ((natural 1 <..> natural 3) <.> (natural 5 <..> natural 7))
  assertParsed
    "a trailing comma concatenates an empty map"
    "(1,)"
    ((<.>)
      (natural 1)
      (AtlasMap []))
  assertAstOutput
    "a trailing comma retains its semantic value"
    "(1,)"
    (natural 1 <.> AST.emptyMap)
  assertAstOutput
    "a trailing comma works at the inferred map boundary"
    "1,"
    (natural 1 <.> AST.emptyMap)
  assertAstOutput
    "a trailing comma can precede a newline and closing delimiter"
    "(1, # no right operand\n)"
    (natural 1 <.> AST.emptyMap)
  assertAstOutput
    "a comma followed by an expression across a newline stays infix"
    "(1,\n2)"
    (natural 1 <.> natural 2)
  assertParsed
    "a trailing comma is removed from an existing concatenation"
    "(1, 2,)"
    ((<.>)
      (natural 1)
      (natural 2))
  assertAstOutput
    "an existing concatenation does not gain an empty map"
    "(1, 2,)"
    (natural 1 <.> natural 2)
  assertAstOutput
    "a trailing comma can precede a map separator"
    "(1,; 2)"
    ((natural 1 <.> AST.emptyMap) <:> natural 2)
  assertAstOutput
    "access consumes a concatenated range insertion"
    "(... @ 1..3, 5..7)"
    ((...) <@> ((natural 1 <..> natural 3) <.> (natural 5 <..> natural 7)))
  assertAstOutput
    "parentheses can concatenate an access result"
    "((... @ 1), 2)"
    (((...) <@> natural 1) <.> natural 2)
  assertAstOutput
    "map expressions are concatenation operands"
    "((1; 2), (3; 4))"
    ((natural 1 <:> natural 2) <.> (natural 3 <:> natural 4))
  assertAstOutput
    "unary grouping does not manufacture map expansion"
    "((1 + 2); (3 * 4))"
    ((natural 1 AST.+ natural 2) <:> (natural 3 AST.* natural 4))
  assertAstOutput
    "outer map parentheses are inferred"
    "2 + 3"
    (natural 2 AST.+ natural 3)
  assertAstOutput
    "completed lines become map elements"
    "2\n3"
    (natural 2 <:> natural 3)
  assertAstOutput
    "a newline after an operator continues the expression"
    "2 +\n3\n4"
    ((natural 2 AST.+ natural 3) <:> natural 4)
  assertAstOutput
    "comments do not hide a required continuation"
    "2 + # continue addition\n3\n# blank comment line\n4"
    ((natural 2 AST.+ natural 3) <:> natural 4)
  assertAstOutput
    "blank lines do not create empty map elements"
    "\n# heading\n2\n\n# between values\n3\n"
    (natural 2 <:> natural 3)
  assertAstOutput
    "a semicolon separates a postfix range from the next map line"
    "2..;\n3..-"
    ((natural 2 ..+) <:> (natural 3 ..-))
  assertAstOutput
    "ellipsis is complete despite ending in dots"
    "...\n2"
    ((...) <:> natural 2)
  assertAstOutput
    "bounded range and concatenation operators continue across lines"
    "2..\n4,\n5.."
    ((natural 2 <..> natural 4) <.> (natural 5 ..+))
  assertAstOutput
    "an ambiguous postfix range greedily consumes a following operand"
    "(2..\n4)"
    (natural 2 <..> natural 4)
  assertAstOutput
    "exponentiation continues and remains right associative"
    "2 ^\n3 ^\n4"
    (natural 2 AST.^ natural 3 AST.^ natural 4)
  assertAstOutput
    "newlines separate expressions in an explicit map"
    "(2\n3)"
    (natural 2 <:> natural 3)
  assertAstOutput
    "newline inference applies independently to nested maps"
    "((1\n2)\n(3\n4))"
    ((natural 1 <:> natural 2) <+> (natural 3 <:> natural 4))
  assertAstOutput
    "separately parenthesized expressions form an implicit outer map"
    "(1)\n2"
    (natural 1 <:> natural 2)
  assertAstOutput
    "parentheses inside comments do not affect outer-map inference"
    "(1)\n2 # ) is only a comment"
    (natural 1 <:> natural 2)
  assertAstOutput
    "operator continuation also applies in explicit maps"
    "(2 +\n3\n4)"
    ((natural 2 AST.+ natural 3) <:> natural 4)
  assertAstOutput
    "newlines inside unfinished expressions are ignored"
    "(2 + \n 3)"
    (natural 2 AST.+ natural 3)
  assertAstOutput
    "multiline parenthesized expressions remain one expression"
    "(2 +\n3)\n4"
    ((natural 2 AST.+ natural 3) <:> natural 4)
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
    (natural 10)
  assertAstOutput
    "one trailing semicolon is ignored"
    "(1; 2; # trailing separator\n)"
    (natural 1 <:> natural 2)
  assertRejected "multiple trailing semicolons are rejected" "(1; 2;;)"
  assertRejected "IdentifierString rejects a missing body" "$"
  assertRejected "IdentifierString rejects a leading apostrophe" "$'bad"
  assertRejected "IdentifierString rejects noncanonical continuation" "$bad-name"
  assertRejected "StandardString rejects unsupported escapes" "\"bad\\t\""
  assertRejected "StandardString rejects an unescaped percent sign" "\"bad%value\""
  assertRejected "StandardString rejects the obsolete dollar escape" "\"bad\\$value\""
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
    "range (1 + 2) to 5"
  assertRejected
    "natural range targets must be literal EllipsisNaturals"
    "range 1 to (2 + 3)"
  assertRejected "natural range keywords require separators" "range1to2"
  assertAstOutput
    "parentheses permit an explicitly nested range"
    "((1..2)..)"
    ((natural 1 <..> natural 2) ..+)
  assertParsed
    "a parenthesized Ellipsis can be a postfix range argument"
    "((...)..)"
    ((..+) (...))
  assertAstOutput
    "a parenthesized Ellipsis can be a prefix range argument"
    "(..(...))"
    (natural 0 <..> (...))
  assertAstOutput
    "a parenthesized Ellipsis can be a bounded range argument"
    "((...)..2; 1..(...))"
    (((...) <..> natural 2) <:> (natural 1 <..> (...)))
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
    (natural 1 <:> natural 2)

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
    , pure NothingLiteral
    , AsciiStringLiteral
        <$> Gen.list (Range.linear 0 24) (Gen.enum '\0' '\255')
    , pure NaturalType
    , pure StringType
    , pure IdentifierValueType
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
    , Gen.subterm2 genExpression genExpression Subfederation
    , Gen.subterm2 genExpression genExpression Equality
    , Gen.subterm genExpression Extract
    , Gen.subterm2 genExpression genExpression Eval
    , Gen.subterm2 genExpression genExpression MapConcatenation
    , Gen.subterm2 genExpression genExpression MapAccess
    , Gen.subterm2 genExpression genExpression MapSpecification
    , IdentifierOperation
        <$> genIdentifierString
        <*> genExpression
        <*> Gen.maybe genExpression
    ]

genIdentifierString :: H.Gen IdentifierString
genIdentifierString = do
  first <- Gen.element (['_'] <> ['a' .. 'z'] <> ['A' .. 'Z'])
  rest <-
    Gen.list
      (Range.linear 0 12)
      (Gen.element
        (['_', '\'']
          <> ['a' .. 'z']
          <> ['A' .. 'Z']
          <> ['0' .. '9']))
  pure (IdentifierString (first : rest))

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
  assert "template rendering escapes a literal optional suffix"
    ( renderExpression
        (StringTemplate
          [ StringTemplateInterpolation IntegerType
          , StringTemplateLiteral "?"
          ])
        == "\"%Int\\?\""
    )
  assert "weak template interpolation retains its marker"
    ( renderExpression
        (StringTemplate [StringTemplateWeakInterpolation StringType])
        == "\"%!String\""
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
        (((natural 2 <..> natural 5) ~> AST.fromUpwards 0))
        == "(~> (<..> 2 5) (range 0 upwards))"
    )
  assert "the extract operator retains its percent AST symbol"
    (renderExpression (Extract StringType) == "(% String)")
  assert "valued natural range constructors retain their distinct prefix"
    ( renderExpression (AST.withinTo 2 5) == "(from 2 to 5)"
      && renderExpression (AST.withinUpwards 2)
        == "(from 2 upwards)"
      && renderExpression AST.naturalType == "Nat"
    )

assertAstOutput :: String -> String -> Expression -> IO ()
assertAstOutput label source expected =
  case parseDatra source of
    Left message -> fail (label <> ": unexpected parse failure: " <> message)
    Right actual
      | canonicalAst actual == canonicalAst expected ->
          assertAstRoundTrip label (renderExpression actual)
      | otherwise ->
          fail
            ( label
                <> ": expected "
                <> show (canonicalAst expected)
                <> ", got "
                <> show (canonicalAst actual)
            )
  where
    canonicalAst = toOperatorExpression . normalizeExpression

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
