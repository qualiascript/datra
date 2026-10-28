module Datra.Interpreter.OverloadTests
  ( overloadTests
  ) where

import Datra.TestSupport
import DatraTypes
  ( FunctionFailure (NoApplicableFunctionAlternative)
  , InterpretingError (..)
  , OverloadFailure (..)
  )
import Test.Tasty (TestTree, testGroup)

overloadTests :: TestTree
overloadTests =
  testGroup "overloading"
    [ overloadOperatorTests
    , defaultedFunctionTests
    , functionBodySpellingTests
    ]

overloadOperatorTests :: TestTree
overloadOperatorTests =
  testGroup "overload operators"
    [ programCase "left overload replaces a default"
        "yield {a? : Nat := 3} << 5"
        "a? : Nat := 5"
    , programCase "right overload reverses the operands"
        "yield 5 >> {a? : Nat := 3}"
        "a? : Nat := 5"
    , programCase "named partial overload preserves other defaults"
        "yield {a? : Nat := 3; b? : Nat := 4} << (b : 8)"
        "{a? : Nat := 3; b? : Nat := 8}"
    , programCase "concatenated argument and empty maps"
        "yield ({a? : Nat := 3}, (), {b? : Nat := 4}) << (b : 8)"
        "a? : Nat := 3, b? : Nat := 8"
    , programCase "empty overload preserves defaults"
        "yield {a? : Nat := 3; b? : Nat := 4} << ()"
        "{a? : Nat := 3; b? : Nat := 4}"
    , programCase "total annotation supplies its only value"
        "yield ({a? : 5} << ()) = {a? : 5}"
        "true"
    , programCase "overload result supports subfederation"
        "yield ({a? : Nat := 3} << 5) of (a? : Nat)"
        "true"
    , programCase "overload result supports specification"
        "yield ({a? : Nat := 3} << 5) ~> (a? : Int)"
        "a? : Int := 5"
    , programFailureCase "overload rejects an incompatible value"
        "yield {a? : Nat := 3} << true"
        (SourceEvaluationFailure
          (OverloadError OverloadNoMatch))
    , programCase "written order resolves a partial unnamed overload"
        "yield {a? : Nat := 3; b? : Nat := 4} << 5"
        "{a? : Nat := 5; b? : Nat := 4}"
    , programCase "overload does not skip a compatible defaulted slot"
        "yield {x? : Nat := 2; Nat} << 4"
        "{x? : Nat := 4; Nat}"
    , programCase "skip advances one positional overload slot"
        "yield {x? : Nat; y? : Nat} << (*; 3)"
        "{x? : Nat; y? : Nat := 3}"
    , programCase "skip composes through argumentative-map overload input"
        "yield {x? : Nat; y? : Nat} << {*; 3}"
        "{x? : Nat; y? : Nat := 3}"
    , programFailureCase "transfinite ordinal is not a skip"
        "yield {x? : Nat; y? : Nat} << (...; 3)"
        (SourceEvaluationFailure
          (OverloadError OverloadNoMatch))
    , programCase "safe overload fills a later compatible slot"
        "yield {x? : Nat := 2; Str} <<< \"a\""
        "{x? : Nat := 2; $a}"
    , programCase "reverse safe overload reverses the operands"
        "yield \"a\" >>> {x? : Nat := 2; Str}"
        "{x? : Nat := 2; $a}"
    , programCase "safe overload accepts the existing default"
        "yield {x? : Nat := 2} <<< 2"
        "x? : Nat := 2"
    , programFailureCase "safe overload rejects a changed default"
        "yield {x? : Nat := 2; Nat} <<< 4"
        (SourceEvaluationFailure
          (OverloadError OverloadChangedDefault))
    , programCase "safe overload result supports subfederation"
        "yield ({x? : Nat := 2; Str} <<< \"a\") of {x? : Nat; Str}"
        "true"
    , programCase "safe overload result supports specification"
        "yield ({x? : Nat := 2} <<< 2) ~> (x? : Int)"
        "x? : Int := 2"
    , programCase "safe overload can leave a default skipped"
        "yield {x? : Nat := 2; y? : Nat} <<< (*; 3)"
        "{x? : Nat := 2; y? : Nat := 3}"
    , programCase "skip specifications match only skip positions"
        (unlines
          [ "yield ("
          , "  ((*; 3) of (*; Nat));"
          , "  ({*; 3} of {*; Nat});"
          , "  (((*; 3) ~> (*; Nat)) of (*; Nat));"
          , "  (({*; 3} ~> {*; Nat}) of {*; Nat});"
          , "  not ((...; 3) of (*; Nat));"
          , "  not ((*; 3) of (...; Nat)))"
          ])
        "(true; true; true; true; true; true)"
    , programCase "skip coerces to one in numerical operators"
        (unlines
          [ "yield ("
          , "  (*) + 2 = 3;"
          , "  4 - * = 3;"
          , "  (*) * 7 = 7;"
          , "  7 * (*) = 7;"
          , "  (*) * (*) = 1;"
          , "  2 ^ * = 2;"
          , "  -* = -1;"
          , "  +* = 1)"
          ])
        "(true; true; true; true; true; true; true; true)"
    ]

defaultedFunctionTests :: TestTree
defaultedFunctionTests =
  testGroup "defaulted function arguments"
    [ programCase "unparenthesized my_pow can check a skipped default"
        (unlines
          [ "my_pow := {base? : Nat := 2; exponent? : Nat} -> Nat do yield base ^ exponent"
          , "yield my_pow (*; 3) = 8"
          ])
        "true"
    , programCase "positional-only my_pow skips its defaulted first argument"
        (unlines
          [ "my_pow := ({base? : Nat := 2; exponent? : Nat} -> Nat do yield base ^ exponent)"
          , "yield my_pow (*; 3)"
          ])
        "8"
    , programCase "positional-only my_pow accepts a skip in an argumentative map"
        (unlines
          [ "my_pow := ({base? : Nat := 2; exponent? : Nat} -> Nat do yield base ^ exponent)"
          , "yield my_pow {*; 3}"
          ])
        "8"
    , programCase "function call can skip a later default"
        (unlines
          [ "add := ({x? : Nat; y? : Nat := 4} -> Nat do yield x + y)"
          , "yield add (3; *)"
          ])
        "7"
    , programFailureCase "function call cannot skip a required argument"
        (unlines
          [ "sum := ({x : Nat; y? : Nat} -> Nat do yield x + y)"
          , "yield sum (*; 3)"
          ])
        (SourceEvaluationFailure
          (OverloadError OverloadSkippedRequiredSlot))
    , programCase "a grouped singleton skip preserves a positional default"
        (unlines
          [ "f := ({value? : Nat := 4} -> Nat do yield value)"
          , "yield f (*)"
          ])
        "4"
    , programFailureCase "function call does not treat an ordinal as skip"
        (unlines
          [ "my_pow := ({base? : Nat := 2; exponent? : Nat} -> Nat do yield base ^ exponent)"
          , "yield my_pow (...; 3)"
          ])
        (SourceEvaluationFailure
          (FunctionEvaluationFailed NoApplicableFunctionAlternative))
    , programCase "empty argument uses the default"
        (unlines
          [ "f := ({n? : Nat := 5} -> Nat do yield n + 1)"
          , "yield f ()"
          ])
        "6"
    , programCase "supplied argument overloads the default"
        (unlines
          [ "f := ({n? : Nat := 5} -> Nat do yield n + 1)"
          , "yield f 8"
          ])
        "9"
    , programCase "partial named call preserves another default"
        (unlines
          [ "f := ({a? : Nat := 3; b? : Nat := 4} -> Nat do yield a + b)"
          , "yield f (b : 8)"
          ])
        "11"
    , programCase "overload result can be passed directly"
        (unlines
          [ "f := ({n? : Nat := 5} -> Nat do yield n + 1)"
          , "arguments := ({n? : Nat := 5} << 8)"
          , "yield f arguments"
          ])
        "9"
    , programCase "total annotation needs no explicit default"
        (unlines
          [ "f := ({n? : 5} -> Nat do yield n + 1)"
          , "yield f ()"
          ])
        "6"
    , programCase "defaulted recursive function checks"
        (unlines
          [ "let factorial := ({n? : Int := 5} -> Int do"
          , "  yield if n = 0 then 1 else n * factorial (n - 1))"
          , "yield (factorial () = 120; factorial 6 = 720)"
          ])
        "(true; true)"
    ]

functionBodySpellingTests :: TestTree
functionBodySpellingTests =
  testGroup "function body spellings"
    [ programCase "yield without a block keyword"
        "f := ({n? : Nat} -> Nat do yield n + 1)\nyield f 4"
        "5"
    , programCase "do block is a function body"
        "f := ({n? : Nat} -> Nat do x := 1; yield n + x)\nyield f 4"
        "5"
    , programFailureCase "begin block is not a function body"
        "f := ({n? : Nat} -> Nat begin x := 1; yield n + x)\nyield f 4"
        (SourceEvaluationFailure (UnknownIdentifier "n"))
    , programCase "multiline do block"
        (unlines
          [ "f := ({n? : Nat} -> Nat do"
          , "  x := 1"
          , "  yield n + x)"
          , "yield f 4"
          ])
        "5"
    , programCase "function body can yield a Boolean check"
        "f := ({n? : Nat} -> Bool do yield n of Nat)\nyield f 4"
        "true"
    , programFailureCase "an unyielded begin operation has no effect"
        "yield begin\n  2 + 3\nyield nothing"
        (SourceEvaluationFailure OperationHasNoEffect)
    , programFailureCase "an unyielded function-body operation has no effect"
        (unlines
          [ "f := (Nat -> Nat do"
          , "  2 + 3"
          , "yield 0)"
          , "yield ()"
          ])
        (SourceEvaluationFailure OperationHasNoEffect)
    , programCase "an unused value declaration has an effect"
        (unlines
          [ "f := (Nat -> Nat do"
          , "  x := 2 + 3"
          , "yield 0)"
          , "yield ()"
          ])
        "()"
    , programCase "an unused let binding has an effect"
        (unlines
          [ "f := (Nat -> Nat do"
          , "  let x := 2 + 3"
          , "yield 0)"
          , "yield ()"
          ])
        "()"
    ]
