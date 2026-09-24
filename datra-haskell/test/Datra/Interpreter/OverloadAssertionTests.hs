module Datra.Interpreter.OverloadAssertionTests
  ( overloadAssertionTests
  ) where

import Datra.TestSupport
import DatraTypes (InterpretingError (..))
import Interpreting
  ( EvaluationMode (DevelopmentMode, ProductionMode) )
import Test.Tasty (TestTree, testGroup)

overloadAssertionTests :: TestTree
overloadAssertionTests =
  testGroup "overloading and assertions"
    [ overloadTests
    , defaultedFunctionTests
    , assertionTests
    , functionBodySpellingTests
    ]

overloadTests :: TestTree
overloadTests =
  testGroup "overload operators"
    [ programCase "left overload replaces a default"
        "yield {a? : Nat := 3} << 5"
        "a? : Nat := 5"
    , programCase "right overload reverses the operands"
        "yield 5 >> {a? : Nat := 3}"
        "a? : Nat := 5"
    , programCase "named partial overload preserves other defaults"
        "yield {a? : Nat := 3, b? : Nat := 4} << (b : 8)"
        "{a? : Nat := 3, b? : Nat := 8}"
    , programCase "concatenated argument and empty maps"
        "yield ({a? : Nat := 3}, (), {b? : Nat := 4}) << (b : 8)"
        "a? : Nat := 3, (), b? : Nat := 8"
    , programCase "empty overload preserves defaults"
        "yield {a? : Nat := 3, b? : Nat := 4} << ()"
        "{a? : Nat := 3, b? : Nat := 4}"
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
          (OverloadError
            "the right operand does not match the left operand without its defaults"))
    , programFailureCase "unnamed unordered overload is ambiguous"
        "yield {a? : Nat := 3, b? : Nat := 4} << 5"
        (SourceEvaluationFailure
          (OverloadError
            "ambiguous overload; supply identifiers to select the intended slots"))
    ]

defaultedFunctionTests :: TestTree
defaultedFunctionTests =
  testGroup "defaulted function arguments"
    [ programCase "empty argument uses the default"
        (unlines
          [ "f := ({n? : Nat := 5} -> Nat yield n + 1)"
          , "yield f ()"
          ])
        "6"
    , programCase "supplied argument overloads the default"
        (unlines
          [ "f := ({n? : Nat := 5} -> Nat yield n + 1)"
          , "yield f 8"
          ])
        "9"
    , programCase "partial named call preserves another default"
        (unlines
          [ "f := ({a? : Nat := 3, b? : Nat := 4} -> Nat yield a + b)"
          , "yield f (b : 8)"
          ])
        "11"
    , programCase "total annotation needs no explicit default"
        (unlines
          [ "f := ({n? : 5} -> Nat yield n + 1)"
          , "yield f ()"
          ])
        "6"
    , programCase "defaulted recursive function assertions"
        (unlines
          [ "let factorial := ({n? : Int := 5} -> Int do"
          , "  yield if n = 0 then 1 else n * factorial (n - 1))"
          , "assert factorial () = 120"
          , "assert factorial 6 = 720"
          ])
        "()"
    ]

assertionTests :: TestTree
assertionTests =
  testGroup "assert"
    [ programCase "true assertion and implicit unit yield"
        "assert 2 + 3 = 5"
        "()"
    , programFailureCase "false assertion fails in development"
        "assert false"
        (SourceEvaluationFailure AssertionFailed)
    , programCaseInMode ProductionMode
        "soft assertion is omitted in production"
        "assert false"
        "()"
    , programCaseInMode ProductionMode
        "omitted production assertion does not evaluate its condition"
        "assert missing"
        "()"
    , programFailureCaseInMode ProductionMode
        "hard assertion remains active in production"
        "assert hard false"
        (SourceEvaluationFailure AssertionFailed)
    , programCaseInMode DevelopmentMode
        "hard assertion succeeds in development"
        "assert hard 5 of Nat"
        "()"
    ]

functionBodySpellingTests :: TestTree
functionBodySpellingTests =
  testGroup "function body spellings"
    [ programCase "yield without a block keyword"
        "f := ({n? : Nat} -> Nat yield n + 1)\nyield f 4"
        "5"
    , programCase "do block"
        "f := ({n? : Nat} -> Nat do x := 1; yield n + x)\nyield f 4"
        "5"
    , programCase "do begin block"
        (unlines
          [ "f := ({n? : Nat} -> Nat do"
          , "begin"
          , "  x := 1"
          , "  yield n + x)"
          , "yield f 4"
          ])
        "5"
    , programCase "begin block without do"
        "f := ({n? : Nat} -> Nat begin x := 1; yield n + x)\nyield f 4"
        "5"
    , programCase "assertion-only function has an explicit unit yield"
        "f := ({n? : Nat} -> () do assert n of Nat; yield ())\nyield f 4"
        "()"
    ]
