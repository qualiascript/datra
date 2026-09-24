module Datra.Interpreter.IntegrationTests
  ( integrationTests
  ) where

import Datra.TestSupport
import Interpreting
  ( EvaluationMode (DevelopmentMode, ProductionMode) )
import Test.Tasty (TestTree, testGroup)

integrationTests :: TestTree
integrationTests =
  testGroup "cross-feature regression programs"
    [ programCase "recursive defaults, overloads, typing, and total blocks"
        recursiveDefaultProgram
        "()"
    , programCase "standard-library syntax and string-template decoding"
        templateBackedProgram
        "()"
    , programCase "let scope composes through an assertion-only function"
        scopedAssertionProgram
        "()"
    , moduleCase moduleOrigin
        "module exports, private closure state, and declared syntax"
        moduleProgram
        "()"
    , programCaseInMode DevelopmentMode
        "development assertions validate the complete pipeline"
        modeProgram
        "()"
    , programCaseInMode ProductionMode
        "production omits soft assertions but retains hard integration checks"
        productionModeProgram
        "()"
    , programFileCase 20
        "twenty-line composed language regression"
        "test/fixtures/integration/composed_features.datra"
        "()"
    ]

recursiveDefaultProgram :: String
recursiveDefaultProgram = unlines
  [ "let factorial := ({n? : Int := 5} -> Int do"
  , "begin"
  , "  assert n of Int"
  , "  yield if n = 0 then 1 else n * factorial (n - 1))"
  , "arguments := ({n? : Int := 5} << 6)"
  , "assert arguments of (n? : Int)"
  , "assert factorial () = 120"
  , "assert factorial arguments = 720"
  , "result := begin yield factorial 6"
  , "assert result = 720"
  , "assert result =/= 719"
  , "assert not (result =/= 720)"
  , "assert 720 of result"
  , "assert (720 ~> result) = result"
  ]

templateBackedProgram :: String
templateBackedProgram = unlines
  [ "successor : \"$Nat next\" as ({value? : Int} -> Int) := (do"
  , "begin"
  , "  assert value of Nat"
  , "  yield value + 1)"
  , "assert successor 4 next = 5"
  , "assert successor of ({value? : Nat} -> Int)"
  , "assert %(\"from 2 to 5\" ~> \"from %Int to %Int\")[1] of Int"
  , "assert %(\"from 2 to 5\" ~> \"from %Int to %Int\")[2] of Int"
  ]

scopedAssertionProgram :: String
scopedAssertionProgram = unlines
  [ "before := seed + 1"
  , "let seed := 10"
  , "check := (() -> () do begin"
  , "  local := before + seed"
  , "  assert local = 21"
  , "  yield ())"
  , "assert before = 11"
  , "assert check () = ()"
  ]

moduleOrigin :: FilePath
moduleOrigin = "test/fixtures/modules/main.datra"

moduleProgram :: String
moduleProgram = unlines
  [ "import \"library_one\""
  , "assert LibraryOne.x[1] = 7"
  , "assert LibraryOne.increment 7 = 11"
  , "assert LibraryOne.shift 7 = 11"
  ]

modeProgram :: String
modeProgram = factorialForMode <> unlines
  [ "assert factorial () = 120"
  , "assert hard factorial 6 = 720"
  ]

productionModeProgram :: String
productionModeProgram = factorialForMode <> unlines
  [ "assert missing_soft_assertion_dependency"
  , "assert hard factorial () = 120"
  , "assert hard ({n? : Int := 5} << 6) of (n? : Int)"
  ]

factorialForMode :: String
factorialForMode = unlines
  [ "let factorial := ({n? : Int := 5} -> Int do"
  , "  yield if n = 0 then 1 else n * factorial (n - 1))"
  ]
