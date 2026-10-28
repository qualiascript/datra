module Datra.Interpreter.IntegrationTests
  ( integrationTests
  ) where

import Datra.TestSupport
import Test.Tasty (TestTree, testGroup)

integrationTests :: TestTree
integrationTests =
  testGroup "cross-feature regression programs"
    [ programCase "recursive defaults, overloads, typing, and total blocks"
        recursiveDefaultProgram
        "(true; true; true; true; true; true; true; true)"
    , programCase "standard-library syntax and string-template decoding"
        templateBackedProgram
        "(true; true; true; true)"
    , programCase "let scope composes through a checking function"
        scopedCheckProgram
        "(true; true)"
    , moduleCase moduleOrigin
        "module exports, private closure state, and declared syntax"
        moduleProgram
        "(true; true; true)"
    , programFileCase 21
        "composed language regression"
        "test/fixtures/integration/composed_features.datra"
        "(true; true; true; true; true; true; true; true)"
    ]

recursiveDefaultProgram :: String
recursiveDefaultProgram = unlines
  [ "let factorial := ({n? : Int := 5} -> Int do"
  , "  yield if n = 0 then 1 else n * factorial (n - 1))"
  , "arguments := ({n? : Int := 5} << 6)"
  , "result := begin yield factorial 6"
  , "argumentsTypeCheck := arguments of (n? : Int)"
  , "defaultCheck := factorial () = 120"
  , "argumentCheck := factorial arguments = 720"
  , "resultCheck := result = 720"
  , "inequalityCheck := result =/= 719"
  , "negatedInequalityCheck := not (result =/= 720)"
  , "membershipCheck := 720 of result"
  , "specificationCheck := (720 ~> result) = result"
  , "yield (argumentsTypeCheck; defaultCheck; argumentCheck; resultCheck;"
  , "  inequalityCheck; negatedInequalityCheck; membershipCheck;"
  , "  specificationCheck)"
  ]

templateBackedProgram :: String
templateBackedProgram = unlines
  [ "\"successor %Nat next\" := ({value? : Int} -> Int) do"
  , "  yield value + 1"
  , "successorResultCheck := successor 4 next = 5"
  , "successorTypeCheck := successor of ({value? : Nat} -> Int)"
  , "fromCheck := (\"from 2 to 5\" ~> \"from %Int to %Int\")[1] of Int"
  , "toCheck := (\"from 2 to 5\" ~> \"from %Int to %Int\")[2] of Int"
  , "yield (successorResultCheck; successorTypeCheck; fromCheck; toCheck)"
  ]

scopedCheckProgram :: String
scopedCheckProgram = unlines
  [ "before := seed + 1"
  , "let seed := 10"
  , "check := (() -> Bool do"
  , "  local := before + seed"
  , "  yield local = 21)"
  , "yield (before = 11; check ())"
  ]

moduleOrigin :: FilePath
moduleOrigin = "test/fixtures/modules/main.datra"

moduleProgram :: String
moduleProgram = unlines
  [ "import \"library_one\" do"
  , "  valueCheck := LibraryOne.x = 7"
  , "  incrementCheck := LibraryOne.increment 7 = 11"
  , "  shiftCheck := LibraryOne.(shift 7) = 11"
  , "yield (valueCheck; incrementCheck; shiftCheck)"
  ]
