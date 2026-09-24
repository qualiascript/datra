{-# LANGUAGE LambdaCase #-}

module Datra.Interpreter.ModuleTests (moduleTests) where

import Data.List (isInfixOf)
import Datra.TestSupport
import DatraTypes (InterpretingError (..))
import ModuleNames (moduleIdentifier)
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit (assertEqual, testCase)

moduleTests :: TestTree
moduleTests =
  testGroup "modules"
    [ testCase "snake-case path becomes a namespace" $
        assertEqual "module namespace" "StdLib"
          (moduleIdentifier "path/std_lib.datra")
    , moduleCase origin "qualified value"
        "import \"library_one\"\nyield LibraryOne.x"
        "x : 7"
    , moduleCase origin "import all"
        "import all \"library_one\"\nyield x"
        "7"
    , moduleCase origin "two qualified modules"
        (unlines
          [ "import \"library_one\""
          , "import \"library_two\""
          , "yield LibraryOne.x[1] + LibraryTwo.x[1]"
          ])
        "16"
    , moduleCase origin "exported function closes over a private helper"
        "import \"library_one\"\nyield LibraryOne.increment 7"
        "11"
    , moduleCase origin "qualified exported syntax"
        "import \"library_one\"\nyield LibraryOne.shift 7"
        "11"
    , moduleCase origin "unqualified exported syntax"
        "import all \"library_one\"\nyield shift 7"
        "11"
    , moduleCase origin "transitive import"
        "import \"nested\"\nyield Nested.x"
        "x : 8"
    , moduleCase origin "explicit export map"
        "import all \"explicit_exports\"\nyield public"
        "7"
    , moduleCase origin "explicit standard-library import is idempotent"
        ("import all \"std_lib\"\n"
          <> "yield StdLib.if true then 11 else (1+\"bad\")")
        "11"
    , moduleFailureCase origin "qualified import does not leak names"
        "import \"library_one\"\nyield x"
        (== ModuleEvaluationFailure (UnknownIdentifier "x"))
    , moduleFailureCase origin "import-all collision"
        ("import all \"library_one\"\n"
          <> "import all \"library_two\"\nyield x")
        (== ModuleEvaluationFailure (IdentifierStringOverlap "x"))
    , moduleFailureCase origin "private value is not exported"
        "import \"library_one\"\nyield LibraryOne._offset"
        isEvaluationFailure
    , moduleFailureCase origin "import all excludes private values"
        "import all \"library_one\"\nyield _offset"
        (== ModuleEvaluationFailure (UnknownIdentifier "_offset"))
    , moduleFailureCase origin "explicit exports exclude private fields"
        "import \"explicit_exports\"\nyield ExplicitExports._hidden"
        isEvaluationFailure
    , moduleFailureCase origin "unexported syntax is unavailable"
        "import \"explicit_exports\"\nyield ExplicitExports.hidden 1 plus"
        (== ModuleEvaluationFailure (UnknownIdentifier "hidden"))
    , moduleFailureCase origin "cyclic imports report the cycle"
        "import \"cycle_a\""
        (\case
          ModuleLoadingFailure message -> "cyclic import:" `isInfixOf` message
          _ -> False)
    , moduleFailureCase origin "missing imports name the requested module"
        "import \"missing\""
        (\case
          ModuleLoadingFailure message -> "cannot import missing" `isInfixOf` message
          _ -> False)
    ]
  where
    isEvaluationFailure (ModuleEvaluationFailure _) = True
    isEvaluationFailure _ = False

origin :: FilePath
origin = "test/fixtures/modules/main.datra"
