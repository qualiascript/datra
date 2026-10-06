{-# LANGUAGE LambdaCase #-}

module Datra.Interpreter.ModuleTests (moduleTests) where

import Datra.TestSupport
import DatraLanguage.Diagnostics.Application
  ( ModuleLoadFailure (..))
import DatraTypes
  ( InterpretingError (..)
  , ModuleEvaluationFailure (..)
  )
import System.FilePath (takeFileName)
import Test.Tasty (TestTree, testGroup)

moduleTests :: TestTree
moduleTests =
  testGroup "modules"
    [ moduleCase origin "qualified value"
        "import \"library_one\"\nyield LibraryOne.x"
        "x : 7"
    , moduleCase origin "declared name is independent of filename"
        "import \"different_filename\"\nyield DeclaredName.x"
        "x : 12"
    , moduleCase origin "import all"
        "import all \"library_one\"\nyield x"
        "7"
    , moduleCase origin "modular import all retains the exported name"
        "import all \"modular_library\"\nyield x"
        "x"
    , moduleCase origin "modular import handles explicit assignments"
        "import all \"modular_library\"\nyield typed"
        "typed"
    , moduleCase origin "qualified modular value retains its module name"
        "import \"modular_library\"\nyield ModularLibrary.x"
        "ModularLibrary.x"
    , moduleCase origin "qualified modular closure retains its canonical name"
        "import \"modular_library\"\nyield ModularLibrary.identity"
        "ModularLibrary.identity"
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
        "import all \"explicit_exports\"\nyield visible"
        "7"
    , moduleCase origin "dotted module exports select named bindings"
        "import all \"selected_exports\"\nyield a + b"
        "3"
    , moduleCase origin "outer yielded block supplies the module namespace"
        "import \"selected_exports\"\nyield SelectedExports.a + SelectedExports.b"
        "3"
    , moduleCase origin "qualified import accepts any total named value"
        "import \"total_value\"\nyield Answer"
        "42"
    , moduleCase origin "qualified import evaluates preceding file bindings"
        "import \"total_value_with_binding\"\nyield AnswerWithBinding"
        "42"
    , moduleCase origin "explicit standard-library import is idempotent"
        ("import all \"std\"\n"
          <> "yield if true then 11 else (1+\"bad\")")
        "11"
    , moduleCase origin "explicit standard-library import retains canonical names"
        "import all \"std\"\nyield Nat"
        "Nat"
    , moduleCase origin "numbers max and min satisfy positional assertions"
        ( "import \"numbers\"\n"
            <> "assert Numbers.max() = nothing\n"
            <> "assert Numbers.max(1) = (Just : 1)\n"
            <> "assert Numbers.max(1, 5, 3) = (Just : 5)\n"
            <> "assert Numbers.min(1, 5, 3) = (Just : 1)"
        )
        "()"
    , moduleCase origin "numbers max and min support mixed named calls"
        ( "import \"numbers\"\n"
            <> "yield (Numbers.max(arg1 := 3, 0); "
            <> "Numbers.min(arg2 := 12, arg0 := 9, 2))"
        )
        "(Just : 3; Just : 2)"
    , moduleCase origin "numbers max and min support integer limits"
        ( "import \"numbers\"\n"
            <> "yield (Numbers.max(-Infinity, 3, Infinity, -4); "
            <> "Numbers.min(Infinity, 3, -Infinity, 4))"
        )
        "(Just : Infinity; Just : -Infinity)"
    , moduleCase origin "numbers max and min retain finite integer behavior"
        ( "import \"numbers\"\n"
            <> "yield (Numbers.max(-20, -3, -11); "
            <> "Numbers.min(-20, -3, -11))"
        )
        "(Just : -3; Just : -20)"
    , moduleCase origin "numbers max matches unmatched names positionally"
        "import \"numbers\"\nyield Numbers.max(arg2 := 3, 0)"
        "Just : 3"
    , moduleFailureCase origin "numbers is not imported by default"
        "yield Numbers.max(1, 2)"
        (== ModuleEvaluationFailure (UnknownIdentifier "Numbers"))
    , moduleCase origin "ordinal arithmetic module"
        ( "import \"ordinals\"\n"
            <> "yield (Ordinals.sum(...; 2); "
            <> "Ordinals.prod(...; 2); "
            <> "Ordinals.exp(...; 2); "
            <> "Ordinals.minus(2; 3))"
        )
        "(... + 2; ... * 2 + 0; ... ^ 2 + 0; 0)"
    , moduleCase origin "ordinal comparisons"
        ( "import \"ordinals\"\n"
            <> "yield (Ordinals.lt(2; 3); Ordinals.lte(3; 3); "
            <> "Ordinals.gt(3; 2); Ordinals.gte(3; 3))"
        )
        "(true; true; true; true)"
    , moduleCase origin "ordinal operations accept x and y argument maps"
        "import \"ordinals\"\nyield Ordinals.sum(y := 3; x := 2)"
        "5"
    , moduleCase origin "OrdValue contains naturals and transfinite ordinals"
        ( "import \"ordinals\"\n"
            <> "yield (Ordinals.OrdValue = (Ordinal | Nat); "
            <> "2 of Ordinals.OrdValue; ... of Ordinals.OrdValue)"
        )
        "(true; true; true)"
    , moduleCase origin "ordinal exponent uniquely reorders positional arguments"
        ( "import \"ordinals\"\n"
            <> "yield (Ordinals.exp(2; ...); Ordinals.exp(...; 2))"
        )
        "(... ^ 2 + 0; ... ^ 2 + 0)"
    , moduleFailureCase origin "qualified import does not leak names"
        "import \"library_one\"\nyield x"
        (== ModuleEvaluationFailure (UnknownIdentifier "x"))
    , moduleFailureCase origin "filename is not an implicit namespace"
        "import \"different_filename\"\nyield DifferentFilename.x"
        isEvaluationFailure
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
    , moduleFailureCase origin "dotted module exports omit unselected bindings"
        "import all \"selected_exports\"\nyield c"
        (== ModuleEvaluationFailure (UnknownIdentifier "c"))
    , moduleFailureCase origin "unexported syntax is unavailable"
        "import \"explicit_exports\"\nyield ExplicitExports.hidden 1 plus"
        (== ModuleEvaluationFailure (UnknownIdentifier "hidden"))
    , moduleFailureCase origin "cyclic imports report the cycle"
        "import \"cycle_a\""
        (\case
          ModuleLoadingFailure (CyclicModuleImport path) ->
            takeFileName path == "cycle_a.datra"
          _ -> False)
    , moduleFailureCase origin "missing imports name the requested module"
        "import \"missing\""
        (\case
          ModuleLoadingFailure (ImportPathResolutionFailed requested _ _) ->
            requested == "missing"
          ModuleLoadingFailure (ModuleReadFailed requested _ _) ->
            requested == "missing"
          _ -> False)
    , moduleFailureCase origin "imported file must yield a simple identifier type"
        "import \"unnamed\""
        (== ModuleEvaluationFailure
          (ModuleEvaluationFailed ImportedModuleRequiresSimpleIdentifierType))
    , moduleFailureCase origin "qualified import requires a total value"
        "import \"non_total_value\""
        (== ModuleEvaluationFailure
          (ModuleEvaluationFailed ImportedModuleRequiresTotalValue))
    , moduleFailureCase origin "import all rejects a scalar total value"
        "import all \"total_value\""
        (== ModuleEvaluationFailure
          (ModuleEvaluationFailed
            ImportAllRequiresTotalMapOfSimpleIdentifierTypes))
    , moduleFailureCase origin "import all rejects unnamed map members"
        "import all \"unnamed_members\""
        (== ModuleEvaluationFailure
          (ModuleEvaluationFailed
            ImportAllRequiresTotalMapOfSimpleIdentifierTypes))
    ]
  where
    isEvaluationFailure (ModuleEvaluationFailure _) = True
    isEvaluationFailure _ = False

origin :: FilePath
origin = "test/fixtures/modules/main.datra"
