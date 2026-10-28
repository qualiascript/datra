{-# LANGUAGE LambdaCase #-}

module Datra.Interpreter.ModuleTests (moduleTests) where

import Datra.TestSupport
import DatraLanguage.Diagnostics.Application
  ( ModuleLoadFailure (..))
import DatraTypes
  ( AtlasMapFederationOperation (..)
  , AtlasMapFederationUncertainty (..)
  , InterpretingError (..)
  , ModuleEvaluationFailure (..)
  , OverloadFailure (OverloadMissingRequiredSlot)
  )
import System.FilePath (takeFileName)
import Test.Tasty (TestTree, testGroup)

moduleTests :: TestTree
moduleTests =
  testGroup "modules"
    [ moduleCase origin "qualified value"
        "import \"library_one\" do yield LibraryOne.x + 0"
        "7"
    , moduleCase origin "declared name is independent of filename"
        "import \"different_filename\" do yield DeclaredName.x + 0"
        "12"
    , moduleCase origin "two qualified modules"
        ( "import (\"library_one\"; \"library_two\") do\n"
            <> "yield LibraryOne.x + LibraryTwo.x"
        )
        "16"
    , moduleCase origin "repeated import paths are idempotent"
        ( "import (\"library_one\"; \"library_one\") do\n"
            <> "yield LibraryOne.x + 0"
        )
        "7"
    , moduleFailureCase origin "overlapping module federations are rejected"
        ( "import (\"overlap_one\"; \"overlap_two\") do\n"
            <> "yield Shared"
        )
        (== ModuleEvaluationFailure
          (AtlasMapFederationOperationUndecidable
            (NoAtlasMapFederationDecisionProcedure
              AtlasMapFederationConcatenation)))
    , moduleCase origin "one module can export multiple qualified binders"
        ( "import \"multiple_exports\" do\n"
            <> "yield First.x + Second.y"
        )
        "7"
    , moduleCase origin "each exported binder retains its syntax scope"
        "import \"multiple_exports\" do yield Second.(shift second 3)"
        "7"
    , programFileCase 2 "with opens several module values and their syntax"
        "test/fixtures/modules/debug_with.datra"
        "10"
    , moduleCase origin "with repeated module values is idempotent"
        ( "import \"multiple_exports\" do\n"
            <> "with First; First do yield x + 0"
        )
        "3"
    , moduleCase origin "with function value uses the same scope operation"
        ( "import \"multiple_exports\" do\n"
            <> "yield 'with ((First; Second); do yield x + y)"
        )
        "7"
    , moduleCase origin "with preserves its enclosing function return"
        ( "import \"multiple_exports\" do\n"
            <> "  f := ({n? : Int} -> Int do\n"
            <> "    with First do yield x + n)\n"
            <> "yield f 8"
        )
        "11"
    , moduleFailureCase origin "with rejects ambiguous public federations"
        ( "import (\"library_one\"; \"library_two\") do\n"
            <> "with LibraryOne; LibraryTwo do yield x"
        )
        (== ModuleEvaluationFailure
          (AtlasMapFederationOperationUndecidable
            (NoAtlasMapFederationDecisionProcedure
              AtlasMapFederationConcatenation)))
    , moduleFailureCase origin "with scope does not leak"
        ( "import \"multiple_exports\" do\n"
            <> "  opened := (with First do yield x)\n"
            <> "yield x"
        )
        (== ModuleEvaluationFailure (UnknownIdentifier "x"))
    , moduleCase origin "import body returns its result"
        ( "import \"library_one\" do\n"
            <> "  doubled := LibraryOne.x * 2\n"
            <> "yield doubled"
        )
        "14"
    , moduleCase origin "import function value uses eager import semantics"
        ( "yield 'import (\"library_one\"; do\n"
            <> "  yield LibraryOne.x + 0\n"
            <> ")"
        )
        "7"
    , moduleCase origin "import function value accepts a path list"
        ( "yield Std.'import ((\"library_one\"; \"library_two\"); do\n"
            <> "  yield LibraryOne.x + LibraryTwo.x\n"
            <> ")"
        )
        "16"
    , moduleCase origin "import function exposes its federated argument as it"
        "import \"library_one\" do yield it.LibraryOne.x"
        "7"
    , moduleCase origin "exported function closes over a private helper"
        "import \"library_one\" do yield LibraryOne.increment 7"
        "11"
    , moduleCase origin "module-scoped exported syntax"
        "import \"library_one\" do yield LibraryOne.(shift 7)"
        "11"
    , moduleCase origin "exported dependent declaration supports lookup"
        ( "import \"dependent_declarations\" do\n"
            <> "yield DependentDeclarations."
            <> "(~\"pair 1 with 2\")[0].value"
        )
        "{_x : Int := 1; _y : Int := 2}"
    , moduleCase origin "scope-protected dependent declaration supports lookup"
        ( "import \"dependent_declarations\" do\n"
            <> "yield DependentDeclarations."
            <> "(~\"protected 3\")[0].value"
        )
        "{_x : Int := 3}"
    , moduleFailureCase origin "private dependent declaration is not exported"
        ( "import \"dependent_declarations\" do\n"
            <> "yield DependentDeclarations."
            <> "(~\"_private 3\")[0].value"
        )
        isEvaluationFailure
    , moduleCase origin "module scope preserves the import function return"
        ( "import \"library_one\" do LibraryOne.(\n"
            <> "  shifted := shift 7\n"
            <> "yield shifted\n"
            <> ")"
        )
        "11"
    , moduleCase origin "function-body import keeps its lexical scope"
        ( "f := ({n? : Int} -> Int do\n"
            <> "  yield (import \"library_one\" do "
            <> "yield LibraryOne.increment n))\n"
            <> "yield f 4"
        )
        "8"
    , moduleCase origin "a returned closure retains its imported binder"
        ( "f := (import \"library_one\" do\n"
            <> "  yield ({n? : Int} -> Int do\n"
            <> "    yield LibraryOne.increment n))\n"
            <> "yield f 3"
        )
        "7"
    , moduleCase origin "transitive import"
        "import \"nested\" do yield Nested.x + 0"
        "8"
    , moduleCase origin "explicit export map"
        "import \"explicit_exports\" do yield ExplicitExports.visible + 0"
        "7"
    , moduleCase origin "selected exports remain qualified"
        ( "import \"selected_exports\" do\n"
            <> "yield SelectedExports.a + SelectedExports.b"
        )
        "3"
    , moduleCase origin "val and transparent exports preserve distinct forms"
        ( "import \"canonical_values\" do\n"
            <> "yield (CanonicalValues.owned; CanonicalValues.transparent)"
        )
        "(CanonicalValues.owned; 8)"
    , moduleCase origin "opened val and transparent exports preserve distinct forms"
        ( "import \"canonical_values\" do\n"
            <> "with CanonicalValues do yield (owned; transparent)"
        )
        "(owned; 8)"
    , moduleCase origin "scalar module value"
        "import \"total_value\" do yield Answer + 0"
        "42"
    , moduleCase origin "module evaluates preceding file bindings"
        "import \"total_value_with_binding\" do yield AnswerWithBinding + 0"
        "42"
    , moduleCase origin "import composes with specification"
        "import \"total_value\" do yield (Answer + 0) ~> Int"
        "42 ~> Int"
    , moduleCase origin "import composes with subfederation"
        "import \"total_value\" do yield (Answer of Int)"
        "true"
    , moduleCase origin "imported values compose with optional names"
        ( "import \"total_value\" do\n"
            <> "  f := ({value? : Int} -> Int do yield value)\n"
            <> "yield f(value : Answer) + 0"
        )
        "42"
    , moduleCase origin "numbers max and min satisfy positional assertions"
        ( "import \"numbers\" do\n"
            <> "yield (Numbers.max() = nothing;\n"
            <> "  Numbers.max(1) = (Just : 1);\n"
            <> "  Numbers.max(1; 5; 3) = (Just : 5);\n"
            <> "  Numbers.min(1; 5; 3) = (Just : 1))"
        )
        "(true; true; true; true)"
    , moduleCase origin "numbers max and min support mixed named calls"
        ( "import \"numbers\" do\n"
            <> "yield (Numbers.max(arg1 : 3, 0); "
            <> "Numbers.min(arg2 : 12, arg0 : 9, 2))"
        )
        "(Just : 3; Just : 2)"
    , moduleCase origin "numbers max and min support integer limits"
        ( "import \"numbers\" do\n"
            <> "yield (Numbers.max(-Infinity; 3; Infinity; -4); "
            <> "Numbers.min(Infinity; 3; -Infinity; 4))"
        )
        "(Just : Infinity; Just : -Infinity)"
    , moduleCase origin "numbers max and min retain finite integer behavior"
        ( "import \"numbers\" do\n"
            <> "yield (Numbers.max(-20; -3; -11); "
            <> "Numbers.min(-20; -3; -11))"
        )
        "(Just : -3; Just : -20)"
    , moduleCase origin "numbers max matches unmatched names positionally"
        "import \"numbers\" do yield Numbers.max(my_arg : 3, 0)"
        "Just : 3"
    , moduleFailureCase origin "numbers max reserves admitted Args names"
        "import \"numbers\" do yield Numbers.max(arg2 : 3, 0)"
        (== ModuleEvaluationFailure
          (OverloadError OverloadMissingRequiredSlot))
    , moduleFailureCase origin "numbers is not imported by default"
        "yield Numbers.max(1, 2)"
        (== ModuleEvaluationFailure (UnknownIdentifier "Numbers"))
    , moduleCase origin "ordinal arithmetic module"
        ( "import \"ordinals\" do\n"
            <> "yield (Ordinals.sum(...; 2); "
            <> "Ordinals.prod(...; 2); "
            <> "Ordinals.exp(...; 2); "
            <> "Ordinals.minus(2; 3))"
        )
        "(... + 2; ... * 2 + 0; ... ^ 2 + 0; 0)"
    , moduleCase origin "ordinal comparisons"
        ( "import \"ordinals\" do\n"
            <> "yield (Ordinals.lt(2; 3); Ordinals.lte(3; 3); "
            <> "Ordinals.gt(3; 2); Ordinals.gte(3; 3))"
        )
        "(true; true; true; true)"
    , moduleCase origin "ordinal operations accept x and y argumentative maps"
        "import \"ordinals\" do yield Ordinals.sum(y : 3; x : 2)"
        "5"
    , moduleCase origin "OrdValue contains naturals and transfinite ordinals"
        ( "import \"ordinals\" do\n"
            <> "yield (Ordinals.OrdValue = (Ordinal | Nat); "
            <> "2 of Ordinals.OrdValue; ... of Ordinals.OrdValue)"
        )
        "(true; true; true)"
    , moduleCase origin "ordinal exponent uniquely reorders positional arguments"
        ( "import \"ordinals\" do\n"
            <> "yield (Ordinals.exp(2; ...); Ordinals.exp(...; 2))"
        )
        "(... ^ 2 + 0; ... ^ 2 + 0)"
    , moduleFailureCase origin "import scope does not leak"
        ( "imported := (import \"library_one\" do yield LibraryOne.x)\n"
            <> "yield LibraryOne.x"
        )
        (== ModuleEvaluationFailure (UnknownIdentifier "LibraryOne"))
    , moduleFailureCase origin "an import in a map does not affect siblings"
        ( "result := (loaded : import \"library_one\" do "
            <> "yield LibraryOne.x; sibling : LibraryOne.x)\n"
            <> "yield result"
        )
        (== ModuleEvaluationFailure (UnknownIdentifier "LibraryOne"))
    , moduleFailureCase origin "module syntax does not leak"
        "import \"library_one\" do yield shift 7"
        (== ModuleEvaluationFailure (UnknownIdentifier "shift"))
    , moduleFailureCase origin "filename is not an implicit namespace"
        ( "import \"different_filename\" do\n"
            <> "yield DifferentFilename.x"
        )
        isEvaluationFailure
    , moduleFailureCase origin "private value is not exported"
        "import \"library_one\" do yield LibraryOne._offset"
        isEvaluationFailure
    , moduleFailureCase origin "explicit exports exclude private fields"
        "import \"explicit_exports\" do yield ExplicitExports._hidden"
        isEvaluationFailure
    , moduleFailureCase origin "unselected exports are unavailable"
        "import \"selected_exports\" do yield SelectedExports.c"
        isEvaluationFailure
    , moduleFailureCase origin "unexported syntax is unavailable"
        ( "import \"explicit_exports\" do\n"
            <> "yield ExplicitExports.(hidden 1 plus)"
        )
        (== ModuleEvaluationFailure (UnknownIdentifier "hidden"))
    , moduleFailureCase origin "cyclic imports report the cycle"
        "import \"cycle_a\" do yield ()"
        (\case
          ModuleLoadingFailure (CyclicModuleImport path) ->
            takeFileName path == "cycle_a.datra"
          _ -> False)
    , moduleFailureCase origin "missing imports name the requested module"
        "import \"missing\" do yield ()"
        (\case
          ModuleLoadingFailure (ImportPathResolutionFailed requested _ _) ->
            requested == "missing"
          ModuleLoadingFailure (ModuleReadFailed requested _ _) ->
            requested == "missing"
          _ -> False)
    , moduleFailureCase origin "imported file must yield an identifier federation"
        "import \"unnamed\" do yield ()"
        (== ModuleEvaluationFailure
          (ModuleEvaluationFailed
            ImportedModuleRequiresIdentifierBinderFederation))
    , moduleFailureCase origin "imported file must reduce to a block"
        "import \"explicit_resource\" do yield ()"
        (== ModuleEvaluationFailure
          (ModuleEvaluationFailed ImportedModuleRequiresBlock))
    , moduleCase origin "qualified import accepts a non-total binder value"
        "import \"non_total_value\" do yield Numbers = Nat"
        "true"
    , moduleCase origin "import accepts a dependent argument federation"
        ( "import \"dependent_export\" do\n"
            <> "yield it = (\"Number%(it)\" : Nat)"
        )
        "true"
    , moduleCase origin "import accepts mixed simple and dependent binders"
        ( "import \"mixed_export\" do\n"
            <> "yield it"
        )
        "(Named : Nat; \"Number%(it)\" : Nat)"
    ]
  where
    isEvaluationFailure (ModuleEvaluationFailure _) = True
    isEvaluationFailure _ = False

origin :: FilePath
origin = "test/fixtures/modules/main.datra"
