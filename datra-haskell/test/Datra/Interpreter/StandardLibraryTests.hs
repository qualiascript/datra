module Datra.Interpreter.StandardLibraryTests
  ( standardLibraryTests
  ) where

import Datra.TestSupport
import DatraTypes
  ( AtlasMapFederationRefutation
      (AtlasMapFederationSpecificationHasNoMatchingMember)
  , InterpretingError (..)
  )
import Test.Tasty (TestTree, testGroup)

standardLibraryTests :: TestTree
standardLibraryTests =
  testGroup "standard library and declarative syntax"
    [ testGroup "qualified syntax"
        [ expressionCase source source expected
        | (source, expected) <-
            [ ("StdLib.if false then (1 + \"bad\") else 11", "11")
            , ("StdLib.from (1 + 1) to 5", "from 2 to 5")
            , ("StdLib.range 2 downwards", "range 2 downwards")
            , ("StdLib.true", "true : true")
            ]
        ]
    , testGroup "scope values"
        [ programCase source source expected
        | (source, expected) <-
            [ ("a:=5\nb:=8\nyield this.a", "a : 5")
            , ("_private:=3\na:=5\nyield this", "a : 5")
            , ("a:=5\nyield this.a of (a?:Nat)", "true")
            , ("a:=5\nyield this.a ~> (a?:Nat)", "a? : Nat := 5")
            , ("yield from (2,5)", "from 2 to 5")
            , ("yield from (2,$upwards)", "from 2 upwards")
            , ("f := external \"datra.add\"\nyield f (b:5;6)", "11")
            , ( "f := (x:Int, {a?:Int,b?:Int} -> Int do yield x+a+b)\n"
                  <> "yield f (x:3,b:5,6)"
              , "14"
              )
            ]
        ]
    , testGroup "scope rejections"
        [ programFailureCase "private member access"
            "_private:=3\na:=5\nyield this._private"
            (SourceEvaluationFailure
              (NamedAccessError "no field named _private"))
        , programFailureCase "private standard-library eval"
            "yield StdLib._eval"
            (SourceEvaluationFailure
              (UnknownIdentifier "_eval"))
        , programFailureCase "duplicate scope member"
            "a:=5\na:=8\nyield this"
            (SourceEvaluationFailure (IdentifierStringOverlap "a"))
        , programFailureCase "specified function validates narrowed input"
            ("f := ({x?:Int} -> Int do yield x+1)\n"
              <> "g := (f ~> ({x?:Nat} -> Int))\nyield g (-1)")
            (SourceEvaluationFailure
              (FunctionError
                "no applicable function alternative; syntax-only alternatives require their AST pattern"))
        , programFailureCase "unknown external shorthand"
            "yield external \"missing.symbol\""
            (SourceEvaluationFailure
              (FunctionError "unknown registered external: missing.symbol"))
        , programFailureCase "the former Iden spelling is no longer exported"
            "yield Iden"
            (SourceEvaluationFailure (UnknownIdentifier "Iden"))
        ]
    , testGroup "library types"
        [ expressionCase source source "true"
        | source <-
            [ "$Nothing = (Nothing : ())"
            , "nothing = $Nothing"
            , "NatRange of IntRange"
            , "not (IntRange of NatRange)"
            , "NatValRange of IntValRange"
            , "not (IntValRange of NatValRange)"
            , "not (NatRange of IntValRange)"
            , "not (NatValRange of IntRange)"
            , "from 2 to 5 of NatValRange"
            , "range 2 upwards of NatRange"
            , "not (from (-2) to 5 of NatValRange)"
            , "(from 2 to 5 ~> NatValRange) of IntValRange"
            , "(range 2 to 5 ~> NatRange) of IntRange"
            , "Expr of AST"
            , "Block of AST"
            , "Pages of AST"
            , "not (Block of Expr)"
            , "(Expr ~> AST) of AST"
            , "\"%Int %IdenStr\" of StringTemplate"
            , "(\"%Int %IdenStr\" ~> StringTemplate) of StringTemplate"
            , "not (2 of StringTemplate)"
            , "String of StringTemplate"
            ]
        ]
    , declaredPatternTests
    ]

declaredPatternTests :: TestTree
declaredPatternTests =
  testGroup "declared patterns"
    [ programCase "syntax pattern call"
        (declaration <> "yield step (1+1) next") "3"
    , programCase "ordinary spelling"
        (ordinaryDeclaration <> "yield step (value:2)") "3"
    , programCase "syntax function subfederation"
        (declaration <> "yield step of ({value?:Nat} -> Int)") "true"
    , programCase "ordinary specified function remains callable"
        (ordinaryDeclaration
          <> "f := (step ~> ({value?:Nat} -> Int))\nyield f 2")
        "3"
    , programFailureCase "syntax pattern checks captures"
        (declaration <> "yield step (-1) next")
        (SourceEvaluationFailure
          (AtlasMapFederationOperationRefuted
            AtlasMapFederationSpecificationHasNoMatchingMember))
    , programFailureCase "syntax-only function rejects ordinary calls"
        (declaration <> "yield step 2")
        (SourceEvaluationFailure
          (FunctionError
            "no applicable function alternative; syntax-only alternatives require their AST pattern"))
    , programFailureCase "duplicate syntax declaration"
        (declaration <> declaration <> "yield this")
        (SourceEvaluationFailure (IdentifierStringOverlap "step"))
    , programFailureCase "ambiguous syntax alternatives"
        ( "step := ((\"$Int next\" as (Int -> Int) external \"datra.abs\")"
            <> " | (\"$Int next\" as (Int -> Int) do yield 2))\n"
            <> "yield step 3 next"
        )
        (SourceEvaluationFailure EitherAlternativesNotDistinct)
    ]
  where
    declaration =
      "step : \"$Nat next\" as ({value?:Int} -> Int) := (do yield value+1)\n"
    ordinaryDeclaration =
      "step : \"$Nat next\" as? ({value?:Int} -> Int) := (do yield value+1)\n"
