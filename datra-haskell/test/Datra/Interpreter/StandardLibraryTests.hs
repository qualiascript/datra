module Datra.Interpreter.StandardLibraryTests
  ( standardLibraryTests
  ) where

import Datra.TestSupport
import DatraTypes
  ( AtlasMapFederationRefutation
      (AtlasMapFederationSpecificationHasNoMatchingMember)
  , ExternalFailure (..)
  , FunctionFailure (..)
  , InterpretingError (..)
  )
import Test.Tasty (TestTree, testGroup)

standardLibraryTests :: TestTree
standardLibraryTests =
  testGroup "standard library and declarative syntax"
    [ testGroup "private AST implementation type"
        [ programFailureCase "AST is no longer implicitly imported"
            "yield AST" (SourceEvaluationFailure (UnknownIdentifier "AST"))
        , programFailureCase "_AST is private to the library"
            "yield _AST" (SourceEvaluationFailure (UnknownIdentifier "_AST"))
        , programFailureCase "Std does not export _AST"
            "yield Std._AST" (SourceEvaluationFailure (UnknownIdentifier "_AST"))
        , programCase "AST can be a user binding"
            "AST := 2\nyield AST" "2"
        , programCase "AST external uses the private type spelling"
            "yield _external \"datra.AST\"" "_AST"
        , programFailureCase "Expr is private to the library"
            "yield Expr" (SourceEvaluationFailure (UnknownIdentifier "Expr"))
        , programFailureCase "Block is private to the library"
            "yield Block" (SourceEvaluationFailure (UnknownIdentifier "Block"))
        , programFailureCase "Pages is private to the library"
            "yield Pages" (SourceEvaluationFailure (UnknownIdentifier "Pages"))
        , programFailureCase "IdenExp is private to the library"
            "yield IdenExp" (SourceEvaluationFailure (UnknownIdentifier "IdenExp"))
        ]
    , testGroup "qualified syntax"
        [ expressionCase source source expected
        | (source, expected) <-
            [ ("Std.if false then (1 + \"bad\") else 11", "11")
            , ("Std.from (1 + 1) to 5", "from 2 to 5")
            , ("Std.range 2 downwards", "range 2 downwards")
            , ("Std.true", "true : true")
            ]
        ]
    , testGroup "inline fixed points"
        [ programCase "literal fixed point"
            "yield fun 5" "5"
        , programCase "recursive Nat function"
            ("factorial := fun {n? : Nat} -> Nat yield "
              <> "if n = 0 then 1 else n * this (n - 1)\n"
              <> "yield factorial 5")
            "120"
        , programCase "fun and let factorials agree"
            ("inlineFactorial := fun {n? : Int} -> Int yield "
              <> "if n = 0 then 1 else n * this (n - 1)\n"
              <> "let boundFactorial := ({n? : Int} -> Int yield "
              <> "if n = 0 then 1 else n * boundFactorial (n - 1))\n"
              <> "assert inlineFactorial 6 = boundFactorial 6\n"
              <> "yield inlineFactorial 6")
            "720"
        , programCase "finite access lazily unfolds recursive data"
            ("name := fun \"hi:\", this\n"
              <> "k : Nat := 1\n"
              <> "yield name[from 0 to 3 * (k + 1) - 1]")
            "\"hi:hi:\""
        , programCase "recursive concatenation is not string-specific"
            ("values := fun 1, this\n"
              <> "yield values[from 0 to 3]")
            "(1; 1; 1; 1)"
        , programCase "recursive semicolon sequence uses map machinery"
            ("values := fun (1; 2; this)\n"
              <> "yield values[from 0 to 5]")
            "(1; 2; 1; 2; 1; 2)"
        , programCase "let and fun share productive fixed-point access"
            ("let name := \"hi:\", name\n"
              <> "k : Nat := 1\n"
              <> "yield name[from 0 to 3 * (k + 1) - 1]")
            "\"hi:hi:\""
        , programCase "fixed point specification"
            "yield (fun 5) ~> Nat" "5 ~> Nat"
        , programCase "fixed point reverse specification"
            "yield Nat <~ (fun 5)" "5 ~> Nat"
        , programCase "fixed point subfederation"
            "yield (fun 5) of Nat" "true"
        , programCase "fixed point as an optional named argument"
            ("apply := ({value? : Nat} -> Nat yield value + 1)\n"
              <> "yield apply (fun 5)")
            "6"
        ]
    , testGroup "scope values"
        [ programCase source source expected
        | (source, expected) <-
            [ ("a:=5\nb:=8\nyield this.a", "a : 5")
            , ("_private:=3\na:=5\nyield public this", "a : 5")
            , ( "yield public (_private:3;a:5) of (a?:Nat)"
              , "true"
              )
            , ( "yield public (_private:3;a:5) ~> (a?:Nat)"
              , "a? : Nat := 5"
              )
            , ("_private:=3\na:=5\nyield this._private", "_private : 3")
            , ("a:=5\nyield this.a of (a?:Nat)", "true")
            , ("a:=5\nyield this.a ~> (a?:Nat)", "a? : Nat := 5")
            , ("a:=(b:2;c:3)\nyield a.(b,c)", "b : 2, c : 3")
            , ("a:=(b:2;c:3)\nyield a.(b,c) of (a.b,a.c)", "true")
            , ( "a:=(b:2;c:3)\n"
                  <> "yield a.(b,c) ~> (b?:Nat,c?:Nat)"
              , "b? : Nat := 2, c? : Nat := 3"
              )
            , ("yield from (2,5)", "from 2 to 5")
            , ("yield from (2,$upwards)", "from 2 upwards")
            , ("f := _external \"datra.add\"\nyield f (b:5;6)", "11")
            , ( "f := (x:Int, {a?:Int,b?:Int} -> Int do yield x+a+b)\n"
                  <> "yield f (x:3,b:5,6)"
              , "14"
              )
            ]
        ]
    , testGroup "value lookup"
        [ programCase "retrieves a named binding"
            "x := 5\nyield !x" "5"
        , programCase "retrieves a quoted binding"
            "\"value with spaces\" := 5\nyield !\"value with spaces\"" "5"
        , programCase "retrieves a private binding"
            "_x := 5\nyield !_x" "5"
        , programCase "further access selects from the retrieved value"
            "x := (5; 8)\nyield !x[1]" "8"
        , programCase "optional names accept named and positional inputs"
            ("f := ({x? : Nat} -> Nat yield !x + 1)\n"
              <> "yield (f 5; f (x := 5))")
            "(6; 6)"
        , programCase "optional names retain defaults"
            "f := ({x? : Nat := 5} -> Nat yield !x + 1)\nyield f ()" "6"
        , programCase "specification accepts the retrieved value"
            "x := 5\nyield (!x ~> Int) of Int" "true"
        , programCase "reverse specification accepts the retrieved value"
            "x := 5\nyield (Int <~ !x) of Int" "true"
        , programCase "subfederation checks the retrieved value"
            "x := 5\nyield !x of Nat" "true"
        , programCase "subfederation rejects a different value"
            "x := 5\nyield !x of 6" "false"
        , programCase "lookup does not change optional-name specification"
            ("x := 5\nyield (x := !x) ~> (x? : Nat)")
            "x? : Nat := 5"
        ]
    , testGroup "scope rejections"
        [ programFailureCase "private standard-library eval"
            "yield Std._eval"
            (SourceEvaluationFailure
              (UnknownIdentifier "_eval"))
        , programFailureCase "duplicate scope member"
            "a:=5\na:=8\nyield this"
            (SourceEvaluationFailure (IdentifierStringOverlap "a"))
        , programFailureCase "specified function validates narrowed input"
            ("f := ({x?:Int} -> Int do yield x+1)\n"
              <> "g := (f ~> ({x?:Nat} -> Int))\nyield g (-1)")
            (SourceEvaluationFailure
              (FunctionEvaluationFailed NoApplicableFunctionAlternative))
        , programFailureCase "unknown external shorthand"
            "yield _external \"missing.symbol\""
            (SourceEvaluationFailure
              (ExternalEvaluationFailed
                (UnknownExternalSymbol "missing.symbol")))
        , programFailureCase "the former Iden spelling is no longer exported"
            "yield Iden"
            (SourceEvaluationFailure (UnknownIdentifier "Iden"))
        ]
    , testGroup "library types"
        [ expressionCase source source "true"
        | source <-
            [ "Any of Any"
            , "Nat of Any"
            , "5 of Any"
            , "(Nat; Str) of Any"
            , "(begin yield (Nat -> Nat)) of Any"
            , "(Nat -> Nat) of Any"
            , "not ((_external \"datra.AST\") of Any)"
            , "not ((Nat; (_external \"datra.AST\")) of Any)"
            , "(5 ~> Any) = 5"
            , "(value : Any := 5) of (value : Any)"
            , "$Nothing = (Nothing : ())"
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
            , "(_external \"datra.Expr\") of (_external \"datra.AST\")"
            , "(_external \"datra.Block\") of (_external \"datra.AST\")"
            , "(_external \"datra.Pages\") of (_external \"datra.AST\")"
            , "not ((_external \"datra.Block\") of (_external \"datra.Expr\"))"
            , "((_external \"datra.Expr\") ~> (_external \"datra.AST\")) of (_external \"datra.AST\")"
            , "\"%Any\" of StrTempl"
            , "\"%Int %IdenStr\" of StrTempl"
            , "(\"%Int %IdenStr\" ~> StrTempl) of StrTempl"
            , "not (2 of StrTempl)"
            , "Str of StrTempl"
            ]
        ]
    , testGroup "dependent List"
        [ programCase "Str is List Char"
            "yield Str = List Char" "true"
        , programCase "an element is the singleton member of its List type"
            "yield 1 of List Nat" "true"
        , programCase "natural list uses semicolon members"
            "yield (1; 2; 3) of List Nat" "true"
        , programCase "natural list rejects a non-natural member"
            "yield (1; \"x\") of List Nat" "false"
        , programCase "List Str preserves nested string members"
            "yield (\"a\"; \"bc\") of List Str" "true"
        , programCase "List Str rejects a non-string member"
            "yield (\"a\"; 2) of List Str" "false"
        , programCase "concatenated strings inhabit List Str as one string"
            "yield (\"a\", \"bc\") of List Str" "true"
        ]
    , testGroup "Maybe and variadic Args"
        [ programCase "Maybe uses tagged Nothing and Just alternatives"
            "yield (($Nothing; Just : 5) of (Maybe Nat; Maybe Nat))"
            "true"
        , programCase "Args accepts every finite positional prefix"
            ( "values := ({Args Int,} -> List Int yield ^it)\n"
                <> "yield values(1, 2, 3)"
            )
            "(1; 2; 3)"
        , programCase "Args reorders named and positional slots"
            ( "values := ({Args Int,} -> List Int yield ^it)\n"
                <> "yield values(arg1 := 3, 0)"
            )
            "(0; 3)"
        , programFailureCase "Args rejects a gap in its finite prefix"
            ( "values := ({Args Int,} -> List Int yield ^it)\n"
                <> "yield values(arg2 := 3, 0)"
            )
            (SourceEvaluationFailure
              (FunctionEvaluationFailed NoApplicableFunctionAlternative))
        , programCase "source-defined Args supports string-template functions"
            ( "MyArgs := (for T? of Any) -> Any do\n"
                <> "  slots := with i in Nat do \"arg%(i)\"? : T\n"
                <> "yield () | with n in Nat do slots[range 0 to n]\n"
                <> "display := {MyArgs Int,} -> Str do yield \"%(^it)\"\n"
                <> "assert ((arg2 := 10, 4) of {MyArgs Int,}) = false\n"
                <> "yield (display(); display(1); display(1, 2, 3); "
                <> "display(arg1 := 10, 4))"
            )
            "(\"()\"; \"1\"; \"(1; 2; 3)\"; \"(4; 10)\")"
        ]
    , testGroup "dependent family sugar"
        [ programCase "with-in-do builds an indexed sum family"
            "yield (with i in range 0 to 2 do i + 1)[2]"
            "3"
        , programCase "for-in-do builds an indexed product family"
            "yield (for i in range 0 to 2 do i + 1)[2]"
            "3"
        ]
    , testGroup "dependent sums"
        [ programCase "optional binder accepts positional witnesses"
            ( "Pair := {with T? of Any; value? : T}\n"
                <> "yield (Nat; 5) of Pair"
            )
            "true"
        , programCase "optional binder accepts named assignment witnesses"
            ( "Pair := {with T? of Any; value? : T}\n"
                <> "yield {T := Nat; value := 5} of Pair"
            )
            "true"
        , programCase "required binder accepts its named assignment form"
            ( "Pair := {with T of Any; value? : T}\n"
                <> "yield {T := Nat; value := 5} of Pair"
            )
            "true"
        , programCase "required binder rejects a positional witness"
            ( "Pair := {with T of Any; value? : T}\n"
                <> "yield not ((Nat; 5) of Pair)"
            )
            "true"
        , programCase "dependent sum validates the selected fibre"
            ( "Pair := {with T? of Any; value? : T}\n"
                <> "yield not ({T := Nat; value := \"bad\"} of Pair)"
            )
            "true"
        , programCase "dependent sum binders scope sequentially"
            ( "Nested := {with T? of Any; with U? of T; value? : U}\n"
                <> "yield {T := Any; U := Nat; value := 5} of Nested"
            )
            "true"
        , programCase "dependent sum composes with forward specification"
            ( "Pair := {with T? of Any; value? : T}\n"
                <> "yield ({T := Nat; value := 5} ~> Pair) of Pair"
            )
            "true"
        , programCase "dependent sum composes with reverse specification"
            ( "Pair := {with T? of Any; value? : T}\n"
                <> "yield (Pair <~ {T := Nat; value := 5}) of Pair"
            )
            "true"
        , programCase "private optional binder is valid in an ordered map"
            ( "Pair := (with _T? of Any; value? : _T)\n"
                <> "yield (_T := Nat; value := 5) of Pair"
            )
            "true"
        , programFailureCase "ordinary map names do not bind later members"
            ( "Bad := {T? : Any; value? : T}\n"
                <> "yield Bad"
            )
            (SourceEvaluationFailure (UnknownIdentifier "T"))
        , programFailureCase "dependent sums do not bind forwards"
            ( "Bad := {value? : T; with T? of Any}\n"
                <> "yield Bad"
            )
            (SourceEvaluationFailure (UnknownIdentifier "T"))
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
          (FunctionEvaluationFailed NoApplicableFunctionAlternative))
    , programFailureCase "duplicate syntax declaration"
        (declaration <> declaration <> "yield this")
        (SourceEvaluationFailure (IdentifierStringOverlap "step"))
    , programFailureCase "ambiguous syntax alternatives"
        ( "step := ((\"$Int next\" as (Int -> Int) _external \"datra.abs\")"
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
