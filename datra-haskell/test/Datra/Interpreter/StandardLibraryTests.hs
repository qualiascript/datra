module Datra.Interpreter.StandardLibraryTests
  ( standardLibraryTests
  ) where

import Datra.TestSupport
import DatraTypes
  ( ExternalFailure (..)
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
            "yield !^\"datra.AST\"" "_AST"
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
            , ("Std.range 2 down", "range 2 down")
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
            "yield (fun 5) ~> Nat" "5 ~> from 0 up"
        , programCase "fixed point reverse specification"
            "yield Nat <~ (fun 5)" "5 ~> from 0 up"
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
              , "a? : from 0 up := 5"
              )
            , ("_private:=3\na:=5\nyield this._private", "_private : 3")
            , ("a:=5\nyield this.a of (a?:Nat)", "true")
            , ("a:=5\nyield this.a ~> (a?:Nat)", "a? : from 0 up := 5")
            , ("a:=(b:2;c:3)\nyield a.(b,c)", "b : 2, c : 3")
            , ("a:=(b:2;c:3)\nyield a.(b,c) of (a.b,a.c)", "true")
            , ( "a:=(b:2;c:3)\n"
                  <> "yield a.(b,c) ~> (b?:Nat,c?:Nat)"
              , "b? : from 0 up := 2, c? : from 0 up := 3"
              )
            , ("yield from (2,5)", "from 2 to 5")
            , ("yield from (2,$up)", "from 2 up")
            , ("f := !^\"datra.add\"\nyield f (b:5;6)", "11")
            , ( "f := (x:Int, {a?:Int,b?:Int} -> Int do yield x+a+b)\n"
                  <> "yield f (x:3,b:5,6)"
              , "14"
              )
            ]
        ]
    , testGroup "value lookup"
        [ programCase "retrieves a named binding"
            "x := 5\nyield ^x" "5"
        , programCase "retrieves a quoted binding"
            "\"value with spaces\" := 5\nyield ^\"value with spaces\"" "5"
        , programCase "retrieves a private binding"
            "_x := 5\nyield ^_x" "5"
        , programCase "further access selects from the retrieved value"
            "x := (5; 8)\nyield ^x[1]" "8"
        , programCase "optional names accept named and positional inputs"
            ("f := ({x? : Nat} -> Nat yield ^x + 1)\n"
              <> "yield (f 5; f (x := 5))")
            "(6; 6)"
        , programCase "optional names retain defaults"
            "f := ({x? : Nat := 5} -> Nat yield ^x + 1)\nyield f ()" "6"
        , programCase "specification accepts the retrieved value"
            "x := 5\nyield (^x ~> Int) of Int" "true"
        , programCase "reverse specification accepts the retrieved value"
            "x := 5\nyield (Int <~ ^x) of Int" "true"
        , programCase "subfederation checks the retrieved value"
            "x := 5\nyield ^x of Nat" "true"
        , programCase "subfederation rejects a different value"
            "x := 5\nyield ^x of 6" "false"
        , programCase "lookup does not change optional-name specification"
            ("x := 5\nyield (x := ^x) ~> (x? : Nat)")
            "x? : from 0 up := 5"
        ]
    , testGroup "mapped access"
        [ expressionCase "coalization is explicit and idempotent"
            ">< >< (20; 30)"
            ">< (20; 30)"
        , expressionCase "coalization preserves an Either boundary"
            ">< (Nat | Str)"
            ">< (from 0 up | Str)"
        , expressionCase "coalization preserves an identifier boundary"
            ">< (x : Nat)"
            ">< (x : from 0 up)"
        , expressionCase "coalization preserves a map-valued member"
            "(10; >< (20; 30))"
            "(10; >< (20; 30))"
        , programCase "coalized members remain directly accessible"
            "yield (>< (10; 20; 30))[1]"
            "20"
        , programCase "coalization occupies one outer sequence position"
            "yield (>< (10; 20); 30)[0][1]"
            "20"
        , programCase "coalization occupies one function argument slot"
            ( "f := ((>< (Nat; Nat); Str) -> Nat yield it[0][1])\n"
                <> "yield f((1; 2); \"x\")"
            )
            "2"
        , programCase "coalization composes with subfederation"
            "yield (>< (1; 2)) of >< (Nat; Nat)"
            "true"
        , programCase "coalization composes with specification"
            "yield ((>< (1; 2)) ~> >< (Nat; Nat)) of >< (Nat; Nat)"
            "true"
        , programCase "coalized types concatenate positionally despite overlap"
            "yield Int, Int"
            ( "((from 0 up; nothing | () | Just : $Complement); "
                <> "(from 0 up; nothing | () | Just : $Complement))"
            )
        , programCase "function inference retains coalization"
            ( "f := (do yield >< (a + 1; a + 2))\n"
                <> "yield f 3"
            )
            ">< (4; 5)"
        , programCase "identifier erasure retains coalization"
            "x := (a : 1; b : 2)\nyield val >< x"
            ">< (1; 2)"
        , programCase "brackets preserve a semicolon selector map"
            "values := (10; 20; 30)\nyield values[0; range 1 up]"
            "(10; >< (20; 30))"
        , programCase "infix access preserves a semicolon selector map"
            "values := (10; 20; 30)\nyield values @ (0; range 1 up)"
            "(10; >< (20; 30))"
        , programCase "comma selectors concatenate their access results"
            "values := (10; 20; 30)\nyield values[0, range 1 up]"
            "(10; 20; 30)"
        , programCase "semicolon access retains overlapping argument types"
            ( "split := ({Args Int,} -> (Int; List Int) do "
                <> "yield (val it)[0; range 1 up])\n"
                <> "yield split(10, 20, 30)"
            )
            "(10; >< (20; 30))"
        ]
    , testGroup "contextual result inference"
        [ programCase "selects a uniquely matching user-defined sum member"
            ("f := (() -> ($MyNothing | MyJust : Int) yield 5)\n"
              <> "yield f()")
            "MyJust : 5"
        , programFailureCase "rejects ambiguous user-defined sum members"
            ("f := (() -> (Left : Int | Right : Int) yield 5)\n"
              <> "yield f()")
            (SourceEvaluationFailure
              (FunctionEvaluationFailed FunctionBodyOutsideDeclaredResult))
        ]
    , testGroup "Maybe and list operators"
        [ programCase "postfix optional aliases Maybe"
            "yield Int? = Maybe Int" "true"
        , programCase "parenthesized postfix optional nests"
            "yield (Int?)? = Maybe (Maybe Int)" "true"
        , programCase "empty list split is nothing"
            "yield ()!" "nothing"
        , programCase "nonempty list split preserves head and tail"
            "yield (1; 2; 3)!" "Just : (1; >< (2; 3))"
        , programCase "Maybe sequencing binds tagged it"
            "yield (1; 2; 3)! ?? val it"
            "Just : (1; >< (2; 3))"
        , programCase "Maybe sequencing leaves the absent branch lazy"
            "yield ()! ?? missing" "nothing"
        , programFailureCase "Maybe sequencing rejects a non-Maybe left operand"
            "yield 1 ?? 2"
            (SourceEvaluationFailure
              (FunctionEvaluationFailed NoApplicableFunctionAlternative))
        , programFailureCase "Maybe sequencing statically requires a Maybe left operand"
            "yield (() -> Int? yield 1 ?? 2)"
            (SourceEvaluationFailure
              (FunctionEvaluationFailed NoApplicableFunctionAlternative))
        , programCase "optional named matcher accepts split positional values"
            ( "head := ({candidate? : Int, remaining? : List Int} -> Int "
                <> "yield candidate)\n"
                <> "yield (1; 2; 3)! ?? head it"
            )
            "Just : 1"
        , programFailureCase "required named matcher rejects split positional values"
            ( "head := ({candidate : Int, remaining : List Int} -> Int "
                <> "yield candidate)\n"
                <> "yield (1; 2; 3)! ?? head it"
            )
            (SourceEvaluationFailure
              (FunctionEvaluationFailed NoApplicableFunctionAlternative))
        , programCase "InhabitedList describes a split list"
            "yield (1; (2; 3)) of InhabitedList Int" "true"
        , programCase "inferred type aliases reduce to their canonical type"
            "Alias := (Nat | Str)\nyield Alias = (Nat | Str)" "true"
        ]
    , testGroup "scope rejections"
        [ programFailureCase "duplicate scope member"
            "a:=5\na:=8\nyield this"
            (SourceEvaluationFailure (IdentifierStringOverlap "a"))
        , programFailureCase "specified function validates narrowed input"
            ("f := ({x?:Int} -> Int do yield x+1)\n"
              <> "g := (f ~> ({x?:Nat} -> Int))\nyield g (-1)")
            (SourceEvaluationFailure
              (FunctionEvaluationFailed NoApplicableFunctionAlternative))
        , programFailureCase "unknown external shorthand"
            "yield !^\"missing.symbol\""
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
            , "not ((!^\"datra.AST\") of Any)"
            , "not ((Nat; (!^\"datra.AST\")) of Any)"
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
            , "from 0 to Infinity of NatValRange"
            , "range 2 up of NatRange"
            , "not (from (-2) to 5 of NatValRange)"
            , "(from 2 to 5 ~> NatValRange) of IntValRange"
            , "(from (-5) to Infinity ~> IntValRange) of IntValRange"
            , "(range 2 to 5 ~> NatRange) of IntRange"
            , "(!^\"datra.Expr\") of (!^\"datra.AST\")"
            , "(!^\"datra.Block\") of (!^\"datra.AST\")"
            , "not ((!^\"datra.Block\") of (!^\"datra.Expr\"))"
            , "((!^\"datra.Expr\") ~> (!^\"datra.AST\")) of (!^\"datra.AST\")"
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
        , programCase "Just is a polymorphic tagged type constructor"
            "yield ((Just Nat) of (Maybe Nat)) and ((Just : 5) of (Just Nat))"
            "true"
        , programCase "Maybe does not infer a missing Just label"
            "yield not (5 of Maybe Nat)"
            "true"
        , programCase "nested Maybe distinguishes Just nothing from nothing"
            ( "yield ((Just nothing) of Maybe (Maybe Nat)) and "
                <> "(nothing of Maybe (Maybe Nat)) and "
                <> "((Just nothing) =/= nothing)"
            )
            "true"
        , programCase "Args accepts every finite positional prefix"
            ( "values := ({Args Int,} -> List Int yield val it)\n"
                <> "yield values(1, 2, 3)"
            )
            "(1; 2; 3)"
        , programCase "Args reorders named and positional slots"
            ( "values := ({Args Int,} -> List Int yield val it)\n"
                <> "yield values(arg1 := 3, 0)"
            )
            "(0; 3)"
        , programFailureCase "Args rejects a gap in its finite prefix"
            ( "values := ({Args Int,} -> List Int yield val it)\n"
                <> "yield values(arg2 := 3, 0)"
            )
            (SourceEvaluationFailure
              (FunctionEvaluationFailed NoApplicableFunctionAlternative))
        , programCase "source-defined Args supports string-template functions"
            ( "MyArgs := (for T? of Any) -> Any do\n"
                <> "  slots := with i in Nat do \"arg%(i)\"? : T\n"
                <> "yield () | with n in Nat do slots[range 0 to n]\n"
                <> "display := {MyArgs Int,} -> Str do yield \"%(val it)\"\n"
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
        , programCase "with-from-do omits the in keyword"
            "yield (with i from 0 to 2 do i + 1)[2]"
            "3"
        , programCase "for-in-do builds an indexed product family"
            "yield (for i in range 0 to 2 do i + 1)[2]"
            "3"
        , programCase "for-from-do maps a finite valued range"
            "yield for i from 0 to 3 do i * 2"
            "(0; 2; 4; 6)"
        , programCase "omitted-in accepts a valued range expression"
            "values := from 0 to 3\nyield for i values do i * 2"
            "(0; 2; 4; 6)"
        , programCase "for-from-do maps an infinite valued range lazily"
            "yield (for i from 0 up do i * i)[5]"
            "25"
        , programFailureCase "for without in rejects an ordinary range"
            "yield for i range 0 to 2 do i"
            (SourceEvaluationFailure (ExpectedBuiltinType "IntValRange"))
        , programFailureCase "with without in rejects an ordinary range"
            "yield with i range 0 to 2 do i"
            (SourceEvaluationFailure (ExpectedBuiltinType "IntValRange"))
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
    , integerLimitTests
    , declaredPatternTests
    ]

integerLimitTests :: TestTree
integerLimitTests =
  testGroup "integer limits and infinity"
    [ testGroup "types"
        [ programCase "Nat is the open upward range"
            "yield Nat" "from 0 up"
        , programCase "Int and IntLimit expose coalized source definitions"
            "yield (Int; IntLimit)"
            ( "(>< (from 0 up; nothing | () | Just : $Complement); "
                <> ">< (>< (from 0 up, Infinity); "
                <> "nothing | () | Just : $Complement))"
            )
        , programCase "unnamed NatLimit functions accept finite and limit values"
            ( "identity := (NatLimit -> NatLimit yield it)\n"
                <> "yield (identity 3; identity Infinity)"
            )
            "(3; Infinity)"
        , programCase "finite and infinite values inhabit their limit types"
            ( "yield (0 of Nat; 23 of Nat; not (-1 of Nat); "
                <> "0 of NatLimit; Infinity of NatLimit; "
                <> "not (-Infinity of NatLimit); "
                <> "-23 of Int; 23 of Int; not (Infinity of Int); "
                <> "Infinity of IntLimit; -Infinity of IntLimit)"
            )
            "(true; true; true; true; true; true; true; true; true; true; true)"
        , programCase "unit and Boolean are not integer members"
            "yield (not (() of Int); not (true of Int))"
            "(true; true)"
        , programCase "unit is neutral in sequences and concatenations"
            "yield ((23; ()) = 23; ((); 23) = 23; (23, ()) = 23; ((), 23) = 23)"
            "(true; true; true; true)"
        , programCase "complement representation inhabits integer types"
            ( "yield ((22; Just : $Complement) of Int; "
                <> "(Infinity; Just : $Complement) of IntLimit)"
            )
            "(true; true)"
        ]
    , testGroup "open and closed ranges"
        [ programCase "from upward excludes positive infinity"
            "yield (Infinity of from 0 up)" "false"
        , programCase "from through infinity includes its endpoint"
            "yield (Infinity of from 0 to Infinity)" "true"
        , programCase "transfinite access reaches positive infinity"
            "yield (from 0 to Infinity)[...]" "Infinity"
        , programCase "valued infinite endpoints are coalized"
            ( "yield (from 0 to Infinity; from -5 to Infinity; "
                <> "from 5 to -Infinity)"
            )
            ( "(>< (from 0 up, Infinity); >< (from -5 up, Infinity); "
                <> ">< (from 5 down, -Infinity))"
            )
        , programCase "signed transfinite access reaches either infinity"
            ( "yield ((from -5 to Infinity)[...]; "
                <> "(from 5 to -Infinity)[...])"
            )
            "(Infinity; -Infinity)"
        , programCase "finite access before the transfinite endpoint"
            "yield ((from 0 to Infinity)[0]; (from 0 to Infinity)[23])"
            "(0; 23)"
        , programCase "range upward excludes positive infinity"
            "yield (Infinity of range 0 up)" "false"
        , programCase "range through infinity includes its endpoint"
            "yield (Infinity of range 0 to Infinity)" "true"
        , programCase "infinite range origins select the expected limits"
            ( "yield (Infinity of range Infinity up; "
                <> "not (0 of range Infinity up); "
                <> "-Infinity of range -Infinity down; "
                <> "not (0 of range -Infinity down); "
                <> "-20 of range Infinity down; "
                <> "0 of range Infinity to -Infinity; "
                <> "20 of range -Infinity to Infinity)"
            )
            "(true; true; true; true; true; true; true)"
        , programFailureCase "from rejects a positive-infinite origin"
            "yield from Infinity down"
            (SourceEvaluationFailure
              (FunctionEvaluationFailed NoApplicableFunctionAlternative))
        , programFailureCase "from rejects a negative-infinite origin"
            "yield from -Infinity up"
            (SourceEvaluationFailure
              (FunctionEvaluationFailed NoApplicableFunctionAlternative))
        ]
    , testGroup "operators"
        [ programCase "addition and subtraction preserve infinite limits"
            ( "yield (Infinity + 23; 23 + Infinity; "
                <> "-Infinity + 23; 23 + -Infinity; "
                <> "Infinity - 23; 23 - Infinity; "
                <> "-Infinity - 23; 23 - -Infinity)"
            )
            ( "(Infinity; Infinity; -Infinity; -Infinity; "
                <> "Infinity; -Infinity; -Infinity; Infinity)"
            )
        , programCase "multiplication applies signs to infinity"
            ( "yield (Infinity * 2; 2 * Infinity; Infinity * -2; "
                <> "-Infinity * -2; -3 * -Infinity)"
            )
            "(Infinity; Infinity; -Infinity; Infinity; Infinity)"
        , programCase "unary operators use canonical infinity forms"
            "yield (+Infinity; -Infinity; -(-Infinity))"
            "(Infinity; -Infinity; Infinity)"
        , programCase "infinite powers respect zero and parity"
            "yield (Infinity ^ 0; Infinity ^ 3; (-Infinity) ^ 2; (-Infinity) ^ 3)"
            "(1; Infinity; Infinity; -Infinity)"
        , programCase "comparisons order all integer limits"
            ( "yield (-Infinity < -23; -23 <= -23; -23 < Infinity; "
                <> "Infinity > 23; Infinity >= Infinity; "
                <> "not (Infinity < Infinity); not (-Infinity > -Infinity))"
            )
            "(true; true; true; true; true; true; true)"
        , programCase "a safe IntLimit function is inferred"
            ( "increment := (IntLimit -> IntLimit yield it + 1)\n"
                <> "yield (increment Infinity; increment (-Infinity))"
            )
            "(Infinity; -Infinity)"
        , programFailureCase "zero times positive infinity is indeterminate"
            "yield 0 * Infinity"
            (SourceEvaluationFailure (IndeterminateInfinityOperation "*"))
        , programFailureCase "zero times negative infinity is indeterminate"
            "yield -Infinity * 0"
            (SourceEvaluationFailure (IndeterminateInfinityOperation "*"))
        , programFailureCase "opposite infinities cannot be added"
            "yield Infinity + -Infinity"
            (SourceEvaluationFailure (IndeterminateInfinityOperation "+"))
        , programFailureCase "equal infinities cannot be subtracted"
            "yield Infinity - Infinity"
            (SourceEvaluationFailure (IndeterminateInfinityOperation "-"))
        , programFailureCase "negative infinities cannot be subtracted"
            "yield (-Infinity) - (-Infinity)"
            (SourceEvaluationFailure (IndeterminateInfinityOperation "-"))
        ]
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
          (FunctionEvaluationFailed NoApplicableFunctionAlternative))
    , programFailureCase "syntax-only function rejects ordinary calls"
        (declaration <> "yield step 2")
        (SourceEvaluationFailure
          (FunctionEvaluationFailed NoApplicableFunctionAlternative))
    , programFailureCase "duplicate syntax declaration"
        (declaration <> declaration <> "yield this")
        (SourceEvaluationFailure (IdentifierStringOverlap "step"))
    , programFailureCase "ambiguous syntax alternatives"
        ( "step := ((\"$Int next\" as (Int -> Int) yield !^\"datra.abs\")"
            <> " | (\"$Int next\" as (Int -> Int) do yield 2))\n"
            <> "yield step 3 next"
        )
        (SourceEvaluationFailure EitherAlternativesNotDistinct)
    ]
  where
    declaration =
      "step : \"$Nat next\" as ({value?:Nat} -> Int) := (do yield value+1)\n"
    ordinaryDeclaration =
      "step : \"$Nat next\" as? ({value?:Int} -> Int) := (do yield value+1)\n"
