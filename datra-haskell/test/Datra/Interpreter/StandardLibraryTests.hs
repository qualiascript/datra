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
  , MapLengthFailure (..)
  , ModuleEvaluationFailure (..)
  )
import Test.Tasty (TestTree, testGroup)

standardLibraryTests :: TestTree
standardLibraryTests =
  testGroup "standard library and declarative syntax"
    [ testGroup "modular exports"
        [ programCase "marker is appended at the final identifier index"
            "x := 7\nyield (modular this).x[2]" "$Modular"
        , programCase "the empty map may be marked repeatedly"
            "yield modular (modular ())" "()"
        , programFailureCase "modular rejects unnamed values"
            "yield modular (1; 2)"
            (SourceEvaluationFailure (ModuleEvaluationFailed
              ModularRequiresTotalMapOfSimpleIdentifierTypes))
        , programFailureCase "modular rejects an existing marker"
            "x := 7\nyield modular (modular this)"
            (SourceEvaluationFailure (ModuleEvaluationFailed
              (ModularIdentifierAlreadyMarked "x")))
        ]
    , testGroup "private AST implementation type"
        [ programFailureCase "AST is no longer implicitly imported"
            "yield AST" (SourceEvaluationFailure (UnknownIdentifier "AST"))
        , programFailureCase "_AST is private to the library"
            "yield _AST" (SourceEvaluationFailure (UnknownIdentifier "_AST"))
        , programFailureCase "Std does not export _AST"
            "yield Std._AST" (SourceEvaluationFailure (UnknownIdentifier "_AST"))
        , programCase "AST can be a user binding"
            "AST := 2\nyield AST" "2"
        , programCase "AST external uses the private type spelling"
            "yield !~\"datra.AST\"" "_AST"
        , programFailureCase "Expr is private to the library"
            "yield Expr" (SourceEvaluationFailure (UnknownIdentifier "Expr"))
        , programFailureCase "Block is private to the library"
            "yield Block" (SourceEvaluationFailure (UnknownIdentifier "Block"))
        , programFailureCase "Pages is private to the library"
            "yield Pages" (SourceEvaluationFailure (UnknownIdentifier "Pages"))
        , programFailureCase "IdenExp is private to the library"
            "yield IdenExp" (SourceEvaluationFailure (UnknownIdentifier "IdenExp"))
        , programFailureCase "_SyntaxTemplate is private to the library"
            "yield _SyntaxTemplate"
            (SourceEvaluationFailure (UnknownIdentifier "_SyntaxTemplate"))
        , programCase "SyntaxTemplate external uses the private type spelling"
            "yield !~\"datra.SyntaxTemplate\"" "_SyntaxTemplate"
        ]
    , testGroup "final-page length"
        [ programCase "finite lengths use the final page"
            ( "yield (len (); len 5; len (1; 2; 3); "
                <> "len ((1; 2); (3; 4)); len \"abc\")"
            )
            "(0; 1; 3; 2; 3)"
        , programCase "omega length is positive infinity"
            "yield len (from 0 up)"
            "Infinity"
        , programCase "ordinary and qualified calls remain available"
            "yield ('len (1; 2; 3); Std.len (4; 5))"
            "(3; 2)"
        , programCase "optional named values retain their map extent"
            ( "measure := ({value? : Any} -> NatLimit do yield len value)\n"
                <> "yield measure (value := (1; 2; 3))"
            )
            "3"
        , programCase "length results compose with specification and subfederation"
            ( "yield (((len (1; 2)) ~> Nat) of Nat; "
                <> "(Nat <~ (len (1; 2))) of Nat; "
                <> "(len (1; 2)) of NatLimit)"
            )
            "(true; true; true)"
        , programFailureCase "host meta-types have indeterminate length"
            "yield len Any"
            (SourceEvaluationFailure
              (MapLengthFailed IndeterminateMapLength))
        ]
    , testGroup "qualified syntax"
        [ expressionCase source source expected
        | (source, expected) <-
            [ ("Std.if false then (1 + \"bad\") else 11", "11")
            , ("Std.from (1 + 1) to 5", "from 2 to 5")
            , ("Std.range 2 down", "range 2 down")
            , ("Std.true", "Std.true")
            ]
        ]
    , testGroup "inline fixed points"
        [ programCase "literal fixed point"
            "yield fun 5" "5"
        , programCase "recursive Nat function"
            ("factorial := fun {n? : Nat} -> Nat do yield "
              <> "if n = 0 then 1 else n * this (n - 1)\n"
              <> "yield factorial 5")
            "120"
        , programCase "fun and let factorials agree"
            ("inlineFactorial := fun {n? : Int} -> Int do yield "
              <> "if n = 0 then 1 else n * this (n - 1)\n"
              <> "let boundFactorial := ({n? : Int} -> Int do yield "
              <> "if n = 0 then 1 else n * boundFactorial (n - 1))\n"
              <> "assert inlineFactorial 6 = boundFactorial 6\n"
              <> "yield inlineFactorial 6")
            "720"
        , programCase "finite access lazily unfolds recursive data"
            ("name := fun (\"hi:\", this)\n"
              <> "k : Nat := 1\n"
              <> "yield name[from 0 to 3 * (k + 1) - 1]")
            "\"hi:hi:\""
        , programCase "recursive concatenation is not string-specific"
            ("values := fun (1, this)\n"
              <> "yield values[from 0 to 3]")
            "(1; 1; 1; 1)"
        , programCase "recursive semicolon sequence uses map machinery"
            ("values := fun (1; 2; this)\n"
              <> "yield values[from 0 to 5]")
            "(1; 2; 1; 2; 1; 2)"
        , programCase "let and fun share productive fixed-point access"
            ("let name := (\"hi:\", name)\n"
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
            ("apply := ({value? : Nat} -> Nat do yield value + 1)\n"
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
            , ("yield 'from (2,5)", "from 2 to 5")
            , ("yield 'from (2,$up)", "from 2 up")
            , ("f := !~\"datra.add\"\nyield f (b:5;6)", "11")
            , ( "f := (x:Int, {a?:Int;b?:Int} -> Int do yield x+a+b)\n"
                  <> "yield f (x:3,b:5,6)"
              , "14"
              )
            ]
        ]
    , testGroup "value lookup"
        [ programCase "retrieves a named binding"
            "x := 5\nyield ~x" "5"
        , programCase "retrieves a quoted binding"
            "\"value with spaces\" := 5\nyield ~\"value with spaces\"" "5"
        , programCase "retrieves a private binding"
            "_x := 5\nyield ~\"_x\"" "5"
        , programCase "further access selects from the retrieved value"
            "x := (5; 8)\nyield ~x[1]" "8"
        , programCase "optional names accept named and positional inputs"
            ("f := ({x? : Nat} -> Nat do yield ~x + 1)\n"
              <> "yield (f 5; f (x := 5))")
            "(6; 6)"
        , programCase "optional names retain defaults"
            "f := ({x? : Nat := 5} -> Nat do yield ~x + 1)\nyield f ()" "6"
        , programCase "specification accepts the retrieved value"
            "x := 5\nyield (~x ~> Int) of Int" "true"
        , programCase "reverse specification accepts the retrieved value"
            "x := 5\nyield (Int <~ ~x) of Int" "true"
        , programCase "subfederation checks the retrieved value"
            "x := 5\nyield ~x of Nat" "true"
        , programCase "subfederation rejects a different value"
            "x := 5\nyield ~x of 6" "false"
        , programCase "lookup does not change optional-name specification"
            ("x := 5\nyield (x := ~x) ~> (x? : Nat)")
            "x? : Nat := 5"
        ]
    , testGroup "mapped access"
        [ expressionCase "coalization is explicit and idempotent"
            ">< >< (20; 30)"
            ">< (20; 30)"
        , expressionCase "coalization preserves an Either boundary"
            ">< (Nat | Str)"
            ">< (Nat | Str)"
        , expressionCase "coalization preserves an identifier boundary"
            ">< (x : Nat)"
            ">< (x : Nat)"
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
            ( "f := ((>< (Nat; Nat); Str) -> Nat do yield it[0][1])\n"
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
            "yield (Int, Int)"
            ( "((Nat; Maybe $Complement); "
                <> "(Nat; Maybe $Complement))"
            )
        , programCase "function results retain coalization"
            ( "f := ({a? : Int} -> >< (Int; Int) do yield >< (a + 1; a + 2))\n"
                <> "yield f 3"
            )
            ">< (4; 5)"
        , programCase "named values do not match a coalized target positionally"
            "yield (a : 1; b : 2) of >< (Nat; Nat)"
            "false"
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
            ( "split := ({Args Int,} -> Any do "
                <> "yield it[0; 1..])\n"
                <> "yield split(10, 20, 30)"
            )
            "(arg0 : 10; >< (arg1 : 20; arg2 : 30))"
        , programCase "clipped access preserves optional identifiers"
            ( "values := (a? : 10; b? : 20)\n"
                <> "yield values[0..10]"
            )
            "(a? : 10; b? : 20)"
        , programCase "clipped access preserves forward specification"
            "yield ((2; 3) ~> (Nat; Nat))[0..10]"
            "(2; 3) ~> (Nat; Nat)"
        , programCase "clipped access preserves reverse specification"
            "yield ((Nat; Nat) <~ (2; 3))[0..10]"
            "(2; 3) ~> (Nat; Nat)"
        , programCase "clipped access composes with subfederation"
            ( "values := (2; 3)\n"
                <> "yield values[0..10] of (Nat; Nat)"
            )
            "true"
        , programCase "repeated specification after clipping terminates"
            ( "values := (2; 3)\n"
                <> "yield ((values[0..10] ~> (Nat; Nat)) "
                <> "~> (Int; Int))"
            )
            "(2; 3) ~> (Int; Int)"
        ]
    , testGroup "contextual result specification"
        [ programCase "selects a uniquely matching user-defined sum member"
            ("f := (() -> ($MyNothing | MyJust : Int) do yield 5)\n"
              <> "yield f()")
            "MyJust : 5"
        , programFailureCase "rejects ambiguous user-defined sum members"
            ("f := (() -> (Left : Int | Right : Int) do yield 5)\n"
              <> "yield f()")
            (SourceEvaluationFailure
              (AtlasMapFederationOperationRefuted
                AtlasMapFederationSpecificationHasNoMatchingMember))
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
            "yield (1; 2; 3)! ?? it[1]"
            "Just : (1; >< (2; 3))"
        , programCase "Maybe sequencing leaves the absent branch lazy"
            "yield ()! ?? missing" "nothing"
        , programCase "list sequencing applies a function to a nonempty split"
            ( "head := ({candidate? : Int; remaining? : List Int} -> Int "
                <> "do yield candidate)\n"
                <> "yield (1; 2; 3) !? head"
            )
            "Just : 1"
        , programCase "list sequencing leaves an empty split lazy"
            "yield () !? missing" "nothing"
        , programCase "list sequencing uses the standard nothing value"
            "yield (() !? missing) = nothing" "true"
        , programCase "list sequencing accepts an optional named parameter"
            ( "head := ({candidate? : Int; remaining? : List Int} -> Int "
                <> "do yield candidate)\n"
                <> "apply := ({values? : List Int} -> Int? "
                <> "do yield values !? head)\n"
                <> "yield apply (4; 5)"
            )
            "Just : 4"
        , programCase "list sequencing result supports specification"
            ( "head := ({candidate? : Int; remaining? : List Int} -> Int "
                <> "do yield candidate)\n"
                <> "yield ((1; 2) !? head) ~> Int?"
            )
            "(Just : 1) ~> Maybe Int"
        , programCase "list sequencing result supports subfederation"
            ( "head := ({candidate? : Int; remaining? : List Int} -> Int "
                <> "do yield candidate)\n"
                <> "yield ((1; 2) !? head) of Int?"
            )
            "true"
        , programFailureCase "Maybe sequencing rejects a non-Maybe left operand"
            "yield 1 ?? 2"
            (SourceEvaluationFailure
              (FunctionEvaluationFailed NoApplicableFunctionAlternative))
        , programFailureCase "Maybe sequencing rejects a non-Maybe operand when called"
            "f := (() -> Int? do yield 1 ?? 2)\nyield f()"
            (SourceEvaluationFailure
              (FunctionEvaluationFailed NoApplicableFunctionAlternative))
        , programCase "optional named matcher accepts split positional values"
            ( "head := ({candidate? : Int; remaining? : List Int} -> Int "
                <> "do yield candidate)\n"
                <> "yield (1; 2; 3)! ?? head it"
            )
            "Just : 1"
        , programFailureCase "required named matcher rejects split positional values"
            ( "head := ({candidate : Int; remaining : List Int} -> Int "
                <> "do yield candidate)\n"
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
            "yield !~\"missing.symbol\""
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
            , "not ((!~\"datra.AST\") of Any)"
            , "not ((Nat; (!~\"datra.AST\")) of Any)"
            , "(5 ~> Any) = 5"
            , "(value : Any := 5) of (value : Any)"
            , "$Nothing = (Nothing : ())"
            , "nothing = (Nothing? : ())"
            , "not (nothing = $Nothing)"
            , "() of nothing"
            , "$Nothing of nothing"
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
            , "(!~\"datra.Expr\") of (!~\"datra.AST\")"
            , "(!~\"datra.Block\") of (!~\"datra.AST\")"
            , "not ((!~\"datra.Block\") of (!~\"datra.Expr\"))"
            , "((!~\"datra.Expr\") ~> (!~\"datra.AST\")) of (!~\"datra.AST\")"
            , "\"%Any\" of Template"
            , "\"%Int %IdenStr\" of Template"
            , "(\"%Int %IdenStr\" ~> Template) of Template"
            , "not (2 of Template)"
            , "Str of Template"
            , "Template of Any"
            , "(\"left\"; \"right\") of InhabitedList Template"
            ]
        ]
    , testGroup "dependent List"
        [ programCase "Str is coalized List Char"
            "yield Str = >< (List Char)" "true"
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
        [ programCase "Maybe uses nothing and Just alternatives"
            "yield ((nothing; Just : 5) of (Maybe Nat; Maybe Nat))"
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
            ( "values := ({Args Int,} -> Any do yield it)\n"
                <> "yield values(1, 2, 3) of {List Int,}"
            )
            "true"
        , programCase "Args reorders named and positional slots"
            ( "values := ({Args Int,} -> Any do yield it)\n"
                <> "yield values(arg1 := 3, 0) of {List Int,}"
            )
            "true"
        , programCase "unmatched Args names fall back positionally"
            ( "values := ({Args Int,} -> Any do yield it)\n"
                <> "yield values(my_arg := 3, 0)"
            )
            "(arg0 : 3; arg1 : 0)"
        , programCase "source-defined Args supports string-template functions"
            ( "MyArgs := &T? -> Any do\n"
                <> "  slots := (^_i :: Nat) -> Any do yield \"arg%(_i)\"? : T\n"
                <> "yield ((^n? :: Nat) -> Any do yield slots[0..n])\n"
                <> "display := {MyArgs Int,} -> Str do yield \"%(it)\"\n"
                <> "assert ((arg2 := 10, 4) of {MyArgs Int,}) = false\n"
                <> "yield (display(); display(1); display(1, 2, 3); "
                <> "display(arg1 := 10, 4))"
            )
            ("(\"()\"; \"arg0 : 1\"; "
              <> "\"(arg0 : 1; arg1 : 2; arg2 : 3)\"; "
              <> "\"(arg0 : 4; arg1 : 10)\")")
        , programCase "only argument maps erase unmatched identifiers"
            ( "assert not ((arg0 : 1; arg1 : 2) of List Int)\n"
                <> "assert ((arg0 : 1; arg1 : 2) of {List Int,})\n"
                <> "yield ()"
            )
            "()"
        , programCase "Args convert to lists through argument map matching"
            ( "ArgsIntMap := {Args Int,}\n"
                <> "ListInt := List Int\n"
                <> "display := ArgsIntMap -> \"%ListInt\" do\n"
                <> "  toList := ArgsIntMap -> {ListInt,} do yield it\n"
                <> "  yield \"%(toList it)\"\n"
                <> "assert display() = \"()\"\n"
                <> "assert display(1) = \"1\"\n"
                <> "assert display(1, 2, 3) = \"(1; 2; 3)\"\n"
                <> "assert display(arg1 := 10, 4) = \"(4; 10)\"\n"
                <> "assert ((arg2 := 10, 4) of ArgsIntMap) = false\n"
                <> "yield ()"
            )
            "()"
        ]
    , testGroup "generic family projection"
        [ programCase "generic sums build indexed families"
            "yield ((^i? :: from 0 to 2) -> Any do yield i + 1)[2]"
            "3"
        , programCase "generic sums accept valued ranges"
            "yield ((^i? :: from 0 to 2) -> Any do yield i + 1)[2]"
            "3"
        , programCase "generic products build indexed families"
            "yield ((&i? :: from 0 to 2) -> Any do yield i + 1)[2]"
            "3"
        , programCase "generic products map finite valued ranges"
            "yield ((&i? :: from 0 to 3) -> Any do yield i * 2)[2]"
            "4"
        , programCase "generic products accept a named range"
            ( "values := from 0 to 3\n"
                <> "yield ((&i? :: values) -> Any do yield i * 2)[3]"
            )
            "6"
        , programCase "generic products accept any ordered Atlas map"
            "yield ((&value? :: 5) -> Any do yield value)[0]"
            "5"
        , programCase "generic products map infinite valued ranges lazily"
            "yield ((&i? :: from 0 up) -> Any do yield i * i)[5]"
            "25"
        ]
    , testGroup "generic sums"
        [ programCase "optional binder accepts positional witnesses"
            ( "Pair := (^T? :: Any) -> Any do yield (value? : T)\n"
                <> "yield (Nat; 5) of Pair"
            )
            "true"
        , programCase "optional binder accepts named assignment witnesses"
            ( "Pair := (^T? :: Any) -> Any do yield (value? : T)\n"
                <> "yield {T := Nat; value := 5} of Pair"
            )
            "true"
        , programCase "dependent sum validates the selected fibre"
            ( "Pair := (^T? :: Any) -> Any do yield (value? : T)\n"
                <> "yield not ({T := Nat; value := \"bad\"} of Pair)"
            )
            "true"
        , programCase "dependent sum composes with forward specification"
            ( "Pair := (^T? :: Any) -> Any do yield (value? : T)\n"
                <> "yield ({T := Nat; value := 5} ~> Pair) of Pair"
            )
            "true"
        , programCase "dependent sum composes with reverse specification"
            ( "Pair := (^T? :: Any) -> Any do yield (value? : T)\n"
                <> "yield (Pair <~ {T := Nat; value := 5}) of Pair"
            )
            "true"
        , programCase "private optional binder is valid in an ordered map"
            ( "Pair := (^_T :: Any) -> Any do yield (value? : _T)\n"
                <> "yield (_T := Nat; value := 5) of Pair"
            )
            "true"
        , programCase "private spelling remains structural in ordinary maps"
            "yield (_a : Nat := 123) of (_a : Nat)"
            "true"
        , programFailureCase "ordinary map names do not bind later members"
            ( "Bad := {T? : Any; value? : T}\n"
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
            "yield Nat" "Nat"
        , programCase "Int and IntLimit expose coalized source definitions"
            "yield (Int; IntLimit)"
            "(Int; IntLimit)"
        , programCase "unnamed NatLimit functions accept finite and limit values"
            ( "identity := (NatLimit -> NatLimit do yield it)\n"
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
        , programCase "unit is neutral only in sequences"
            "yield ((23; ()) = 23; ((); 23) = 23; (23, ()) = 23; ((), 23) = 23)"
            "(true; true; false; false)"
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
            "yield 'from (Infinity, $down)"
            (SourceEvaluationFailure
              (FunctionEvaluationFailed NoApplicableFunctionAlternative))
        , programFailureCase "from rejects a negative-infinite origin"
            "yield 'from (-Infinity, $up)"
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
        , programCase "an IntLimit function retains its declared result"
            ( "increment := (IntLimit -> IntLimit do yield it + 1)\n"
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
    [ programCase "zero-hole syntax completes a total domain"
        ( "answer := \"the answer\" % (42 -> Nat) do yield it\n"
            <> "yield the answer"
        )
        "42"
    , programCase "value holes evaluate expressions before selection"
        ( "double := \"double %Nat\" % (Nat -> Nat) do yield it * 2\n"
            <> "yield double (2 + 2)"
        )
        "8"
    , programCase "syntax pattern call"
        (declaration <> "yield step (1+1) next") "3"
    , programCase "surface syntax name may differ from its binding"
        ( "abc := \"def %Nat next\" % ({value?:Nat} -> Int)"
            <> " do yield value+1\n"
            <> "yield def 2 next"
        )
        "3"
    , programCase "the complete literal prefix is matched before its first hole"
        ( "abc := \"my name is %Nat\" % ({value?:Nat} -> Int)"
            <> " do yield value+1\n"
            <> "yield my name is 2"
        )
        "3"
    , programCase "a template may begin with a postfix operand hole"
        ( "increment := \"%Int++\" % ({value?:Int} -> Int)"
            <> " do yield value+1\n"
            <> "yield 2++"
        )
        "3"
    , programCase "one function accepts an inhabited total map of templates"
        ( "increment := (\"%Int++\"; \"increment %Int\")"
            <> " % ({value?:Int} -> Int) do yield value+1\n"
            <> "yield (2++; increment 2)"
        )
        "(3; 3)"
    , programFailureCase
        "% rejects an opening grouping character in a syntax template"
        "yield (\"call (%Int)\" % (Int -> Int))"
        (SourceEvaluationFailure (InvalidSyntaxTemplateCharacter '('))
    , programFailureCase
        "% rejects a closing grouping character in a syntax template"
        "yield (\"call %Int)\" % (Int -> Int))"
        (SourceEvaluationFailure (InvalidSyntaxTemplateCharacter ')'))
    , programFailureCase
        "one forbidden member rejects a complete template map"
        "yield ((\"step %Int\"; \"call (%Int)\") % (Int -> Int))"
        (SourceEvaluationFailure (InvalidSyntaxTemplateCharacter '('))
    , programFailureCase "% rejects a non-string map member"
        "yield ((\"step %Int\"; 1) % (Int -> Int))"
        (SourceEvaluationFailure InvalidSyntaxTemplateOperand)
    , programFailureCase "% rejects an empty total map"
        "yield (() % (Int -> Int))"
        (SourceEvaluationFailure InvalidSyntaxTemplateOperand)
    , programCase "syntax annotation canonicalizes as an explicit function"
        "yield (\"step %Int next\" % (Int -> Int))" "(Int -> Int)"
    , programCase "ordinary spelling"
        (ordinaryDeclaration <> "yield step (value:2)") "3"
    , programCase "syntax function subfederation"
        (declaration <> "yield step of ({value?:Nat} -> Int)") "true"
    , programCase "identical syntax attachments are subfederations"
        ( "yield ((\"step %Int mark\" % (Int -> Int))"
            <> " of (\"step %Int mark\" % (Int -> Int)))"
        )
        "true"
    , programCase "distinct syntax attachments are not subfederations"
        ( "yield ((\"step %Int left\" % (Int -> Int))"
            <> " of (\"step %Int right\" % (Int -> Int)))"
        )
        "false"
    , programFailureCase "specification preserves syntax attachment identity"
        ( "yield ((\"step %Int left\" % (Int -> Int))"
            <> " ~> (\"step %Int right\" % (Int -> Int)))"
        )
        (SourceEvaluationFailure
          (FunctionEvaluationFailed FunctionSignatureVarianceViolation))
    , programCase "ordinary specified function remains callable"
        (ordinaryDeclaration
          <> "f := (step ~> ({value?:Nat} -> Int))\nyield f 2")
        "3"
    , programFailureCase "syntax pattern checks captures"
        (declaration <> "yield step (-1) next")
        (SourceEvaluationFailure
          (FunctionEvaluationFailed NoApplicableFunctionAlternative))
    , programFailureCase "%Int syntax holes reject Infinity"
        ( "finite := \"finite %Int\" % ({value?:Int} -> Int)"
            <> " do yield value\n"
            <> "yield finite Infinity"
        )
        (SourceEvaluationFailure
          (FunctionEvaluationFailed NoApplicableFunctionAlternative))
    , programCase "%IntLimit syntax holes accept Infinity"
        ( "limit := \"limit %IntLimit\" % ({value?:IntLimit} -> IntLimit)"
            <> " do yield value\n"
            <> "yield limit Infinity"
        )
        "Infinity"
    , programFailureCase "syntax captures must also inhabit the function domain"
        ( "step := \"step %Int next\" % ({value?:Nat} -> Int)"
            <> " do yield value+1\n"
            <> "yield step (-1) next"
        )
        (SourceEvaluationFailure
          (FunctionEvaluationFailed NoApplicableFunctionAlternative))
    , programCase "declared syntax functions always permit ordinary calls"
        (declaration <> "yield step 2")
        "3"
    , programFailureCase "duplicate syntax declaration"
        (declaration <> declaration <> "yield this")
        (SourceEvaluationFailure (IdentifierStringOverlap "step"))
    , programFailureCase "ambiguous syntax alternatives"
        ( "step := ((\"step %Int next\" % (Int -> Int) !~\"datra.abs\")"
            <> " | (\"step %Int next\" % (Int -> Int) do yield 2))\n"
            <> "yield step"
        )
        (SourceEvaluationFailure EitherAlternativesNotDistinct)
    , programFailureCase
        "distinct literal syntax alternatives still require distinct calls"
        ( "step := ((\"step %Int left\" % ({value?:Int} -> Int) do yield value)"
            <> " | (\"step %Int right\" % ({value?:Int} -> Int) do yield value))\n"
            <> "yield step"
        )
        (SourceEvaluationFailure EitherAlternativesNotDistinct)
    , programFailureCase
        "syntax alternatives require disjoint ordinary domains"
        ( "step := ((\"step %Int left\" % (Int -> Int) !~\"datra.abs\")"
            <> " | (\"step %Int right\" % (Int -> Int) !~\"datra.abs\"))\n"
            <> "yield step"
        )
        (SourceEvaluationFailure EitherAlternativesNotDistinct)
    , programFailureCase "overlapping syntax hole domains are rejected"
        ( "choose := ((\"choose %Nat mark\" % (Nat -> Int) !~\"datra.abs\")"
            <> " | (\"choose %Int mark\" % (Int -> Int) !~\"datra.abs\"))\n"
            <> "yield choose"
        )
        (SourceEvaluationFailure EitherAlternativesNotDistinct)
    ]
  where
    declaration =
      "step := \"step %Nat next\" % ({value?:Nat} -> Int) do yield value+1\n"
    ordinaryDeclaration =
      "step := \"step %Nat next\" % ({value?:Int} -> Int) do yield value+1\n"
