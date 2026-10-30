module Datra.Interpreter.StandardLibraryTests
  ( standardLibraryTests
  ) where

import Datra.TestSupport
import DatraLanguage.Diagnostics.Application
  ( ParseFailure (NeutralSourceParseFailure) )
import DatraTypes
  ( AtlasMapFederationRefutation
      (AtlasMapFederationSpecificationHasNoMatchingMember)
  , FunctionFailure (..)
  , InterpretingError (..)
  , MapLengthFailure (..)
  )
import Test.Tasty (TestTree, testGroup)

standardLibraryTests :: TestTree
standardLibraryTests =
  testGroup "standard library and declarative syntax"
    [ testGroup "canonical value declarations"
        [ programCase "val retains its named member"
            "begin val x := 7; yield this" "x : 7"
        , programCase "def stores the definition marker on its identifier"
            "begin def x := 7; yield this[0][2]" "$def"
        , programCase "val does not imply definition protection"
            "val x := 7\nyield begin x := 8; yield x" "8"
        , programCase "def does not imply canonical presentation"
            "def x := 7\nyield x" "7"
        , programCase "def values participate in specification"
            "def x := 7\nyield x ~> Int" "7 ~> Int"
        , programCase "def values participate in subfederation checks"
            "def x := 7\nyield x of Int" "true"
        , programCase "let composes outside val"
            "begin a := x + 1; let val x := 10; yield a" "11"
        , programCase "the full declaration modifier form is accepted"
            "begin a := x + 1; let def val x := 10; yield a" "11"
        , programCase "val composes with optional names"
            "begin val x? := 7; yield x + 0" "7"
        , programCase "def composes with optional names"
            "begin def x? := 7; yield x + 0" "7"
        , programFailureCase "val rejects an annotated assignment"
            "begin val x : Nat := 7; yield x"
            (SourceParseFailure
              (NeutralSourceParseFailure "operation has no effect inside block"))
        , programFailureCase "val syntax rejects a non-declaration"
            "yield val (1; 2)"
            (SourceEvaluationFailure
              (FunctionEvaluationFailed NoApplicableFunctionAlternative))
        , programFailureCase "modifier order errors share one diagnostic"
            "begin val let x := 7; yield x"
            (SourceParseFailure (NeutralSourceParseFailure
              "invalid declaration modifiers: val let\ncorrect form: let val"))
        , programFailureCase "duplicate modifiers share the same diagnostic"
            "begin val val x := 7; yield x"
            (SourceParseFailure (NeutralSourceParseFailure
              "invalid declaration modifiers: val val\ncorrect form: val"))
        , programFailureCase "def before let reports the canonical correction"
            "begin def let x := 7; yield x"
            (SourceParseFailure (NeutralSourceParseFailure
              "invalid declaration modifiers: def let\ncorrect form: let def"))
        , programFailureCase "val before def reports the canonical correction"
            "begin val def x := 7; yield x"
            (SourceParseFailure (NeutralSourceParseFailure
              "invalid declaration modifiers: val def\ncorrect form: def val"))
        , programFailureCase "late def reports the full canonical correction"
            "begin let val def x := 7; yield x"
            (SourceParseFailure (NeutralSourceParseFailure
              ("invalid declaration modifiers: let val def"
                <> "\ncorrect form: let def val")))
        , programFailureCase "duplicate def uses the unified diagnostic"
            "begin def def x := 7; yield x"
            (SourceParseFailure (NeutralSourceParseFailure
              "invalid declaration modifiers: def def\ncorrect form: def"))
        ]
    , testGroup "private syntax categories"
        [ programFailureCase "AST is no longer implicitly imported"
            "yield AST" (SourceEvaluationFailure (UnknownIdentifier "AST"))
        , programFailureCase "_AST is private to the library"
            "yield _AST" (SourceEvaluationFailure (UnknownIdentifier "_AST"))
        , programFailureCase "Std does not export _AST"
            "yield Std._AST" (SourceEvaluationFailure (UnknownIdentifier "_AST"))
        , programCase "AST can be a user binding"
            "AST := 2\nyield AST" "2"
        , programFailureCase "Expr is private to the library"
            "yield Expr" (SourceEvaluationFailure (UnknownIdentifier "Expr"))
        , programFailureCase "Block is private to the library"
            "yield Block" (SourceEvaluationFailure (UnknownIdentifier "Block"))
        , programFailureCase "Pages is private to the library"
            "yield Pages" (SourceEvaluationFailure (UnknownIdentifier "Pages"))
        , programFailureCase "DependentArgument is private to the library"
            "yield DependentArgument"
            (SourceEvaluationFailure
              (UnknownIdentifier "DependentArgument"))
        , programFailureCase "DependentDeclaration is private to the library"
            "yield DependentDeclaration"
            (SourceEvaluationFailure
              (UnknownIdentifier "DependentDeclaration"))
        , programFailureCase "the former Declaration name is unavailable"
            "yield Declaration"
            (SourceEvaluationFailure (UnknownIdentifier "Declaration"))
        , programFailureCase "_SyntaxTemplate is private to the library"
            "yield _SyntaxTemplate"
            (SourceEvaluationFailure (UnknownIdentifier "_SyntaxTemplate"))
        , programCase "SyntaxTemplate retains its host-map canonical spelling"
            "yield datra.SyntaxTemplate" "datra.SyntaxTemplate"
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
        , programCase "ordinary and scoped calls remain available"
            "yield ('len (1; 2; 3); Std.(len (4; 5)))"
            "(3; 2)"
        , programCase "external syntax adapters permit ordinary calls"
            "yield 'if (false; 4; 5)"
            "5"
        , programCase "recursive let aliases to syntax bodies are discovered"
            ( "answer := choose (false; 1; 2)\n"
                <> "let choose := datra.if_body\n"
                <> "yield answer"
            )
            "2"
        , programCase "direct begin rewrites its result in the block scope"
            ( "yield 'begin ((\n"
                <> "  \"apply %_Expr\" := (_Expr -> _Expr) datra.fun_body\n"
                <> "); apply 7)"
            )
            "7"
        , programCase "optional named values retain their map extent"
            ( "measure := ({value? : Any} -> NatLimit do yield len value)\n"
                <> "yield measure (value : (1; 2; 3))"
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
            [ ("Std.(if false then (1 + \"bad\") else 11)", "11")
            , ("Std.(from (1 + 1) to 5)", "from 2 to 5")
            , ("Std.(range 2 down)", "range 2 down")
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
              <> "yield (inlineFactorial 6 = boundFactorial 6; "
              <> "inlineFactorial 6)")
            "(true; 720)"
        , programCase "finite access lazily unfolds recursive data"
            ("name := fun (\"hi:\", this)\n"
              <> "k := 1\n"
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
              <> "k := 1\n"
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
            [ ("begin a:=5; b:=8; yield this.a", "5")
            , ("begin _private:=3; a:=5; yield public this", "a : 5")
            , ( "yield public (_private:3;a:5) of (a?:Nat)"
              , "true"
              )
            , ( "yield public (_private:3;a:5) ~> (a?:Nat)"
              , "a? : Nat := 5"
              )
            , ("begin _private:=3; a:=5; yield this._private", "3")
            , ("begin a:=5; yield this.a of (a?:Nat)", "true")
            , ("begin a:=5; yield this.a ~> (a?:Nat)", "a? : Nat := 5")
            , ("a:=(b:2;c:3)\nyield a.(b+c)", "5")
            , ( "a:=(b:2;c:3)\n"
                  <> "yield a.(left : b; right : c)"
              , "(left : 2; right : 3)"
              )
            , ("yield 'from (2;5)", "from 2 to 5")
            , ("yield 'from (2;$up)", "from 2 up")
            , ( "body := datra.add\n"
                  <> "f := ({a? : Int; b? : Int} -> Int) body\n"
                  <> "yield f (b:5;6)"
              , "11"
              )
            , ( "f := (x:Int, {a?:Int;b?:Int} -> Int do yield x+a+b)\n"
                  <> "yield f (x:3,b:5,6)"
              , "14"
              )
            ]
        ]
    , testGroup "lookup operator"
        [ programCase "returns a raw key-value row for a bound key"
            "begin x := 5; yield ((~\"x\")[0].key; (~\"x\")[0].value)"
            "($x; 5)"
        , programCase "returns an empty map for an absent key"
            "begin x := 5; yield ~\"missing\"" "()"
        , programCase "evaluates an identifier operand as a string"
            "begin key := \"x\"; x := 5; yield (~key)[0].value" "5"
        , programCase "resolves a quoted binding"
            ("begin \"value with spaces\" := 5; "
              <> "yield (~\"value with spaces\")[0].value")
            "5"
        , programCase "resolves a private binding"
            "begin _x := 5; yield (~\"_x\")[0].value" "5"
        , programCase "folds a total template to one concrete key"
            "begin arg4 := 8; yield (~\"arg%(2 + 2)\")[0].value" "8"
        , programCase "filters missing members from an infinite family"
            ("begin arg4 := 8; arg0 := 3; "
              <> "yield ((~\"arg%Nat\")[0].key; (~\"arg%Nat\")[1].key)")
            "($arg0; $arg4)"
        , programCase "retains the lexical scope where lookup is evaluated"
            ("rows := begin hidden := 7; yield ~\"hidden\"\n"
              <> "hidden := 9\nyield rows[0].value + 1")
            "8"
        , programFailureCase "defers binding failure until a row is selected"
            "begin broken := missing; rows := ~\"broken\"; yield rows[0].value"
            (SourceEvaluationFailure (UnknownIdentifier "missing"))
        , programFailureCase "rejects a capture without a generic map view"
            "yield ~\"value%Any\""
            (SourceEvaluationFailure
              (LookupCaptureHasNoGenericMapView 0 "Any"))
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
                <> "yield split(10; 20; 30)"
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
            "yield () !? Just it" "nothing"
        , programCase "nonempty list split preserves head and tail"
            "yield (1; 2; 3) !? Just it" "Just : (1; >< (2; 3))"
        , programCase "Maybe sequencing binds tagged it"
            "yield (1; 2; 3) !? it[1]"
            "Just : (1; >< (2; 3))"
        , programCase "Maybe sequencing leaves the absent branch lazy"
            "yield () !? missing" "nothing"
        , programCase "list sequencing applies a function to a nonempty split"
            ( "head := ({candidate? : Int; remaining? : List Int} -> Int "
                <> "do yield candidate)\n"
                <> "yield (1; 2; 3) !? head it"
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
                <> "do yield values !? head it)\n"
                <> "yield apply (4; 5)"
            )
            "Just : 4"
        , programCase "list sequencing result supports specification"
            ( "head := ({candidate? : Int; remaining? : List Int} -> Int "
                <> "do yield candidate)\n"
                <> "yield ((1; 2) !? head it) ~> Int?"
            )
            "(Just : 1) ~> Maybe Int"
        , programCase "list sequencing result supports subfederation"
            ( "head := ({candidate? : Int; remaining? : List Int} -> Int "
                <> "do yield candidate)\n"
                <> "yield ((1; 2) !? head it) of Int?"
            )
            "true"
        , programCase "optional named matcher accepts split positional values"
            ( "head := ({candidate? : Int; remaining? : List Int} -> Int "
                <> "do yield candidate)\n"
                <> "yield (1; 2; 3) !? head it"
            )
            "Just : 1"
        , programFailureCase "required named matcher rejects split positional values"
            ( "head := ({candidate : Int; remaining : List Int} -> Int "
                <> "do yield candidate)\n"
                <> "yield (1; 2; 3) !? head it"
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
            (SourceParseFailure (NeutralSourceParseFailure
              "OverlappingDependentDeclarations \"a\" \"a\""))
        , programFailureCase "specified function validates narrowed input"
            ("f := ({x?:Int} -> Int do yield x+1)\n"
              <> "g := (f ~> ({x?:Nat} -> Int))\nyield g (-1)")
            (SourceEvaluationFailure
              (FunctionEvaluationFailed NoApplicableFunctionAlternative))
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
            , "datra.Expr of Any"
            , "datra.DependentArgument of Any"
            , "datra.DependentDeclaration of Any"
            , "datra.Block of Any"
            , "datra.FunctionBody of Any"
            , "(Nat; datra.Expr) of Any"
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
            , "not (datra.Block of datra.Expr)"
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
                <> "yield values(1; 2; 3) of {List Int,}"
            )
            "true"
        , programCase "Args reorders named and positional slots"
            ( "values := ({Args Int,} -> Any do yield it)\n"
                <> "yield values(arg1 : 3, 0) of {List Int,}"
            )
            "true"
        , programCase "unmatched Args names fall back positionally"
            ( "values := ({Args Int,} -> Any do yield it)\n"
                <> "yield values(my_arg : 3, 0)"
            )
            "(arg0 : 3; arg1 : 0)"
        , programCase "source-defined Args supports string-template functions"
            ( "MyArgs := &T? -> Any do\n"
                <> "  slots := (^_i :: Nat) -> Any do yield \"arg%(_i)\"? : T\n"
                <> "yield ((^n? :: Nat) -> Any do yield slots[0..n])\n"
                <> "display := {MyArgs Int,} -> Str do yield \"%(it)\"\n"
                <> "yield (((arg2 : 10, 4) of {MyArgs Int,}) = false; "
                <> "display(); display(1); display(1; 2; 3); "
                <> "display(arg1 : 10, 4))"
            )
            ("(true; \"()\"; \"arg0 : 1\"; "
              <> "\"(arg0 : 1; arg1 : 2; arg2 : 3)\"; "
              <> "\"(arg0 : 4; arg1 : 10)\")")
        , programCase "only argumentative maps erase unmatched identifiers"
            ( "yield (not ((arg0 : 1; arg1 : 2) of List Int); "
                <> "((arg0 : 1; arg1 : 2) of {List Int,}))"
            )
            "(true; true)"
        , programCase "Args convert to lists through argumentative map matching"
            ( "ArgsIntMap := {Args Int,}\n"
                <> "ListInt := List Int\n"
                <> "display := ArgsIntMap -> \"%ListInt\" do\n"
                <> "  toList := ArgsIntMap -> {ListInt,} do yield it\n"
                <> "  yield \"%(toList it)\"\n"
                <> "yield (display() = \"()\"; display(1) = \"1\";\n"
                <> "  display(1; 2; 3) = \"(1; 2; 3)\";\n"
                <> "  display(arg1 : 10, 4) = \"(4; 10)\";\n"
                <> "  ((arg2 : 10, 4) of ArgsIntMap) = false)"
            )
            "(true; true; true; true; true)"
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
        , programCase "optional binder accepts named dependent arguments"
            ( "Pair := (^T? :: Any) -> Any do yield (value? : T)\n"
                <> "yield {T : Nat; value : 5} of Pair"
            )
            "true"
        , programCase "dependent sum validates the selected fibre"
            ( "Pair := (^T? :: Any) -> Any do yield (value? : T)\n"
                <> "yield not ({T : Nat; value : \"bad\"} of Pair)"
            )
            "true"
        , programCase "dependent sum composes with forward specification"
            ( "Pair := (^T? :: Any) -> Any do yield (value? : T)\n"
                <> "yield ({T : Nat; value : 5} ~> Pair) of Pair"
            )
            "true"
        , programCase "dependent sum composes with reverse specification"
            ( "Pair := (^T? :: Any) -> Any do yield (value? : T)\n"
                <> "yield (Pair <~ {T : Nat; value : 5}) of Pair"
            )
            "true"
        , programCase "private optional binder is valid in an ordered map"
            ( "Pair := (^_T :: Any) -> Any do yield (value? : _T)\n"
                <> "yield (_T : Nat; value : 5) of Pair"
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
        , programCase "unit is neutral in sequences"
            "yield ((23; ()) = 23; ((); 23) = 23)"
            "(true; true)"
        , programCase "complement representation inhabits integer types"
            ( "yield ((22; Just : $Complement) of Int; "
                <> "(Infinity; Just : $Complement) of IntLimit)"
            )
            "(true; true)"
        ]
    , testGroup "open and closed ranges"
        [ programCase "from resolves its selected positional captures"
            "yield from 0 up" "from 0 up"
        , programCase "from upward excludes positive infinity"
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
            "yield 'from (Infinity; $down)"
            (SourceEvaluationFailure
              (FunctionEvaluationFailed NoApplicableFunctionAlternative))
        , programFailureCase "from rejects a negative-infinite origin"
            "yield 'from (-Infinity; $up)"
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
        ( "\"the answer\" := (42 -> Nat) do yield it\n"
            <> "yield the answer"
        )
        "42"
    , programCase "value holes evaluate expressions before selection"
        ( "\"double %Nat\" := (Nat -> Nat) do yield it * 2\n"
            <> "yield double (2 + 2)"
        )
        "8"
    , programCase "dependent captures call ordinary functions through subfederation"
        ( "\"successor %Nat next\" := ({value?:Int} -> Int)"
            <> " do yield value + 1\n"
            <> "yield successor 4 next"
        )
        "5"
    , programCase "dependent declaration descriptors expose their functions"
        ( "\"successor %Nat next\" := ({value?:Int} -> Int)"
            <> " do yield value + 1\n"
            <> "yield ((~\"successor Nat next\")[0].value)"
            <> " of ({value?:Nat} -> Int)"
        )
        "true"
    , programCase "syntax pattern call"
        (declaration <> "yield step (1+1) next") "3"
    , programCase "an application spine is one syntax boundary"
        ( "\"prefix %_Expr\" := ({value?:Any} -> Any)"
            <> " do yield value\n"
            <> "\"%_Expr otherwise %_Expr\" := "
            <> "({left?:Any; right?:Any} -> Any) do yield right\n"
            <> "yield prefix 1 otherwise 2"
        )
        "2"
    , programCase "a direct declaration uses its template's surface name"
        ( "\"def %Nat next\" := ({value?:Nat} -> Int)"
            <> " do yield value+1\n"
            <> "yield def 2 next"
        )
        "3"
    , programCase "the complete literal prefix is matched before its first hole"
        ( "\"my name is %Nat\" := ({value?:Nat} -> Int)"
            <> " do yield value+1\n"
            <> "yield my name is 2"
        )
        "3"
    , programCase "a template may begin with a postfix operand hole"
        ( "\"%Int++\" := ({value?:Int} -> Int)"
            <> " do yield value+1\n"
            <> "yield 2++"
        )
        "3"
    , programCase
        "a direct declaration accepts a complete value-of literal"
        ( "\"call ~name\" := (() -> Int) do yield 7\n"
            <> "yield call ~name"
        )
        "7"
    , programCase "a direct declaration accepts a comma-boundary template"
        ( "\"take,%Int\" := ({value?:Int} -> Int)"
            <> " do yield value+1\n"
            <> "yield (take,2)"
        )
        "3"
    , programFailureCase "syntax pattern checks captures"
        (declaration <> "yield step (-1) next")
        (SourceEvaluationFailure
          (FunctionEvaluationFailed NoApplicableFunctionAlternative))
    , programFailureCase "%Int syntax holes reject Infinity"
        ( "\"finite %Int\" := ({value?:Int} -> Int)"
            <> " do yield value\n"
            <> "yield finite Infinity"
        )
        (SourceEvaluationFailure
          (FunctionEvaluationFailed NoApplicableFunctionAlternative))
    , programCase "%IntLimit syntax holes accept Infinity"
        ( "\"limit %IntLimit\" := ({value?:IntLimit} -> IntLimit)"
            <> " do yield value\n"
            <> "yield limit Infinity"
        )
        "Infinity"
    , programFailureCase "syntax captures must also inhabit the function domain"
        ( "\"step %Int next\" := ({value?:Nat} -> Int)"
            <> " do yield value+1\n"
            <> "yield step (-1) next"
        )
        (SourceEvaluationFailure
          (FunctionEvaluationFailed NoApplicableFunctionAlternative))
    , programFailureCase "duplicate syntax declaration"
        (declaration <> declaration <> "yield this")
        (SourceParseFailure (NeutralSourceParseFailure
          "OverlappingDependentDeclarations \"step %Nat next\" \"step %Nat next\""))
    ]
  where
    declaration =
      "\"step %Nat next\" := ({value?:Nat} -> Int) do yield value+1\n"
