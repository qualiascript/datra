module Datra.Interpreter.FunctionTests (functionTests) where

import Datra.TestSupport
import DatraTypes
  ( AtlasMapFederationRefutation
      (AtlasMapFederationSpecificationHasNoMatchingMember)
  , ExternalFailure (..)
  , FunctionFailure (..)
  , InterpretingError (..)
  )
import Test.Tasty (TestTree, testGroup)

functionTests :: TestTree
functionTests =
  testGroup "functions"
    [ argumentSchemaMatrixTests
    , testGroup "application"
        [ programCase "it observes the complete given map"
            (unlines
              [ "sum := (Nat, Nat -> Nat do yield it[0] + it[1])"
              , "assert sum (1, 2) = 3"
              ])
            "()"
        , programCase "sequenced Int annotations remain individual slots"
            (unlines
              [ "sum := ((Int; Int) -> Int do yield it[0] + it[1])"
              , "assert sum ((2 ~> Int); (5 ~> Int)) = 7"
              ])
            "()"
        , programCase "it observes defaults after skipped-argument overloading"
            (unlines
              [ "my_pow := ({base? : Nat := 2; exponent? : Nat} -> Nat do yield it.base[1] ^ it.exponent[1])"
              , "assert my_pow (*, 3) = 8"
              ])
            "()"
        , programCase "explicit unordered parameters"
            "f := ({a?:Int;b?:Int} -> Int do yield a+b)\nyield f (b:5;6)"
            "11"
        , programFailureCase "standalone do requires a function type"
            "f := (do yield 3)\nyield f ()"
            (SourceEvaluationFailure
              (FunctionEvaluationFailed ExpectedFunctionType))
        , programFailureCase "generic identifiers cannot repeat in one domain"
            (unlines
              [ "f := ({a? : &T; b? : ^T?} -> T do yield a)"
              , "yield f"
              ])
            (SourceEvaluationFailure (DuplicateGenericIdentifier "T"))
        , programFailureCase "generic bounds cannot refer to later binders"
            (unlines
              [ "f := ({a? : &T :: U; b? : &U} -> Any do yield a)"
              , "yield f"
              ])
            (SourceEvaluationFailure
              (ForwardGenericBoundReference "T" "U"))
        , programFailureCase "generic bounds cannot refer to themselves"
            (unlines
              [ "f := ({a? : &T :: T} -> Any do yield a)"
              , "yield f"
              ])
            (SourceEvaluationFailure
              (ForwardGenericBoundReference "T" "T"))
        , programCase "generic bounds may refer to earlier binders"
            (unlines
              [ "f := ({a? : &T; b? : &U :: T} -> Any do yield a)"
              , "yield ()"
              ])
            "()"
        , programCase "generic function types compile their prepared prefix"
            ( "assert ((x : T; y : ^T) -> Any) of "
                <> "((T : Any; x : Any; y : Any) -> Any)"
            )
            "()"
        , programFailureCase "generic names cannot overlap domain names"
            (unlines
              [ "f := ({T? : Any; marker? : &T} -> Any do yield marker)"
              , "yield f"
              ])
            (SourceEvaluationFailure (GenericIdentifierOverlap "T"))
        , programFailureCase "optional generic names overlap required codomain names"
            (unlines
              [ "f := ({marker? : &T?} -> (T : Any) do yield marker)"
              , "yield f"
              ])
            (SourceEvaluationFailure (GenericIdentifierOverlap "T"))
        , programFailureCase "generic collisions inspect specification targets"
            (unlines
              [ "f := ({marker? : &T; ((value : Nat := 1) ~> (T : Nat))} -> Any do yield marker)"
              , "yield f"
              ])
            (SourceEvaluationFailure (GenericIdentifierOverlap "T"))
        , programFailureCase
            "generic collisions inspect reverse specification targets"
            (unlines
              [ "f := ({marker? : &T; ((T : Nat) <~ (value : Nat := 1))} -> Any do yield marker)"
              , "yield f"
              ])
            (SourceEvaluationFailure (GenericIdentifierOverlap "T"))
        , programCase
            "subfederation operands do not introduce function-scope names"
            (unlines
              [ "f := ({marker? : &T; ((T : Nat) of (value : Nat))} -> Any do yield marker)"
              , "yield ()"
              ])
            "()"
        , programFailureCase "generic names test every dependent-name fibre"
            (unlines
              [ "f := ({marker? : &n5; \"n%(it)\"? : Nat} -> Any do yield marker)"
              , "yield f"
              ])
            (SourceEvaluationFailure (GenericIdentifierOverlap "n5"))
        , programCase
            "nested function names are outside an outer generic collision scope"
            (unlines
              [ "f := ({marker? : &T; inner? : ({T? : Any} -> Any)} -> Any do yield marker)"
              , "yield ()"
              ])
            "()"
        , programCase "required public product accepts a named witness"
            (unlines
              [ "identity := ({marker? : &T; value? : T} -> T do yield value)"
              , "yield identity {T := Nat; marker := 3; value := 5}"
              ])
            "5"
        , programFailureCase "required public product rejects a positional witness"
            (unlines
              [ "identity := ({marker? : &T; value? : T} -> T do yield value)"
              , "yield identity (Nat; 3; 5)"
              ])
            (SourceEvaluationFailure
              (FunctionEvaluationFailed NoApplicableFunctionAlternative))
        , programCase "optional-name public product accepts a positional witness"
            (unlines
              [ "identity := ({marker? : &T?; value? : T} -> T do yield value)"
              , "yield identity (Nat; 3; 5)"
              ])
            "5"
        , programCase "optional-name public product accepts a named witness"
            (unlines
              [ "identity := ({marker? : &T?; value? : T} -> T do yield value)"
              , "yield identity {T := Nat; marker := 3; value := 5}"
              ])
            "5"
        , programCase "private product is inferred from consistent arguments"
            (unlines
              [ "genericPrivate := ({marker? : &_T; value? : _T} -> _T do yield value)"
              , "yield genericPrivate {marker := 3; value := 5}"
              ])
            "5"
        , programCase "private product is inserted into the body prefix"
            (unlines
              [ "genericPrefix := ({marker? : &_T; value? : _T} -> Any do yield it[0])"
              , "yield genericPrefix {marker := 3; value := 5}"
              ])
            "_T : 3 | 5"
        , programCase "unrelated arguments do not widen private inference"
            (unlines
              [ "genericEvidence := ({marker? : &_T; unrelated? : Any} -> Any do yield it[0])"
              , "yield genericEvidence {marker := 3; unrelated := 5}"
              ])
            "_T : 3"
        , programCase "private product remains positional in an ordered map"
            (unlines
              [ "orderedGeneric := ((marker : &_T; value : _T) -> _T do yield value)"
              , "yield orderedGeneric (Nat; marker := 3; value := 5)"
              ])
            "5"
        , programCase "required public sum accepts a named witness"
            (unlines
              [ "identity := ({marker? : ^T; value? : T} -> T do yield value)"
              , "yield identity {T := Nat; marker := 3; value := 5}"
              ])
            "5"
        , programFailureCase "required public sum rejects a positional witness"
            (unlines
              [ "identity := ({marker? : ^T; value? : T} -> T do yield value)"
              , "yield identity (Nat; 3; 5)"
              ])
            (SourceEvaluationFailure
              (FunctionEvaluationFailed NoApplicableFunctionAlternative))
        , programCase "optional-name public sum accepts a positional witness"
            (unlines
              [ "identity := ({marker? : ^T?; value? : T} -> T do yield value)"
              , "yield identity (Nat; 3; 5)"
              ])
            "5"
        , programCase "optional-name public sum accepts a named witness"
            (unlines
              [ "identity := ({marker? : ^T?; value? : T} -> T do yield value)"
              , "yield identity {T := Nat; marker := 3; value := 5}"
              ])
            "5"
        , programCase "private sum is inferred from consistent arguments"
            (unlines
              [ "genericPrivate := ({marker? : ^_T; value? : _T} -> _T do yield value)"
              , "yield genericPrivate {marker := 3; value := 5}"
              ])
            "5"
        , programCase "private sum is inserted into the body prefix"
            (unlines
              [ "genericPrefix := ({marker? : ^_T; value? : _T} -> Any do yield it[0])"
              , "yield genericPrefix {marker := 3; value := 5}"
              ])
            "_T : 3 | 5"
        , programCase "private sum remains positional in an ordered map"
            (unlines
              [ "orderedGeneric := ((marker : ^_T; value : _T) -> _T do yield value)"
              , "yield orderedGeneric (Nat; marker := 3; value := 5)"
              ])
            "5"
        , programCase "mixed generic prefixes respect telescope order"
            (unlines
              [ "mixed := ((a : ^S; b : &T; c : ^U; value : U) -> U do yield value)"
              , "yield mixed (Nat; Nat; Nat; a := 1; b := 3; c := 5; value := 5)"
              ])
            "5"
        , programCase "variadic Args contributes private generic evidence"
            (unlines
              [ "genericArgs := ({Args (&_T :: Nat),} -> Any do yield it[0])"
              , "yield genericArgs (3, 5)"
              ])
            "_T : 3 | 5"
        , programCase "optional name accepts an unnamed value"
            "f := ({x?:Int} -> Int do yield x)\nyield f 2"
            "2"
        , programCase "optional name accepts a named value"
            "f := ({x?:Int} -> Int do yield x)\nyield f (x:2)"
            "2"
        , programCase "optional value retains a required name"
            "f := ({x:Maybe Int} -> Maybe Int do yield x)\nyield f (x:nothing)"
            "nothing"
        , programCase "higher-order parameter"
            (unlines
              [ "apply := (((Int -> Int), Int) -> Int do yield it[0] it[1])"
              , "increment := ({n?:Int} -> Int do yield n+1)"
              , "yield apply (increment,4)"
              ])
            "5"
        , programCase "Any accepts a canonical argument value"
            (unlines
              [ "identity := ({value?:Any} -> Any do yield value)"
              , "yield identity 5"
              ])
            "5"
        , programCase "Any accepts a canonical function argument value"
            (unlines
              [ "identity := ({value?:Any} -> Any do yield value)"
              , "yield (identity (Nat -> Nat)) of (Nat -> Nat)"
              ])
            "true"
        , programCase "function sum selects the numerical alternative"
            (unlines
              [ "f := (({x?:Nat} -> Int do yield x+1) | ({x?:Str} -> Str do yield x))"
              , "yield f 4"
              ])
            "5"
        , programCase "function sum selects the string alternative"
            (unlines
              [ "f := (({x?:Nat} -> Int do yield x+1) | ({x?:Str} -> Str do yield x))"
              , "yield f \"ok\""
              ])
            "$ok"
        ]
    , testGroup "identifier-preserving input maps"
        [ programCase "optional names survive positional calls"
            (unlines
              [ "f := {abc? : Nat; xyz? : Nat} -> Bool do"
              , "  yield it.abc[0] = $abc and it.abc[1] = abc and it.xyz[0] = $xyz and it.xyz[1] = xyz"
              , "assert f(3, 4)"
              , "assert f(xyz := 4, abc := 3)"
              ]) "()"
        , programCase "mixed slots preserve their written positions"
            (unlines
              [ "f := (abc? : Nat; Nat; xyz? : Nat) -> Bool do"
              , "  yield it[0][0] = $abc and it[0][1] = 3 and it[1] = 4 and it[2][0] = $xyz and it[2][1] = 5"
              , "assert f(3; 4; 5)"
              ]) "()"
        , programCase "named access satisfies a declared output type"
            "f := ({abc? : Nat} -> Nat do yield it.abc[1] + 1)\nyield f 6"
            "7"
        , programCase "computed input schemas preserve names without special functions"
            (unlines
              [ "Slots := (() -> Any do yield (abc? : Nat; Nat))"
              , "f := {Slots (),} -> Bool do"
              , "  yield it.abc[0] = $abc and it.abc[1] = 3 and it[1] = 4"
              , "assert f(3; 4)"
              ]) "()"
        , programCase "aliased schemas preserve names"
            (unlines
              [ "Schema := (abc? : Nat; Nat)"
              , "f := Schema -> Bool do"
              , "  yield it.abc[1] = 3 and it[1] = 4"
              , "assert f(3; 4)"
              ]) "()"
        , programCase "projected schemas retain names inside the body"
            (unlines
              [ "Slots := (for T? of Any) -> Any do"
              , "  slots := with i in Nat do \"field%(i)\"? : T"
              , "yield with n in Nat do slots[0..n]"
              , "f := {Slots Nat,} -> Any do yield it"
              , "assert (f(3; 4))[0][1] = 3"
              , "assert (f(3; 4)).field1[1] = 4"
              ]) "()"
        , programCase "projected input maps retain names after returning"
            (unlines
              [ "f := {Args Int,} -> Any do yield it"
              , "assert (f(3; 4)).arg0[0] = $arg0"
              , "assert (f(arg1 := 4, 3)).arg1[1] = 4"
              ]) "()"
        , programCase "empty and singleton unnamed inputs keep their shape"
            (unlines
              [ "emptyInput := (() -> Any do yield it)"
              , "single := (Nat -> Nat do yield it)"
              , "assert emptyInput() = ()"
              , "assert single 8 = 8"
              ]) "()"
        , programCase "mixed parameters can be returned positionally"
            "f := ((abc? : Nat; Nat) -> (Nat; Nat) do yield (abc; it[1]))\nyield f(3; 4)"
            "(3; 4)"
        , programCase "named input access works through local bindings"
            "f := ({abc? : Nat} -> Nat do\n  args := it\nyield args.abc[1])\nyield f 7"
            "7"
        , programCase "unmatched identifiers match argument slots positionally"
            "yield (my_val : 3) of {value : Int}"
            "true"
        , programCase "matching identifiers reserve their candidate"
            "yield (my_val : 3) of {value : Int, my_val : Str}"
            "false"
        , programCase "reserved identifiers do not fill other required slots"
            "yield (my_val : 3) of {value : Str; my_val : Int}"
            "false"
        , programCase "identifier maps do not inhabit unnamed recursive lists"
            "yield (arg0 : 1; arg1 : 2; arg2 : 3) of List Int"
            "false"
        ]
    , testGroup "externals"
        [ programCase "short external descriptor"
            "f := !~\"datra.add\"\nyield f (b:5;6)"
            "11"
        , programCase "structured external descriptor"
            ("f := !~(backend:\"haskell\";symbol:\"datra.add\")\n"
              <> "yield f (b:5;6)")
            "11"
        , expressionFailureCase "unknown external backend"
            "!~(backend:\"missing\";symbol:\"datra.add\")"
            (SourceEvaluationFailure
              (ExternalEvaluationFailed
                (UnsupportedExternalBackend "missing")))
        , expressionFailureCase "unknown external symbol"
            "!~(backend:\"haskell\";symbol:\"missing\")"
            (SourceEvaluationFailure
              (ExternalEvaluationFailed (UnknownExternalSymbol "missing")))
        , expressionFailureCase "duplicate external descriptor field"
            "!~(backend:\"haskell\";backend:\"haskell\";symbol:\"datra.add\")"
            (SourceEvaluationFailure
              (ExternalEvaluationFailed DuplicateExternalDescriptorField))
        , expressionFailureCase "unknown external descriptor field"
            "!~(backend:\"haskell\";extra:\"value\";symbol:\"datra.add\")"
            (SourceEvaluationFailure
              (ExternalEvaluationFailed
                (UnknownExternalDescriptorFields ["extra"])))
        , expressionFailureCase "missing external descriptor field"
            "!~(backend:\"haskell\")"
            (SourceEvaluationFailure
              (ExternalEvaluationFailed
                (MissingExternalDescriptorField "symbol")))
        , expressionFailureCase "external descriptor requires string fields"
            "!~(1; 2)"
            (SourceEvaluationFailure
              (ExternalEvaluationFailed ExternalDescriptorRequiresStringMap))
        ]
    , testGroup "typing"
        [ expressionCase "contravariant input and covariant output"
            "(Int -> Nat) of (Nat -> Int)"
            "true"
        , expressionCase "invalid function variance"
            "(Nat -> Int) of (Int -> Nat)"
            "false"
        , programCase "required names accept matching named input"
            "f := ({x:Int} -> Int do yield x+1)\nyield f (x:2)"
            "3"
        , programFailureCase "required names reject positional input"
            "f := ({x:Int} -> Int do yield x+1)\nyield f 2"
            (SourceEvaluationFailure
              (FunctionEvaluationFailed NoApplicableFunctionAlternative))
        , programCase "written order resolves otherwise ambiguous arguments"
            "f := ({x?:Int;y?:Int} -> Int do yield x+y)\nyield f {2;3}"
            "5"
        , programCase "ordinary-map private parameter accepts its written name"
            ( "f := ((_x:Int) -> Int do yield ~\"_x\"+1)\n"
                <> "yield f (_x:2)"
            )
            "3"
        , programCase "private parameter remains in the positional argument aggregate"
            ( "f := ((_x:Nat) -> Nat do yield it[0][1])\n"
                <> "yield f (_x:2)"
            )
            "2"
        , programFailureCase
            "private parameter is not automatically reduced in the body"
            "f := ((_x:Int) -> Int do yield _x+1)\nyield f (_x:2)"
            (SourceEvaluationFailure (UnknownIdentifier "_x"))
        , programFailureCase
            "singleton argument-map private parameter rejects its written name"
            ( "f := ({_x:Int} -> Int do yield ~\"_x\"+1)\n"
                <> "yield f (_x:2)"
            )
            (SourceEvaluationFailure
              (FunctionEvaluationFailed NoApplicableFunctionAlternative))
        , programFailureCase "private required names reject positional input"
            ( "sum := ({_x:Int;_y:Int} -> Int do "
                <> "yield ~\"_x\"+~\"_y\")\nyield sum (1,2)"
            )
            (SourceEvaluationFailure
              (FunctionEvaluationFailed NoApplicableFunctionAlternative))
        , programFailureCase "private parameter slots reject named input"
            ( "sum := ({_x:Int;_y:Int} -> Int do "
                <> "yield ~\"_x\"+~\"_y\")\nyield sum (_x:1,_y:2)"
            )
            (SourceEvaluationFailure
              (FunctionEvaluationFailed NoApplicableFunctionAlternative))
        , programFailureCase "ambiguous reorder is reported structurally"
            ( "f := ({a?:Int;b?:Str;c?:Str} -> Int do yield a)\n"
                <> "yield f ($x,$y,5)"
            )
            (SourceEvaluationFailure
              (FunctionEvaluationFailed
                AmbiguousFunctionArgumentBindings))
        , programFailureCase "declared result rejects the returned value"
            "f := ({a?:Int} -> Str do yield a+1)\nyield f 5"
            (SourceEvaluationFailure
              (AtlasMapFederationOperationRefuted
                AtlasMapFederationSpecificationHasNoMatchingMember))
        , programFailureCase "required named Maybe parameter rejects an unnamed value"
            "f := ({x:Maybe Int} -> Maybe Int do yield x)\nyield f nothing"
            (SourceEvaluationFailure
              (FunctionEvaluationFailed NoApplicableFunctionAlternative))
        , programCase "function type annotates an identifier"
            "assert (callback : (Nat -> Nat)) of (callback : (Nat -> Nat))"
            "()"
        , programCase "block binding accepts a canonical function annotation"
            "callback : (Nat -> Nat)\nyield callback of (Nat -> Nat)"
            "true"
        , expressionFailureCase "noncanonical standard type cannot annotate an identifier"
            "node : (!~\"datra.AST\")"
            (SourceEvaluationFailure NonCanonicalIdentifierTypeAnnotation)
        , programCase "function parameter annotation is canonical"
            "f := ({callback?:(Nat -> Nat)} -> Nat do yield 0)\nyield f ({n?:Nat} -> Nat do yield n)"
            "0"
        ]
    , testGroup "dependent products"
        [ programCase "argument maps evaluate homogeneous products"
            "yield ({for i? of from 0 to 2; i})[1]"
            "(0; 1; 2)"
        , programCase "optional binder accepts positional witnesses"
            ( "identity := ({for T? of Any; value? : T} -> T do yield value)\n"
                <> "yield identity (Nat; 5)"
            )
            "5"
        , programCase "optional binder accepts named assignment witnesses"
            ( "identity := ({for T? of Any; value? : T} -> T do yield value)\n"
                <> "yield identity {T := Nat; value := 5}"
            )
            "5"
        , programCase "required binder accepts only its named assignment form"
            ( "identity := ({for T of Any; value? : T} -> T do yield value)\n"
                <> "yield identity {T := Nat; value := 5}"
            )
            "5"
        , programFailureCase "required binder rejects a positional witness"
            ( "identity := ({for T of Any; value? : T} -> T do yield value)\n"
                <> "yield identity (Nat; 5)"
            )
            (SourceEvaluationFailure
              (FunctionEvaluationFailed NoApplicableFunctionAlternative))
        , programFailureCase "dependent value must inhabit its selected type"
            ( "identity := ({for T? of Any; value? : T} -> T do yield value)\n"
                <> "yield identity (Nat; \"bad\")"
            )
            (SourceEvaluationFailure
              (FunctionEvaluationFailed NoApplicableFunctionAlternative))
        , programCase "dependent binders scope sequentially"
            ( "identity := ({for T? of Any; for U? of T; value? : U} -> U do yield value)\n"
                <> "yield identity (Any; Nat; 5)"
            )
            "5"
        , programCase "dependent product composes with of"
            ( "identity := ({for T? of Any; value? : T} -> T do yield value)\n"
                <> "yield identity of ({for T? of Any; value? : T} -> T)"
            )
            "true"
        , programCase "dependent product composes with specification"
            ( "identity := ({for T? of Any; value? : T} -> T do yield value)\n"
                <> "yield (identity ~> ({for T? of Any; value? : T} -> T)) (Nat; 5)"
            )
            "5"
        , programFailureCase "ordinary parameters do not bind later annotations"
            ( "bad := ({T? : Any; value? : T} -> Any do yield value)\n"
                <> "yield bad"
            )
            (SourceEvaluationFailure (UnknownIdentifier "T"))
        , programFailureCase "dependent products do not bind forwards"
            ( "bad := ({value? : T; for T? of Any} -> Any do yield value)\n"
                <> "yield bad"
            )
            (SourceEvaluationFailure (UnknownIdentifier "T"))
        , programCase "mixed dependent binders scope sequentially"
            ( "identity := ({for T? of Any; with U? of T; value? : U} "
                <> "-> U do yield value)\n"
                <> "yield identity (Any; Nat; 5)"
            )
            "5"
        ]
    , recursionTests
    ]

data ArgumentSchemaCase = ArgumentSchemaCase
  { argumentCaseName :: String
  , argumentCaseDomain :: String
  , argumentCaseBody :: String
  , argumentCaseInput :: String
  , argumentCaseExpected :: String
  }

-- This is the regression matrix for the shared overload/function argument
-- schema.  Each row exercises a distinct routing rule rather than a separate
-- call-only implementation.
argumentSchemaMatrixTests :: TestTree
argumentSchemaMatrixTests =
  testGroup "shared argument-schema matrix"
    [ programCase (argumentCaseName testCase)
        ( "f := (" <> argumentCaseDomain testCase
            <> " -> Int do yield " <> argumentCaseBody testCase <> ")\n"
            <> "yield f " <> argumentCaseInput testCase
        )
        (argumentCaseExpected testCase)
    | testCase <-
        [ ArgumentSchemaCase
            "written order wins for equal positional annotations"
            "{x? : Int; y? : Int}" "x * 10 + y" "(2, 3)" "23"
        , ArgumentSchemaCase
            "the sole valid reorder is accepted"
            "{x? : Int; y? : Str}" "x" "($value, 2)" "2"
        , ArgumentSchemaCase
            "names select an otherwise ambiguous reorder"
            "{x : Int; y : Int}" "x * 10 + y" "(y : 3, x : 2)" "23"
        , ArgumentSchemaCase
            "concatenated ordered and argument-map segments compose"
            "x : Int, {y? : Int; z? : Int}"
            "x * 100 + y * 10 + z" "(x : 2, z : 4, 3)" "234"
        , ArgumentSchemaCase
            "a total annotation fills an omitted slot"
            "{x? : 5}" "x" "()" "5"
        , ArgumentSchemaCase
            "a skip preserves a private positional default"
            "{base? : Nat := 2; exponent? : Nat}"
            "base ^ exponent" "(*, 3)" "8"
        ]
    ]

recursionTests :: TestTree
recursionTests =
  testGroup "recursion"
    ( [ programCase ("factorial " <> show input)
          (factorialDeclaration <> "yield factorial " <> show input)
          expected
      | (input, expected) <-
          ([(0, "1"), (1, "1"), (5, "120"), (8, "40320")] :: [(Integer, String)])
      ]
      <> [ programCase "named recursive argument"
            (factorialDeclaration <> "yield factorial (n : 6)")
            "720"
         , programCase "recursive function specification"
            (factorialDeclaration
              <> "f := (factorial ~> ({n? : Nat} -> Int))\nyield f 5")
            "120"
         , programCase "recursive function subfederation"
            (factorialDeclaration
              <> "yield factorial of ({n? : Nat} -> Int)")
            "true"
         , programFailureCase "recursive argument type mismatch"
            (factorialDeclaration <> "yield factorial true")
            (SourceEvaluationFailure
              (FunctionEvaluationFailed NoApplicableFunctionAlternative))
         , programFailureCase "recursive result type mismatch"
            (unlines
              [ "let factorial := ({n? : Int} -> Str do"
              , "  yield if n = 0 then 1 else factorial (n - 1))"
              , "yield factorial 0"
              ])
            (SourceEvaluationFailure
              (AtlasMapFederationOperationRefuted
                AtlasMapFederationSpecificationHasNoMatchingMember))
         , programFailureCase "ordinary declarations cannot see later names"
            "a := b\nb := a\nyield a"
            (SourceEvaluationFailure
              (UnknownIdentifier "b"))
         , programFailureCase "recursion requires let"
            (dropLet factorialDeclaration <> "yield factorial 3")
            (SourceEvaluationFailure
              (UnknownIdentifier "factorial"))
         ]
    )

factorialDeclaration :: String
factorialDeclaration = unlines
  [ "let factorial := ({n? : Int} -> Int do"
  , "  yield if n = 0 then 1 else n * factorial (n - 1))"
  ]

dropLet :: String -> String
dropLet source = case words source of
  "let" : _ -> drop 4 source
  _ -> source
