module Datra.Interpreter.FunctionTests (functionTests) where

import Datra.TestSupport
import DatraTypes (InterpretingError (..))
import Test.Tasty (TestTree, testGroup)

functionTests :: TestTree
functionTests =
  testGroup "functions"
    [ argumentSchemaMatrixTests
    , testGroup "application"
        [ programCase "it observes the complete given map"
            (unlines
              [ "sum := (Nat, Nat -> Nat yield it[0] + it[1])"
              , "assert sum (1, 2) = 3"
              ])
            "()"
        , programCase "it observes defaults after skipped-argument overloading"
            (unlines
              [ "my_pow := ({_base : Nat := 2, _exponent : Nat} -> Nat yield it[0] ^ it[1])"
              , "assert my_pow (*, 3) = 8"
              ])
            "()"
        , programCase "explicit unordered parameters"
            "f := ({a?:Int,b?:Int} -> Int do yield a+b)\nyield f (b:5;6)"
            "11"
        , programCase "inferred parameters"
            "f := (do yield a+b)\nyield f (6;5)"
            "11"
        , programCase "zero parameters"
            "f := (do yield 3)\nyield f ()"
            "3"
        , programCase "optional name accepts an unnamed value"
            "f := ({x?:Int} -> Int do yield x)\nyield f 2"
            "2"
        , programCase "optional name accepts a named value"
            "f := ({x?:Int} -> Int do yield x)\nyield f (x:2)"
            "2"
        , programCase "optional value retains a required name"
            "f := ({x:Int?} -> Int? do yield x)\nyield f (x:nothing)"
            "nothing"
        , programCase "lexical closure"
            "offset:=3\nf := (do yield a+offset)\nyield f 8"
            "11"
        , programCase "higher-order parameter"
            (unlines
              [ "apply := ({f?:(Int -> Int), x?:Int} -> Int do yield f x)"
              , "increment := ({n?:Int} -> Int do yield n+1)"
              , "yield apply (f:increment,x:4)"
              ])
            "5"
        , programCase "function sum selects the numerical alternative"
            (unlines
              [ "f := (({x?:Nat} -> Int do yield x+1) | ({x?:String} -> String do yield x))"
              , "yield f 4"
              ])
            "5"
        , programCase "function sum selects the string alternative"
            (unlines
              [ "f := (({x?:Nat} -> Int do yield x+1) | ({x?:String} -> String do yield x))"
              , "yield f \"ok\""
              ])
            "$ok"
        ]
    , testGroup "externals"
        [ programCase "short external descriptor"
            "f := external \"datra.add\"\nyield f (b:5;6)"
            "11"
        , programCase "structured external descriptor"
            ("f := external (backend:\"haskell\";symbol:\"datra.add\")\n"
              <> "yield f (b:5;6)")
            "11"
        , expressionFailureCase "unknown external backend"
            "external (backend:\"missing\";symbol:\"datra.add\")"
            (SourceEvaluationFailure
              (FunctionError "unknown external backend: missing"))
        , expressionFailureCase "unknown external symbol"
            "external (backend:\"haskell\";symbol:\"missing\")"
            (SourceEvaluationFailure
              (FunctionError "unknown registered external: missing"))
        ]
    , testGroup "typing"
        [ expressionCase "contravariant input and covariant output"
            "(Int -> Nat) of (Nat -> Int)"
            "true"
        , expressionCase "invalid function variance"
            "(Nat -> Int) of (Int -> Nat)"
            "false"
        , programCase "required names accept deterministic positional input"
            "f := ({x:Int} -> Int do yield x+1)\nyield f 2"
            "3"
        , programCase "written order resolves otherwise ambiguous arguments"
            "f := ({x?:Int,y?:Int} -> Int do yield x+y)\nyield f {2,3}"
            "5"
        , programCase "private parameter names expose positional slots"
            "sum := ({_x:Int,_y:Int} -> Int yield _x+_y)\nyield sum (1,2)"
            "3"
        , programFailureCase "private parameter slots reject named input"
            "sum := ({_x:Int,_y:Int} -> Int yield _x+_y)\nyield sum (_x:1,_y:2)"
            (SourceEvaluationFailure
              (FunctionError
                "no applicable function alternative; syntax-only alternatives require their AST pattern"))
        , programFailureCase "ambiguous reorder is reported structurally"
            ( "f := ({a:Int,b:String,c:String} -> Int yield a)\n"
                <> "yield f ($x,$y,5)"
            )
            (SourceEvaluationFailure
              (FunctionError
                "ambiguous argument bindings; supply identifiers to select the intended slots"))
        , programFailureCase "declared result rejects inferred body"
            "f := ({a?:Int} -> String do yield a+1)\nyield f 5"
            (SourceEvaluationFailure
              (FunctionError
                "function body does not satisfy its declared output type"))
        , programCase "positional absence can acquire a required name"
            "f := ({x:Int?} -> Int? do yield x)\nyield f nothing"
            "nothing"
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
            <> " -> Int yield " <> argumentCaseBody testCase <> ")\n"
            <> "yield f " <> argumentCaseInput testCase
        )
        (argumentCaseExpected testCase)
    | testCase <-
        [ ArgumentSchemaCase
            "written order wins for equal positional annotations"
            "{x : Int, y : Int}" "x * 10 + y" "(2, 3)" "23"
        , ArgumentSchemaCase
            "the sole valid reorder is accepted"
            "{x : Int, y : String}" "x" "($value, 2)" "2"
        , ArgumentSchemaCase
            "names select an otherwise ambiguous reorder"
            "{x : Int, y : Int}" "x * 10 + y" "(y : 3, x : 2)" "23"
        , ArgumentSchemaCase
            "concatenated ordered and argument-map segments compose"
            "x : Int, {y? : Int, z? : Int}"
            "x * 100 + y * 10 + z" "(x : 2, z : 4, 3)" "234"
        , ArgumentSchemaCase
            "a total annotation fills an omitted slot"
            "{x? : 5}" "x" "()" "5"
        , ArgumentSchemaCase
            "a skip preserves a private positional default"
            "{_base : Nat := 2, _exponent : Nat}"
            "_base ^ _exponent" "(*, 3)" "8"
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
              (FunctionError
                "no applicable function alternative; syntax-only alternatives require their AST pattern"))
         , programFailureCase "recursive result type mismatch"
            (unlines
              [ "let factorial := ({n? : Int} -> String do"
              , "  yield if n = 0 then 1 else factorial (n - 1))"
              , "yield factorial 0"
              ])
            (SourceEvaluationFailure
              (FunctionError
                "function body does not satisfy its declared output type"))
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
