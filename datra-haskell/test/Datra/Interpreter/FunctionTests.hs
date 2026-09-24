module Datra.Interpreter.FunctionTests (functionTests) where

import Datra.TestSupport
import DatraTypes (InterpretingError (..))
import Test.Tasty (TestTree, testGroup)

functionTests :: TestTree
functionTests =
  testGroup "functions"
    [ testGroup "application"
        [ programCase "explicit unordered parameters"
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
