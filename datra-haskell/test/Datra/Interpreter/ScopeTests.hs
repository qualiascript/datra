module Datra.Interpreter.ScopeTests (scopeTests) where

import Datra.TestSupport
import DatraTypes
  ( InterpretingError (IdentifierStringOverlap, UnknownIdentifier)
  )
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit (assertFailure, testCase)

scopeTests :: TestTree
scopeTests =
  testGroup "lexical scope"
    [ testGroup "ordinary block declarations"
        [ testCase "quoted identifier cannot declare a block binding" $
            -- Use the supported block terminator so this checks the declaration,
            -- rather than rejecting an unrelated `end` syntax error.
            case runExpression "begin\n \"~~~\" : 2\nyield ()" of
              Left _ -> pure ()
              Right _ -> assertFailure
                "quoted identifier was accepted as an ordinary block binding"
        , programCase "computed this projection demands only its selected declaration"
            "x : 2\ny : 3\nz : this[y-x][1]\nyield z"
            "3"
        , programCase "computed this name projection"
            "x : 2\ny : 3\nz : this[y-x][0]\nyield z"
            "$y"
        , expressionCase "explicit begin sees earlier declarations"
            "begin a := 1; b := a + 1 yield b"
            "2 <~ begin\n a := 1\n b := a + 1\nyield b"
        , programCase "implicit begin sees earlier declarations"
            "a := 1\nb := a + 1\nyield b"
            "2"
        , expressionFailureCase "explicit begin cannot see later declarations"
            "begin a := b; b := 1 yield a"
            (SourceEvaluationFailure (UnknownIdentifier "b"))
        , programFailureCase "implicit begin cannot see later declarations"
            "a := b\nb := 1\nyield a"
            (SourceEvaluationFailure (UnknownIdentifier "b"))
        , expressionFailureCase "a declaration cannot see itself"
            "begin a := a yield a"
            (SourceEvaluationFailure (UnknownIdentifier "a"))
        , programCase "identifier directly binds an inferred begin block"
            "my_val := begin\n a := 2\n b := 3\nyield a + b\nyield my_val"
            "5"
        , programCase "identifier specifies a begin block explicitly"
            "my_val := 5 ~> begin\n a := 2\n b := 3\nyield a + b\nyield my_val"
            "5"
        , programCase "optional identifier specifies a begin block"
            "my_val? := 5 ~> begin\n a := 2\n b := 3\nyield a + b\nyield my_val"
            "5"
        , programCase "begin-block binding supports a federation annotation"
            "my_val := Int ~> begin\n a := 2\n b := 3\nyield a + b\nyield my_val of Int"
            "true"
        ]
    , testGroup "let block declarations"
        [ expressionCase "let is visible before its declaration"
            "begin a := x + 1; let x := 10 yield a"
            "11 <~ begin\n a := x + 1\n let x := 10\nyield a"
        , programCase "implicit let is visible before its declaration"
            "a := x + 1\nlet x := 10\nyield a"
            "11"
        ]
    , testGroup "function bodies"
        [ programCase "explicit do sees earlier declarations"
            "f := (() -> Int do a := 1; b := a + 1; yield b)\nyield f ()"
            "2"
        , programFailureCase "explicit do cannot see later declarations"
            "f := (() -> Int do a := b; b := 1; yield a)\nyield f ()"
            (SourceEvaluationFailure (UnknownIdentifier "b"))
        , programCase "inferred do sees earlier declarations"
            "f := (do a := 1; b := a + 1; yield b)\nyield f ()"
            "2"
        , programFailureCase "inferred do cannot see later declarations"
            "f := (do a := b + 1; b := 1; yield a)\nyield f 5"
            (SourceEvaluationFailure (IdentifierStringOverlap "b"))
        , programCase "let declarations are visible throughout do"
            "f := (() -> Int do a := x + 1; let x := 10; yield a)\nyield f ()"
            "11"
        ]
    , testGroup "map members"
        [ programCase "quoted identifier remains valid in a map"
            "yield (\"~~~\" : 2)[1]"
            "2"
        , programFailureCase "ordinary map member cannot see itself"
            "yield (a : a)"
            (SourceEvaluationFailure (UnknownIdentifier "a"))
        , programFailureCase "ordinary map member cannot see an earlier sibling"
            "yield (a : Nat, b : a)"
            (SourceEvaluationFailure (UnknownIdentifier "a"))
        , programFailureCase "ordinary map member cannot see a later sibling"
            "yield (a : b, b : Nat)"
            (SourceEvaluationFailure (UnknownIdentifier "b"))
        , programFailureCase "argument-map member cannot see itself"
            "yield {a : a}"
            (SourceEvaluationFailure (UnknownIdentifier "a"))
        , programFailureCase "argument-map member cannot see an earlier sibling"
            "yield {a : Nat, b : a}"
            (SourceEvaluationFailure (UnknownIdentifier "a"))
        , programFailureCase "argument-map member cannot see a later sibling"
            "yield {a : b, b : Nat}"
            (SourceEvaluationFailure (UnknownIdentifier "b"))
        , expressionFailureCase "ordinary map members do not escape into a block"
            "begin (a : 1, b : 2) yield a"
            (SourceEvaluationFailure (UnknownIdentifier "a"))
        , expressionFailureCase "argument-map members do not escape into a block"
            "begin {a : 1, b : 2} yield a"
            (SourceEvaluationFailure (UnknownIdentifier "a"))
        , expressionFailureCase "specified map members do not become block declarations"
            "begin (a : Nat) ~> (a : Int) yield a"
            (SourceEvaluationFailure (UnknownIdentifier "a"))
        ]
    ]
