module Datra.Interpreter.ScopeTests (scopeTests) where

import Datra.TestSupport
import Data.List.NonEmpty (NonEmpty (..))
import DatraTypes
  ( DynamicScopeLabel (..)
  , FunctionFailure (NoApplicableFunctionAlternative)
  , ScopeProtection (..)
  , ScopeProtectionPolicy (..)
  , InterpretingError
      ( InconsistentShadowing
      , FunctionEvaluationFailed
      , LetBindingCannotShadowConsistentIdentifier
      , UnknownIdentifier
      )
  , interpretedScopeProtection
  , naturalValue
  , neverValue
  )
import Rendering (renderInterpretedValue)
import GenericScopeProtection
import ScopeProtection
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit (assertBool, assertEqual, testCase)

scopeTests :: TestTree
scopeTests =
  testGroup "lexical scope"
    [ scopeProtectionTests
    , testGroup "contextual depth"
        [ programCase "this selects current and outer declaration scopes"
            ( "outer := 10\n"
                <> "yield begin middle := 20; "
                <> "yield begin inner := 30; "
                <> "yield ((_this 0).inner[1]; "
                <> "(_this 1).middle[1]; (_this 2).outer[1])"
            )
            "(30; 20; 10)"
        , programCase "this has the exact available valued-natural domain"
            "yield begin marker := 1; yield _this"
            "(from 0 to 1 -> !~\"datra.Any\")"
        , programCase "it skips scopes which introduce no it binding"
            ( "outer := (Nat -> Nat do\n"
                <> " inner := (Nat -> Nat do "
                <> "yield begin marker := 0; yield _it 1)\n"
                <> " yield inner 9)\n"
                <> "yield outer 7"
            )
            "7"
        , programCase "it has the exact available valued-natural domain"
            ( "outer := (Nat -> Any do\n"
                <> " inner := (Nat -> Any do yield _it)\n"
                <> " yield inner 9)\n"
                <> "yield outer 7"
            )
            "(from 0 to 1 -> !~\"datra.Any\")"
        , programCase "closure-local _inner_this cannot collide with source"
            "_inner_this := 23\nvalue := 4\nyield this.value[1]"
            "4"
        , programCase "closure-local _inner_it cannot collide with source"
            ( "f := (Nat -> Nat do _inner_it := 23; yield it)\n"
                <> "yield f 7"
            )
            "7"
        , programFailureCase "it rejects the first unavailable outer depth"
            ( "outer := (Nat -> Nat do\n"
                <> " inner := (Nat -> Nat do yield _it 2)\n"
                <> " yield inner 9)\n"
                <> "yield outer 7"
            )
            (SourceEvaluationFailure
              (FunctionEvaluationFailed NoApplicableFunctionAlternative))
        ]
    , testGroup "ordinary block declarations"
        [ programCase "quoted identifier can name a block entry"
            "value := begin\n \"~~~\" : 2\nyield this.\"~~~\"[1]\nyield value"
            "2"
        , programCase "computed this projection demands only its selected declaration"
            "x : 2\ny : 3\nz : this[y-x][1]\nyield z"
            "3"
        , programCase "computed this name projection"
            "x : 2\ny : 3\nz : this[y-x][0]\nyield z"
            "$y"
        , expressionCase "explicit begin sees earlier declarations"
            "begin a := 1; b := a + 1 yield b"
            "2 <~ begin a := 1; b := a + 1; yield b"
        , programCase "implicit begin sees earlier declarations"
            "a := 1\nb := a + 1\nyield b"
            "2"
        , programCase "local aliases reveal an enclosing canonical name on exit"
            "x := Str\ny := x\nyield y"
            "Str"
        , programCase "local aliases reveal canonical application names on exit"
            "type := List\nelement := Char\nyield type element"
            "List Char"
        , expressionCase "shadowing removes only the inner canonical name"
            "begin Str := Str yield Str"
            "(Str) <~ begin Str := Str; yield Str"
        , expressionCase "explicit begin aliases this"
            "begin value := 4; my_this := this; yield my_this.value[1]"
            "4 <~ begin value := 4; my_this := this; yield my_this.value[1]"
        , programCase "implicit begin aliases this"
            "value := 4\nmy_this := this\nyield my_this.value[1]"
            "4"
        , expressionCase "explicit begin may shadow private _this"
            "begin _this := 23 yield _this"
            "23 <~ begin _this := 23; yield _this"
        , programCase "implicit begin may shadow private _this"
            "_this := 23\nyield _this"
            "23"
        , programCase "ordinary identifier named this remains addressable"
            "this := 23\nyield ~this"
            "23"
        , programCase "explicit private this accepts literal zero"
            "value := 4\nyield (_this 0).value[1]"
            "4"
        , programFailureCase "apostrophe names require shadowing consistency"
            "'locked := 1\nyield begin 'locked := 2; yield 'locked"
            (SourceEvaluationFailure (InconsistentShadowing "'locked"))
        , programCase "an equal value is a consistent fixed point"
            "'locked := 1\nyield begin 'locked := 1; yield 'locked"
            "1"
        , programFailureCase
            "let cannot shadow a consistent binding even with an equal value"
            "'locked := 1\nyield begin let 'locked := 1; yield 'locked"
            (SourceEvaluationFailure
              (LetBindingCannotShadowConsistentIdentifier "'locked"))
        , programCase "a reducing expression may establish a fixed point"
            ( "identity := ({x?:Int} -> Int do yield x)\n"
                <> "'locked := 1\n"
                <> "yield begin 'locked := identity 'locked; yield 'locked"
            )
            "1"
        , programFailureCase "divergence cannot establish a fixed point"
            ( "let loop := ({x?:Int} -> Int do yield loop x)\n"
                <> "'locked := 1\n"
                <> "yield begin 'locked := loop 'locked; yield 'locked"
            )
            (SourceEvaluationFailure (InconsistentShadowing "'locked"))
        , programFailureCase "quoted apostrophe names require consistency"
            ( "\"''not compact\" := 1\n"
                <> "yield begin \"''not compact\" := 2; yield \"''not compact\""
            )
            (SourceEvaluationFailure
              (InconsistentShadowing "''not compact"))
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
            "my_val : 5 := begin\n a := 2\n b := 3\nyield a + b\nyield my_val"
            "5"
        , programCase "optional identifier specifies a begin block"
            "my_val? : 5 := (begin\n a := 2\n b := 3\nyield a + b)\nyield my_val"
            "5"
        , programCase "begin-block binding supports a federation annotation"
            "my_val : Int := begin\n a := 2\n b := 3\nyield a + b\nyield my_val of Int"
            "true"
        ]
    , testGroup "let block declarations"
        [ expressionCase "let is visible before its declaration"
            "begin a := x + 1; let x := 10 yield a"
            "11 <~ begin a := x + 1; let x := 10; yield a"
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
        , programCase "let declarations are visible throughout do"
            "f := (() -> Int do a := x + 1; let x := 10; yield a)\nyield f ()"
            "11"
        , programCase "function input binding may be shadowed privately"
            "f := (() -> Int do _it := 23; yield _it)\nyield f ()"
            "23"
        , programCase "ordinary identifier named it remains addressable"
            "f := (() -> Int do it := 23; yield ~it)\nyield f ()"
            "23"
        , programCase "explicit private it accepts literal zero"
            "f := (Nat -> Nat do yield _it 0)\nyield f 7"
            "7"
        , programFailureCase
            "apostrophe domain binding is consistent within the body"
            ( "f := ({'x:Int} -> Int do 'x := 2; yield 'x)\n"
                <> "yield f ('x:1)"
            )
            (SourceEvaluationFailure (InconsistentShadowing "'x"))
        , programCase
            "apostrophe domain binding permits an equal body rebinding"
            ( "f := ({'x:Int} -> Int do 'x := 'x; yield 'x)\n"
                <> "yield f ('x:1)"
            )
            "1"
        , programCase "recursive self binding may be shadowed privately"
            "yield (fun (() -> Int do _this := 23; yield _this)) ()"
            "23"
        ]
    , testGroup "condition-local declarations"
        [ programCase "named comparison operand is available in a branch"
            "yield if 1 >= (next : 2) then 1 else next"
            "2"
        , programCase "named condition value works outside comparisons"
            "yield if (next : 2) = 2 then next else 0"
            "2"
        , programCase "or skips a condition-local declaration on its right"
            "yield if true or (unused : missing) then 1 else unused"
            "1"
        , programCase "and skips a condition-local declaration on its right"
            "yield if false and (unused : missing) then unused else 2"
            "2"
        , programCase "Maybe branch aliases it"
            "yield (1; 2; 3)! ?? begin my_it := it; yield my_it[1][0]"
            "Just : 1"
        , programCase "Maybe branch binding may be shadowed privately"
            "yield (1; 2; 3)! ?? begin _it := 23; yield _it"
            "Just : 23"
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
            "yield {a : Nat; b : a}"
            (SourceEvaluationFailure (UnknownIdentifier "a"))
        , programFailureCase "argument-map member cannot see a later sibling"
            "yield {a : b; b : Nat}"
            (SourceEvaluationFailure (UnknownIdentifier "b"))
        , expressionFailureCase "ordinary map members do not escape into a block"
            "begin (a : 1, b : 2) yield a"
            (SourceEvaluationFailure (UnknownIdentifier "a"))
        , expressionFailureCase "argument-map members do not escape into a block"
            "begin {a : 1; b : 2} yield a"
            (SourceEvaluationFailure (UnknownIdentifier "a"))
        , expressionFailureCase "specified map members do not become block declarations"
            "begin\n ((a : Nat) ~> (a : Int))\nyield a"
            (SourceEvaluationFailure (UnknownIdentifier "a"))
        ]
    ]

scopeProtectionTests :: TestTree
scopeProtectionTests =
  testGroup "scope-protection substrate"
    [ testCase "fresh nested scopes receive distinct monotonic labels" $ do
        let root = initialScopeActivation (0 :: Int)
            child = enterScopeActivation (1 :: Int) root
            grandchild = enterScopeActivation (2 :: Int) child
            DynamicScopeLabel first = currentScopeLabel child
            DynamicScopeLabel second = currentScopeLabel grandchild
        assertBool "the second label follows the first" (second > first)
    , testCase "an active ancestor label authorizes observation" $ do
        let root = initialScopeActivation (0 :: Int)
            child = enterScopeActivation (1 :: Int) root
            label = currentScopeLabel child
            protected = protectGenericExistential label (naturalValue 3)
        case authorizeProtectedValue child protected of
          Left inaccessible ->
            assertEqual "authorized value became inaccessible"
              "3" (renderInterpretedValue inaccessible)
          Right actual ->
            assertEqual "authorized value did not unwrap temporarily"
              "3" (renderInterpretedValue actual)
    , testCase "an expired label produces Never without running the operation" $ do
        let root = initialScopeActivation (0 :: Int)
            child = enterScopeActivation (1 :: Int) root
            label = currentScopeLabel child
            protected = protectGenericExistential label (naturalValue 3)
            result = runProtectedOperation root [protected]
              (\_ -> error "inaccessible operation was evaluated")
        case result of
          Left failure -> assertBool (show failure) False
          Right value -> assertEqual "inaccessible observation"
            (renderInterpretedValue neverValue)
            (renderInterpretedValue value)
    , testCase "derived results retain normalized policy metadata" $ do
        let root = initialScopeActivation (0 :: Int)
            child = enterScopeActivation (1 :: Int) root
            label = currentScopeLabel child
            protected = protectGenericExistential label (naturalValue 3)
            result = runProtectedOperation child [protected]
              (const (Right (naturalValue 4)))
        case result of
          Left failure -> assertBool (show failure) False
          Right value ->
            case interpretedScopeProtection value of
              Nothing -> assertBool "missing protection" False
              Just protection -> do
                assertEqual "derived label"
                  label (scopeProtectionLabel protection)
                assertEqual "derived policies"
                  [GenericExistentialProtection]
                  (case scopeProtectionPolicies protection of
                    first :| remaining -> first : remaining)
    , testCase "handoff preserves an ancestor-protected wrapper" $ do
        let root = initialScopeActivation (0 :: Int)
            child = enterScopeActivation (1 :: Int) root
            protected = protectGenericExistential
              (currentScopeLabel root) (naturalValue 3)
            handed = handoffProtectedValue child root
              (const PreserveScopeProtection) protected
        assertEqual "preserved protection"
          (interpretedScopeProtection protected)
          (interpretedScopeProtection handed)
    , testCase "handoff transfers protection to the receiver" $ do
        let root = initialScopeActivation (0 :: Int)
            child = enterScopeActivation (1 :: Int) root
            protected = protectGenericExistential
              (currentScopeLabel child) (naturalValue 3)
            handed = handoffProtectedValue child root
              (const TransferScopeProtection) protected
        case interpretedScopeProtection handed of
          Nothing -> assertBool "missing transferred protection" False
          Just protection -> assertEqual "receiver label"
            (currentScopeLabel root)
            (scopeProtectionLabel protection)
    , testCase "handoff rejection produces Never" $ do
        let root = initialScopeActivation (0 :: Int)
            child = enterScopeActivation (1 :: Int) root
            protected = protectGenericExistential
              (currentScopeLabel child) (naturalValue 3)
            handed = handoffProtectedValue child root
              (const RejectScopeProtection) protected
        assertEqual "rejected handoff"
          (renderInterpretedValue neverValue)
          (renderInterpretedValue handed)
    ]
