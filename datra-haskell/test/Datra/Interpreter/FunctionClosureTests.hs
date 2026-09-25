module Datra.Interpreter.FunctionClosureTests (functionClosureTests) where

import Data.List (isInfixOf)
import Datra.TestSupport
import DatraTypes
import Interpreting (canonicalStringCodec, interpretClosedExpression)
import Parsing (parseDatra)
import DatraLanguage.AST (Expression (FunctionApplication))
import Rendering (renderInterpretedValue)
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit

functionClosureTests :: TestTree
functionClosureTests = testGroup "canonical function reconstruction"
  [ roundTrip "recursive factorial" factorial "5" "120"
  , roundTrip "recursive base case" factorial "0" "1"
  , roundTrip "user local named _fun"
      "let factorial := ({n? : Int} -> Int do _fun : 0; yield if n = _fun then 1 else n * factorial (n - 1))\nyield factorial"
      "5" "120"
  , roundTrip "quoted local matches generated root"
      "let factorial := ({n? : Int} -> Int do \"__fun\" : 0; yield if n = this.\"__fun\"[1] then 1 else n * factorial (n - 1))\nyield factorial"
      "5" "120"
  , roundTrip "captured name matches generated root"
      "_fun := 4\nyield ({n? : Int} -> Int yield n + _fun)"
      "3" "7"
  , roundTrip "quoted capture matches generated root"
      "\"__fun\" := 4\nyield ({n? : Int} -> Int yield n + this.\"__fun\"[1])"
      "3" "7"
  , roundTrip "user names retain every leading underscore" underscoredCaptures "0" "15"
  , roundTrip "three dependency levels reconstruct independently" threeLevels "3" "7"
  , testCase "each dependency level uses the closure-local namespace" $ do
      value <- requireProgram threeLevels
      let text = renderInterpretedValue value
      mapM_ (\userName -> do
        let dependency = "___" <> userName
        assertBool ("wrong dependency for " <> show userName)
          ((show dependency <> " :") `isInfixOf` text)
        assertBool ("wrong dependency reference for " <> show userName)
          (("this." <> show dependency <> "[1]") `isInfixOf` text))
        ["next", "step", "base"]
      assertBool "no temporary recursive declaration" (not ("let \"__fun\"" `isInfixOf` text))
  , roundTrip "user value is distinct from the inline fixed point"
      "userFun := 4\nyield ({n? : Int} -> Int yield n + userFun)"
      "3" "7"
  , roundTrip "outer user name cannot capture a nested fixed point"
      "userFun := 4\ninc := ({x? : Int} -> Int yield x + 1)\nyield ({n? : Int} -> Int yield userFun + inc n)"
      "3" "8"
  , testCase "user injection adds one marker after the scope prefix" $ do
      value <- requireProgram underscoredCaptures
      let text = renderInterpretedValue value
      mapM_ (\name -> do
        let encoded = replicate 3 '_' <> name
        assertBool ("missing encoded declaration for " <> show name)
          ((show encoded <> " :") `isInfixOf` text)
        assertBool ("missing encoded reference for " <> show name)
          (("this." <> show encoded <> "[1]") `isInfixOf` text))
        ["abc", "_abc", "_____abc", "__fun", "___abc"]
  , testCase "generated recursion uses fun without a temporary name" $ do
      value <- requireProgram factorial
      let text = renderInterpretedValue value
      assertBool "closure yields an inline fixed point" ("yield fun " `isInfixOf` text)
      assertBool "recursive reference is this" ("this (n - 1)" `isInfixOf` text)
      assertBool "temporary name is absent" (not ("__fun" `isInfixOf` text))
  , roundTrip "transitive captured definitions"
      "seed := 2\noffset := seed + 2\nf := ({x? : Int} -> Int yield x + offset)\nyield f"
      "7" "11"
  , roundTrip "eager capture retains its definition"
      "seed := 2\nlet offset := seed + 2\nf := ({x? : Int} -> Int yield x + offset)\nyield f"
      "7" "11"
  , roundTrip "defaults survive serialization"
      "f := ({base? : Nat := 2, exponent? : Nat} -> Nat yield base ^ exponent)\nyield f"
      "(*, 3)" "8"
  , roundTrip "local this is not polluted by dependency bindings"
      "offset := 4\nf := ({x? : Int} -> Int do local := x + offset; yield this.local[1])\nyield f"
      "7" "11"
  , roundTrip "higher-order captured value"
      "inc := ({x? : Int} -> Int yield x + 1)\nf := ({n? : Int} -> Int yield inc n)\nyield f"
      "8" "9"
  , roundTrip "captured standard-library Boolean"
      "flag := true\nf := ({x? : Int} -> Int yield if flag then x + 1 else x)\nyield f"
      "7" "8"
  , roundTrip "quoted parameter reference"
      "yield ({\"value with spaces\" : Int} -> Int yield this.\"value with spaces\"[1] + 1)"
      "4" "5"
  , roundTrip "library inlining preserves a user _AST parameter"
      "yield ({_AST : Int} -> Int yield _AST + 1)" "4" "5"
  , roundTrip "quoted captured identifier"
      "\"name.with.dots\" := 4\nyield ({x? : Int} -> Int yield x + this.\"name.with.dots\"[1])"
      "7" "11"
  , roundTrip "captured computed this projection"
      "x : 2\ny : 3\nz : this[y-x][1]\nyield ({n? : Int} -> Int yield n + z)"
      "4" "7"
  , roundTrip "computed this projection inside a function"
      "yield (() -> Int do x : 2; y : 3; z : this[y-x][1]; yield z)"
      "()" "3"
  , roundTrip "nothing result" "yield (() -> nothing yield nothing)"
      "()" "nothing"
  , roundTrip "inferred parameters" "yield (do yield a + b)" "(2, 3)" "5"
  , roundTrip "narrowed callable"
      "f := ({x? : Int} -> Int yield x + 1)\nyield f ~> ({x? : Nat} -> Int)"
      "4" "5"
  , roundTrip "mutual recursive definitions"
      "let even := ({n? : Int} -> Bool yield if n = 0 then true else odd (n - 1))\nlet odd := ({n? : Int} -> Bool yield if n = 0 then false else even (n - 1))\nyield even"
      "4" "true"
  , roundTrip "registered native function" "yield external \"datra.add\""
      "(2, 3)" "5"
  , roundTrip "syntax function ordinary application"
      "step : \"$Nat next\" as? ({value? : Int} -> Int) := (do yield value + 1)\nyield step"
      "4" "5"
  , testCase "unused ambient bindings are absent" $ do
      value <- requireProgram
        "unused := 987654321\noffset := 4\nf := ({x? : Int} -> Int yield x + offset)\nyield f"
      let text = renderInterpretedValue value
      assertBool "unreferenced definition leaked" (not ("987654321" `isInfixOf` text))
      assertBool "qualified standard-library dependency" ("\"___Std.Int\"" `isInfixOf` text)
      assertBool "explicit primitive implementation" ("external \"datra.Int\"" `isInfixOf` text)
      assertBool "dependency selected through this" ("this.\"___Std.Int\"" `isInfixOf` text)
  , testCase "different captured values have different representations" $ do
      a <- requireProgram "offset := 4\nyield ({x? : Int} -> Int yield x + offset)"
      b <- requireProgram "offset := 5\nyield ({x? : Int} -> Int yield x + offset)"
      assertBool "capture identity was erased"
        (interpretedCanonicalResult a /= interpretedCanonicalResult b)
  , testCase "only the selected module member is reconstructed" $ do
      original <- runModuleProgram "test/fixtures/modules/main.datra"
        "import \"library_one\"\nyield ({n? : Int} -> Int yield LibraryOne.increment n)"
      value <- either (assertFailure . show) pure original
      let text = renderInterpretedValue value
      assertBool "module filename is not a runtime dependency" (not ("import " `isInfixOf` text))
      assertBool "closure has no generated let root"
        (not ("let \"___fun\" :" `isInfixOf` text))
      reconstructed <- requireExpression text
      assertEqual "stable module reconstruction" text (renderInterpretedValue reconstructed)
      result <- requireProgram ("f := " <> text <> "\nyield f 7")
      assertEqual "private closure dependency survived" "11" (renderInterpretedValue result)
  , testCase "import-all dependency names retain their module origin" $ do
      original <- runModuleProgram "test/fixtures/modules/main.datra"
        "import all \"library_one\"\nyield ({n? : Int} -> Int yield x + n)"
      value <- either (assertFailure . show) pure original
      let text = renderInterpretedValue value
      assertBool "actual module provenance is retained"
        ("\"___LibraryOne.x\"" `isInfixOf` text)
      reconstructed <- requireExpression text
      assertEqual "stable imported origin" text (renderInterpretedValue reconstructed)
      result <- requireProgram ("f := " <> text <> "\nyield f 3")
      assertEqual "captured imported value" "10" (renderInterpretedValue result)
  , testCase "user name cannot collide with a nested module function" $ do
      original <- runModuleProgram "test/fixtures/modules/main.datra"
        "import \"library_one\"\nuserFun := 4\nyield ({n? : Int} -> Int yield userFun + LibraryOne.increment n)"
      value <- either (assertFailure . show) pure original
      let text = renderInterpretedValue value
      reconstructed <- requireExpression text
      assertEqual "stable module reconstruction" text (renderInterpretedValue reconstructed)
      result <- requireProgram ("f := " <> text <> "\nyield f 7")
      assertEqual "user capture and nested root remain distinct" "15" (renderInterpretedValue result)
  , programCase "function types belong to Any" "assert (Nat -> Nat) of Any" "()"
  , programCase "functions can annotate named parameters"
      "apply := ({callback? : (Nat -> Nat), value? : Nat} -> Nat yield callback value)\nyield apply (({n? : Nat} -> Nat yield n + 1), 4)"
      "5"
  ]

factorial :: String
factorial = "let factorial := ({n? : Int} -> Int do\n yield if n = 0 then 1 else n * factorial (n - 1))\nyield factorial"

underscoredCaptures :: String
underscoredCaptures =
  "abc := 1\n_abc := 2\n\"_____abc\" := 3\n\"__fun\" := 4\n\"___abc\" := 5\n\
  \yield ({n? : Int} -> Int yield n + abc + _abc + this.\"_____abc\"[1] + this.\"__fun\"[1] + this.\"___abc\"[1])"

threeLevels :: String
threeLevels =
  "base := 2\nstep := base + 1\nnext := step + 1\nyield ({n? : Int} -> Int yield n + next)"

roundTrip :: String -> String -> String -> String -> TestTree
roundTrip name program argument expected = testCase name $ do
  original <- requireProgram program
  let text = renderInterpretedValue original
  reconstructed <- requireExpression text
  assertEqual "canonical text is idempotent" text (renderInterpretedValue reconstructed)
  assertEqual "canonical identity survives"
    (interpretedCanonicalResult original) (interpretedCanonicalResult reconstructed)
  case toStringValue canonicalStringCodec original of
    Left failure -> assertFailure (show failure)
    Right _ -> pure ()
  result <- requireProgram ("f := " <> text <> "\nyield f " <> argument)
  assertEqual "reconstructed call" expected (renderInterpretedValue result)
  closed <- either (assertFailure . show) pure (parseDatra ("(" <> text <> "\n)"))
  input <- either (assertFailure . show) pure (parseDatra ("(" <> argument <> ")"))
  independent <- either (assertFailure . show) pure
    (interpretClosedExpression (FunctionApplication closed input))
  assertEqual "call needs no implicit Std or modules" expected (renderInterpretedValue independent)

requireProgram :: String -> IO InterpretedValue
requireProgram = either (assertFailure . show) pure . runProgram

requireExpression :: String -> IO InterpretedValue
requireExpression = either (assertFailure . show) pure . runExpression
