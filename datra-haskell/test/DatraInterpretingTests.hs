{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE PostfixOperators #-}

module DatraInterpretingTests (main) where

import AtlasMapFederationExpression
  ( AtlasMapFederationDecision (..))
import Datra.Interpreter.FunctionClosureTests (functionClosureTests)
import Datra.Interpreter.FunctionTests (functionTests)
import Datra.Interpreter.DatraTypeLawTests (datraTypeLawTests)
import Datra.Interpreter.IntegrationTests (integrationTests)
import Datra.Interpreter.ModuleTests (moduleTests)
import Datra.Interpreter.OverloadAssertionTests (overloadAssertionTests)
import Datra.Interpreter.ScopeTests (scopeTests)
import Datra.Interpreter.StandardLibraryTests (standardLibraryTests)
import DatraLanguage.AST
  ( Expression (..)
  , IdentifierString (IdentifierString)
  , StringTemplatePart (..)
  , contextualAccess
  )
import DatraLanguage.AST.Syntax
  ( natural
  , (...)
  , (<:>)
  , (<+>)
  , (<..>)
  , (..+)
  , (..-)
  , (<.>)
  , (<@>)
  , (~>)
  )
import DatraLanguage.AST.Syntax qualified as AST
import DatraLanguage.SyntaxTemplate
  ( FunctionSyntax (FunctionSyntax) )
import DatraTypes qualified as Types
import Interpreting
  ( ModuleSource (..)
  , InterpretedValue
  , InterpretedValueKind (..)
  , InterpretingError (..)
  , OperandSide (..)
  , interpretExpressionReason
  , interpretLocatedExpression
  , canonicalStringCodec
  , interpretedExplicitOrdinal
  , interpretedInteger
  , interpretedFormulationLevel
  , interpretedMap
  , interpretedMapCardinality
  , interpretedMapFinalOrderType
  , interpretedMapValueAt
  , interpretedRangeDescription
  , interpretedValueKind
  , matchesValueSyntaxHoleWith
  , moduleExportNames
  , moduleSyntaxRules
  , parseDatraSourceLocatedWithImportsAndStandardLibrary
  )
import DatraLanguage.Diagnostics.Interpreter
  ( AtlasMapFederationOperation (..)
  , AtlasMapFederationRefutation (..)
  , AtlasMapFederationUncertainty (..)
  )
import Rendering
  ( renderInterpretedValue
  , renderInterpretedValueAsNewlineMap
  )
import DatraOrdinal
  ( finiteOrdinal
  , naturalAtOrdinal
  , omega
  , ordinal
  )
import DatraLanguage.Diagnostics
  ( DatraError (DatraError)
  , Located (Located)
  , locatedValue
  , SourcePosition (SourcePosition)
  , SourceSpan (SourceSpan)
  )
import DatraLanguage.Diagnostics.Application
  ( ParseFailure (parseFailureMessage) )
import DatraLanguage.Diagnostics.Localization
  ( Locale (English, Romanian)
  , renderDatraError
  )
import MapOperators.AccessOperator
  ( AccessError
      ( AccessPositionOutOfBounds )
  )
import Numeric.Natural (Natural)
import SyntaxDefinitions
  ( SyntaxHoleKind (..)
  , SyntaxPiece (SyntaxHole, SyntaxLiteral)
  , SyntaxRule (..)
  , SyntaxTemplate (SyntaxTemplate)
  , qualifySyntaxRule
  )
import SyntaxTemplateMatching
  ( SyntaxTemplateFederationFailure (..)
  , SyntaxTemplateMatchFailure (NoMatchingSyntaxTemplate)
  , compileSyntaxTemplateFederation
  , matchSyntaxTemplates
  )
import Hedgehog qualified as H
import Hedgehog.Gen qualified as Gen
import Hedgehog.Range qualified as Range
import SuperEllipsisRange
  ( SuperEllipsisRangeConcatError (SuperEllipsisRangesOverlap)
  , SuperEllipsisRangeDescription (SuperEllipsisRangeDescription)
  , SuperEllipsisRangeTarget (GivenTarget, MinusSign, PlusSign)
  )
import Test.Tasty (TestTree, defaultMain, testGroup)
import Test.Tasty.Hedgehog (testProperty)
import Test.Tasty.HUnit (assertBool, assertEqual, assertFailure, testCase)

main :: IO ()
main = defaultMain testTree

testTree :: TestTree
testTree =
  testGroup "Datra interpreter"
    [ testGroup "examples"
        [ testCase "literals and arithmetic" testLiteralsAndArithmetic
        , testCase "slot ordinal distinctness" testSlotOrdinalDistinctness
        , testCase "string templates" testStringTemplates
        , testCase "named field access" testNamedAccess
        , testCase "argument maps" testArgumentMaps
        , testCase "argument maps in concatenation" testArgumentMapConcatenation
        , testCase "argument maps in string templates" testArgumentMapTemplates
        , testCase "internal typed decoding" testEval
        , testCase "template-backed keyword forms" testEvalBackedKeywords
        , testCase "begin/yield scope and provenance" testBegin
        , testCase "begin/yield scope rejections" testBeginRejections
        , testCase "module aliases retain syntax rules" testModuleSyntaxAlias
        , testCase "qualified syntax excludes hole-led rules"
            testQualifiedSyntaxRules
        , testCase "implicit programs" testPrograms
        , testCase "integers and integer ranges" testIntegers
        , testCase "closed infinite valued range" testClosedInfiniteValuedRange
        , testCase "booleans and Either" testBooleansAndEither
        , testCase "optionals and conditionals" testOptionalsAndConditionals
        , testCase "combined type systems" testCombinedTypeSystems
        , testCase "combinatorial numerical systems" testCombinatorialNumericalSystems
        , testCase "ranges" testRanges
        , testCase "canonical results" testCanonicalResults
        , testCase "rendering" testRendering
        , testCase "maps" testMaps
        , testCase "atlas-map federations" testAtlasMapFederations
        , testCase "access" testAccess
        , testCase "specification" testSpecification
        , testCase "identifier types and assignments" testIdentifiers
        , testCase "Datra and canonical type capabilities" testCanonicalTypes
        , testCase "typed rejections" testTypedRejections
        , testCase "located rejection" testLocatedRejection
        ]
    , functionClosureTests
    , functionTests
    , datraTypeLawTests
    , integrationTests
    , scopeTests
    , moduleTests
    , overloadAssertionTests
    , standardLibraryTests
    , testGroup "properties"
        [ testProperty "natural addition agrees with Haskell" propNaturalAddition
        , testProperty "natural multiplication agrees with Haskell" propNaturalMultiplication
        , testProperty "natural exponentiation agrees with Haskell" propNaturalExponentiation
        , testProperty "integer addition agrees with Haskell" propIntegerAddition
        , testProperty "integer subtraction agrees with Haskell" propIntegerSubtraction
        , testProperty "integer multiplication agrees with Haskell" propIntegerMultiplication
        , testProperty "integer powers agree with Haskell" propIntegerExponentiation
        , testProperty
            "nested integer ranges compose by subtyping"
            propNestedIntegerRangeSubtyping
        , testProperty
            "conditional arithmetic specifies into integer ranges"
            propConditionalArithmeticRange
        , testProperty
            "optional integer ranges accept both branches"
            propOptionalIntegerRangeBranches
        ]
    ]

assert :: String -> Bool -> IO ()
assert = assertBool

testQualifiedSyntaxRules :: IO ()
testQualifiedSyntaxRules = do
  let expressionHole =
        SyntaxHole (ExpressionSyntaxHole (identifierReference "_Expr"))
      rule template = SyntaxRule
        "syntax" template (AtlasMap []) False Nothing (AtlasMap [])
      literalHeaded = rule (SyntaxTemplate
        [ SyntaxLiteral "if"
        , expressionHole
        , SyntaxLiteral "then"
        , expressionHole
        ])
      holeLed = rule (SyntaxTemplate
        [ expressionHole
        , SyntaxLiteral "or"
        , expressionHole
        ])
  assertEqual "literal syntax receives a qualified surface head"
    (Just literalHeaded
      { syntaxName = "Std.syntax"
      , syntaxTemplate = SyntaxTemplate
          [ SyntaxLiteral "Std.if"
          , expressionHole
          , SyntaxLiteral "then"
          , expressionHole
          ]
      })
    (qualifySyntaxRule "Std" literalHeaded)
  assertEqual "hole-led syntax cannot be qualified without leaking globally"
    Nothing
    (qualifySyntaxRule "Std" holeLed)

testModuleSyntaxAlias :: IO ()
testModuleSyntaxAlias = do
  let astType = External (AsciiStringLiteral "datra.AST")
      expressionType = External (AsciiStringLiteral "datra.Expr")
      blockType = External (AsciiStringLiteral "datra.Block")
      beginValue = SyntaxType
        (Extract (AsciiStringLiteral "begin $_Block yield $_Expr"))
        (FunctionType (AtlasMap [astType, astType]) astType)
      binding name value = IdentifierOperation
        (IdentifierString name) value (Just value)
      moduleBody = Begin
        [binding "begin" (identifierReference "begin")]
        (contextualAccess (IdentifierString "_this"))
      source = ModuleSource "alias-module.datra"
        (Program
          [ binding "_Expr" expressionType
          , binding "_Block" blockType
          , binding "begin" beginValue
          , binding "outerOnly" (natural 7)
          ]
          (binding "AliasModule" moduleBody))
        []
  case moduleExportNames source of
    Right names -> assert "only inner declarations are module members"
      (names == ["begin"])
    Left failure -> assertFailure
      ("module export discovery failed: " <> show failure)
  case moduleSyntaxRules "alias-module" source of
    Right [rule] -> do
      assert "the inner alias retains the outer function's syntax"
        (syntaxName rule == "begin")
      assert "the retained rule keeps its declared literal"
        (syntaxTemplate rule == SyntaxTemplate
          [ SyntaxLiteral "begin"
          , SyntaxHole (BlockSyntaxHole
              (InModule "alias-module" (identifierReference "_Block")))
          , SyntaxLiteral "yield"
          , SyntaxHole (ExpressionSyntaxHole
              (InModule "alias-module" (identifierReference "_Expr")))
          ])
    Right rules -> assertFailure
      ("expected one exported syntax rule, got: " <> show rules)
    Left failure -> assertFailure
      ("module syntax discovery failed: " <> show failure)
  let shadowingSource = ModuleSource "shadowing-module.datra"
        (Program
          [ binding "_Expr" expressionType
          , binding "_Block" blockType
          , binding "begin" beginValue
          ]
          (binding "ShadowingModule" (Begin
            [binding "begin" (natural 123)]
            (contextualAccess (IdentifierString "_this")))))
        []
  case moduleSyntaxRules "shadowing-module" shadowingSource of
    Right [] -> pure ()
    Right rules -> assertFailure
      ("a non-function shadow retained syntax rules: " <> show rules)
    Left failure -> assertFailure
      ("shadowing module syntax discovery failed: " <> show failure)
  let preservingSource = ModuleSource "preserving-module.datra"
        (Program
          [ binding "_Expr" expressionType
          , binding "_Block" blockType
          , binding "begin" beginValue
          ]
          (binding "PreservingModule" (Begin
            [ binding "_begin" (identifierReference "begin")
            , binding "begin" (natural 123)
            ]
            (contextualAccess (IdentifierString "_this")))))
        []
  case moduleSyntaxRules "preserving-module" preservingSource of
    Right [rule] -> assert
      "an alias made before shadowing retains the original syntax rules"
      (syntaxName rule == "_begin"
        && syntaxTemplate rule == SyntaxTemplate
          [ SyntaxLiteral "begin"
          , SyntaxHole (BlockSyntaxHole
              (InModule "preserving-module"
                (identifierReference "_Block")))
          , SyntaxLiteral "yield"
          , SyntaxHole (ExpressionSyntaxHole
              (InModule "preserving-module"
                (identifierReference "_Expr")))
          ])
    Right rules -> assertFailure
      ("expected only the preserved alias rule, got: " <> show rules)
    Left failure -> assertFailure
      ("syntax-preserving shadow failed: " <> show failure)
  let duplicateSource = ModuleSource "duplicate-module.datra"
        (Program [] (binding "DuplicateModule" (Begin
          [ binding "abc" (natural 123)
          , binding "abc" (natural 456)
          ]
          (contextualAccess (IdentifierString "_this")))))
        []
  case moduleExportNames duplicateSource of
    Left (IdentifierStringOverlap "abc") -> pure ()
    result -> assertFailure
      ("same-block redeclaration was not rejected: " <> show result)
  let isolatedBody = Begin
        [binding "x" (identifierReference "Int")]
        (contextualAccess (IdentifierString "_this"))
      isolatedSource = ModuleSource "isolated-module.datra"
        (Program [] (binding "IsolatedModule" isolatedBody)) []
  case moduleExportNames isolatedSource of
    Left (UnknownIdentifier "Int") -> pure ()
    result -> assertFailure
      ("a loaded module implicitly received Std: " <> show result)
  let explicitStd = ModuleSource "std.datra"
        (Program [] (binding "Std" (Begin
          [binding "Int" (natural 7)]
          (contextualAccess (IdentifierString "_this")))))
        []
      importingSource = ModuleSource "importing-module.datra"
        (Program
          [Import True "std"]
          (binding "ImportingModule" isolatedBody))
        [("std", explicitStd)]
  case moduleExportNames importingSource of
    Right ["x"] -> pure ()
    result -> assertFailure
      ("an explicit import-all did not supply module bindings: " <> show result)

identifierReference :: String -> Expression
identifierReference = IdentifierReference . IdentifierString

matchSingleRule
  :: (SyntaxHoleKind Expression -> Expression -> Bool)
  -> SyntaxRule
  -> Expression
  -> Either SyntaxTemplateMatchFailure Expression
matchSingleRule holeMatches rule expressionValue =
  case compileSyntaxTemplateFederation
      (\_ _ -> AtlasMapFederationProved ()) [rule] of
    Right federation ->
      matchSyntaxTemplates holeMatches federation expressionValue
    Left _ -> Left NoMatchingSyntaxTemplate

sourceNatType :: String
sourceNatType = "Nat"

sourceIntType :: String
sourceIntType = "Int"

maybeType :: Expression -> Expression
maybeType = FunctionApplication
  (IdentifierReference (IdentifierString "Maybe"))

justValue :: Expression -> Expression
justValue value = AST.assignment "Just" value value

maybeExpansion :: Expression -> Expression
maybeExpansion value =
  AST.eitherType
    (AST.eitherType
      (AST.assignment "Nothing" AST.emptyMap AST.emptyMap)
      AST.emptyMap)
    (AST.dependentIdentifierType "Just" value)

ordinalCall :: String -> [Expression] -> Expression
ordinalCall name arguments =
  FunctionApplication
    (External (AsciiStringLiteral ("datra.ordinal." <> name)))
    (AtlasMap arguments)

ordinalSum, ordinalProduct, ordinalExponent :: Expression -> Expression -> Expression
ordinalSum left right = ordinalCall "sum" [left, right]
ordinalProduct left right = ordinalCall "prod" [left, right]
ordinalExponent left right = ordinalCall "exp" [left, right]

propNaturalAddition :: H.Property
propNaturalAddition = H.property $ do
  left <- H.forAll naturalGen
  right <- H.forAll naturalGen
  interpretedNatural (Addition (EllipsisNatural left) (EllipsisNatural right))
    H.=== Just (left + right)

propNaturalMultiplication :: H.Property
propNaturalMultiplication = H.property $ do
  left <- H.forAll naturalGen
  right <- H.forAll naturalGen
  interpretedNatural
      (Multiplication (EllipsisNatural left) (EllipsisNatural right))
    H.=== Just (left * right)

propNaturalExponentiation :: H.Property
propNaturalExponentiation = H.property $ do
  base <- H.forAll (Gen.integral (Range.linear 0 12))
  exponentValue <- H.forAll (Gen.integral (Range.linear 0 8))
  interpretedNatural
      (Exponentiation (EllipsisNatural base) (EllipsisNatural exponentValue))
    H.=== Just (base ^ exponentValue)

propIntegerAddition :: H.Property
propIntegerAddition = H.property $ do
  left <- H.forAll integerGen
  right <- H.forAll integerGen
  interpretedSigned
      (Addition (integerExpression left) (integerExpression right))
    H.=== Just (left + right)

propIntegerSubtraction :: H.Property
propIntegerSubtraction = H.property $ do
  left <- H.forAll integerGen
  right <- H.forAll integerGen
  interpretedSigned
      (Subtraction (integerExpression left) (integerExpression right))
    H.=== Just (left - right)

propIntegerMultiplication :: H.Property
propIntegerMultiplication = H.property $ do
  left <- H.forAll integerGen
  right <- H.forAll integerGen
  interpretedSigned
      (Multiplication (integerExpression left) (integerExpression right))
    H.=== Just (left * right)

propIntegerExponentiation :: H.Property
propIntegerExponentiation = H.property $ do
  base <- H.forAll (Gen.integral (Range.linear (-12) 12))
  exponentValue <- H.forAll (Gen.integral (Range.linear 0 8))
  interpretedSigned
      (Exponentiation
        (integerExpression base)
        (EllipsisNatural exponentValue))
    H.=== Just (base ^ exponentValue)

propNestedIntegerRangeSubtyping :: H.Property
propNestedIntegerRangeSubtyping = H.property $ do
  outerLower <- H.forAll (Gen.integral (Range.linear (-30) 10))
  outerWidth <- H.forAll (Gen.integral (Range.linear 0 30))
  let outerUpper = outerLower + outerWidth
  innerLowerOffset <-
    H.forAll (Gen.integral (Range.linear 0 outerWidth))
  innerUpperOffset <-
    H.forAll
      (Gen.integral (Range.linear innerLowerOffset outerWidth))
  let innerLower = outerLower + innerLowerOffset
      innerUpper = outerLower + innerUpperOffset
  selected <- H.forAll (Gen.integral (Range.linear innerLower innerUpper))
  let expressionValue =
        ( integerExpression selected
            ~> AST.integerWithinTo innerLower innerUpper
        ) ~> AST.integerWithinTo outerLower outerUpper
  case interpretExpressionReason expressionValue of
    Right _ -> H.success
    Left rejection -> H.annotateShow rejection >> H.failure

propConditionalArithmeticRange :: H.Property
propConditionalArithmeticRange = H.property $ do
  left <- H.forAll (Gen.integral (Range.linear (-20) 20))
  right <- H.forAll (Gen.integral (Range.linear (-20) 20))
  let commutativeCondition =
        AST.equal
          ((AST.+) (integerExpression left) (integerExpression right))
          ((AST.+) (integerExpression right) (integerExpression left))
      selectedResult =
        (AST.-) (integerExpression left) (integerExpression right)
      rejectedDeadBranch =
        AST.and (natural 1) (AST.boolean True)
      expressionValue =
        AST.conditional
          commutativeCondition
          selectedResult
          rejectedDeadBranch
          ~> AST.integerWithinTo (-40) 40
  case interpretExpressionReason expressionValue of
    Right _ -> H.success
    Left rejection -> H.annotateShow rejection >> H.failure

propOptionalIntegerRangeBranches :: H.Property
propOptionalIntegerRangeBranches = H.property $ do
  selectValue <- H.forAll Gen.bool
  selected <- H.forAll (Gen.integral (Range.linear (-25) 25))
  let nothingValue =
        AST.assignment "Nothing" AST.emptyMap AST.emptyMap
      expressionValue =
        AST.conditional
          (AST.boolean selectValue)
          (justValue (integerExpression selected))
          nothingValue
          ~> maybeType (AST.integerWithinTo (-25) 25)
  case interpretExpressionReason expressionValue of
    Right _ -> H.success
    Left rejection -> H.annotateShow rejection >> H.failure

naturalGen :: H.Gen Natural
naturalGen = Gen.integral (Range.linear 0 10000)

integerGen :: H.Gen Integer
integerGen = Gen.integral (Range.linear (-10000) 10000)

integerExpression :: Integer -> Expression
integerExpression value
  | value < 0 = Minus (EllipsisNatural (fromInteger (negate value)))
  | otherwise = EllipsisNatural (fromInteger value)

interpretedSigned :: Expression -> Maybe Integer
interpretedSigned expressionValue =
  case interpretExpressionReason expressionValue of
    Left _ -> Nothing
    Right value -> interpretedInteger value

interpretedNatural :: Expression -> Maybe Natural
interpretedNatural expressionValue =
  case interpretExpressionReason expressionValue of
    Left _ -> Nothing
    Right value -> naturalOrdinal value

expectValue :: String -> Expression -> (InterpretedValue -> IO ()) -> IO ()
expectValue label expressionValue check =
  case interpretExpressionReason expressionValue of
    Left rejection ->
      fail (label <> ": unexpected rejection: " <> show rejection)
    Right value -> check value

expectSourceValue :: String -> String -> (InterpretedValue -> IO ()) -> IO ()
expectSourceValue label source check =
  case parseProductionSource ("(" <> source <> "\n)") of
    Left message -> fail
      (label <> ": unexpected parse failure: " <> parseFailureMessage message)
    Right expressionValue -> expectValue label expressionValue check

expectSourceRejection
  :: String
  -> String
  -> (InterpretingError -> Bool)
  -> IO ()
expectSourceRejection label source matches =
  case parseProductionSource ("(" <> source <> "\n)") of
    Left message -> fail
      (label <> ": unexpected parse failure: " <> parseFailureMessage message)
    Right expressionValue ->
      case interpretExpressionReason expressionValue of
        Left rejection
          | matches rejection -> pure ()
          | otherwise ->
              fail (label <> ": unexpected rejection: " <> show rejection)
        Right value ->
          fail
            (label <> ": unexpectedly produced " <> renderInterpretedValue value)

naturalOrdinal :: InterpretedValue -> Maybe Natural
naturalOrdinal value = do
  (level, ordinalValue) <- interpretedExplicitOrdinal value
  if level == 1
    then naturalAtOrdinal ordinalValue
    else Nothing

testIntegers :: IO ()
testIntegers = do
  expectValue "unary natural plus" (AST.plus (natural 6)) $ \value ->
    assert "unary plus preserves a natural"
      ( interpretedInteger value == Just 6
        && renderInterpretedValue value == "6"
      )
  expectValue "unary integer plus" (AST.plus (AST.minus (natural 6))) $ \value ->
    assert "unary plus preserves a negative integer"
      ( interpretedInteger value == Just (-6)
        && renderInterpretedValue value == "-6"
      )
  expectValue "integer negation" (AST.minus (natural 6)) $ \value ->
    assert "minus creates the complemented integer -6"
      ( interpretedValueKind value == IntegerValueKind
        && interpretedInteger value == Just (-6)
        && renderInterpretedValue value == "-6"
      )
  expectValue
      "integer addition"
      ((AST.+) (AST.minus (natural 6)) (natural 2)) $ \value ->
    assert "addition extends to finite integers"
      (interpretedInteger value == Just (-4))
  expectValue
      "integer subtraction"
      ((AST.-) (natural 5) (natural 8)) $ \value ->
    assert "subtraction produces a complemented integer"
      (interpretedInteger value == Just (-3))
  expectValue
      "integer multiplication"
      ((AST.*) (AST.minus (natural 2)) (AST.minus (natural 3))) $ \value ->
    assert "multiplication extends to finite integers"
      (interpretedInteger value == Just 6)
  expectValue
      "odd integer power"
      ((AST.^) (AST.minus (natural 2)) (natural 3)) $ \value ->
    assert "negative bases support natural exponents"
      (interpretedInteger value == Just (-8))
  expectValue
      "even integer power"
      ((AST.^) (AST.minus (natural 2)) (natural 2)) $ \value ->
    assert "even powers canonicalize back to naturals"
      (interpretedInteger value == Just 4)
  expectValue
      "descending integer range"
      (AST.integerFromDownwards (-1)) $ \value ->
    assert "integer range rendering retains its signed bound and direction"
      (renderInterpretedValue value == "range -1 down")
  expectValue
      "valued integer range"
      (AST.integerWithinTo (-3) 4) $ \value ->
    assert "valued integer ranges retain inclusive signed syntax"
      (renderInterpretedValue value == "from -3 to 4")
  expectValue "integer type" AST.integerType $ \value ->
    assert "Int is the full Nat-product-with-two federation"
      (renderInterpretedValue value == "Int")
  expectValue
      "negative integer specification into Int"
      (AST.minus (natural 6) ~> AST.integerType) $ \value ->
    assert "Int specification selects complemented members"
      (renderInterpretedValue value == "-6 ~> Int")
  expectValue
      "directed integer sequence specification"
      ( (AST.minus (natural 2)
          <:> AST.minus (natural 1)
          <:> natural 0)
          ~> AST.integerFromTo (-3) 2
      ) $ \value ->
    assert "integer ranges select contiguous signed sequences"
      (renderInterpretedValue value == "(-2; -1; 0) ~> range -3 to 2")
  expectValue
      "valued integer subfederation composition"
      ( (AST.minus (natural 2) ~> AST.integerWithinTo (-2) 3)
          ~> AST.integerType
      ) $ \value ->
    assert "valued integer ranges are subfederations of Int"
      (renderInterpretedValue value == "-2 ~> Int")
  expectValue
      "Nat subfederation of Int"
      ((natural 2 ~> AST.naturalType) ~> AST.integerType) $ \value ->
    assert "the direct half of Int contains every natural"
      (renderInterpretedValue value == "2 ~> Int")
  expectValue
      "signed arithmetic coerces the first transfinite formulation to Infinity"
      ((AST.+) (AST.minus (natural 1)) (...)) $ \value ->
    assert "finite addition preserves positive Infinity"
      (renderInterpretedValue value == "Infinity")
  expectValue
      "unary plus coerces the first transfinite formulation to Infinity"
      (AST.plus (...)) $ \value ->
    assert "unary plus preserves positive Infinity"
      (renderInterpretedValue value == "Infinity")
  assert "negative exponents remain unsupported"
    (case interpretExpressionReason
        ((AST.^) (natural 2) (AST.minus (natural 1))) of
      Left (ExpectedNaturalExponent IntegerValueKind) -> True
      _ -> False)

testClosedInfiniteValuedRange :: IO ()
testClosedInfiniteValuedRange =
  case do
      infinity <- Types.asciiStringValue "PosInf"
      Types.integerLimitRangeValue
        Types.ValuedIntegerRangeKind
        (Types.naturalValue 0)
        infinity of
    Left failure ->
      assertFailure ("closed infinite valued range construction failed: " <> show failure)
    Right closed -> do
      assert "closed infinite valued range has order type omega plus one"
        (interpretedMapFinalOrderType (interpretedMap closed) == ordinal [1, 1])
      case Types.requireCanonicalTypeAnnotation closed of
        Left failure ->
          assertFailure ("closed infinite valued range is not canonical: " <> show failure)
        Right () -> pure ()
      complement <- either
        (assertFailure . ("Complement construction failed: " <>) . show)
        pure
        (Types.asciiStringValue "Complement")
      complementBranch <- either
        (assertFailure . ("complement branch construction failed: " <>) . show)
        pure
        (Types.eitherValue complement (Types.makeAtlasMap 0 []))
      let signedLimit = Types.makeAtlasMap 2 [closed, complementBranch]
      case Types.requireCanonicalTypeAnnotation signedLimit of
        Left failure ->
          assertFailure ("IntLimit representation is not canonical: " <> show failure)
        Right () -> pure ()
      case Types.specifyValues closed Types.integerValuedRangeTypeValue of
        Left failure ->
          assertFailure ("closed infinite valued range typing failed: " <> show failure)
        Right _ -> pure ()
      case Types.accessValues closed (Types.formulationValue 1) of
        Left failure ->
          assertFailure ("closed infinite valued range access failed: " <> show failure)
        Right endpoint -> do
          let rendered = renderInterpretedValue endpoint
          assert
            ("the ellipsis position selects positive infinity, got " <> rendered)
            (rendered == "Infinity")

testLiteralsAndArithmetic :: IO ()
testLiteralsAndArithmetic = do
  expectValue "ASCII string literal" (AsciiStringLiteral "a\255a") $ \value -> do
    let valueMap = interpretedMap value
        characterCodes =
          map
            (\position ->
              interpretedMapValueAt valueMap (finiteOrdinal position)
                >>= naturalOrdinal)
            [0 .. 3]
    assert "ASCII strings retain their map shape and character order"
      ( interpretedValueKind value == AsciiStringValueKind
        && interpretedMapCardinality valueMap == 2
        && interpretedMapFinalOrderType valueMap == finiteOrdinal 3
        && characterCodes == map Just [97, 255, 97] <> [Nothing]
        && renderInterpretedValue value == "\"a\\FFa\""
      )
  expectValue "empty ASCII string" (AsciiStringLiteral "") $ \value ->
    assert "the empty ASCII string retains its literal while using an empty map"
      ( interpretedValueKind value == AsciiStringValueKind
        && interpretedMapCardinality (interpretedMap value) == 0
        && renderInterpretedValue value == "\"\""
      )
  expectValue "Str type" AST.stringType $ \value ->
    assert "Str renders as the ASCII string federation"
      ( interpretedValueKind value == MapValueKind
        && renderInterpretedValue value == "Str"
      )
  expectValue
      "string membership"
      (AST.equal
        (AST.subfederation (AST.asciiString "my_string") AST.stringType)
        (AST.boolean True)) $ \value ->
    assert "a string literal is a member of Str"
      (renderInterpretedValue value == "true")
  expectValue "natural literal" (natural 10) $ \value ->
    assert "naturals remain typed rank-one explicit values"
      ( interpretedValueKind value == NaturalValueKind
        && interpretedExplicitOrdinal value
          == Just (1, finiteOrdinal 10)
      )
  expectValue "Ellipsis literal" (...) $ \value ->
    assert "Ellipsis remains a formulation rather than an explicit ordinal"
      (interpretedFormulationLevel value == Just 1)
  expectValue
      "arithmetic precedence AST"
      ((AST.+)
        (natural 1)
        ((AST.*) (natural 2) (natural 3))) $ \value ->
    assert "natural arithmetic evaluates through ordinal operators"
      (interpretedExplicitOrdinal value == Just (1, finiteOrdinal 7))
  expectValue
      "empty-map numerical coercion"
      (AST.equal ((AST.+) AST.emptyMap (natural 3)) (natural 3)) $ \value ->
    assert "the total empty map coerces to numerical zero"
      (renderInterpretedValue value == "true")
  expectValue
      "Nothing numerical coercion chain"
      (AST.equal
        ((AST.+) AST.nothing (natural 3))
        (natural 3)) $ \value ->
    assert "nothing follows its identifier string and unit map to zero"
      (renderInterpretedValue value == "true")
  expectValue "transfinite addition" ((AST.+) (...) (natural 0)) $ \value ->
    assert "the first transfinite formulation coerces to Infinity for addition"
      (renderInterpretedValue value == "Infinity")
  expectValue "transfinite multiplication" ((AST.*) (...) (...)) $ \value ->
    assert "the first transfinite formulation coerces to Infinity for multiplication"
      (renderInterpretedValue value == "Infinity")
  expectValue "transfinite exponentiation" ((AST.^) (...) (natural 2)) $ \value ->
    assert "the first transfinite formulation coerces to Infinity for exponentiation"
      (renderInterpretedValue value == "Infinity")
  testRemainingLiterals

testArgumentMaps :: IO ()
testArgumentMaps = do
  mapM_ (\source -> expectSourceValue source source $ \value ->
    assert "argument-map relation holds" (renderInterpretedValue value == "true"))
    [ "{} = ()"
    , "{2} = 2"
    , "{1; 2} = ((1; 2) | (2; 1))"
    , "{b := 8; 2} = {2; b := 8}"
    , "{b := 8; 2} of {a? : Nat := 2; b? : Nat}"
    , "{(1, 2); 3} = {3; (1, 2)}"
    , "{2; 2} = (2; 2)"
    , "{1; 2; 3} = {3; 1; 2}"
    , "{(1; 2); 3} = {3; (1; 2)}"
    , "{b := 8; 2} of {a? : Nat := 2; b? : Nat}"
    , "{2; b := 8} of {b? : Nat; a? : Nat}"
    , "{2; 8} of {a? : Nat; b? : Nat}"
    , "{a := 2; b := 8} of {a : Nat; b : Nat}"
    , "(2; 8) of {a : Nat; b : Nat}"
    , "{a? : Nat; b? : Nat} of {b? : Int; a? : Int}"
    , "{1; 2}[0] = (1 | 2)"
    , "\"(b : 8; 2)\" of \"%({a? : Nat; b? : Nat})\""
    ]
  mapM_ (\source -> expectSourceValue source source $ \value ->
    assert "invalid argument-map relation is rejected"
      (renderInterpretedValue value == "false"))
    [ "{c := 8; 2} of {a? : Nat; b? : Nat}"
    , "{b := $wrong; 2} of {a? : Nat; b? : Nat}"
    , "{2; 8} of {a : Nat; b : Nat}"
    , "{b := 8; b := 2} of {a? : Nat; b? : Nat}"
    , "{1; 2; 3} of {a? : Nat; b? : Nat}"
    ]
  expectSourceRejection
    "duplicate unnamed argument types have no distinct permutations"
    "($a, $b, 5) of {Int; Str; Str}"
    (== EitherAlternativesNotDistinct)
  expectSourceValue "written order wins over other valid permutations"
      "(1, 2) ~> {x : Int; y : Int}" $ \value ->
    assert "required names accept positional values in written order"
      (renderInterpretedValue value
        == "(1; 2) ~> {x : " <> sourceIntType
          <> "; y : " <> sourceIntType <> "}")
  expectSourceValue "a unique valid argument reorder is selected"
      "($a, 5) ~> {x : Int; y : IdenStr}" $ \value ->
    assert "the unique reordered presentation is retained"
      (renderInterpretedValue value
        == "($a; 5) ~> {x : " <> sourceIntType <> "; y : IdenStr}")
  let example = "{b : 8; 2} ~> {a? : Nat := 2; b? : Nat}"
  expectSourceValue "argument specification preserves written source" example $ \value ->
    assert "argument-map source order and partial names survive"
      (renderInterpretedValue value
        == "{b : 8; 2} ~> {a? : " <> sourceNatType
          <> " := 2; b? : " <> sourceNatType <> "}")
  expectSourceValue "argument specification source order reverses independently"
      "{2; b := 8} ~> {a? : Nat; b? : Nat}" $ \value ->
    assert "source order is not rewritten to match the target"
      (renderInterpretedValue value
        == "{2; b : 8} ~> {a? : " <> sourceNatType
          <> "; b? : " <> sourceNatType <> "}")
  expectSourceValue "ordered source can select an argument-map presentation"
      "((b := 8; 2) ~> {a? : Nat; b? : Nat})[1] * 5" $ \value ->
    assert "access follows the selected target permutation"
      (renderInterpretedValue value == "10")
  expectSourceValue "argument-map reverse specification"
      "{a? : Nat; b? : Nat} <~ {b := 8; 2}" $ \value ->
    assert "reverse specification preserves the same source"
      (renderInterpretedValue value
        == "{b : 8; 2} ~> {a? : " <> sourceNatType
          <> "; b? : " <> sourceNatType <> "}")
  expectSourceValue "widening reselects a reordered argument target"
      "(((b := 8; 2) ~> {a? : Nat; b? : Nat}) ~> {b? : Int; a? : Int})[1] * 5" $ \value ->
    assert "the widened witness still follows source order"
      (renderInterpretedValue value == "10")
  expectSourceValue "argument-family specification widens"
      "({b := 8; 2} ~> {a? : Nat; b? : Nat}) ~> {b? : Int; a? : Int}" $ \value ->
    assert "family widening retains the original source"
      (renderInterpretedValue value
        == "{b : 8; 2} ~> {b? : " <> sourceIntType
          <> "; a? : " <> sourceIntType <> "}")
  mapM_ (\source -> expectSourceValue
    ("argument rendering round trip: " <> source) source $ \value ->
    let rendered = renderInterpretedValue value
    in expectSourceValue ("rendered arguments remain equivalent: " <> rendered) rendered $ \roundTrip ->
      assert ("argument rendering is stable: " <> rendered
        <> " became " <> renderInterpretedValue roundTrip)
        (renderInterpretedValue roundTrip == rendered))
    [ example
    , "{b := 8; 2} ~> {a? : Nat := 2; b? : Nat}"
    , "{(1, 2); 3}"
    , "{(a : Nat; b : Nat); 3}"
    , "{(1 ~> Nat); b := 8}"
    ]
  expectSourceRejection "argument specification checks every supplied name"
    "{c := 8; 2} ~> {a? : Nat; b? : Nat}"
    (\case
      AtlasMapFederationOperationRefuted
        AtlasMapFederationSpecificationHasNoMatchingMember -> True
      _ -> False)

testArgumentMapConcatenation :: IO ()
testArgumentMapConcatenation = do
  let source = "x : 3, {b : 8; 2}"
      target = "x : 3, {a? : Nat := 2; b? : Nat}"
      example = source <> " ~> " <> target
      renderedExample =
        source <> " ~> x : 3, "
          <> "{a? : Nat := 2; b? : Nat}"
  mapM_ (\expression -> expectSourceValue expression expression $ \value -> do
    assert "concatenated specification preserves the supplied presentation"
      (renderInterpretedValue value == renderedExample)
    expectSourceValue "concatenated specification rendering round trip"
      (renderInterpretedValue value) $ \roundTrip ->
        assert "concatenated canonical output is stable"
          (renderInterpretedValue roundTrip == renderedExample))
    [ example, target <> " <~ " <> source ]
  mapM_ (\expression -> expectSourceValue expression expression $ \value ->
    assert "concatenated argument-map inclusion holds"
      (renderInterpretedValue value == "true"))
    [ source <> " of " <> target
    , "({b : 8; 2}, x : 3) of ({a? : Nat; b? : Nat}, x : 3)"
    , "x : 3, {a? : Nat; b? : Nat} of x : Int, {b? : Int; a? : Int}"
    ]
  mapM_ (\expression -> expectSourceValue expression expression $ \value ->
    let rendered = renderInterpretedValue value
    in expectSourceValue "distributed concatenation round trip" rendered $ \roundTrip ->
      assert "both sides and nested concatenations preserve their source"
        (renderInterpretedValue roundTrip == rendered))
    [ "{b : 8; 2}, x : 3 ~> {a? : Nat; b? : Nat}, x : Nat"
    , "x : 3, {b : 8; 2}, y : 4 ~> x : Nat, {a? : Nat; b? : Nat}, y : Nat"
    , "{b : 8; 2}, {d : 6; 4} ~> {a? : Nat; b? : Nat}, {c? : Nat; d? : Nat}"
    , "(" <> example <> ") ~> x : Int, {b? : Int; a? : Int}"
    ]
  expectSourceValue "one ordered presentation matches the ordered target"
    "x : 3, (b : 8; 2) ~> x : 3, (b : Nat; Nat)" $ \_ -> pure ()
  mapM_ (\expression -> expectSourceRejection
    ("every concatenated presentation must match: " <> expression) expression
    (\case
      AtlasMapFederationOperationRefuted
        AtlasMapFederationSpecificationHasNoMatchingMember -> True
      AtlasMapFederationOperationUndecidable
        (NoAtlasMapFederationDecisionProcedure AtlasMapFederationSpecification) -> True
      _ -> False))
    [ "x : 4, {b : 8; 2} ~> " <> target
    , "x : 3, {c : 8; 2} ~> " <> target
    , "x : 3, {b : $wrong; 2} ~> " <> target
    , source <> " ~> x : 3, (b : Nat; Nat)"
    ]

testArgumentMapTemplates :: IO ()
testArgumentMapTemplates = do
  let template = "\"%({a? : Nat; b? : Nat})\""
  mapM_ (\member -> expectSourceValue "template accepts an argument ordering"
    (show member <> " of " <> template) $ \value ->
      assert "canonical argument presentation belongs to the template"
        (renderInterpretedValue value == "true"))
    [ "(b : 8; 2)", "(2; b : 8)", "(2; 8)" ]
  mapM_ (\member -> expectSourceValue "template rejects incompatible arguments"
    (show member <> " of " <> template) $ \value ->
      assert "wrong names, types, and arities are outside the template"
        (renderInterpretedValue value == "false"))
    [ "(c : 8; 2)", "(b : $wrong; 2)", "(b : 8; 2; 3)" ]
  let member = "\"(b : 8; 2)\""
      specification = member <> " ~> " <> template
      renderedSpecification =
        member <> " ~> \"%({a? : Nat; b? : Nat})\""
  mapM_ (\expression -> expectSourceValue "template argument specification"
    expression $ \value ->
      assert "forward and reverse template specifications agree"
        (renderInterpretedValue value == renderedSpecification))
    [ specification, template <> " <~ " <> member ]
  expectSourceValue "template captures the typed argument map"
    ("%(" <> specification <> ")[1]") $ \value ->
      assert "capture retains the source ordering and target argument map"
        (renderInterpretedValue value
          == "(b : 8; 2) ~> "
            <> "{a? : Nat; b? : Nat}")
  expectSourceValue "argument template capture supports access and arithmetic"
    ("%(" <> specification <> ")[1][1] * 5") $ \value ->
      assert "captured unnamed argument remains numeric"
        (renderInterpretedValue value == "10")
  expectSourceValue "literal-delimited argument template"
    "\"args=(2; b : 8)!\" of \"args=%({a? : Nat; b? : Nat})!\"" $ \value ->
      assert "template literals surround the whole argument-map capture"
        (renderInterpretedValue value == "true")
  expectSourceValue "argument template assigns required names positionally"
    "\"(2; 8)\" of \"%({a : Nat; b : Nat})\"" $ \value ->
      assert "written order determines required-name template slots"
        (renderInterpretedValue value == "true")

testEval :: IO ()
testEval = do
  mapM_ (\(source, target, expected) ->
    expectInternalEvalValue source target $ \value ->
      assertEqual (source <> " decoded at " <> target)
        expected (renderInterpretedValue value))
    [ ( "\"12\""
      , "Int"
      , "12 ~> Int"
      )
    , ("\"alco\"", "IdenStr", "$alco ~> IdenStr")
    , ("\"hello world\"", "Str", "\"hello world\" ~> Str")
    , ( "(\"1\", \"2\")"
      , "Int"
      , "12 ~> Int"
      )
    , ( "\"x : 3, (b : 8; 2)\""
      , "x : 3; {a? : Nat := 2; b? : Nat}"
      , "x : 3, (b : 8; 2) ~> "
          <> "(x : 3; {a? : Nat := 2; b? : Nat})"
      )
    , ( "\"(2; 8)\""
      , "{a : Nat; b : Nat}"
      , "(2; 8) ~> {a : Nat; b : Nat}"
      )
    ]
  mapM_ (\(source, target) ->
    expectInternalEvalRejection source target
      (\case
        AtlasMapFederationOperationRefuted
          AtlasMapFederationSpecificationHasNoMatchingMember -> True
        AtlasMapFederationOperationUndecidable
          (NoAtlasMapFederationDecisionProcedure
            AtlasMapFederationSpecification) -> True
        _ -> False))
    [ ("\"nope\"", "Nat")
    , ("\"1 + 2\"", "Nat")
    , ("\"(c : 8; 2)\"", "{a? : Nat; b? : Nat}")
    , ("12", "Nat")
    ]

expectInternalEvalValue
  :: String
  -> String
  -> (InterpretedValue -> IO ())
  -> IO ()
expectInternalEvalValue source target check = do
  sourceExpression <- parseTestExpression source
  targetExpression <- parseTestExpression target
  sourceValue <- either (fail . show) pure
    (interpretExpressionReason sourceExpression)
  targetValue <- either (fail . show) pure
    (interpretExpressionReason targetExpression)
  stringType <- either (fail . show) pure
    (interpretExpressionReason
      (IdentifierReference (IdentifierString "Str")))
  either (fail . show) check
    (Types.evalValues canonicalStringCodec stringType sourceValue targetValue)

expectInternalEvalRejection
  :: String
  -> String
  -> (InterpretingError -> Bool)
  -> IO ()
expectInternalEvalRejection source target matches = do
  sourceExpression <- parseTestExpression source
  targetExpression <- parseTestExpression target
  case do
      sourceValue <- interpretExpressionReason sourceExpression
      targetValue <- interpretExpressionReason targetExpression
      stringType <- interpretExpressionReason
        (IdentifierReference (IdentifierString "Str"))
      Types.evalValues canonicalStringCodec stringType sourceValue targetValue of
    Left rejection
      | matches rejection -> pure ()
      | otherwise -> fail ("unexpected internal decode rejection: " <> show rejection)
    Right value ->
      fail ("internal decode unexpectedly produced " <> renderInterpretedValue value)

parseTestExpression :: String -> IO Expression
parseTestExpression source =
  case parseProductionSource ("(" <> source <> "\n)") of
    Left message -> fail
      ("test expression failed to parse: " <> parseFailureMessage message)
    Right expressionValue -> pure expressionValue

testBegin :: IO ()
testBegin = do
  expectSourceValue "retained block canonicalizes value lookup"
    "begin \"value with spaces\" : 5; yield this.\"value with spaces\"[1] + 1" $ \value -> do
      let rendered = renderInterpretedValue value
      assert "block uses the symbolic lookup operator"
        (rendered == "6 <~ begin \"value with spaces\" : 5; yield ~\"value with spaces\" + 1")
      expectSourceValue "canonical value lookup block round trip" rendered $ \decoded ->
        assert "canonical block remains stable"
          (renderInterpretedValue decoded == rendered)
  let example = "begin\n a : 2 * 3\n b : 5\nyield a + b"
  expectSourceValue "retained block" example $ \value -> do
    assert "the arithmetic result is eleven" (interpretedInteger value == Just 11)
    assert "the block remains in reverse-specification output"
      (renderInterpretedValue value == "11 <~ begin a : (2 * 3); b : 5; yield a + b")
    expectSourceValue "retained block output can be read again"
      (renderInterpretedValue value) $ \decoded ->
        assert "output preserves its value" (interpretedInteger decoded == Just 11)
  expectSourceValue "begin block is a total canonical type" "begin yield Nat" $ \value ->
    assert "block totality does not depend on the yielded federation"
      (Types.interpretedTypeIsTotal value)
  mapM_ (\(source, expected) -> expectSourceValue source source $ \value ->
    assert (source <> ": " <> renderInterpretedValue value)
      (Types.interpretedCanonicalResult value
        == Types.interpretedCanonicalResult (Types.booleanValue expected)))
    [ ("(begin yield 11) of (begin yield 11)", True)
    , ("11 of (begin yield 11)", True)
    , ("(begin yield 11) of 11", True)
    , ("(begin yield 11) = 11", True)
    , ("(begin x := 11 yield x) = (begin yield 11)", True)
    , ("12 of (begin yield 11)", False)
    , ("((begin yield 11) ~> (begin yield 11)) of (begin yield 11)", True)
    ]
  expectSourceValue "equal value specifies a begin block"
    "11 ~> (begin yield 11)" $ \value ->
      assert
        ("specification retains the block and yielded value: "
          <> renderInterpretedValue value)
        (renderInterpretedValue value == "11 <~ begin yield 11")
  expectSourceRejection "a different value cannot specify a begin block"
    "12 ~> (begin yield 11)"
    (\case
      AtlasMapFederationOperationRefuted
        AtlasMapFederationSpecificationHasNoMatchingMember -> True
      _ -> False)
  mapM_ (\(source, expected) -> expectSourceValue source source $ \value ->
    assert (source <> ": " <> renderInterpretedValue value)
      (interpretedInteger value == Just expected))
    [ ("begin a : 2 * 3; b : 5 yield a + b", 11)
    , ("begin bad : 1 + \"bad\" yield 11", 11)
    , ("begin a : x + 1; let x : 10 yield a", 11)
    , ("begin let x : 10 yield begin y : 1 yield x + y", 11)
    , ("begin a : Nat := 6; b : 5 yield a + b", 11)
    , ("begin a? : Nat := 6; b : 5 yield a + b", 11)
    , ("begin T : Nat; a : T := 6 yield a + 0", 6)
    , ("begin a : (begin b : 2 yield b + 1) yield a * 2", 6)
    , ("begin a : 1 yield begin a : 2 yield a", 2)
    , ("begin yield 11", 11)
    , ("(begin a : 6 yield a) + 5", 11)
    , ("begin T : Int yield %(\"12\" ~> \"%(T)\")[1] + 0", 12)
    , ("begin a : 6 yield %(\"%Nat\" <~ \"6\")[1] + a", 12)
    ]
  mapM_ (\source -> expectSourceValue source source $ \value ->
    assert (source <> ": " <> renderInterpretedValue value)
      (Types.interpretedCanonicalResult value == Types.interpretedCanonicalResult (Types.booleanValue True)))
    [ "(begin a : 6 yield a) of Nat"
    , "((begin a : 6 yield a) ~> Int) = (6 ~> Int)"
    , "(Int <~ (begin a : 6 yield a)) = (6 ~> Int)"
    , "(begin a? : Nat := 6 yield a) of Int"
    , "(begin T : Nat yield {b : 8; 2} ~> {a? : T := 2; b? : T}) of {b? : Int; a? : Int}"
    ]

testCanonicalTypes :: IO ()
testCanonicalTypes = do
  mapM_ expectCanonicalType
    [ "Any"
    , "Nat"
    , "Int"
    , "Str"
    , "IdenStr"
    , "Bool"
    , "(Nat; Int)"
    , "begin yield 11"
    , "Nat -> Nat"
    , "Nat | (Nat -> Nat)"
    , "Template"
    ]
  mapM_ expectNonCanonicalDatraType
    [ "!~\"datra.AST\""
    , "!~\"datra.Expr\""
    , "!~\"datra.Block\""
    , "NatRange"
    , "IntRange"
    , "NatValRange"
    , "IntValRange"
    , "(Nat; (!~\"datra.AST\"))"
    ]
  expectSourceValue "canonical function string capability" "Nat -> Nat" $ \value ->
    assert "functions carry a CanonicalType"
      (case Types.datraCanonicalType (Types.interpretedDatraType value) of
        Nothing -> False
        Just _ -> True)
  expectSourceValue "canonical begin block capability" "begin yield 11" $ \value -> do
    assert "a retained total block embeds a CanonicalType"
      (case Types.datraCanonicalType (Types.interpretedDatraType value) of
        Just _ -> True
        Nothing -> False)
    case Types.toStringValue canonicalStringCodec value of
      Left rejection ->
        fail ("canonical block conversion was rejected: " <> show rejection)
      Right rendered ->
        assert "canonical block conversion retains block and yielded value"
          (renderInterpretedValue rendered
            == "\"11 <~ begin yield 11\"")
  where
    expectCanonicalType source =
      expectSourceValue (source <> " is canonical") source $ \value ->
        assert (source <> " embeds the narrower CanonicalType")
          (case Types.datraCanonicalType
              (Types.interpretedDatraType value) of
            Just _ -> True
            Nothing -> False)
    expectNonCanonicalDatraType source =
      expectSourceValue (source <> " is noncanonical") source $ \value ->
        assert (source <> " is a DatraType without a CanonicalType")
          (case Types.datraCanonicalType
              (Types.interpretedDatraType value) of
            Nothing -> True
            Just _ -> False)

testPrograms :: IO ()
testPrograms = do
  mapM_ (\(source, expected) ->
    case parseProductionSource source of
      Left message -> fail (parseFailureMessage message)
      Right expression -> expectValue source expression $ \value ->
        assert (source <> ": " <> renderInterpretedValue value)
          (renderInterpretedValue value == expected))
    [ ("a := 2 * 3\nb := 5\nyield a + b", "11")
    , ("a : 2 * 3\nb : 8\nyield a + b", "14")
    , ("a : 2 * 3\nb : 5", "()")
    , ("", "()")
    , ("2 + 3", "()")
    , ("# comment\n(2 + 3) # trailing comment", "5")
    , ("yield (1; 2)", "(1; 2)")
    , ("(2 + 3)", "5")
    , ("yield begin a : 6 yield a + 5", "11")
    , ("a : x + 1\nlet x : 10\nyield a", "11")
    ]

testBeginRejections :: IO ()
testBeginRejections = do
  mapM_ (\source -> expectSourceRejection source source
    (\case IdentifierStringOverlap "a" -> True; _ -> False))
    [ "begin a : 1; a : 2 yield a"
    , "begin a : 1; let a : 2 yield a"
    , "begin a? : Nat := 1; a : 2 yield a"
    ]
  mapM_ (\source -> expectSourceRejection source source
    (\case UnknownIdentifier _ -> True; _ -> False))
    [ "begin yield missing"
    , "begin a : b + 1; b : 5 yield a"
    , "begin let x : y + 1; y : 9 yield x"
    , "begin a : a yield a"
    , "begin a : b; b : a yield a"
    , "begin (a : 1; b : 2) yield a"
    , "begin {a : 1; b : 2} yield a"
    , "begin let (a : 1; b : a) yield 0"
    , "begin let {a : 1; b : a} yield 0"
    , "begin a : b yield begin b : 2 yield a"
    , "(begin a : 2 yield a), (begin yield a)"
    ]
  expectSourceRejection "unused let must be evaluated"
    "begin let bad : 1 + \"bad\" yield 11" (const True)
  expectSourceRejection "let annotation checked before yield"
    "begin let a : Nat := \"bad\" yield 11" (const True)

testEvalBackedKeywords :: IO ()
testEvalBackedKeywords = do
  mapM_ (\(source, expected) -> expectSourceValue source source $ \value ->
    assert (source <> " rendered as " <> renderInterpretedValue value)
      (renderInterpretedValue value == expected))
    [ ("from 2 to 5", "from 2 to 5")
    , ("from -3 to 4", "from -3 to 4")
    , ("from 5 to 2", "from 5 to 2")
    , ("from 2 up", "from 2 up")
    , ("from -2 up", "from -2 up")
    , ("from 2 down", "from 2 down")
    , ("range 2 to 5", "range 2 to 5")
    , ("range -3 to 4", "range -3 to 4")
    , ("range 5 to 2", "range 5 to 2")
    , ("range -2 up", "range -2 up")
    , ("range 2 down", "range 2 down")
    , ("from -3 to # normalized source trivia\n4", "from -3 to 4")
    , ("if (true ~> Bool) then 7 else (1 and false)", "7")
    , ("if false then (1 and false) else 9", "9")
    , ("if false then (1 and false)", "()")
    , ("if true then (if false then (1 and false) else 4) else (1 and false)", "4")
    , ( "%(\"from 2 to 5\" ~> \"from %Int to %Int\")[1]"
      , "2 ~> Int"
      )
    , ( "%(\"from 2 to 5\" ~> \"from %Int to %Int\")[2]"
      , "5 ~> Int"
      )
    , ( "%(\"range -3 down\" ~> \"range %Int down\")[1]"
      , "-3 ~> Int"
      )
    , ("%(\"if true then\" ~> \"if %Bool then\")[1]", "true ~> Bool")
    ]
  mapM_ (\source -> expectSourceValue source source $ \value ->
    assert ("keyword forms compose with identifiers, specification, and inclusion: " <> source)
      (renderInterpretedValue value == "true"))
    [ "(2 ~> from 0 to 5) of from -1 to 8"
    , "(from 0 to 5 <~ 2) = (2 ~> from 0 to 5)"
    , "(2..3 ~> range 0 to 5) of range 0 to 8"
    , "(range 0 to 5 <~ 2..3) = (2..3 ~> range 0 to 5)"
    , "(2, b : 5) of (a? : from 0 to 8, b? : from 0 to 8)"
    , "%(\"(b : 5; 2)\" ~> \"%({a? : from 0 to 8; b? : from 0 to 8})\")[1] of {b? : Int; a? : Int}"
    , "(if true then 2 else (1 and false)) of from 0 to 5"
    , "((if false then (1 and false) else 2) ~> from 0 to 5) of Int"
    , "(from 0 to 5 <~ (if true then 2 else (1 and false))) = (2 ~> from 0 to 5)"
    , "(if true then (b? : from 0 to 5 := 2) else (1 and false)) of (b? : Int)"
    ]
  expectSourceRejection "keyword schema rejects an invalid bound"
    "\"from nope to 5\" ~> \"from %Int to %Int\""
    (\case
      AtlasMapFederationOperationRefuted
        AtlasMapFederationSpecificationHasNoMatchingMember -> True
      _ -> False)
  expectSourceRejection "keyword schema rejects an invalid condition"
    "\"if 1 then\" ~> \"if %Bool then\""
    (\case
      AtlasMapFederationOperationRefuted
        AtlasMapFederationSpecificationHasNoMatchingMember -> True
      _ -> False)

testSlotOrdinalDistinctness :: IO ()
testSlotOrdinalDistinctness = do
  let coalizedString = Coalization AST.stringType
      importAllDomain = AtlasMap
        [AsciiStringLiteral "all", coalizedString]
      unitFunction domain = FunctionType domain (AtlasMap [])
  assert "different exact slot ordinals distinguish function alternatives"
    (case interpretExpressionReason
        (EitherType
          (unitFunction importAllDomain)
          (unitFunction coalizedString)) of
      Right _ -> True
      Left _ -> False)

testStringTemplates :: IO ()
testStringTemplates = do
  case interpretExpressionReason
      (SyntaxType (Extract (AsciiStringLiteral "choose $Int mark"))
        (FunctionType IntegerType IntegerType)) of
    Right value -> do
      assert "syntax annotations are erased from canonical function rendering"
        (renderInterpretedValue value == "(Int -> Int)")
      assert "evaluated function types retain their structured syntax attachment"
        (case Types.interpretedFunction value >>= Types.functionSyntax of
          Just (FunctionSyntax
            [ SyntaxTemplate
                [ SyntaxLiteral "choose"
                , SyntaxHole (ValueSyntaxHole _)
                , SyntaxLiteral "mark"
                ]]) -> True
          _ -> False)
    Left failure -> assertFailure
      ("syntax function type failed to evaluate: " <> show failure)
  assert "an Int syntax hole rejects the Infinity AST through template membership"
    (not (matchesValueSyntaxHoleWith
      interpretExpressionReason
      (ValueSyntaxHole (identifierReference "Int"))
      (IdentifierReference (IdentifierString "Infinity"))))
  assert "an IntLimit syntax hole accepts the Infinity AST through template membership"
    (matchesValueSyntaxHoleWith
      interpretExpressionReason
      (ValueSyntaxHole (identifierReference "IntLimit"))
      (IdentifierReference (IdentifierString "Infinity")))
  let valueHole = SyntaxHole . ValueSyntaxHole
      syntaxRule targetKind implementation = SyntaxRule
        { syntaxName = "from"
        , syntaxTemplate = SyntaxTemplate
            [ SyntaxLiteral "from"
            , valueHole (identifierReference "Int")
            , SyntaxLiteral "to"
            , valueHole targetKind
            ]
        , syntaxSignature = FunctionType
            (AtlasMap [IntegerType, IdentifierReference
              (IdentifierString "IntLimit")])
            (IdentifierReference (IdentifierString "IntValRange"))
        , syntaxRecursive = False
        , syntaxModule = Nothing
        , syntaxImplementation =
            External (AsciiStringLiteral implementation)
        }
      fromInfinity = foldl FunctionApplication
        (IdentifierReference (IdentifierString "from"))
        [ EllipsisNatural 0
        , IdentifierReference (IdentifierString "to")
        , IdentifierReference (IdentifierString "Infinity")
        ]
      matchesHole = matchesValueSyntaxHoleWith interpretExpressionReason
  assert "the AST matcher rejects Infinity from an incorrectly declared Int hole"
    (matchSingleRule matchesHole
      (syntaxRule (identifierReference "Int") "datra.wrong-from")
      fromInfinity
      == Left NoMatchingSyntaxTemplate)
  assert "the AST matcher accepts Infinity from the declared IntLimit hole"
    (case matchSingleRule matchesHole
        (syntaxRule (identifierReference "IntLimit") "datra.from")
        fromInfinity of
      Right _ -> True
      Left _ -> False)
  let overlappingRule holeKind implementation = SyntaxRule
        { syntaxName = "choose"
        , syntaxTemplate = SyntaxTemplate
            [ SyntaxLiteral "choose"
            , valueHole holeKind
            , SyntaxLiteral "mark"
            ]
        , syntaxSignature = FunctionType
            holeKind
            IntegerType
        , syntaxRecursive = False
        , syntaxModule = Nothing
        , syntaxImplementation =
            External (AsciiStringLiteral implementation)
        }
  assert "overlapping Nat and Int templates are rejected before AST matching"
    (case compileSyntaxTemplateFederation
        (\_ _ -> AtlasMapFederationRefuted ())
        [ overlappingRule (identifierReference "Nat") "datra.choose-nat"
        , overlappingRule (identifierReference "Int") "datra.choose-int"
        ] of
      Left failure -> failure == OverlappingSyntaxTemplates
        "choose $Nat mark" "choose $Int mark"
      Right _ -> False)
  expectSourceValue
      "Int template excludes Infinity"
      "\"Infinity\" of \"%Int\"" $ \value ->
    assert "Infinity is not an Int template member"
      (renderInterpretedValue value == "false")
  expectSourceValue
      "IntLimit template includes Infinity"
      "\"Infinity\" of \"%IntLimit\"" $ \value ->
    assert "Infinity is an IntLimit template member"
      (renderInterpretedValue value == "true")
  expectSourceValue
      "surface arithmetic interpolation equality"
      "\"2 + 2 = %(2+2)\" = \"2 + 2 = 4\"" $ \value ->
    assert "the interpolated arithmetic result equals the expected string"
      (renderInterpretedValue value == "true")
  expectSourceValue
      "IdenStr template accepts a compact-string value"
      "\"My name is alco\" ~> \"My name is %IdenStr\"" $ \value ->
    assert "a compact name matches IdenStr"
      ( interpretedValueKind value == SpecificationValueKind
        && renderInterpretedValue value
          == "\"My name is alco\" ~> \"My name is %IdenStr\""
      )
  expectSourceRejection
    "IdenStr template rejects whitespace within the captured value"
    "\"My name is whatever you call me\" ~> \"My name is %IdenStr\""
    (\case
      AtlasMapFederationOperationRefuted
        AtlasMapFederationSpecificationHasNoMatchingMember -> True
      _ -> False)
  expectSourceValue
      "IdenStr accepts a digit-leading alphanumeric value"
      "\"345abc\" ~> \"%IdenStr\"" $ \value ->
    assert "a digit-leading nonnumeric compact string matches IdenStr"
      (interpretedValueKind value == SpecificationValueKind)
  expectSourceRejection
    "IdenStr rejects an entirely numeric string"
    "\"12\" ~> \"%IdenStr\""
    (\case
      AtlasMapFederationOperationRefuted
        AtlasMapFederationSpecificationHasNoMatchingMember -> True
      _ -> False)
  expectSourceValue
      "a space separates adjacent IdenStr interpolations"
      "\"name alco\" ~> \"%IdenStr %IdenStr\"" $ \value ->
    assert "the separated identifier values are selected uniquely"
      ( interpretedValueKind value == SpecificationValueKind
        && renderInterpretedValue value
          == "\"name alco\" ~> \"%IdenStr %IdenStr\""
      )
  expectSourceRejection
    "adjacent IdenStr interpolations are ambiguous"
    "\"%IdenStr%IdenStr\""
    (\case
      AmbiguousStringTemplate -> True
      _ -> False)
  expectSourceValue
      "numeric template with an apostrophe suffix"
      "$12' of \"%(Nat)'\"" $ \value ->
    assert "the compact string belongs to the suffixed Nat template"
      (renderInterpretedValue value == "true")
  expectSourceValue
      "plain identifier value belongs to an optional identifier template"
      "\"my name is alco\" of \"my name is %(ie? : IdenStr)\"" $ \value ->
    assert "the missing-name branch renders the plain identifier value"
      (renderInterpretedValue value == "true")
  expectSourceValue
      "canonical optional assignment belongs to its string template"
      ( "\"my name is (ie? : IdenStr := $alco)\" of "
          <> "\"my name is %(ie? : IdenStr)\""
      ) $ \value ->
    assert "the present-name branch renders its canonical assignment"
      (renderInterpretedValue value == "true")
  expectSourceValue
      "noncanonical assignment spelling is outside the template"
      ( "\"my name is (ie := $alco)\" of "
          <> "\"my name is %(ie? : IdenStr)\""
      ) $ \value ->
    assert "only the optional canonical assignment spelling is accepted"
      (renderInterpretedValue value == "false")
  expectSourceValue
      "simple identifier type has an injective string conversion"
      "\"ie : 12\" of \"%(ie : Nat)\"" $ \value ->
    assert "a direct simple identifier member is decoded canonically"
      (renderInterpretedValue value == "true")
  expectValue
      "map containing a simple identifier type is injective"
      (AST.subfederation
        (AsciiStringLiteral "(ie : 12; $alco)")
        (StringTemplate
          [StringTemplateInterpolation
            (MapSequence
              [ IdentifierOperation
                  (IdentifierString "ie") NaturalType Nothing
              , IdentifierValueType
              ])])) $ \value ->
    assert "the canonical map member is decoded componentwise"
      (renderInterpretedValue value == "true")
  expectSourceValue
      "Either containing a simple identifier type is injective"
      "\"ie : 12\" of \"%(ie : Nat | IdenStr)\"" $ \value ->
    assert "the simple identifier alternative is decoded canonically"
      (renderInterpretedValue value == "true")
  expectSourceValue
      "other branch beside a simple identifier type remains injective"
      "\"alco\" of \"%(ie : Nat | IdenStr)\"" $ \value ->
    assert "the string-valued alternative retains identity conversion"
      (renderInterpretedValue value == "true")
  expectSourceValue
      "extract returns the source string and typed template holes"
      "%(\"%IdenStr %Int\" <~ \"alco 100\")" $ \value ->
    assert "extract follows the retained string-template selection witness"
      ( renderInterpretedValue value
          == "(\"alco 100\"; $alco ~> IdenStr; "
            <> "100 ~> Int)"
      )
  expectSourceValue
      "extract forgets a simple identifier assignment wrapper"
      "%(a : \"%IdenStr %Int\" := \"alco 100\")" $ \value ->
    assert "identifier extraction matches direct specification extraction"
      ( renderInterpretedValue value
          == "(\"alco 100\"; $alco ~> IdenStr; "
            <> "100 ~> Int)"
      )
  expectSourceValue
      "extract index zero selects the original string"
      "%(my_val : \"%IdenStr %Int\" := \"alco 100\") [0]" $ \value ->
    assert "the first extracted component is always the source string"
      (renderInterpretedValue value == "\"alco 100\"")
  expectSourceValue
      "extract index one selects the IdenStr hole"
      "%(my_val : \"%IdenStr %Int\" := \"alco 100\") [1]" $ \value ->
    assert "the second extracted component is the first typed hole"
      (renderInterpretedValue value == "$alco ~> IdenStr")
  expectSourceValue
      "extract index two selects the Int hole"
      "%(my_val : \"%IdenStr %Int\" := \"alco 100\") [2]" $ \value ->
    assert "the third extracted component is the second typed hole"
      (renderInterpretedValue value
        == "100 ~> Int")
  expectSourceValue
      "extracted numerical specifications participate in arithmetic"
      "%(my_val : \"%IdenStr %Int\" := \"alco 12\") [2] * 5 = 60" $ \value ->
    assert "a specification with a valued-range target coerces to its source"
      (renderInterpretedValue value == "true")
  expectSourceValue
      "extract treats a literal template as one Str hole"
      "%(\"hello world\" <~ \"hello world\")" $ \value ->
    assert "a holeless template retains its source and synthesized hole"
      ( renderInterpretedValue value
          == "(\"hello world\"; \"hello world\" ~> Str)"
      )
  expectSourceValue
      "extract treats percent Str as the whole-string hole"
      "%(\"%Str\" <~ \"hello world\")" $ \value ->
    assertEqual "Str extraction retains its declarative canonical target"
      "(\"hello world\"; \"hello world\" ~> Str)"
      (renderInterpretedValue value)
  expectSourceValue
      "extract maps pointwise over a sequence of templates"
      "%(\"left\"; \"right\")" $ \value ->
    assert "each template retains its ordinary extraction result"
      ( renderInterpretedValue value
          == "(($left; $left ~> Str); ($right; $right ~> Str))"
      )
  let template = StringTemplate
        [ StringTemplateLiteral "example"
        , StringTemplateInterpolation
            (Addition (natural 2) (natural 2))
        ]
  expectValue "arithmetic interpolation" template $ \value ->
    assert "a fully total template collapses to one ASCII string"
      ( interpretedValueKind value == AsciiStringValueKind
        && Types.interpretedValueHasTotalMap value
        && renderInterpretedValue value == "$example4"
      )
  expectValue
      "numeric interpolation"
      (StringTemplate [StringTemplateInterpolation (natural 4)]) $ \value ->
    assert "numeric interpolation produces a string rather than an integer"
      ( interpretedValueKind value == AsciiStringValueKind
        && interpretedInteger value == Nothing
        && renderInterpretedValue value == "\"4\""
      )
  expectValue
      "negative interpolation"
      (StringTemplate
        [StringTemplateInterpolation (Minus (natural 10))]) $ \value ->
    assert "compound signed values retain their canonical minus spelling"
      ( interpretedValueKind value == AsciiStringValueKind
        && renderInterpretedValue value == "\"-10\""
      )
  expectValue
      "string interpolation"
      (StringTemplate
        [ StringTemplateLiteral "hello, "
        , StringTemplateInterpolation (AsciiStringLiteral "world")
        , StringTemplateLiteral "!"
        ]) $ \value ->
    assert "toString strips the interpolated string's source delimiter"
      (renderInterpretedValue value == "\"hello, world!\"")
  expectValue
      "empty string interpolation"
      (StringTemplate
        [ StringTemplateLiteral "left"
        , StringTemplateInterpolation (AsciiStringLiteral "")
        , StringTemplateLiteral "right"
        ]) $ \value ->
    assert "empty interpolated strings are concatenation identities"
      (renderInterpretedValue value == "$leftright")
  expectValue
      "map interpolation"
      (StringTemplate
        [StringTemplateInterpolation
          (AtlasMap [natural 1, natural 2])]) $ \value ->
    assert "total maps use their canonical pretty spelling"
      (renderInterpretedValue value == "\"(1; 2)\"")
  expectValue
      "Boolean interpolation"
      (StringTemplate
        [StringTemplateInterpolation (BooleanLiteral True)]) $ \value ->
    assert "non-string total values use canonical source text"
      (renderInterpretedValue value == "$true")
  expectValue
      "single non-total interpolation"
      (StringTemplate
        [StringTemplateInterpolation NaturalType]) $ \value ->
    assert "a non-total hole remains a non-total string federation"
      ( interpretedValueKind value == AsciiStringValueKind
        && not (Types.interpretedValueHasTotalMap value)
        && renderInterpretedValue value == "\"%(from 0 up)\""
      )
  expectValue
      "fixed prefix and suffix around a non-total interpolation"
      (StringTemplate
        [ StringTemplateLiteral "n="
        , StringTemplateInterpolation NaturalType
        , StringTemplateLiteral "."
        ]) $ \value ->
    assert "singletons concatenate with a non-total string federation"
      ( interpretedValueKind value == AsciiStringValueKind
        && not (Types.interpretedValueHasTotalMap value)
      )
  expectValue
      "delimiter-separated non-total interpolations"
      (StringTemplate
        [ StringTemplateInterpolation NaturalType
        , StringTemplateLiteral ":"
        , StringTemplateInterpolation NaturalType
        ]) $ \value ->
    assert "a delimiter excluded from Nat establishes a unique boundary"
      ( interpretedValueKind value == AsciiStringValueKind
        && not (Types.interpretedValueHasTotalMap value)
      )
  let separatedNaturals =
        StringTemplate
          [ StringTemplateInterpolation NaturalType
          , StringTemplateLiteral ":"
          , StringTemplateInterpolation NaturalType
          ]
  expectValue
      "\"12:3\" ~> \"%Nat:%Nat\" terminates"
      (AsciiStringLiteral "12:3" ~> separatedNaturals) $ \value ->
    assert "a concrete delimited string selects both natural fields"
      ( interpretedValueKind value == SpecificationValueKind
        && renderInterpretedValue value
          == "\"12:3\" ~> \"%(from 0 up):%(from 0 up)\""
      )
  assert "an invalid natural field is finitely refuted"
    (case interpretExpressionReason
        (AsciiStringLiteral "12:x" ~> separatedNaturals) of
      Left
          (AtlasMapFederationOperationRefuted
            AtlasMapFederationSpecificationHasNoMatchingMember) -> True
      _ -> False)
  expectValue
      "matching delimited string-template subfederation"
      (AST.subfederation separatedNaturals separatedNaturals) $ \value ->
    assert "string-template inclusion follows the same component structure"
      (renderInterpretedValue value == "true")
  expectValue
      "delimited string template is a Str subfederation"
      (AST.subfederation separatedNaturals AST.stringType) $ \value ->
    assert "every member produced by the template is a string"
      (renderInterpretedValue value == "true")
  let booleanTemplate =
        StringTemplate [StringTemplateInterpolation BooleanType]
      adjacentBooleans =
        StringTemplate
          [ StringTemplateInterpolation BooleanType
          , StringTemplateInterpolation BooleanType
          ]
      optionalIntegerTemplate =
        StringTemplate
          [StringTemplateInterpolation (maybeType IntegerType)]
  expectValue
      "\"true\" ~> \"%Bool\""
      (AsciiStringLiteral "true" ~> booleanTemplate) $ \value ->
    assert "a Boolean canonical spelling selects its Boolean member"
      ( interpretedValueKind value == SpecificationValueKind
        && renderInterpretedValue value == "$true ~> \"%Bool\""
      )
  expectValue
      "\"falsetrue\" ~> \"%Bool%Bool\""
      (AsciiStringLiteral "falsetrue" ~> adjacentBooleans) $ \value ->
    assert "adjacent fixed Boolean spellings have a unique split"
      ( interpretedValueKind value == SpecificationValueKind
        && renderInterpretedValue value
          == "$falsetrue ~> \"%Bool%Bool\""
      )
  expectValue
      "\"nothing\" ~> \"%(Maybe Int)\""
      (AsciiStringLiteral "nothing" ~> optionalIntegerTemplate) $ \value ->
    assert
      ("the optional missing constructor selects through toString: got "
        <> renderInterpretedValue value)
      ( interpretedValueKind value == SpecificationValueKind
        && renderInterpretedValue value
          == "$nothing ~> \"%(Maybe Int)\""
      )
  expectValue
      "non-digit delimiter between natural interpolations"
      (StringTemplate
        [ StringTemplateInterpolation NaturalType
        , StringTemplateLiteral "-"
        , StringTemplateInterpolation NaturalType
        ]) $ \value ->
    assert "a dash also cannot occur in Nat's rendered members"
      (not (Types.interpretedValueHasTotalMap value))
  expectValue
      "natural then arbitrary string separated by a delimiter"
      (StringTemplate
        [ StringTemplateInterpolation NaturalType
        , StringTemplateLiteral ":"
        , StringTemplateInterpolation AST.stringType
        ]) $ \value ->
    assert "a delimiter excluded from the left side fixes the first split"
      (not (Types.interpretedValueHasTotalMap value))
  expectValue
      "arbitrary string then natural separated by a delimiter"
      (StringTemplate
        [ StringTemplateInterpolation AST.stringType
        , StringTemplateLiteral ":"
        , StringTemplateInterpolation NaturalType
        ]) $ \value ->
    assert "a delimiter excluded from the right side fixes the final split"
      (not (Types.interpretedValueHasTotalMap value))
  assert "a possible natural digit is not a safe delimiter"
    (case interpretExpressionReason
        (StringTemplate
          [ StringTemplateInterpolation NaturalType
          , StringTemplateLiteral "1"
          , StringTemplateInterpolation NaturalType
          ]) of
      Left AmbiguousStringTemplate -> True
      _ -> False)
  expectValue
      "three delimiter-separated non-total interpolations"
      (StringTemplate
        [ StringTemplateInterpolation NaturalType
        , StringTemplateLiteral ":"
        , StringTemplateInterpolation NaturalType
        , StringTemplateLiteral ":"
        , StringTemplateInterpolation NaturalType
        ]) $ \value ->
    assert "the final-delimiter proof composes for repeated fields"
      (not (Types.interpretedValueHasTotalMap value))
  expectValue
      "nested non-total string template interpolation"
      (StringTemplate
        [StringTemplateInterpolation
          (StringTemplate
            [ StringTemplateLiteral "n="
            , StringTemplateInterpolation NaturalType
            ])]) $ \value ->
    assert "toString is identity on an already converted template federation"
      ( interpretedValueKind value == AsciiStringValueKind
        && not (Types.interpretedValueHasTotalMap value)
      )
  assert "adjacent Nat interpolations have a dedicated ambiguity error"
    (case interpretExpressionReason
        (StringTemplate
          [ StringTemplateInterpolation NaturalType
          , StringTemplateInterpolation NaturalType
          ]) of
      Left AmbiguousStringTemplate -> True
      _ -> False)
  assert "adjacent Str interpolations are ambiguous"
    (case interpretExpressionReason
        (StringTemplate
          [ StringTemplateInterpolation AST.stringType
          , StringTemplateInterpolation AST.stringType
          ]) of
      Left AmbiguousStringTemplate -> True
      _ -> False)
  assert "a delimiter cannot disambiguate arbitrary Str values"
    (case interpretExpressionReason
        (StringTemplate
          [ StringTemplateInterpolation AST.stringType
          , StringTemplateLiteral ":"
          , StringTemplateInterpolation AST.stringType
          ]) of
      Left AmbiguousStringTemplate -> True
      _ -> False)
  case (Types.naturalTypeValue, Types.asciiStringValue "1") of
    (Right naturals, Right oneString) -> do
      let dependentIdentifier =
            Types.dependentIdentifierTypeValue "n" (const "same") naturals
      assert "widest dependent identifier type is weakToString-only"
        (Types.datraStringRepresentation
          (Types.interpretedDatraType dependentIdentifier)
            == Types.WeakStringRepresentation)
      assert "widest dependent identifier is not a CanonicalType"
        (case Types.datraCanonicalType
            (Types.interpretedDatraType dependentIdentifier) of
          Nothing -> True
          Just _ -> False)
      assert "dependent identifier type has no proven injective toString"
        (case Types.toStringValue
            canonicalStringCodec dependentIdentifier of
          Left NonInjectiveStringInterpolation -> True
          _ -> False)
      case Types.weakToStringValue
          canonicalStringCodec dependentIdentifier of
        Left rejection ->
          fail
            ("dependent weakToString was rejected: " <> show rejection)
        Right weakConversion -> do
          assert "dependent identifier type retains the explicit weak marker"
            (renderInterpretedValue weakConversion
              == "\"%!(n : from 0 up)\"")
          assert "dependent weakToString is rejected by specification"
            (case Types.specifyValues oneString weakConversion of
              Left NoCanonicalStringConversion -> True
              _ -> False)
    (Left rejection, _) ->
      fail ("Nat construction was rejected: " <> show rejection)
    (_, Left rejection) ->
      fail ("string construction was rejected: " <> show rejection)
  expectValue
      "weak interpolation normalizes when toString is injective"
      (StringTemplate [StringTemplateWeakInterpolation NaturalType]) $ \value ->
    assert "the proven strong form is canonical"
      (renderInterpretedValue value == "\"%(from 0 up)\"")
  expectValue
      "weak and strong interpolation agree when toString is injective"
      (AST.equal
        (StringTemplate [StringTemplateWeakInterpolation NaturalType])
        (StringTemplate [StringTemplateInterpolation NaturalType])) $ \value ->
    assert "%!x equals %x when the strong proof exists"
      (renderInterpretedValue value == "true")
  expectValue
      "interpolated output is not reparsed"
      (StringTemplate
        [ StringTemplateInterpolation (AsciiStringLiteral "$4")
        , StringTemplateInterpolation (AsciiStringLiteral "#text")
        ]) $ \value ->
    assert "dollar and hash characters produced by holes remain data"
      (renderInterpretedValue value == "\"$4\\#text\"")
  expectValue "programmatic empty template" (StringTemplate []) $ \value ->
    assert "an empty template is the empty total ASCII string"
      ( Types.interpretedValueHasTotalMap value
        && renderInterpretedValue value == "\"\""
      )
  assert "errors raised inside a hole are not reported as ambiguity"
    (case interpretExpressionReason
        (StringTemplate
          [StringTemplateInterpolation
            (Addition (AsciiStringLiteral "x") (natural 1))]) of
      Left (ExpectedFiniteIntegerOperand LeftOperand AsciiStringValueKind) -> True
      _ -> False)

testRemainingLiterals :: IO ()
testRemainingLiterals = do
  expectValue
      "zero ordinal exponent"
      (ordinalExponent (...) (natural 0)) $ \value ->
    assert "an ordinal to zero evaluates to one"
      (renderInterpretedValue value == "1")
  expectValue
      "second ordinal exponent"
      (ordinalExponent (...) (natural 2)) $ \value ->
    assert "ordinal exponentiation returns an explicit ordinal"
      (renderInterpretedValue value == "... ^ 2 + 0")
  expectValue
      "ordinal multiplication order"
      (ordinalProduct
        (ordinalSum (...) (natural 1))
        (natural 2)) $ \value ->
    assert "ordinal multiplication preserves noncommutative order"
      (interpretedExplicitOrdinal value
        == Just (2, ordinal [2, 1]))

testBooleansAndEither :: IO ()
testBooleansAndEither = do
  expectValue "False literal" (AST.boolean False) $ \value ->
    assert "False is the named zero map"
      ( interpretedValueKind value == BooleanValueKind
        && renderInterpretedValue value == "false"
      )
  expectValue "Boolean type" AST.booleanType $ \value ->
    assert "the exact Boolean federation restores its shorthand"
      ( renderInterpretedValue value == "Bool"
        && interpretedValueKind value == EitherValueKind
      )
  expectValue
      "Boolean numerical coercion"
      (AST.equal
        ((AST.+) (AST.boolean True) (AST.boolean True))
        (natural 2)) $ \value ->
    assert "true + true follows the shared named-value coercion to 2"
      (renderInterpretedValue value == "true")
  expectValue
      "surface Boolean definition"
      (AST.equal
        AST.booleanType
        (AST.eitherType
          (AST.assignment "False" (natural 0) (natural 0))
          (AST.assignment "True" (natural 1) (natural 1)))) $ \value ->
    assert "Bool is definitionally False : 0 | True : 1"
      (renderInterpretedValue value == "true")
  expectValue
      "Boolean specification"
      (AST.boolean False ~> AST.booleanType) $ \value ->
    assert "Boolean alternatives use ordinary federation specification"
      (renderInterpretedValue value
        == "false ~> Bool")
  expectValue
      "Boolean conjunction"
      (AST.and (AST.boolean True) (AST.boolean False)) $ \value ->
    assert "True and False is False"
      (renderInterpretedValue value == "false")
  expectValue
      "Boolean disjunction"
      (AST.or (AST.boolean False) (AST.boolean True)) $ \value ->
    assert "False or True is True"
      (renderInterpretedValue value == "true")
  expectValue "Boolean negation" (AST.not (AST.boolean False)) $ \value ->
    assert "not False is True"
      (renderInterpretedValue value == "true")
  expectValue
      "canonical Boolean identifier values"
      (AST.and
        (AST.dependentIdentifierType "True" (natural 1))
        (AST.dependentIdentifierType "False" (natural 0))) $ \value ->
    assert "True : 1 and False : 0 retain Boolean behavior"
      (renderInterpretedValue value == "false")
  expectValue
      "equal federations"
      (AST.equal
        (AST.eitherType (natural 0) (natural 1))
        (AST.eitherType (natural 0) (natural 1))) $ \value ->
    assert "mutual subfederation is true"
      (renderInterpretedValue value == "true")
  expectValue
      "Either federation order is irrelevant"
      (AST.equal
        (AST.eitherType (natural 0) (natural 1))
        (AST.eitherType (natural 1) (natural 0))) $ \value ->
    assert "the same Atlas maps form the same federation in either order"
      (renderInterpretedValue value == "true")
  assert "Either rejects duplicate Atlas-map alternatives"
    (case interpretExpressionReason
        (AST.eitherType AST.naturalType AST.naturalType) of
      Left EitherAlternativesNotDistinct -> True
      _ -> False)
  assert "Either rejects a member overlapping a federation"
    (case interpretExpressionReason
        (AST.eitherType (natural 0) AST.naturalType) of
      Left EitherAlternativesNotDistinct -> True
      _ -> False)
  assert "Either rejects a nested duplicate alternative"
    (case interpretExpressionReason
        (AST.eitherType
          (AST.eitherType (natural 0) (natural 1))
          (natural 1)) of
      Left EitherAlternativesNotDistinct -> True
      _ -> False)
  expectValue
      "identifier alternatives distinguish otherwise equal types"
      (AST.eitherType
        (AST.dependentIdentifierType "x" AST.naturalType)
        (AST.dependentIdentifierType "y" AST.naturalType)) $ \value ->
    assert "identifier Atlas maps remain distinct federation members"
      (renderInterpretedValue value
        == "x : from 0 up | y : from 0 up")
  expectValue
      "disjoint primitive families form an Either federation"
      (AST.eitherType AST.naturalType AST.stringType) $ \value ->
    assert "numeric and string Atlas maps are distinguishable"
      (renderInterpretedValue value == "from 0 up | Str")
  case interpretExpressionReason
      (AST.eitherType
        (AST.dependentIdentifierType "x" (natural 0))
        (AST.dependentIdentifierType "x" AST.naturalType)) of
    Left failure -> assertEqual
      "the same identifier does not distinguish overlapping alternatives"
      EitherAlternativesNotDistinct failure
    Right value -> assertFailure
      ("overlapping alternatives unexpectedly produced "
        <> renderInterpretedValue value)
  expectValue
      "Either source branches are included as federation members"
      (AST.subfederation
        (AST.eitherType (natural 0) (natural 1))
        AST.naturalType) $ \value ->
    assert "a union is included when each alternative is in the target"
      (renderInterpretedValue value == "true")
  expectValue
      "associative Either"
      (AST.equal
        (AST.eitherType
          (AST.eitherType (natural 0) (natural 1))
          (natural 2))
        (AST.eitherType
          (natural 0)
          (AST.eitherType (natural 1) (natural 2)))) $ \value ->
    assert "Either association normalizes before subfederation comparison"
      (renderInterpretedValue value == "true")
  expectValue
      "Either subfederation widening"
      ( (natural 1
          ~> AST.eitherType (natural 0) (natural 1))
          ~> AST.eitherType
                (natural 0)
                (AST.eitherType (natural 1) (natural 2))
      ) $ \value ->
    assert "specification composes through a larger Either federation"
      (renderInterpretedValue value == "1 ~> (0 | 1 | 2)")
  assert "Boolean operators reject non-Booleans"
    (case interpretExpressionReason
        (AST.and (natural 1) (AST.boolean True)) of
      Left (ExpectedBooleanOperand LeftOperand NaturalValueKind) -> True
      _ -> False)

testOptionalsAndConditionals :: IO ()
testOptionalsAndConditionals = do
  let nothingValue =
        AST.assignment "Nothing" AST.emptyMap AST.emptyMap
      optionalIntegerSlots =
        MapConcatenation
          (AST.eitherType
            (AST.dependentIdentifierType "a" AST.integerType)
            AST.integerType)
          (AST.eitherType
            (AST.dependentIdentifierType "b" AST.integerType)
            AST.integerType)
      optionalAssigned identifierString value =
        AST.eitherType
          (AST.assignment
            identifierString AST.integerType (natural value))
          AST.integerType
      optionalIdentifier identifierString =
        AST.eitherType
          (AST.dependentIdentifierType identifierString AST.integerType)
          AST.integerType
  expectSourceValue
      "inferred assignment belongs to an optional IdenStr slot"
      "(ie := $alco) of (ie? : IdenStr)" $ \value ->
    assert "the inferred assignment widens through its identifier target"
      (renderInterpretedValue value == "true")
  expectSourceValue
      "canonical optional assignment belongs to its optional IdenStr slot"
      "(ie? : IdenStr := $alco) of (ie? : IdenStr)" $ \value ->
    assert "the optional assignment retains the present branch"
      (renderInterpretedValue value == "true")
  expectSourceValue
      "plain identifier value belongs to an optional IdenStr slot"
      "$alco of (ie? : IdenStr)" $ \value ->
    assert "the plain value selects the unnamed branch"
      (renderInterpretedValue value == "true")
  expectValue "Maybe Nat" (maybeType AST.naturalType) $ \value ->
    assert "Maybe evaluates to its source-defined federation"
      (renderInterpretedValue value == "Maybe (from 0 up)")
  expectValue
      "expanded optional equality"
      (AST.equal
        (maybeType AST.naturalType)
        (maybeExpansion AST.naturalType)) $ \value ->
    assert "optional syntax is definitionally its expanded federation"
      (renderInterpretedValue value == "true")
  expectValue
      "Nothing specification"
      (nothingValue ~> maybeType AST.naturalType) $ \value ->
    assert "absence selects the tagged optional alternative"
      (renderInterpretedValue value
        == "nothing ~> Maybe (from 0 up)")
  expectValue
      "canonical Nothing identifier"
      (AST.dependentIdentifierType "Nothing" AST.emptyMap
        ~> maybeType AST.naturalType) $ \value ->
    assert "Nothing : () round-trips as the distinguished absence"
      (renderInterpretedValue value
        == "nothing ~> Maybe (from 0 up)")
  expectValue
      "optional identifier"
      (AST.eitherType
        (AST.dependentIdentifierType "a" AST.naturalType)
        AST.naturalType) $ \value ->
    assert "a? : Nat includes the missing-identifier Nat branch"
      (renderInterpretedValue value == "a? : from 0 up")
  expectValue
      "positional values specify into optional identifier slots"
      ( MapConcatenation (natural 12) (natural 23)
          ~> optionalIntegerSlots
      ) $ \value ->
    assert "positional values canonicalize as optional assignments"
      (renderInterpretedValue value
        == "a? : Int := 12, b? : Int := 23")
  expectValue
      "named value specifies into its matching optional identifier slot"
      ( MapConcatenation
          (natural 12)
          (AST.assignment "b" (natural 23) (natural 23))
          ~> optionalIntegerSlots
      ) $ \value ->
    assert "named and positional values share assignment canonicalization"
      (renderInterpretedValue value
        == "a? : Int := 12, b? : Int := 23")
  expectValue
      "optional assignment reverse-specifies within a concatenation slot"
      (MapConcatenation
        (optionalAssigned "a" 12)
        (optionalAssigned "b" 23 ~> optionalIdentifier "b")) $ \value ->
    assert "the present optional branch supplies a concrete specification source"
      (renderInterpretedValue value
        == "a? : Int := 12, b? : Int := 23")
  expectValue
      "optional-slot specification equals its assigned federation"
      (AST.equal
        ( MapConcatenation
            (natural 12)
            (AST.dependentIdentifierType "b" (natural 23))
            ~> optionalIntegerSlots
        )
        (MapConcatenation
          (optionalAssigned "a" 12)
          (optionalAssigned "b" 23))) $ \value ->
    assert "specification wrappers preserve composite federation equality"
      (renderInterpretedValue value == "true")
  let optionalAssignmentSequence =
        AtlasMap [optionalAssigned "a" 12, optionalAssigned "b" 23]
      optionalAssignmentConcatenation =
        MapConcatenation
          (optionalAssigned "a" 12)
          (optionalAssigned "b" 23)
  expectValue
      "optional assignment sequence retains semicolon form"
      optionalAssignmentSequence $ \value ->
    assert "ordered optional slots preserve their map boundary"
      (renderInterpretedValue value
        == "(a? : Int := 12; b? : Int := 23)")
  expectValue
      "optional assignment sequence differs from concatenation"
      (AST.equal
        optionalAssignmentSequence
        optionalAssignmentConcatenation) $ \value ->
    assert "semicolon and comma retain different cardinalities"
      (renderInterpretedValue value == "false")
  expectValue
      "optional identifier specification morphism exists"
      (AST.subfederation
        (MapConcatenation
          (natural 2)
          (AST.assignment "b" (natural 5) (natural 5)))
        (MapConcatenation
          (optionalAssigned "a" 2)
          (optionalIdentifier "b"))) $ \value ->
    assert "of recognizes the pointwise optional-identifier morphism"
      (renderInterpretedValue value == "true")
  expectValue
      "optional identifier range subfederation morphism exists"
      (AST.subfederation
        (MapConcatenation
          (natural 2)
          (AST.assignment "b" (natural 5) (natural 5)))
        (MapConcatenation
          (AST.eitherType
            (AST.dependentIdentifierType "a" AST.integerType)
            AST.integerType)
          (AST.eitherType
            (AST.dependentIdentifierType "b" (AST.withinTo 3 8))
            (AST.withinTo 3 8)))) $ \value ->
    assert "2 and b := 5 inhabit their optional integer range slots"
      (renderInterpretedValue value == "true")
  expectValue
      "ternary true branch"
      (AST.conditional
        (AST.boolean True)
        (natural 3)
        (AST.minus (natural 8))) $ \value ->
    assert "if selects its consequent"
      (renderInterpretedValue value == "3")
  expectValue
      "binary false branch"
      (AST.conditionalWithoutElse (AST.boolean False) (natural 3)) $ \value ->
    assert "binary if defaults its alternative to unit"
      (renderInterpretedValue value == "()")
  expectValue
      "lazy dead conditional branch"
      (AST.conditional
        (AST.boolean True)
        (natural 7)
        (AST.and (natural 1) (AST.boolean False))) $ \value ->
    assert "an unselected ill-typed branch is not evaluated"
      (renderInterpretedValue value == "7")
  assert "if rejects a non-Boolean condition"
    (case interpretExpressionReason
        (AST.conditional (natural 1) (natural 2) (natural 3)) of
      Left (ExpectedBooleanCondition NaturalValueKind) -> True
      _ -> False)

testCombinedTypeSystems :: IO ()
testCombinedTypeSystems = do
  let nothingValue =
        AST.assignment "Nothing" AST.emptyMap AST.emptyMap
      expandedBool =
        AST.eitherType
          (AST.assignment "False" (natural 0) (natural 0))
          (AST.assignment "True" (natural 1) (natural 1))
      condition =
        AST.and
          (AST.equal AST.booleanType expandedBool)
          (AST.not (AST.boolean False))
      computedInteger =
        (AST.+) (AST.minus (natural 6)) (natural 2)
  expectValue
      "equality-driven optional integer specification"
      ( AST.conditional condition (justValue computedInteger) nothingValue
          ~> maybeType AST.integerType
      ) $ \value ->
    assert "Boolean equality and arithmetic compose into Maybe Int"
      (renderInterpretedValue value
        == "(Just : -4) ~> Maybe Int")
  expectValue
      "false branch optional specification"
      ( AST.conditional
          (AST.and (AST.boolean True) (AST.boolean False))
          (justValue computedInteger)
          nothingValue
          ~> maybeType AST.integerType
      ) $ \value ->
    assert "a conditional absence composes through optional specification"
      (renderInterpretedValue value
        == "nothing ~> Maybe Int")
  expectValue
      "missing optional identifier path"
      ( AST.conditional
          (AST.equal
            (maybeType AST.naturalType)
            (maybeExpansion AST.naturalType))
          (natural 12)
          (natural 99)
          ~> AST.eitherType
                (AST.dependentIdentifierType "a" AST.naturalType)
                AST.naturalType
      ) $ \value ->
    assert "conditional results canonicalize as optional assignments"
      (renderInterpretedValue value == "a? : from 0 up := 12")

testCombinatorialNumericalSystems :: IO ()
testCombinatorialNumericalSystems = do
  let smallRange = AST.integerWithinTo (-2) 2
      largeRange = AST.integerWithinTo (-5) 5
      nothingValue =
        AST.assignment "Nothing" AST.emptyMap AST.emptyMap
      optionalIdentifierRange =
        AST.eitherType
          (AST.assignment "x" largeRange (AST.minus (natural 3)))
          largeRange
  expectValue
      "identical signed range equality"
      (AST.equal smallRange smallRange) $ \value ->
    assert "equal numerical federations are mutual subfederations"
      (renderInterpretedValue value == "true")
  expectValue
      "proper signed range inclusion is not equality"
      (AST.equal smallRange largeRange) $ \value ->
    assert "a proper numerical subtype is not extensionally equal"
      (renderInterpretedValue value == "false")
  expectValue
      "proper signed range subfederation"
      (AST.subfederation smallRange largeRange) $ \value ->
    assert "of proves an existing inclusion morphism"
      (renderInterpretedValue value == "true")
  expectValue
      "missing reverse signed range subfederation"
      (AST.subfederation largeRange smallRange) $ \value ->
    assert "of is false when the inclusion morphism does not exist"
      (renderInterpretedValue value == "false")
  expectValue
      "chained signed range subtyping"
      ( (AST.minus (natural 1) ~> smallRange)
          ~> largeRange
      ) $ \value ->
    assert "a selected inner-range member widens through its super-range"
      (renderInterpretedValue value == "-1 ~> from -5 to 5")
  expectValue
      "descending range through optional Int"
      ( AST.assignment
          "Just"
          (AST.integerWithinTo 2 (-2))
          (AST.minus (natural 1))
          ~> maybeType AST.integerType
      ) $ \value ->
    assert "descending numerical subtypes compose into optional Int"
      (renderInterpretedValue value
        == "(Just : -1) ~> Maybe Int")
  expectValue
      "conditional power and subtraction range check"
      ( AST.conditional
          (AST.equal smallRange smallRange)
          (justValue
            ((AST.-)
              ((AST.^) (AST.minus (natural 2)) (natural 4))
              (natural 9)))
          nothingValue
          ~> maybeType (AST.integerWithinTo (-10) 10)
      ) $ \value ->
    assert "range equality can guard signed arithmetic and optional subtyping"
      (renderInterpretedValue value
        == "(Just : 7) ~> Maybe (from -10 to 10)")
  expectValue
      "optional numerical identifier equality"
      (AST.equal optionalIdentifierRange optionalIdentifierRange) $ \value ->
    assert "optional identifier ranges retain reflexive subfederation"
      (renderInterpretedValue value == "true")

testRanges :: IO ()
testRanges = do
  expectValue
      "inclusive natural range"
      (NaturalRange 2 5) $ \value ->
    assert "natural ranges retain their inclusive canonical form"
      ( interpretedRangeDescription value
          == Just
            (SuperEllipsisRangeDescription
              omega
              (finiteOrdinal 2)
              (GivenTarget (finiteOrdinal 6)))
        && renderInterpretedValue value == "range 2 to 5"
      )
  expectValue
      "descending inclusive natural range"
      (NaturalRange 5 0) $ \value ->
    assert "zero-target natural ranges use the descending open boundary"
      ( interpretedRangeDescription value
          == Just
            (SuperEllipsisRangeDescription
              omega
              (finiteOrdinal 5)
              MinusSign)
        && renderInterpretedValue value == "range 5 to 0"
      )
  expectValue
      "up natural range"
      (NaturalRangeUpwards 2) $ \value ->
    assert "up natural ranges retain their canonical keyword"
      ( interpretedRangeDescription value
          == Just
            (SuperEllipsisRangeDescription
              omega
              (finiteOrdinal 2)
              PlusSign)
        && renderInterpretedValue value == "range 2 up"
      )
  expectValue
      "inclusive valued natural range"
      (ValuedNaturalRange 2 5) $ \value ->
    assert "valued natural ranges retain from syntax"
      ( interpretedRangeDescription value
          == Just
            (SuperEllipsisRangeDescription
              omega
              (finiteOrdinal 2)
              (GivenTarget (finiteOrdinal 6)))
        && renderInterpretedValue value == "from 2 to 5"
      )
  expectValue
      "descending valued natural range"
      (ValuedNaturalRange 5 2) $ \value ->
    assert "descending valued ranges retain from syntax"
      (renderInterpretedValue value == "from 5 to 2")
  expectValue
      "up valued natural range"
      (ValuedNaturalRangeUpwards 2) $ \value ->
    assert "up valued ranges retain from syntax"
      (renderInterpretedValue value == "from 2 up")
  expectSourceValue "Nat synonym" "Nat" $ \value ->
    assert "Nat is the open upward valued range"
      (renderInterpretedValue value == "Nat")
  expectValue
      "bounded range"
      ((<..>) (natural 2) (natural 5)) $ \value ->
    assert "bounded range retains its typed description"
      (interpretedRangeDescription value
        == Just
          (SuperEllipsisRangeDescription
            omega
            (finiteOrdinal 2)
            (GivenTarget (finiteOrdinal 5))))
  expectValue
      "open range"
      ((..+) (natural 2)) $ \value ->
    assert "postfix range retains its open target"
      (interpretedRangeDescription value
        == Just
          (SuperEllipsisRangeDescription
            omega
            (finiteOrdinal 2)
            PlusSign))
  expectValue
      "parenthesized Ellipsis range semantics"
      ((..+) (...)) $ \value ->
    assert "Ellipsis range endpoint is silently promoted to rank two"
      (interpretedRangeDescription value
        == Just
          (SuperEllipsisRangeDescription
            (ordinal [1, 0, 0])
            omega
            PlusSign))
  expectValue
      "descending range"
      ((..-) (natural 2)) $ \value ->
    assert "descending range syntax retains its target"
      (interpretedRangeDescription value
        == Just
          (SuperEllipsisRangeDescription
            omega
            (finiteOrdinal 2)
            MinusSign))

testCanonicalResults :: IO ()
testCanonicalResults = do
  expectValue
      "adjacent ascending ranges"
      ((<.>)
        ((<..>) (natural 2) (natural 5))
        ((..+) (natural 5))) $ \value ->
    assert "adjacent ascending ranges canonicalize to one open range"
      (renderInterpretedValue value == "2..")
  expectValue
      "adjacent descending ranges"
      ((<.>)
        ((<..>) (natural 9) (natural 5))
        ((<..>) (natural 5) (natural 2))) $ \value ->
    assert "adjacent descending ranges canonicalize in traversal order"
      (renderInterpretedValue value == "9..2")
  let levelTwoFormulation =
        ordinalExponent (...) (natural 2)
  expectValue
      "adjacent cross-rank ranges"
      ((<.>)
        ((<..>) (natural 2) (natural 5))
        ((<..>) (natural 5) levelTwoFormulation)) $ \value ->
    assert "contiguous cross-rank ranges widen to the larger range"
      (renderInterpretedValue value == "2..(... ^ 2)")
  expectValue
      "disjoint ranges"
      ((<.>)
        ((<..>) (natural 2) (natural 5))
        ((..+) (natural 8))) $ \value ->
    assert "disjoint ranges retain their ordered concatenation"
      (renderInterpretedValue value == "2..5, 8..")
  expectValue
      "empty then nonempty range"
      ((<.>)
        ((<..>) (natural 2) (natural 2))
        ((..+) (natural 5))) $ \value ->
    assert "empty ranges are canonical concatenation identities"
      (renderInterpretedValue value == "5..")
  expectValue
      "overlapping range value"
      ((<.>)
        ((..+) (natural 3))
        ((..+) (natural 4))) $ \value ->
    assert "overlapping ranges remain an ordered map result"
      (renderInterpretedValue value == "3.., 4..")

testRendering :: IO ()
testRendering = do
  expectValue
      "root map rendering modes"
      (AtlasMap [natural 1, natural 2]) $ \value ->
    assert "only newline mode removes the root map parentheses"
      ( renderInterpretedValue value == "(1; 2)"
        && renderInterpretedValueAsNewlineMap value == "1\n2"
      )
  expectValue
      "newline map rendering disambiguates an open range"
      (AtlasMap [(..+) (natural 1), natural 10]) $ \value ->
    assert "an open range keeps a semicolon before the next line"
      (renderInterpretedValueAsNewlineMap value == "1..;\n10")
  expectValue
      "singleton arithmetic map"
      (AtlasMap [(AST.+) (natural 2) (natural 2)]) $ \value ->
    assert "singleton maps render as their sole canonical value"
      (renderInterpretedValue value == "4")
  expectValue "formulation Ellipsis" (...) $ \value ->
    assert "literal Ellipsis retains formulation syntax"
      (renderInterpretedValue value == "...")
  expectValue
      "explicit omega"
      (ordinalSum (...) (natural 0)) $ \value ->
    assert "explicit omega is distinguished from the formulation"
      (renderInterpretedValue value == "... + 0")
  expectValue
      "second explicit ordinal power"
      (ordinalExponent (...) (natural 2)) $ \value ->
    assert "higher ordinal powers render canonically"
      (renderInterpretedValue value == "... ^ 2 + 0")
  expectValue
      "zero multiplication"
      (ordinalSum
        (ordinalProduct (...) (natural 0))
        (natural 2)) $ \value ->
    assert "arithmetic results return to their minimal rank"
      (renderInterpretedValue value == "2")
  expectValue
      "map containing a canonical range"
      (AtlasMap
        [ (<.>)
            ((<..>) (natural 2) (natural 5))
            ((..+) (natural 5))
        ]) $ \value ->
    assert "singleton range maps render without enumeration or delimiters"
      (renderInterpretedValue value == "2..")
  mapM_ assertCanonicalMapRoundTrip
    [ AtlasMap [natural 1, natural 2]
    , AtlasMap
        [ AtlasMap [natural 1, natural 2]
        , AtlasMap [natural 3, natural 4]
        ]
    , MapExpansion
        (AtlasMap [natural 1, natural 2])
        (AtlasMap [natural 3, natural 4])
    ]
  where
    assertCanonicalMapRoundTrip expressionValue =
      case interpretExpressionReason expressionValue of
        Left rejection ->
          fail ("map construction was rejected: " <> show rejection)
        Right original ->
          let rendered = renderInterpretedValue original
          in case parseProductionSource ("(" <> rendered <> "\n)") of
              Left message ->
                fail
                  ("canonical map did not parse: "
                    <> parseFailureMessage message)
              Right roundTripExpression ->
                case interpretExpressionReason roundTripExpression of
                  Left rejection ->
                    fail
                      ("canonical map round trip was rejected: "
                        <> show rejection)
                  Right roundTripped ->
                    assert
                      "rendered map nesting uniquely determines cardinality"
                      ( Types.interpretedCanonicalResult original
                          == Types.interpretedCanonicalResult roundTripped
                        && interpretedMapCardinality (interpretedMap original)
                          == interpretedMapCardinality
                            (interpretedMap roundTripped)
                      )

parseProductionSource :: String -> Either ParseFailure Expression
parseProductionSource source =
  locatedValue <$> parseDatraSourceLocatedWithImportsAndStandardLibrary
    True [] "<input>" source

testMaps :: IO ()
testMaps = do
  expectValue
      "unary maps are structural identities"
      (AtlasMap [AtlasMap [natural 1]]) $ \value ->
    assert "repeated unary wrapping adds no genuine page"
      ( interpretedValueKind value == NaturalValueKind
        && interpretedMapCardinality (interpretedMap value) == 1
        && renderInterpretedValue value == "1"
      )
  expectValue
      "unary operands do not raise sequence cardinality"
      (AtlasMap
        [ AtlasMap [natural 1]
        , AtlasMap [natural 2]
        ]) $ \value ->
    assert "a sequence of unary operands has one new genuine page"
      ( interpretedMapCardinality (interpretedMap value) == 2
        && renderInterpretedValue value == "(1; 2)"
      )
  expectValue
      "empty sequence members normalize away"
      (AtlasMap
        [ AtlasMap []
        , natural 1
        , AtlasMap []
        ]) $ \value ->
    assert "only exact empty maps are sequence identities"
      ( interpretedValueKind value == NaturalValueKind
        && renderInterpretedValue value == "1"
      )
  expectValue
      "ASCII-string concatenation"
      ((<.>) (AsciiStringLiteral "ab") (AsciiStringLiteral "_1")) $ \value ->
    assert "ordinary concatenation remembers its ASCII-string result"
      ( interpretedValueKind value == AsciiStringValueKind
        && interpretedMapCardinality (interpretedMap value) == 2
        && interpretedMapFinalOrderType (interpretedMap value)
          == finiteOrdinal 4
        && renderInterpretedValue value == "$ab_1"
      )
  expectValue
      "empty ASCII-string concatenation"
      ((<.>) (AsciiStringLiteral "") (AsciiStringLiteral "")) $ \value ->
    assert "concatenating empty strings remains an empty ASCII string"
      ( interpretedValueKind value == AsciiStringValueKind
        && interpretedMapCardinality (interpretedMap value) == 0
        && renderInterpretedValue value == "\"\""
      )
  expectValue
      "operator sequence"
      (natural 1 <:> natural 2) $ \value ->
    assert "sequential AST syntax constructs a two-position map"
      ( interpretedMapCardinality (interpretedMap value) == 2
        && interpretedMapFinalOrderType (interpretedMap value)
          == finiteOrdinal 2
      )
  let compoundSequence =
        MapSequence
          [ (<..>) (natural 1) (natural 4)
          , AsciiStringLiteral "ab"
          ]
  expectValue "sequence preserves compound operands" compoundSequence $ \value ->
    assert "each sequence operand occupies exactly one final-page position"
      ( interpretedMapFinalOrderType (interpretedMap value)
          == finiteOrdinal 2
        && renderInterpretedValue value == "(1..4; $ab)"
      )
  expectValue
      "sequence access returns a compound operand intact"
      ((<@>) compoundSequence (natural 0)) $ \value ->
    assert "access does not flatten the selected sequence operand"
      (renderInterpretedValue value == "1..4")
  expectValue
      "concatenation flattens compound operands"
      ((<.>)
        ((<..>) (natural 1) (natural 4))
        (AsciiStringLiteral "ab")) $ \value ->
    assert "concatenation appends operand final-page contents"
      (interpretedMapFinalOrderType (interpretedMap value)
        == finiteOrdinal 5)
  expectValue
      "operator expansion"
      ((natural 1 <:> natural 2) <+> (natural 3 <:> natural 4)) $ \value ->
    assert "expansion AST syntax introduces one additional map level"
      (interpretedMapCardinality (interpretedMap value) == 3)
  let nested =
        AtlasMap
          [ AtlasMap [natural 1, natural 2]
          , AtlasMap [natural 3, natural 4]
          ]
  expectValue "nested map" nested $ \value -> do
    let valueMap = interpretedMap value
        values =
          map
            (\position ->
              renderInterpretedValue
                <$> interpretedMapValueAt valueMap (finiteOrdinal position))
            [0 .. 2]
    assert "nested map has the requested three-page cardinality"
      (interpretedMapCardinality valueMap == 3)
    assert "nested sequence operands remain distinct final-page values"
      (values == [Just "(1; 2)", Just "(3; 4)", Nothing])
    assert "nested maps retain their sequence boundaries when rendered"
      (renderInterpretedValue value == "((1; 2); (3; 4))")
  let leftNested =
        AtlasMap
          [ AtlasMap [natural 1, natural 2]
          , natural 3
          ]
      rightNested =
        AtlasMap
          [ natural 1
          , AtlasMap [natural 2, natural 3]
          ]
  expectValue "left-nested map" leftNested $ \leftValue ->
    expectValue "right-nested map" rightNested $ \rightValue ->
      assert "binary map nesting remains non-associative"
        ( interpretedMapCardinality (interpretedMap leftValue) == 3
          && interpretedMapCardinality (interpretedMap rightValue) == 3
          && renderInterpretedValue leftValue == "((1; 2); 3)"
          && renderInterpretedValue rightValue == "(1; (2; 3))"
        )
  expectValue
      "map concatenation"
      ((<.>)
        (AtlasMap [natural 1, natural 2])
        (AtlasMap [natural 3])) $ \value ->
    assert "map concatenation appends final-page order types"
      (interpretedMapFinalOrderType (interpretedMap value)
        == finiteOrdinal 3)

testAtlasMapFederations :: IO ()
testAtlasMapFederations = do
  expectValue
      "a structured map retains NaturalRange syntax"
      (AtlasMap [natural 2, NaturalRange 2 10]) $ \value ->
    assert "NaturalRange structure survives a sequential product"
      (renderInterpretedValue value == "(2; range 2 to 10)")
  let coalitionSequence =
        AtlasMap [ValuedIntegerRange 1 3, ValuedIntegerRange 4 6]
      coalitionConcatenation =
        (<.>) (ValuedIntegerRange 1 3) (ValuedIntegerRange 4 6)
  expectValue
      "a sequence of coalitions retains its map boundary"
      coalitionSequence $ \value ->
    assert "coalition components retain semicolons"
      (renderInterpretedValue value
        == "(from 1 to 3; from 4 to 6)")
  expectValue
      "a coalition sequence differs from its concatenation"
      (AST.equal coalitionSequence coalitionConcatenation) $ \value ->
    assert ("semicolon maps preserve higher cardinality: got "
      <> renderInterpretedValue value)
      (renderInterpretedValue value == "false")
  expectValue
      "disjoint NaturalRange concatenation"
      ((<.>) (NaturalRange 2 5) (NaturalRange 6 9)) $ \value ->
    assert "disjoint finite NaturalRanges form a federation"
      (renderInterpretedValue value
        == "range 2 to 5, range 6 to 9")
  expectValue
      "descending disjoint NaturalRange concatenation"
      ((<.>) (NaturalRange 9 6) (NaturalRange 5 2)) $ \value ->
    assert "NaturalRange disjointness ignores traversal direction"
      (renderInterpretedValue value
        == "range 9 to 6, range 5 to 2")
  expectValue
      "finite then disjoint up NaturalRange"
      ((<.>) (NaturalRange 2 5) (NaturalRangeUpwards 6)) $ \value ->
    assert "a finite domain below an up domain is disjoint"
      (renderInterpretedValue value
        == "range 2 to 5, range 6 up")
  assert "overlapping finite NaturalRanges have a collision witness"
    (case interpretExpressionReason
        ((<.>) (NaturalRange 2 5) (NaturalRange 3 6)) of
      Left
          (AtlasMapFederationOperationRefuted
            (AtlasMapFederationConcatenationCollision 3)) -> True
      _ -> False)
  assert "a shared NaturalRange endpoint is overlap"
    (case interpretExpressionReason
        ((<.>) (NaturalRange 2 5) (NaturalRangeUpwards 5)) of
      Left
          (AtlasMapFederationOperationRefuted
            (AtlasMapFederationConcatenationCollision 5)) -> True
      _ -> False)
  assert "two up NaturalRanges always overlap"
    (case interpretExpressionReason
        ((<.>)
          (NaturalRangeUpwards 2)
          (NaturalRangeUpwards 20)) of
      Left
          (AtlasMapFederationOperationRefuted
            (AtlasMapFederationConcatenationCollision 20)) -> True
      _ -> False)
  expectValue
      "disjoint ValuedNaturalRange concatenation"
      ((<.>) (ValuedNaturalRange 2 5) (ValuedNaturalRange 6 9)) $ \value ->
    assert "disjoint valued ranges form a federation"
      (renderInterpretedValue value
        == "from 2 to 5, from 6 to 9")
  assert "overlapping ValuedNaturalRanges have a collision witness"
    (case interpretExpressionReason
        ((<.>) (ValuedNaturalRange 2 5) (ValuedNaturalRange 4 8)) of
      Left
          (AtlasMapFederationOperationRefuted
            (AtlasMapFederationConcatenationCollision 4)) -> True
      _ -> False)
  assert "NaturalRange and ValuedNaturalRange singleton Atlases can collide"
    (case interpretExpressionReason
        ((<.>) (NaturalRange 2 5) (ValuedNaturalRange 5 8)) of
      Left
          (AtlasMapFederationOperationRefuted
            (AtlasMapFederationConcatenationCollision 5)) -> True
      _ -> False)
  assert "unknown structured concatenation is undecidable, not refuted"
    (case interpretExpressionReason
        ((<.>)
          (NaturalRange 2 4 <:> NaturalRange 8 10)
          (NaturalRange 20 22 <:> NaturalRange 30 32)) of
      Left
          (AtlasMapFederationOperationUndecidable
            (NoAtlasMapFederationDecisionProcedure
              AtlasMapFederationConcatenation)) -> True
      _ -> False)

testAccess :: IO ()
testAccess = do
  let threeValues =
        (<.>)
          (natural 1)
          ((<.>) (natural 2) (natural 3))
      fiveValues = AtlasMap (map natural [0 .. 4])
      sequenceSpecification =
        (~>)
          (AtlasMap [natural 2, natural 3])
          (AtlasMap [NaturalType, NaturalType])
      expectRangeAccess label expectedKind sourceValue selectionValue expected =
        expectValue label ((<@>) sourceValue selectionValue) $ \value ->
          assert label
            ( interpretedValueKind value == expectedKind
              && renderInterpretedValue value == expected
            )
  expectValue
      "access projects one specification fiber"
      ((<@>) sequenceSpecification (natural 0)) $ \value ->
    assert "the selected source and target remain related"
      ( interpretedValueKind value == SpecificationValueKind
        && renderInterpretedValue value == "2 ~> from 0 up"
      )
  expectValue
      "range access projects specification fibers"
      ((<@>)
        sequenceSpecification
        ((<..>) (natural 0) (natural 2))) $ \value ->
    assert "a specification range retains both selected fibers"
      ( interpretedValueKind value == SpecificationValueKind
        && renderInterpretedValue value
          == "(2; 3) ~> (from 0 up; from 0 up)"
      )
  expectValue
      "natural up range access"
      ((<@>) threeValues (NaturalRangeUpwards 1)) $ \value ->
    assert "natural range access clips up to the largest fitting range"
      (renderInterpretedValue value == "(2; 3)")
  expectValue
      "bounded natural range access"
      ((<@>) threeValues (NaturalRange 1 10)) $ \value ->
    assert "bounded natural range access clips its inclusive target"
      (renderInterpretedValue value == "(2; 3)")
  expectValue
      "descending natural range access"
      ((<@>) threeValues (NaturalRange 10 0)) $ \value ->
    assert "descending natural range access clips its inclusive origin"
      (renderInterpretedValue value == "(3; 2; 1)")
  expectValue
      "empty natural range access"
      ((<@>) threeValues (NaturalRangeUpwards 10)) $ \value ->
    assert "natural range access always has its empty federation member"
      (renderInterpretedValue value == "()")
  expectValue
      "concrete range access clips its upper boundary"
      ((<@>) fiveValues ((<..>) (natural 3) (natural 10))) $ \value ->
    assert "only existing ascending positions remain"
      (renderInterpretedValue value == "(3; 4)")
  expectValue
      "descending concrete range access clips its origin"
      ((<@>) fiveValues ((<..>) (natural 10) (natural 2))) $ \value ->
    assert "descending traversal order survives clipping"
      (renderInterpretedValue value == "(4; 3)")
  expectValue
      "wholly out-of-bounds concrete range access is empty"
      ((<@>) fiveValues ((..+) (natural 10))) $ \value ->
    assert "an absent concrete tail clips to empty"
      (renderInterpretedValue value == "()")
  expectValue
      "every concrete range clips against an empty source"
      ((<@>) (AtlasMap []) ((..+) (natural 0))) $ \value ->
    assert "an empty source produces an empty result"
      (renderInterpretedValue value == "()")
  assert "valued ranges remain exact access insertions"
    (case interpretExpressionReason
        ((<@>) fiveValues (ValuedNaturalRange 3 10)) of
      Left (AccessRejected (AccessPositionOutOfBounds _ _)) -> True
      _ -> False)
  expectValue
      "a sequential selector map preserves separate access results"
      ((<@>)
        threeValues
        (AtlasMap [natural 0, NaturalRangeUpwards 1])) $ \value ->
    assert "head and tail access retains a semantic coalization boundary"
      ( renderInterpretedValue value == "(1; >< (2; 3))"
        && case interpretedMapValueAt
            (interpretedMap value) (finiteOrdinal 1) of
          Just member ->
            case Types.interpretedCanonicalResult member of
              Types.CanonicalCoalization _ -> True
              _ -> False
          Nothing -> False
      )
  expectValue
      "an empty clipped sequence component keeps its position"
      ((<@>)
        (AtlasMap [natural 1])
        (AtlasMap [natural 0, ((..+) (natural 1))])) $ \value ->
    assert "head and empty tail remain two sequence positions"
      ( renderInterpretedValue value == "(1; >< ())"
        && case interpretedMapValueAt
            (interpretedMap value) (finiteOrdinal 1) of
          Just member ->
            case Types.interpretedCanonicalResult member of
              Types.CanonicalCoalization _ -> True
              _ -> False
          Nothing -> False
      )
  expectValue
      "overlapping sequence selectors clip independently"
      ((<@>)
        threeValues
        (AtlasMap
          [ ((<..>) (natural 0) (natural 2))
          , ((<..>) (natural 1) (natural 10))
          ])) $ \value ->
    assert "sequence overlap preserves both coalition results"
      (renderInterpretedValue value == "(>< (1; 2); >< (2; 3))")
  expectValue
      "a concatenated selector map concatenates access results"
      ((<@>)
        threeValues
        ((<.>) (natural 0) (NaturalRangeUpwards 1))) $ \value ->
    assert "comma access flattens the selected head and tail"
      (renderInterpretedValue value == "(1; 2; 3)")
  expectValue
      "concrete head and tail selectors clip and flatten"
      ((<@>)
        threeValues
        ((<.>)
          ((<..>) (natural 0) (natural 1))
          ((..+) (natural 1)))) $ \value ->
    assert "concrete comma selectors preserve selector order"
      (renderInterpretedValue value == "(1; 2; 3)")
  expectValue
      "range-federation head and tail selectors clip and flatten"
      ((<@>)
        threeValues
        ((<.>) (NaturalRange 0 0) (NaturalRangeUpwards 1))) $ \value ->
    assert "range comma selectors preserve selector order"
      (renderInterpretedValue value == "(1; 2; 3)")
  assert "an exact leaf rejects a mixed selector concatenation"
    (case interpretExpressionReason
        ((<@>)
          threeValues
          ((<.>)
            ((<..>) (natural 0) (natural 1))
            (ValuedNaturalRange 1 10))) of
      Left (AccessRejected (AccessPositionOutOfBounds _ _)) -> True
      _ -> False)
  let stableConcatenationPrefix =
        (<.>)
          (natural 1)
          ((<.>)
            (natural 2)
            ((<.>) (natural 3) (NaturalRange 5 20)))
  expectValue
      "access stays within a total concatenation prefix"
      ((<@>)
        stableConcatenationPrefix
        ((<..>) (natural 0) (natural 3))) $ \value ->
    assert "an uncertain suffix does not obscure a known prefix"
      (renderInterpretedValue value == "(1; 2; 3)")
  expectValue
      "NaturalRange access stays within a total concatenation prefix"
      ((<@>) stableConcatenationPrefix (NaturalRange 0 2)) $ \value ->
    assert "federated selections use the same accessible regions"
      (renderInterpretedValue value == "(1; 2; 3)")
  expectValue
      "valued range access flattens through concatenation"
      ((<@>)
        ((<.>) (ValuedNaturalRange 1 3) (NaturalRange 5 20))
        (natural 0)) $ \value ->
    assert
      ("comma concatenation exposes the valued range members: got "
        <> renderInterpretedValue value)
      (renderInterpretedValue value == "1")
  let crossingUncertainSuffix = interpretExpressionReason
        ((<@>)
          stableConcatenationPrefix
          ((<..>) (natural 0) (natural 4)))
  assert
    ("access crossing an uncertain concatenation suffix is undecidable: got "
      <> either show renderInterpretedValue crossingUncertainSuffix)
    (case crossingUncertainSuffix of
      Left
          (AtlasMapFederationOperationUndecidable
            (NoAtlasMapFederationDecisionProcedure
              AtlasMapFederationAccess)) -> True
      _ -> False)
  let valuedCoalitionSequence =
        AtlasMap
          [ natural 2
          , natural 3
          , ValuedNaturalRange 1 20
          , natural 5
          ]
  expectValue
      "a sequence containing a valued-range coalition supports open access"
      ((<@>) valuedCoalitionSequence (NaturalRangeUpwards 0)) $ \value ->
    assert "open access preserves the valued-range coalition as one position"
      ( interpretedMapFinalOrderType (interpretedMap value) == finiteOrdinal 4
        && renderInterpretedValue value == "(2; 3; from 1 to 20; 5)"
      )
  expectValue
      "bounded access slices a sequence of coalitions"
      ((<@>) valuedCoalitionSequence (NaturalRange 1 2)) $ \value ->
    assert "bounded access retains the selected valued-range coalition"
      (renderInterpretedValue value == "(3; from 1 to 20)")
  expectValue
      "singleton access selects a valued-range coalition"
      ((<@>) valuedCoalitionSequence (natural 2)) $ \value ->
    assert "singleton access returns the selected coalition"
      (renderInterpretedValue value == "from 1 to 20")
  expectValue
      "a valued range is its own coalition"
      ((<@>) (ValuedNaturalRange 1 20) (NaturalRangeUpwards 0)) $ \value ->
    assert "access preserves a standalone valued-range coalition"
      (renderInterpretedValue value == "from 1 to 20")
  expectRangeAccess
    "natural up access canonicalizes a bounded source range"
    RangeValueKind
    ((<..>) (natural 100) (natural 123))
    (NaturalRangeUpwards 5)
    "105..123"
  expectRangeAccess
    "bounded natural access canonicalizes a source range"
    RangeValueKind
    ((<..>) (natural 100) (natural 123))
    (NaturalRange 5 10)
    "105..111"
  expectRangeAccess
    "descending natural access canonicalizes a source range"
    RangeValueKind
    ((<..>) (natural 100) (natural 123))
    (NaturalRange 10 5)
    "110..104"
  expectRangeAccess
    "natural up access preserves source range gaps"
    RangeConcatenationValueKind
    ((<.>)
      ((<..>) (natural 2) (natural 5))
      ((<..>) (natural 10) (natural 14)))
    (NaturalRangeUpwards 1)
    "3..5, 10..14"
  expectRangeAccess
    "natural up access canonicalizes an open source range"
    RangeValueKind
    ((..+) (natural 10))
    (NaturalRangeUpwards 5)
    "15.."
  expectRangeAccess
    "open range access stays an open range"
    RangeValueKind
    ((..+) (natural 10))
    ((..+) (natural 5))
    "15.."
  expectRangeAccess
    "bounded range access canonicalizes selected runs"
    RangeConcatenationValueKind
    ((<..>) (natural 2) (natural 20))
    ((<.>)
      ((<..>) (natural 3) (natural 8))
      ((<..>) (natural 11) (natural 13)))
    "5..10, 13..15"
  expectRangeAccess
    "an open selector crosses a finite source prefix"
    RangeValueKind
    ((<.>)
      ((<..>) (natural 2) (natural 4))
      ((..+) (natural 10)))
    ((..+) (natural 2))
    "10.."
  expectRangeAccess
    "source and selector concatenations stay range concatenations"
    RangeConcatenationValueKind
    ((<.>)
      ((<..>) (natural 2) (natural 4))
      ((..+) (natural 10)))
    ((<.>)
      ((<..>) (natural 2) (natural 5))
      ((..+) (natural 8)))
    "10..13, 16.."
  expectRangeAccess
    "ascending source with descending selection"
    RangeValueKind
    ((<..>) (natural 2) (natural 20))
    ((<..>) (natural 8) (natural 3))
    "10..5"
  expectRangeAccess
    "descending source with ascending selections"
    RangeConcatenationValueKind
    ((<..>) (natural 20) (natural 2))
    ((<.>)
      ((<..>) (natural 3) (natural 8))
      ((<..>) (natural 11) (natural 13)))
    "17..12, 9..7"
  expectRangeAccess
    "descending source and selection compose to ascending"
    RangeValueKind
    ((<..>) (natural 20) (natural 2))
    ((<..>) (natural 8) (natural 3))
    "12..17"
  expectRangeAccess
    "descending selection reverses source-component order"
    RangeConcatenationValueKind
    ((<.>)
      ((<..>) (natural 2) (natural 5))
      ((<..>) (natural 10) (natural 14)))
    ((<..>) (natural 6) (natural 1))
    "13..9, 4..3"
  expectRangeAccess
    "a descending result ending at zero uses the minus form"
    RangeValueKind
    ((<..>) (natural 0) (natural 10))
    ((..-) (natural 5))
    "5..-"
  expectRangeAccess
    "a selection crossing source ranges splits at the value gap"
    RangeConcatenationValueKind
    ((<.>)
      ((<..>) (natural 2) (natural 5))
      ((<..>) (natural 10) (natural 14)))
    ((<..>) (natural 1) (natural 6))
    "3..5, 10..13"
  expectRangeAccess
    "empty range-on-range access stays empty"
    MapValueKind
    ((<..>) (natural 2) (natural 20))
    ((<..>) (natural 5) (natural 5))
    "()"
  expectRangeAccess
    "bounded transfinite range access remains symbolic"
    RangeValueKind
    ((<..>) (natural 2) (...))
    ((<..>) (natural 3) (...))
    "5..(...)"
  expectRangeAccess
    "open transfinite range access computes its limit boundary"
    RangeValueKind
    ((..+) (ordinalSum (...) (natural 2)))
    ((..+) (natural 3))
    "(... + 5)..(... * 2 + 0)"
  expectRangeAccess
    "selection can begin after an infinite source component"
    RangeValueKind
    ((<.>)
      ((..+) (natural 2))
      ((..+) (ordinalSum (...) (natural 10))))
    ((..+) (...))
    "(... + 10).."
  expectRangeAccess
    "descending transfinite selection preserves finite-tail arithmetic"
    RangeValueKind
    ((<.>)
      ((..+) (natural 2))
      ((..+) (ordinalSum (...) (natural 10))))
    ((<..>)
      (ordinalSum (...) (natural 2))
      (ordinalSum (...) (natural 0)))
    "(... + 12)..(... + 10)"
  expectRangeAccess
    "a computed range result remains reusable as an insertion"
    RangeValueKind
    ((..+) (natural 0))
    ((<@>) ((..+) (natural 10)) ((..+) (natural 5)))
    "15.."
  expectValue
      "ASCII-string singleton access"
      ((<@>) (AsciiStringLiteral "abcd") (natural 2)) $ \value ->
    assert "ordinary access remembers its ASCII-string result"
      ( interpretedValueKind value == AsciiStringValueKind
        && interpretedMapFinalOrderType (interpretedMap value)
          == finiteOrdinal 1
        && renderInterpretedValue value == "$c"
      )
  expectValue
      "ASCII-string range access"
      ((<@>)
        (AsciiStringLiteral "abcd")
        ((<..>) (natural 1) (natural 3))) $ \value ->
    assert "range access retains the selected ASCII string"
      ( interpretedValueKind value == AsciiStringValueKind
        && renderInterpretedValue value == "$bc"
      )
  expectValue
      "empty ASCII-string access"
      ((<@>)
        (AsciiStringLiteral "abcd")
        ((<..>) (natural 1) (natural 1))) $ \value ->
    assert "empty access remains an empty ASCII string"
      ( interpretedValueKind value == AsciiStringValueKind
        && interpretedMapCardinality (interpretedMap value) == 0
        && renderInterpretedValue value == "\"\""
      )
  let source = AtlasMap (map natural [0 .. 9])
      insertion =
        (<.>)
          ((<..>) (natural 2) (natural 5))
          ((<..>) (natural 5) (natural 8))
  expectValue "range-concatenation access" ((<@>) source insertion) $ \value -> do
    let valueMap = interpretedMap value
        selected =
          map
            (\position ->
              interpretedMapValueAt valueMap (finiteOrdinal position)
                >>= naturalOrdinal)
            [0 .. 6]
    assert "access follows concatenated insertion order"
      (selected == map Just [2 .. 7] <> [Nothing])
    assert "finite access renders its selected result values"
      (renderInterpretedValue value == "(2; 3; 4; 5; 6; 7)")
  assert "range overlap is rejected before clipping"
    (case interpretExpressionReason
        ((<@>)
          (AtlasMap [natural 0])
          ((<.>)
            ((<..>) (natural 3) (natural 10))
            ((<..>) (natural 4) (natural 12)))) of
      Left
          (RangeConcatenationRejected
            (SuperEllipsisRangesOverlap _ _ _ _)) -> True
      _ -> False)
  let computedConcatenation =
        (<@>)
          ((<.>)
            ((<..>) (natural 0) (natural 2))
            ((<..>) (natural 4) (natural 6)))
          ((..+) (natural 0))
  expectValue
      "computed concatenated ranges retain their clipping policies"
      ((<@>) (AtlasMap (map natural [0 .. 4])) computedConcatenation) $ \value ->
    assert "each computed selector leaf clips independently"
      (renderInterpretedValue value == "(0; 1; 4)")
  expectValue
      "empty access"
      ((<@>)
        (AtlasMap [])
        ((<..>) (natural 3) (natural 3))) $ \value ->
    assert "empty maps and ranges are accepted by access"
      ( interpretedMapCardinality (interpretedMap value) == 0
        && interpretedMapFinalOrderType (interpretedMap value)
          == finiteOrdinal 0
      )
  assert "Infinity cannot be accessed at its own boundary"
    (case interpretExpressionReason ((<@>) (...) (...)) of
      Left
          (AccessRejected
            (AccessPositionOutOfBounds position orderType)) ->
        position == omega && orderType == omega
      _ -> False)
  expectValue
      "cofinal formulation range access"
      ((<@>) (...) ((..+) (natural 5))) $ \value ->
    assert "a cofinal formulation tail canonicalizes as the formulation"
      ( interpretedValueKind value == FormulationValueKind
        && renderInterpretedValue value == "..."
      )
  assert "Infinity is an index, not a full-prefix range selector"
    (case interpretExpressionReason ((<@>) ((..+) (natural 10)) (...)) of
      Left
          (AccessRejected
            (AccessPositionOutOfBounds position orderType)) ->
        position == omega && orderType == omega
      _ -> False)
  expectValue
      "a sequence wrapper preserves its range operand"
      ((<@>)
        (AtlasMap [((..+) (natural 2))])
        (NaturalRangeUpwards 0)) $ \value ->
    assert "sequence access returns the range operand without flattening it"
      (renderInterpretedValue value == "2..")
  expectValue
      "an open selector beyond a finite sequence clips to empty"
      ((<@>)
        (AtlasMap [natural 42, ((..+) (natural 2))])
        ((..+) (natural 5))) $ \value ->
    assert "a concrete open range is no longer a strict infinite insertion"
      (renderInterpretedValue value == "()")
  expectValue
      "NaturalRange accessed by NaturalRange"
      ((<@>) (NaturalRange 2 10) (NaturalRangeUpwards 1)) $ \value ->
    assert "NaturalRange access returns a NaturalRange"
      (renderInterpretedValue value == "range 3 to 10")
  expectValue
      "up NaturalRange accessed by NaturalRange"
      ((<@>)
        (NaturalRangeUpwards 2)
        (NaturalRangeUpwards 5)) $ \value ->
    assert "open NaturalRange access stays open"
      (renderInterpretedValue value == "range 7 up")
  expectValue
      "descending NaturalRange accessed in reverse"
      ((<@>) (NaturalRange 10 2) (NaturalRange 3 1)) $ \value ->
    assert "NaturalRange access composes traversal directions"
      (renderInterpretedValue value == "range 7 to 9")
  expectValue
      "NaturalRange access with no fitting member"
      ((<@>)
        (NaturalRange 2 4)
        (NaturalRangeUpwards 10)) $ \value ->
    assert "the empty result is the common NaturalRange access member"
      (renderInterpretedValue value == "()")
  expectValue
      "NaturalRange accessed by empty ordinary range"
      ((<@>)
        (NaturalRange 2 10)
        ((<..>) (natural 0) (natural 0))) $ \value ->
    assert "empty selection succeeds on every federation member"
      (renderInterpretedValue value == "()")
  expectValue
      "clipped concrete access is total over NaturalRange"
      ((<@>)
        (NaturalRange 2 10)
        ((<..>) (natural 0) (natural 1))) $ \value ->
    assert "the empty and singleton pointwise results form a NaturalRange"
      (renderInterpretedValue value == "range 2 to 2")
  assert "exact valued-range access still sees the empty counterexample"
    (case interpretExpressionReason
        ((<@>) (NaturalRange 2 10) (ValuedNaturalRange 0 0)) of
      Left
          (AtlasMapFederationOperationRefuted
            AtlasMapFederationAccessHasEmptyCounterexample) -> True
      _ -> False)
  let concatenatedNaturalRanges =
        (<.>) (NaturalRange 1 10) (NaturalRange 20 30)
  assert "nonempty access into concatenated NaturalRanges is refuted explicitly"
    (case interpretExpressionReason
        ((<@>) concatenatedNaturalRanges (natural 5)) of
      Left
          (AtlasMapFederationOperationRefuted
            AtlasMapFederationAccessHasEmptyCounterexample) -> True
      _ -> False)
  expectValue
      "whole-range access is total over concatenated NaturalRanges"
      ((<@>) concatenatedNaturalRanges (NaturalRangeUpwards 0)) $ \value ->
    assert "every source member is preserved pointwise"
      (renderInterpretedValue value
        == "range 1 to 10, range 20 to 30")
  expectValue
      "empty access into concatenated NaturalRanges still succeeds"
      ((<@>)
        concatenatedNaturalRanges
        ((<..>) (natural 0) (natural 0))) $ \value ->
    assert "empty selection succeeds on every concatenated federation member"
      (renderInterpretedValue value == "()")
  expectValue
      "sequence access preserves structured federation operands"
      ((<@>)
        (NaturalRange 2 5 <:> NaturalRange 8 10)
        ((<..>) (natural 0) (natural 2))) $ \value ->
    assert "sequence access never flattens operand federations"
      (renderInterpretedValue value
        == "(range 2 to 5; range 8 to 10)")

testSpecification :: IO ()
testSpecification = do
  let expectSpecification label source target expected =
        expectValue label ((~>) source target) $ \value ->
          assert label
            ( interpretedValueKind value == SpecificationValueKind
              && renderInterpretedValue value == expected
            )
      expectNoMember label source target =
        assert label
          (case interpretExpressionReason ((~>) source target) of
            Left
                (AtlasMapFederationOperationRefuted
                  AtlasMapFederationSpecificationHasNoMatchingMember) -> True
            _ -> False)
      boundedRange = (<..>) (natural 2) (natural 5)
      rangeConcatenation =
        (<.>) boundedRange ((..+) (natural 8))
      rangeSequence =
        AtlasMap [boundedRange, AsciiStringLiteral "a"]
      compositeSequenceSource =
        AtlasMap [AsciiStringLiteral "a", natural 50]
      compositeSequenceTarget =
        AtlasMap [AsciiStringLiteral "a", NaturalType]
      compositeSequenceIntermediate =
        AtlasMap
          [ AsciiStringLiteral "a"
          , ValuedNaturalRange 1 100
          ]
      compositeExpansionSource =
        MapExpansion
          (AtlasMap [AsciiStringLiteral "a"])
          (AtlasMap [natural 50])
      compositeExpansionTarget =
        MapExpansion
          (AtlasMap [AsciiStringLiteral "a"])
          (AtlasMap [NaturalType])
      compositeExpansionIntermediate =
        MapExpansion
          (AtlasMap [AsciiStringLiteral "a"])
          (AtlasMap [ValuedNaturalRange 1 100])
      concatenate = foldr1 (<.>)
      compositeConcatenationSource =
        concatenate
          [ AsciiStringLiteral "a"
          , natural 3
          , natural 4
          , natural 5
          ]
      compositeConcatenationTarget =
        (<.>)
          (AsciiStringLiteral "a")
          (NaturalRange 1 10)
      compositeConcatenationWidenedTarget =
        (<.>)
          (AsciiStringLiteral "a")
          (NaturalRangeUpwards 0)
  let expectIdentity label expressionValue expectedKind expected =
        expectValue label ((~>) expressionValue expressionValue) $ \value ->
          assert label
            ( interpretedValueKind value == expectedKind
              && renderInterpretedValue value == expected
            )
  expectIdentity
    "ASCII string self-specification"
    (AsciiStringLiteral "a")
    AsciiStringValueKind
    "$a"
  expectIdentity
    "natural self-specification"
    (natural 2)
    NaturalValueKind
    "2"
  expectIdentity
    "range self-specification"
    boundedRange
    RangeValueKind
    "2..5"
  expectIdentity
    "range concatenation self-specification"
    rangeConcatenation
    RangeConcatenationValueKind
    "2..5, 8.."
  expectIdentity
    "sequence self-specification"
    rangeSequence
    MapValueKind
    "(2..5; $a)"
  expectIdentity
    "non-total federation identity specification"
    NaturalType
    RangeValueKind
    "from 0 up"
  expectValue
      "specification composed with its target identity"
      ((~>) ((~>) (natural 5) NaturalType) NaturalType) $ \value ->
    assert "the target identity leaves a general specification unchanged"
      ( interpretedValueKind value == SpecificationValueKind
        && renderInterpretedValue value == "5 ~> from 0 up"
      )
  expectNoMember
    "different singleton total maps do not specify each other"
    (AsciiStringLiteral "a")
    (AsciiStringLiteral "b")
  expectSpecification
    "sequence federation selects members pointwise"
    compositeSequenceSource
    compositeSequenceTarget
    "($a; 50) ~> ($a; from 0 up)"
  expectSpecification
    "concatenated federation partitions and selects members"
    compositeConcatenationSource
    compositeConcatenationTarget
    "($a; 3; 4; 5) ~> $a, range 1 to 10"
  expectValue
      "expansion federation selects members pointwise"
      ((~>) compositeExpansionSource compositeExpansionTarget) $ \value ->
    assert "expansion specification is defined"
      (interpretedValueKind value == SpecificationValueKind)
  expectValue
      "sequence subfederations compose pointwise"
      ((~>)
        ((~>) compositeSequenceSource compositeSequenceIntermediate)
        compositeSequenceTarget) $ \value ->
    assert "sequence composition retains the final target"
      (renderInterpretedValue value
        == "($a; 50) ~> ($a; from 0 up)")
  expectValue
      "concatenated subfederations compose pointwise"
      ((~>)
        ((~>)
          compositeConcatenationSource
          compositeConcatenationTarget)
        compositeConcatenationWidenedTarget) $ \value ->
    assert "concatenation composition retains the final target"
      (renderInterpretedValue value
        == "($a; 3; 4; 5) ~> $a, range 0 up")
  expectValue
      "expansion subfederations compose pointwise"
      ((~>)
        ((~>) compositeExpansionSource compositeExpansionIntermediate)
        compositeExpansionTarget) $ \value ->
    assert "expansion composition retains a specification"
      (interpretedValueKind value == SpecificationValueKind)
  assert "composite subfederations report a missing component"
    (case interpretExpressionReason
        ((~>)
          ((~>) compositeSequenceSource compositeSequenceIntermediate)
          (AtlasMap [AsciiStringLiteral "b", NaturalType])) of
      Left
          (AtlasMapFederationOperationRefuted
            AtlasMapFederationSubfederationHasMissingMember) -> True
      _ -> False)
  expectSpecification
    "bounded ascending range specification"
    boundedRange
    (NaturalRange 0 10)
    "2..5 ~> range 0 to 10"
  expectSpecification
    "bounded descending range specification"
    ((<..>) (natural 5) (natural 2))
    (NaturalRange 10 0)
    "5..2 ~> range 10 to 0"
  expectSpecification
    "open range specification"
    ((..+) (natural 2))
    (NaturalRangeUpwards 0)
    "2.. ~> range 0 up"
  expectSpecification
    "empty range specification"
    ((<..>) (natural 0) (natural 0))
    (NaturalRange 5 8)
    "0..0 ~> range 5 to 8"
  expectSpecification
    "flat total Atlas map specification"
    (AtlasMap [natural 2, natural 3, natural 4])
    (NaturalRange 0 10)
    "(2; 3; 4) ~> range 0 to 10"
  expectSpecification
    "EllipsisNatural specification into a ValuedNaturalRange"
    (natural 2)
    (ValuedNaturalRange 0 5)
    "2 ~> from 0 to 5"
  expectSpecification
    "computed EllipsisNatural specification into a ValuedNaturalRange"
    ((AST.+) (natural 1) (natural 1))
    (ValuedNaturalRange 0 5)
    "2 ~> from 0 to 5"
  expectSpecification
    "EllipsisNatural specification into a descending ValuedNaturalRange"
    (natural 2)
    (ValuedNaturalRange 5 0)
    "2 ~> from 5 to 0"
  expectSpecification
    "EllipsisNatural specification into Nat"
    (natural 2)
    NaturalType
    "2 ~> from 0 up"
  expectValue
      "ValuedNaturalRange subfederation specification composition"
      ((~>)
        ((~>) (natural 2) (ValuedNaturalRange 2 5))
        NaturalType) $ \value ->
    assert "Nat composition erases the intermediate valued range"
      (renderInterpretedValue value == "2 ~> from 0 up")
  expectValue
      "ValuedNaturalRange inclusion ignores traversal direction"
      ((~>)
        ((~>) (natural 2) (ValuedNaturalRange 2 5))
        (ValuedNaturalRange 5 0)) $ \value ->
    assert "valued subfederation composition retains the final direction"
      (renderInterpretedValue value == "2 ~> from 5 to 0")
  expectValue
      "NaturalRange subfederation specification composition"
      ((~>)
        ((~>)
          ((<..>) (natural 2) (natural 3))
          (NaturalRange 2 5))
        (NaturalRange 2 8)) $ \value ->
    assert "composition erases the intermediate subfederation"
      ( interpretedValueKind value == SpecificationValueKind
        && renderInterpretedValue value == "2..3 ~> range 2 to 8"
      )
  expectValue
      "finite NaturalRange subfederation of an up NaturalRange"
      ((~>)
        ((~>)
          ((<..>) (natural 3) (natural 5))
          (NaturalRange 2 5))
        (NaturalRangeUpwards 0)) $ \value ->
    assert "finite-to-up composition is canonicalized"
      (renderInterpretedValue value == "3..5 ~> range 0 up")
  expectValue
      "up NaturalRange subfederation composition"
      ((~>)
        ((~>)
          ((..+) (natural 3))
          (NaturalRangeUpwards 2))
        (NaturalRangeUpwards 0)) $ \value ->
    assert "up-to-up composition is canonicalized"
      (renderInterpretedValue value == "3.. ~> range 0 up")
  expectValue
      "descending NaturalRange subfederation composition"
      ((~>)
        ((~>)
          ((<..>) (natural 5) (natural 2))
          (NaturalRange 6 1))
        (NaturalRange 8 0)) $ \value ->
    assert "descending composition preserves the original source"
      (renderInterpretedValue value == "5..2 ~> range 8 to 0")
  expectValue
      "singleton NaturalRange subfederation changes direction"
      ((~>)
        ((~>)
          ((<..>) (natural 2) (natural 3))
          (NaturalRange 2 2))
        (NaturalRange 5 0)) $ \value ->
    assert "a singleton federation belongs to either direction"
      (renderInterpretedValue value == "2..3 ~> range 5 to 0")
  expectNoMember
    "range outside the target NaturalRange is a counterexample"
    ((<..>) (natural 2) (natural 5))
    (NaturalRange 3 10)
  expectNoMember
    "open range cannot select a finite NaturalRange member"
    ((..+) (natural 2))
    (NaturalRange 0 10)
  expectNoMember
    "a noncontiguous total map has no NaturalRange member"
    (AtlasMap [natural 2, natural 4])
    (NaturalRange 0 10)
  expectNoMember
    "a one-page natural has no identity-pagination NaturalRange member"
    (natural 2)
    (NaturalRange 0 10)
  expectNoMember
    "a value outside a ValuedNaturalRange is a counterexample"
    (natural 6)
    (ValuedNaturalRange 0 5)
  expectNoMember
    "a range is not an EllipsisNatural value member"
    ((<..>) (natural 2) (natural 3))
    (ValuedNaturalRange 0 5)
  assert "a NaturalRange federation is not itself a TotalAtlasMap"
    (case interpretExpressionReason
        ((~>) (NaturalRange 2 5) (NaturalRange 0 10)) of
      Left (ExpectedTotalAtlasMap RangeValueKind) -> True
      _ -> False)
  expectNoMember
    "a different singleton total target has no matching member"
    ((<..>) (natural 2) (natural 5))
    ((<..>) (natural 0) (natural 10))
  assert "composition rejects an intermediate federation with a missing member"
    (case interpretExpressionReason
        ((~>)
          ((~>)
            ((<..>) (natural 2) (natural 4))
            (NaturalRange 2 5))
          (NaturalRange 2 3)) of
      Left
          (AtlasMapFederationOperationRefuted
            AtlasMapFederationSubfederationHasMissingMember) -> True
      _ -> False)
  assert "composition rejects incompatible NaturalRange directions"
    (case interpretExpressionReason
        ((~>)
          ((~>)
            ((<..>) (natural 2) (natural 3))
            (NaturalRange 2 5))
          (NaturalRange 5 2)) of
      Left
          (AtlasMapFederationOperationRefuted
            AtlasMapFederationSubfederationHasMissingMember) -> True
      _ -> False)
  assert "an up intermediate federation is not finite"
    (case interpretExpressionReason
        ((~>)
          ((~>)
            ((..+) (natural 3))
            (NaturalRangeUpwards 2))
          (NaturalRange 0 10)) of
      Left
          (AtlasMapFederationOperationRefuted
            AtlasMapFederationSubfederationHasMissingMember) -> True
      _ -> False)
  assert "an unknown subfederation relation remains undecided"
    (case interpretExpressionReason
        ((~>)
          ((~>)
            ((<..>) (natural 2) (natural 3))
            (NaturalRange 2 5))
          ((<..>) (natural 0) (natural 10))) of
      Left
          (AtlasMapFederationOperationUndecidable
            (NoAtlasMapFederationDecisionProcedure
              AtlasMapFederationSubfederation)) -> True
      _ -> False)
  assert "NaturalRange and ValuedNaturalRange are distinct federation families"
    (case interpretExpressionReason
        ((~>)
          ((~>) (natural 2) (ValuedNaturalRange 0 5))
          (NaturalRange 0 5)) of
      Left
          (AtlasMapFederationOperationRefuted
            AtlasMapFederationSubfederationHasMissingMember) -> True
      _ -> False)

testIdentifiers :: IO ()
testIdentifiers = do
  mapM_ (\name -> mapM_ (\source ->
      expectSourceValue source source $ \value ->
        assert source (renderInterpretedValue value == "true"))
      [ "$" <> name <> " = (" <> name <> " : ())"
      , "$" <> name <> " of (" <> name <> " : ())"
      , "(" <> name <> " : ()) of $" <> name
      , "($" <> name <> " ~> (" <> name <> " : ())) = $" <> name
      ]) ["abc", "Value", "_private", "Nothing"]
  mapM_ (\name ->
      let source =
            "($" <> name <> " ~> (" <> name <> "? : ())) of ("
              <> name <> "? : ())"
      in expectSourceValue source source $ \value ->
        assert source (renderInterpretedValue value == "true"))
    ["abc", "Value", "Nothing"]
  let identifier identifierString typeAnnotation =
        IdentifierOperation
          (IdentifierString identifierString)
          typeAnnotation
          Nothing
      assignment identifierString typeAnnotation givenValue =
        IdentifierOperation
          (IdentifierString identifierString)
          typeAnnotation
          (Just givenValue)
      xNatural = identifier "x" NaturalType
      xAssignment = assignment "x" NaturalType (natural 5)
      valueUnit = identifier "Value" (AtlasMap [])
      equivalentSpecification =
        (identifier "x" (natural 5)) ~> xNatural
  case ( interpretExpressionReason xAssignment
       , interpretExpressionReason equivalentSpecification
       ) of
    (Right assignmentValue, Right specificationValue) ->
      assert "assignment and equivalent specification share one canonical form"
        ( renderInterpretedValue assignmentValue
            == renderInterpretedValue specificationValue
          && renderInterpretedValue assignmentValue
            == "x : from 0 up := 5"
        )
    (Left rejection, _) ->
      fail ("assignment construction was rejected: " <> show rejection)
    (_, Left rejection) ->
      fail ("equivalent specification was rejected: " <> show rejection)
  expectValue
      "assignment equals its equivalent specification"
      (AST.equal xAssignment equivalentSpecification) $ \value ->
    assert "shared canonical spelling denotes equal values"
      (renderInterpretedValue value == "true")
  expectValue
      "quoted reserved identifier"
      (identifier "Str" NaturalType) $ \value ->
    assert "reserved identifier names render with their full-string spelling"
      (renderInterpretedValue value == "Str : from 0 up")
  expectValue "unit identifier" valueUnit $ \value ->
    assert "a unit identifier canonicalizes to its identifier string"
      ( interpretedValueKind value == AsciiStringValueKind
        && renderInterpretedValue value == "$Value"
      )
  expectValue
      "unit identifier string equality"
      (AST.equal (AsciiStringLiteral "Value") valueUnit) $ \value ->
    assert "identifier strings and unit identifiers are definitionally equal"
      (renderInterpretedValue value == "true")
  expectValue
      "unit assignment"
      (assignment "Value" (AtlasMap []) (AtlasMap [])) $ \value ->
    assert "a unit assignment also canonicalizes to its identifier string"
      (renderInterpretedValue value == "$Value")
  expectValue "simple identifier type" xNatural $ \value ->
    assert "identifier types retain their two-position map view"
      ( interpretedValueKind value == DependentIdentifierTypeValueKind
        && interpretedMapCardinality (interpretedMap value) == 2
        && interpretedMapFinalOrderType (interpretedMap value)
          == finiteOrdinal 2
        && renderInterpretedValue value == "x : from 0 up"
      )
  let xFive = identifier "x" (natural 5)
      xFiveAssignment = assignment "x" (natural 5) (natural 5)
  expectValue "total simple identifier type" xFive $ \value ->
    assert "a simple identifier over a total map keeps canonical type syntax"
      ( interpretedValueKind value == DependentIdentifierTypeValueKind
        && renderInterpretedValue value == "x : 5"
      )
  expectValue
      "total identifier addition"
      (AST.equal
        ((AST.+) xFive (identifier "y" (natural 10)))
        (natural 15)) $ \value ->
    assert "total numerical identifier maps participate in addition"
      (renderInterpretedValue value == "true")
  expectSourceValue
      "numerical assignment coercion"
      "(x : Int := 12) * 5 = 60" $ \value ->
    assert "an identifier exposes its numerical specification to arithmetic"
      (renderInterpretedValue value == "true")
  expectValue
      "total identifiers in finite numerical operators"
      (AST.equal
        ((AST.*)
          ((AST.-) (identifier "y" (natural 10)) xFive)
          (identifier "z" (natural 2)))
        (natural 10)) $ \value ->
    assert "subtraction and multiplication share identifier coercion"
      (renderInterpretedValue value == "true")
  expectValue
      "total identifiers in exponentiation"
      (AST.equal
        ((AST.^) xFive (identifier "power" (natural 2)))
        (natural 25)) $ \value ->
    assert "exponentiation shares identifier coercion"
      (renderInterpretedValue value == "true")
  expectValue
      "total identifier unary minus"
      (AST.equal (AST.minus xFive) (AST.minus (natural 5))) $ \value ->
    assert "unary minus shares identifier coercion"
      (renderInterpretedValue value == "true")
  let omegaSquared = ordinalExponent (...) (natural 2)
  expectValue
      "transfinite identifier addition"
      (AST.equal
        (ordinalSum
          (identifier "x" omegaSquared)
          (identifier "y" (natural 1)))
        (ordinalSum omegaSquared (natural 1))) $ \value ->
    assert "higher-rank identifiers retain ordinal arithmetic"
      (renderInterpretedValue value == "true")
  expectValue
      "identity assignment specifies its total identifier"
      ((~>) xFiveAssignment xFive) $ \value ->
    assert "assignment-to-identifier identity canonicalizes"
      (renderInterpretedValue value == "x : 5")
  expectValue
      "total identifier specifies its identity assignment"
      ((~>) xFive xFiveAssignment) $ \value ->
    assert "identifier-to-assignment identity canonicalizes"
      (renderInterpretedValue value == "x : 5")
  expectValue
      "identifier string access"
      ((<@>) xNatural (natural 0)) $ \value ->
    assert "position zero projects the identifier string"
      ( interpretedValueKind value == AsciiStringValueKind
        && renderInterpretedValue value == "$x"
      )
  expectValue
      "identifier value access"
      ((<@>) xNatural (natural 1)) $ \value ->
    assert "position one projects the wrapped federation"
      (renderInterpretedValue value == "from 0 up")
  expectValue
      "whole identifier access"
      ((<@>)
        xNatural
        ((<..>) (natural 0) (natural 2))) $ \value ->
    assert "selecting both positions preserves identifier provenance"
      (renderInterpretedValue value == "x : from 0 up")
  expectValue "full assignment" xAssignment $ \value ->
    assert "assignment remains a marked specification"
      ( interpretedValueKind value == SpecificationValueKind
        && renderInterpretedValue value == "x : from 0 up := 5"
      )
  expectValue
      "identifier specification canonicalizes as assignment"
      ((~>) (identifier "x" (natural 5)) xNatural) $ \value ->
    assert "the equivalent identifier specification uses assignment syntax"
      (renderInterpretedValue value == "x : from 0 up := 5")
  expectValue
      "assignment specification into its own target"
      ((~>)
        (assignment "a" NaturalType (natural 5))
        (identifier "a" NaturalType)) $ \value ->
    assert "composition with the assignment target preserves the assignment"
      ( interpretedValueKind value == SpecificationValueKind
        && renderInterpretedValue value == "a : from 0 up := 5"
      )
  expectValue
      "assignment widens through identifier subfederations"
      ((~>)
        (assignment "a" (ValuedNaturalRange 0 10) (natural 5))
        (identifier "a" NaturalType)) $ \value ->
    assert "identifier composition retains canonical assignment syntax"
      (renderInterpretedValue value == "a : from 0 up := 5")
  let d28 = assignment "d" (natural 28) (natural 28)
      d25To35 = assignment "d" (ValuedNaturalRange 25 35) (natural 28)
      d20To40 = assignment "d" (ValuedNaturalRange 20 40) (natural 28)
      d0To100 = identifier "d" (ValuedNaturalRange 0 100)
  expectValue
      "assignment chain widens through nested valued ranges"
      ((~>) ((~>) ((~>) d28 d25To35) d20To40) d0To100) $ \value ->
    assert "nested assignment specifications retain the original value"
      (renderInterpretedValue value == "d : from 0 to 100 := 28")
  expectValue
      "assignment identifier-string access"
      ((<@>) xAssignment (natural 0)) $ \value ->
    assert "the identifier-string fiber is an identity specification and coerces"
      (renderInterpretedValue value == "$x")
  expectValue
      "assignment value access"
      ((<@>) xAssignment (natural 1)) $ \value ->
    assert "the value fiber is the underlying specification"
      ( interpretedValueKind value == SpecificationValueKind
        && renderInterpretedValue value == "5 ~> from 0 up"
      )
  expectValue
      "binary assignment canonicalization"
      (assignment "x" (natural 5) (natural 5)) $ \value ->
    assert "equal total type and value use canonical identifier syntax"
      ( interpretedValueKind value == SpecificationValueKind
        && renderInterpretedValue value == "x : 5"
      )
  expectValue
      "binary assignment value access"
      ((<@>)
        (assignment "x" (natural 5) (natural 5))
        (natural 1)) $ \value ->
    assert "an identity value fiber is coerced to its value"
      (renderInterpretedValue value == "5")
  let sequenceSource =
        AtlasMap [identifier "x" (natural 5), identifier "y" (natural 6)]
      sequenceTarget =
        AtlasMap [identifier "x" NaturalType, identifier "y" NaturalType]
  expectValue
      "identifier sequence access"
      ((<@>) sequenceTarget (natural 0)) $ \value ->
    assert "sequence access preserves the selected identifier type"
      (renderInterpretedValue value == "x : from 0 up")
  expectValue
      "identifier sequence specification"
      ((~>) sequenceSource sequenceTarget) $ \value ->
    assert "identifier selection composes pointwise through sequences"
      ( interpretedValueKind value == SpecificationValueKind
        && renderInterpretedValue value
          == "(x : 5; y : 6) ~> (x : from 0 up; y : from 0 up)"
      )
  assert "different identifier strings do not specify each other"
    (case interpretExpressionReason
        ((~>)
          (identifier "x" (natural 5))
          (identifier "y" NaturalType)) of
      Left (IdentifierStringMismatch expected given) ->
        expected == "$y" && given == "$x"
      _ -> False)
  assert "assignment widening reports a mismatched identifier string"
    (case interpretExpressionReason
        ((~>)
          (assignment "b" (natural 10) (natural 10))
          (identifier "a" NaturalType)) of
      Left (IdentifierStringMismatch expected given) ->
        expected == "$a" && given == "$b"
      _ -> False)
  assert "an identifier value outside its annotation gets a direct type error"
    (case interpretExpressionReason
        ((~>)
          (identifier "x" (natural 12))
          (identifier "x" (ValuedNaturalRange 1 10))) of
      Left (GivenValueOutsideTypeAnnotation expected given) ->
        expected == "from 1 to 10" && given == "12"
      _ -> False)
  assert "a failed annotation widening reports the intermediate annotation"
    (case interpretExpressionReason
        ((~>)
          ((~>)
            (assignment "x" (natural 8) (natural 8))
            (identifier "x" (ValuedNaturalRange 5 20)))
          (identifier "x" (ValuedNaturalRange 1 10))) of
      Left (IntermediateTypeAnnotationOutsideTarget expected given) ->
        expected == "from 1 to 10"
          && given == "from 5 to 20"
      _ -> False)
  assert "an assignment outside its annotation gets a direct type error"
    (case interpretExpressionReason
        (assignment
          "a"
          NaturalType
          (SuperEllipsisRange (natural 1) (natural 3))) of
      Left (GivenValueOutsideTypeAnnotation expected given) ->
        expected == "from 0 up" && given == "1..3"
      _ -> False)
  case ( interpretExpressionReason (natural 5)
       , interpretExpressionReason NaturalType
       ) of
    (Right five, Right naturals) -> do
      let dependentIdentifierString canonical =
            case canonical of
              Types.CanonicalExplicit _ ordinalValue ->
                maybe "transfinite" (("n" <>) . show)
                  (naturalAtOrdinal ordinalValue)
              _ -> "natural"
          source =
            Types.dependentIdentifierTypeValue "n" dependentIdentifierString five
          target =
            Types.dependentIdentifierTypeValue "n" dependentIdentifierString naturals
      case Types.accessValues source (Types.naturalValue 0) of
        Left rejection ->
          fail
            ("dependent identifier string access was rejected: "
              <> show rejection)
        Right value ->
          assert "dependent string access evaluates the selected identifier string"
            (renderInterpretedValue value == "$n5")
      case Types.specifyValues source target of
        Left rejection ->
          fail
            ("dependent identifier specification was rejected: "
              <> show rejection)
        Right specification -> do
          assert "dependent identifiers use the root specification rule"
            (interpretedValueKind specification == SpecificationValueKind)
          case Types.accessValues specification (Types.naturalValue 0) of
            Left rejection ->
              fail
                ("dependent identifier specification access was rejected: "
                  <> show rejection)
            Right identifierStringFiber ->
              assert "dependent identifier-string fibers remain specifications"
                ( interpretedValueKind identifierStringFiber
                    == SpecificationValueKind
                )
    _ -> fail "dependent identifier setup failed"

testTypedRejections :: IO ()
testTypedRejections = do
  assert "non-ASCII programmatic string literals are rejected"
    (case interpretExpressionReason (AsciiStringLiteral "λ") of
      Left (InvalidAsciiStringCharacter 'λ') -> True
      _ -> False)
  assert "maps are rejected as numerical operands with a specific side"
    (case interpretExpressionReason
        ((AST.+) (AtlasMap [natural 0, natural 1]) (natural 1)) of
      Left (ExpectedFiniteIntegerOperand LeftOperand MapValueKind) -> True
      _ -> False)
  assert "non-total identifiers are rejected as numerical operands"
    (case interpretExpressionReason
        ((AST.+) (AST.dependentIdentifierType "x" NaturalType) (natural 1)) of
      Left
          (ExpectedFiniteIntegerOperand
            LeftOperand DependentIdentifierTypeValueKind) -> True
      _ -> False)
  assert "computed non-natural values are rejected as exponents"
    (case interpretExpressionReason
        ((AST.^)
          (natural 2)
          (ordinalSum (...) (natural 0))) of
      Left (ExpectedNaturalExponent ExplicitOrdinalValueKind) -> True
      _ -> False)
  expectValue
      "out-of-bounds concrete range access clips"
      ((<@>)
        (AtlasMap (map natural [0 .. 2]))
        ((<..>)
          (natural 2)
          (natural 5))) $ \value ->
    assert "the existing suffix remains"
      (renderInterpretedValue value == "2")
  assert "infinite-rank access reports the map order type"
    (case interpretExpressionReason
        ((<@>)
          (AtlasMap (map natural [0 .. 2]))
          (...)) of
      Left
          (AccessRejected
            (AccessPositionOutOfBounds position mapOrderType)) ->
        position == omega && mapOrderType == finiteOrdinal 3
      _ -> False)
  expectValue
      "ordinary open ranges clip against finite maps"
      ((<@>)
        ((<.>)
          (natural 1)
          ((<.>) (natural 2) (natural 3)))
        ((..+) (natural 1))) $ \value ->
    assert "the available tail is selected"
      (renderInterpretedValue value == "(2; 3)")
  assert "overlapping access ranges retain the exact overlap rejection"
    (case interpretExpressionReason
        ((<@>)
          (AtlasMap (map natural [0 .. 9]))
          ((<.>)
            ((<..>)
              (natural 2)
              (natural 5))
            ((<..>)
              (natural 4)
              (natural 7)))) of
      Left
          (RangeConcatenationRejected
            (SuperEllipsisRangesOverlap _ _ lower upper)) ->
        lower == finiteOrdinal 4 && upper == finiteOrdinal 5
      _ -> False)

testLocatedRejection :: IO ()
testLocatedRejection = do
  let sourceSpan =
        SourceSpan
          "<test>"
          (SourcePosition 4 1 5)
          (SourcePosition 10 1 11)
      expressionValue =
        (AST.+) (AtlasMap [natural 0, natural 1]) (natural 1)
  assert "typed interpretation errors retain their supplied source span"
    (case interpretLocatedExpression (Located sourceSpan expressionValue) of
      Left
          (DatraError
            (Just actualSpan)
            (ExpectedFiniteIntegerOperand LeftOperand MapValueKind)) ->
        actualSpan == sourceSpan
      _ -> False)
  assert "English interpretation errors are localized only at display time"
    (case interpretLocatedExpression (Located sourceSpan expressionValue) of
      Left valueError ->
        renderDatraError English valueError
          == "<test>:1:5: left operand must be a finite integer\n"
              <> "  actual value kind: map"
      Right _ -> False)
  assert "Romanian interpretation errors are localized only at display time"
    (case interpretLocatedExpression (Located sourceSpan expressionValue) of
      Left valueError ->
        renderDatraError Romanian valueError
          == "<test>:1:5: operandul stâng trebuie să fie un întreg finit\n"
              <> "  tipul efectiv al valorii: hartă"
      Right _ -> False)
  let ambiguousTemplate =
        StringTemplate
          [ StringTemplateInterpolation NaturalType
          , StringTemplateInterpolation NaturalType
          ]
  assert "string-template ambiguity has a specific English diagnostic"
    (case interpretLocatedExpression
        (Located sourceSpan ambiguousTemplate) of
      Left valueError ->
        renderDatraError English valueError
          == "<test>:1:5: ambiguous string template\n"
              <> "  the template does not map each source configuration to a unique string"
      Right _ -> False)
  assert "string-template ambiguity has a specific Romanian diagnostic"
    (case interpretLocatedExpression
        (Located sourceSpan ambiguousTemplate) of
      Left valueError ->
        renderDatraError Romanian valueError
          == "<test>:1:5: șablon de șir ambiguu\n"
              <> "  șablonul nu mapează fiecare configurație sursă la un șir unic"
      Right _ -> False)
  let invalidAssignment =
        IdentifierOperation
          (IdentifierString "a")
          NaturalType
          (Just (SuperEllipsisRange (natural 1) (natural 3)))
  assert "assignment mismatches have a concise English diagnostic"
    (case interpretLocatedExpression (Located sourceSpan invalidAssignment) of
      Left valueError ->
        renderDatraError English valueError
          == "<test>:1:5: the given value is outside the type annotation\n"
              <> "  expected: from 0 up\n"
              <> "  given: 1..3"
      Right _ -> False)
  assert "assignment mismatches have a concise Romanian diagnostic"
    (case interpretLocatedExpression (Located sourceSpan invalidAssignment) of
      Left valueError ->
        renderDatraError Romanian valueError
          == "<test>:1:5: valoarea dată este în afara adnotării de tip\n"
              <> "  așteptat: from 0 up\n"
              <> "  dat: 1..3"
      Right _ -> False)
  let mismatchedIdentifier =
        (~>)
          (IdentifierOperation
            (IdentifierString "b")
            (natural 10)
            (Just (natural 10)))
          (IdentifierOperation (IdentifierString "a") NaturalType Nothing)
  assert "identifier mismatches show expected and given identifier strings"
    (case interpretLocatedExpression
        (Located sourceSpan mismatchedIdentifier) of
      Left valueError ->
        renderDatraError English valueError
          == "<test>:1:5: the identifier string does not match\n"
              <> "  expected: $a\n"
              <> "  given: $b"
      Right _ -> False)
  let valueOutsideIdentifierAnnotation =
        (~>)
          (IdentifierOperation (IdentifierString "x") (natural 12) Nothing)
          (IdentifierOperation
            (IdentifierString "x")
            (ValuedNaturalRange 1 10)
            Nothing)
  assert "identifier membership errors show canonical expected and given values"
    (case interpretLocatedExpression
        (Located sourceSpan valueOutsideIdentifierAnnotation) of
      Left valueError ->
        renderDatraError English valueError
          == "<test>:1:5: the given value is outside the type annotation\n"
              <> "  expected: from 1 to 10\n"
              <> "  given: 12"
      Right _ -> False)
  let incompatibleIntermediateAnnotation =
        (~>)
          ((~>)
            (IdentifierOperation
              (IdentifierString "x")
              (natural 8)
              (Just (natural 8)))
            (IdentifierOperation
              (IdentifierString "x")
              (ValuedNaturalRange 5 20)
              Nothing))
          (IdentifierOperation
            (IdentifierString "x")
            (ValuedNaturalRange 1 10)
            Nothing)
  assert "failed annotation widening identifies the intermediate federation"
    (case interpretLocatedExpression
        (Located sourceSpan incompatibleIntermediateAnnotation) of
      Left valueError ->
        renderDatraError English valueError
          == "<test>:1:5: the intermediate type annotation does not fit in the target type annotation\n"
              <> "  expected: from 1 to 10\n"
              <> "  given: from 5 to 20"
      Right _ -> False)
  let overlapExpression =
        (<@>)
          (AtlasMap (map natural [0 .. 9]))
          ((<.>)
            ((<..>)
              (natural 2)
              (natural 5))
            ((<..>)
              (natural 4)
              (natural 7)))
  assert "overlap diagnostics use source range notation and half-open bounds"
    (case interpretLocatedExpression (Located sourceSpan overlapExpression) of
      Left valueError ->
        renderDatraError English valueError
          == "<test>:1:5: cannot use overlapping ranges to access a map\n"
              <> "  first range: 2..5\n"
              <> "  second range: 4..7\n"
              <> "  overlap: 4..5 (upper bound excluded)"
      Right _ -> False)
  assert "Romanian overlap diagnostics use Datra range notation"
    (case interpretLocatedExpression (Located sourceSpan overlapExpression) of
      Left valueError ->
        renderDatraError Romanian valueError
          == "<test>:1:5: intervalele suprapuse nu pot fi folosite pentru a accesa o hartă\n"
              <> "  primul interval: 2..5\n"
              <> "  al doilea interval: 4..7\n"
              <> "  suprapunere: 4..5 (limita superioară este exclusă)"
      Right _ -> False)


testNamedAccess :: IO ()
testNamedAccess = do
  mapM_ (\(source, expected) -> expectSourceValue source source $ \value ->
      assert (source <> " preserves the selected field") (renderInterpretedValue value == expected))
    [ ("{a : Nat := 5; b : Str}.a", "a : Nat := 5")
    , ("{b : Str; a : Nat := 5}.a", "a : Nat := 5")
    , ("{a? : Nat := 5; b : Str}.a", "a : Nat := 5")
    , ( "({b:8;2} ~> {a?:Nat:=2;b?:Nat}).b"
      , "b : Nat := 8"
      )
    , ("{a:Nat:=5;b:Str}.a of (a:Nat)", "true")
    , ( "{a:Nat:=5;b:Str}.a ~> (a:Int)"
      , "a : " <> sourceIntType <> " := 5"
      )
    , ("(x:3, {a:5;b:8}).b", "b : 8")
    , ("{a:5;b:8}.a[1] * 2", "10")
    ]
  mapM_ (\(source, expected) ->
      expectSourceRejection source source (== NamedAccessFailed expected))
    [ ("{a:2;b:3}.missing", Types.NamedFieldNotFound "missing")
    , ("{a:2;a:3}.a", Types.NamedFieldAmbiguous "a")
    , ("{}.a", Types.NamedFieldNotFound "a")
    ]
