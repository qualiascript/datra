{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE PostfixOperators #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeApplications #-}

module Main (main) where

import AsciiMap
import qualified AsciiString
import Atlas
  ( Atlas
  , atlasCardinality
  , atlasDataAt
  , atlasOriginCell
  , atlasPageElements
  , atlasWitness
  , withAtlasMorphismImage
  )
import AtlasConfederation
  ( AtlasConfederationObject
  , MergedAtlasConfederationScope
  , SingletonAtlasConfederationScope
  , identityAtlasConfederationHom
  , mergeAtlasConfederations
  , rightAtlasConfederationInclusion
  , singletonAtlasConfederation
  )
import AtlasFederation
  ( AtlasFederationSeparation (SeparatedCorrespondingPageElements)
  , atlasFederationIndexDominion
  , atlasFederationSeparation
  )
import AtlasCoveredPageElement
  ( atlasCoveredPageElement
  , withAtlasCoveredPageElement
  )
import AtlasMap (AtlasMap, withAtlasMapExtent)
import AtlasTransposal
  ( atlasTransposalElement
  , withAtlasTransposalElement
  )
import AtlasSequence (atlasSequenceDatumMember)
import ChainedDominionAtlas (ChainedDominionAtlas)
import Control.Monad (join)
import Dominion
import Chain
  ( chain
  , chainIndex
  , chainObjectAt
  , chainOrderType
  , spine
  )
import DatraOrdinal
  ( addOrdinals
  , finiteOrdinal
  , naturalAtOrdinal
  , omega
  , ordinal
  , ordinalCoefficients
  )
import qualified DatraTypes as Types
import DatraLanguage.AST qualified as AST
import DomanialInclusion (dominionAtlas, dominionCellDataValue)
import Dot
  ( Dot
  , dot
  , dotAtlas
  , dotAtlasMap
  , dotDominion
  , dotTerminal
  )
import DomanialInsertion (applyInsertion, preimage)
import DatraLanguage.Diagnostics
  ( LocalizedMessage (LocalizedMessage)
  , SourcePosition (SourcePosition)
  , SourceSpan (SourceSpan)
  , atSourceSpan
  )
import DatraLanguage.Diagnostics.Application
  ( CommandLineOptionFailure (UnsupportedEvaluationMode)
  , ModuleLoadFailure (CyclicModuleImport)
  , ParseFailure (ParseFailure)
  , SyntaxExpansionFailure (InvalidSyntaxControlCaptures)
  )
import DatraLanguage.Diagnostics.Localization
  ( Locale (English, Romanian)
  , LocalizedDiagnostic (localizeDiagnostic)
  , renderDatraError
  )
import Ellipsis
import EllipsisNatural qualified as DatraNatural
import EllipsisInteger qualified as DatraInteger
import BooleanType qualified as DatraBoolean
import IntegerRange qualified
import IntegerType qualified
import ValuedIntegerRange qualified
import MapOperators
import MapOperators.OrderedAtlasMap qualified as OrderedValues
import NaturalRange
import NaturalType qualified
import Numeric.Natural (Natural)
import NumericalOperators.Range
  ( boundedSuperEllipsisRange
  , openMinusSuperEllipsisRange
  , openPlusSuperEllipsisRange
  )
import PageElements
  ( pageElement
  , pageElementIndex
  , pageElementPage
  , pageElementPosition
  , withPageElement
  )
import OrderedAtlasTransposal
  ( mapOrderedAtlasTransposalObject
  , mapOrderedAtlasTransposalData
  , orderedAtlasTransposalPreimage
  )
import StableAtlasTransversal
  ( stableAtlasTransversalPreservesCoverage
  )
import StableConfederalData
  ( StableConfederalData
  , StableConfederalDataHom
  , mapStableConfederalData
  , mapStableConfederalDataHom
  )
import SuperEllipsis
import SuperEllipsisInsertion
import qualified SuperEllipsisRange as SuperRange
import SuperEllipsisValue
import ValuedNaturalRange

import Data.Maybe (fromMaybe, isNothing)
import Hedgehog qualified as H
import Hedgehog.Gen qualified as Gen
import Hedgehog.Range qualified as Range
import qualified NumericalOperators as Numeric
import Test.Tasty (TestTree, defaultMain, testGroup)
import Test.Tasty.Hedgehog (testProperty)
import Test.Tasty.HUnit (assertBool, testCase)

main :: IO ()
main = defaultMain testTree

testTree :: TestTree
testTree =
  testGroup "Datra types"
    [ testGroup "examples"
        [ testCase "ordinal inspection" testOrdinalInspection
        , testCase "diagnostics" testDiagnostics
        , testCase "evaluation boundary" testEvaluationBoundary
        , testCase "ASCII map" testAsciiMap
        , testCase "ASCII string" testAsciiString
        , testCase "access operator" testAccessOperator
        , testCase "dot" testDot
        , testCase "sequential operator" testSequentialOperator
        , testCase "concatenation operator" testConcatOperator
        , testCase "grouped sequential expansion" testGroupedSequentialExpansion
        , testCase "complex operator structure" testComplexOperatorStructure
        , testCase "ellipsis" testEllipsis
        , testCase "super ellipsis" testSuperEllipsis
        , testCase "super ellipsis range" testSuperEllipsisRange
        , testCase "super ellipsis insertion" testSuperEllipsisInsertion
        , testCase "super ellipsis insertion dominion" testSuperEllipsisInsertionDominion
        , testCase "rank-one range" testRankOneRange
        , testCase "rank-one range merge" testRankOneRangeMerge
        , testCase "rank-one range analysis" testRankOneRangeAnalysis
        , testCase "ellipsis natural" testEllipsisNatural
        , testCase "natural range" testNaturalRange
        , testCase "valued natural range" testValuedNaturalRange
        , testCase "integer ranges" testIntegerRanges
        , testCase "numerical operators" testNumericalOperators
        , testCase "typed and evaluated numerical semantics agree"
            testNumericalSemanticsAgreement
        , testCase "typing abstractions" testTypingAbstractions
        , testCase "argument schemas" testArgumentSchemas
        ]
    , testGroup "properties"
        [ testProperty "ASCII strings preserve every byte" propAsciiStringRoundTrip
        , testProperty "ASCII map lookup agrees with character codes" propAsciiMapLookup
        , testProperty "ordinal sequence append preserves order and lookup"
            propOrdinalSequenceAppend
        , testProperty "argument schema skip preserves a default"
            propArgumentSchemaSkipDefault
        ]
    ]

testOrdinalInspection :: IO ()
testOrdinalInspection = do
  assert "ordinal inspection exposes canonical coefficients"
    (ordinalCoefficients (ordinal [0, 2, 0, 3]) == [2, 0, 3])
  assert "zero has no canonical coefficients"
    (null (ordinalCoefficients (finiteOrdinal 0)))

testEvaluationBoundary :: IO ()
testEvaluationBoundary = do
  let nonemptyMap =
        Types.makeAtlasMap
          2
          [Types.naturalValue 0, Types.naturalValue 1]
  assert "DatraTypes rejects non-numerical operands without AST interpretation"
    (case Types.addValues nonemptyMap (Types.naturalValue 1) of
      Left
          (Types.ExpectedNumericalOperand
            Types.LeftOperand Types.MapValueKind) -> True
      _ -> False)
  assert "DatraTypes owns checked range construction"
    (case Types.boundedRangeValue
        (Types.formulationValue 1)
        (Types.naturalValue 2) of
      Left
          (Types.RangeConstructionRejected
            (SuperRange.SuperEllipsisRangeInvalidDescendingBounds
              start target)) ->
        start == omega && target == finiteOrdinal 2
      _ -> False)

testDiagnostics :: IO ()
testDiagnostics = do
  let sourceSpan =
        SourceSpan
          "<test>"
          (SourcePosition 4 1 5)
          (SourcePosition 12 1 13)
      reason = AccessPositionOutOfBounds
        (finiteOrdinal 4)
        (finiteOrdinal 3)
      localized = localizeDiagnostic English reason
      rendered = renderDatraError English (atSourceSpan sourceSpan reason)
      localizedRomanian = localizeDiagnostic Romanian reason
      renderedRomanian =
        renderDatraError Romanian (atSourceSpan sourceSpan reason)
  assert "English access localization has exact structured text"
    (localized
      == LocalizedMessage
          "the access insertion selects a position outside the map"
          [ "selected position: 4"
          , "map final-page order type: 3"
          ])
  assert "localized diagnostics render exact source position and text"
    (rendered
      == "<test>:1:5: the access insertion selects a position outside the map\n  selected position: 4\n  map final-page order type: 3")
  assert "Romanian access localization has exact structured text"
    (localizedRomanian
      == LocalizedMessage
          "inserția de acces selectează o poziție din afara hărții"
          [ "poziția selectată: 4"
          , "tipul de ordine al ultimei pagini din hartă: 3"
          ])
  assert "Romanian diagnostics retain source positions and diacritics"
    (renderedRomanian
      == "<test>:1:5: inserția de acces selectează o poziție din afara hărții\n  poziția selectată: 4\n  tipul de ordine al ultimei pagini din hartă: 3")
  assert "English diagnostics render omega in Datra notation"
    (localizeDiagnostic
        English
        (AccessInsertionRankExceedsMap omega (finiteOrdinal 256))
      == LocalizedMessage
          "the access insertion has a larger rank than the map"
          [ "insertion rank limit: (...)"
          , "map final-page order type: 256"
          ])
  assert "English diagnostics put ordinal coefficients on the right"
    (localizeDiagnostic
        English
        (AccessInsertionRankExceedsMap
          (ordinal [2, 0, 3])
          (finiteOrdinal 256))
      == LocalizedMessage
          "the access insertion has a larger rank than the map"
          [ "insertion rank limit: (...) ^ 2 * 2 + 3"
          , "map final-page order type: 256"
          ])
  assert "private optional parameters are localized from a structured error"
    ( localizeDiagnostic English
        (Types.PrivateParameterCannotBeOptional "_value")
        == LocalizedMessage
          "private function parameter cannot be optional"
          ["identifier: _value"]
      && localizeDiagnostic Romanian
        (Types.PrivateParameterCannotBeOptional "_value")
        == LocalizedMessage
          "parametrul privat al funcției nu poate fi opțional"
          ["identificator: _value"]
    )
  assert "function failures are localized from semantic fields"
    ( localizeDiagnostic English
        (Types.FunctionEvaluationFailed
          (Types.UnconstrainedInferredParameter "value"))
        == LocalizedMessage
          "cannot infer an unconstrained function parameter"
          ["parameter: value", "provide an explicit input type"]
      && localizeDiagnostic Romanian
        (Types.FunctionEvaluationFailed
          (Types.UnconstrainedInferredParameter "value"))
        == LocalizedMessage
          "nu se poate deduce un parametru de funcție fără constrângeri"
          ["parametru: value", "furnizați un tip de intrare explicit"]
    )
  assert "external failures are localized from semantic fields"
    ( localizeDiagnostic English
        (Types.ExternalEvaluationFailed
          (Types.UnsupportedExternalBackend "native"))
        == LocalizedMessage
          "external backend is not supported"
          ["backend: native"]
      && localizeDiagnostic Romanian
        (Types.ExternalEvaluationFailed
          (Types.UnsupportedExternalBackend "native"))
        == LocalizedMessage
          "backendul extern nu este acceptat"
          ["backend: native"]
    )
  assert "module failures are localized from semantic fields"
    ( localizeDiagnostic English
        (Types.ModuleEvaluationFailed (Types.ModuleNotLoaded "missing"))
        == LocalizedMessage "module was not loaded" ["module: missing"]
      && localizeDiagnostic Romanian
        (Types.ModuleEvaluationFailed (Types.ModuleNotLoaded "missing"))
        == LocalizedMessage "modulul nu a fost încărcat" ["modul: missing"]
    )
  assert "unnamed imported files have a localized module failure"
    ( localizeDiagnostic English
        (Types.ModuleEvaluationFailed
          Types.ImportedModuleRequiresSimpleIdentifierType)
        == LocalizedMessage
          "imported file must yield a simple identifier type"
          ["use yield Name := value"]
      && localizeDiagnostic Romanian
        (Types.ModuleEvaluationFailed
          Types.ImportedModuleRequiresSimpleIdentifierType)
        == LocalizedMessage
          "fișierul importat trebuie să producă un tip de identificator simplu"
          ["folosiți yield Nume := valoare"]
      && localizeDiagnostic English
        (Types.ModuleEvaluationFailed Types.ImportedModuleRequiresTotalValue)
        == LocalizedMessage
          "imported identifier must have a total value" []
      && localizeDiagnostic Romanian
        (Types.ModuleEvaluationFailed Types.ImportedModuleRequiresTotalValue)
        == LocalizedMessage
          "identificatorul importat trebuie să aibă o valoare totală" []
      && localizeDiagnostic English
        (Types.ModuleEvaluationFailed
          Types.ImportAllRequiresTotalMapOfSimpleIdentifierTypes)
        == LocalizedMessage
          "import all requires a total map of simple identifier types" []
      && localizeDiagnostic Romanian
        (Types.ModuleEvaluationFailed
          Types.ImportAllRequiresTotalMapOfSimpleIdentifierTypes)
        == LocalizedMessage
          "import all necesită o hartă totală de tipuri de identificator simplu" []
    )
  assert "named-access failures are localized from semantic fields"
    ( localizeDiagnostic English
        (Types.NamedAccessFailed (Types.NamedFieldNotFound "field"))
        == LocalizedMessage "named field does not exist" ["field: field"]
      && localizeDiagnostic Romanian
        (Types.NamedAccessFailed (Types.NamedFieldNotFound "field"))
        == LocalizedMessage "câmpul denumit nu există" ["câmp: field"]
    )
  assert "noncanonical identifier annotations are localized structurally"
    ( localizeDiagnostic English Types.NonCanonicalIdentifierTypeAnnotation
        == LocalizedMessage
          "identifier type annotation is not canonical"
          ["identifier type annotations must implement canonical toString"]
      && localizeDiagnostic Romanian Types.NonCanonicalIdentifierTypeAnnotation
        == LocalizedMessage
          "adnotarea de tip a identificatorului nu este canonică"
          ["adnotările de tip ale identificatorilor trebuie să implementeze toString canonic"]
    )
  assert "parser failures have exact bilingual localization"
    ( localizeDiagnostic English (ParseFailure "bad token")
        == LocalizedMessage "source could not be parsed" ["bad token"]
      && localizeDiagnostic Romanian (ParseFailure "bad token")
        == LocalizedMessage "sursa nu a putut fi analizată" ["bad token"]
    )
  assert "module-loading failures have exact bilingual localization"
    ( localizeDiagnostic English (CyclicModuleImport "cycle.datra")
        == LocalizedMessage "cyclic module import" ["module: cycle.datra"]
      && localizeDiagnostic Romanian (CyclicModuleImport "cycle.datra")
        == LocalizedMessage "import ciclic de modul" ["modul: cycle.datra"]
    )
  assert "syntax-expansion failures have exact bilingual localization"
    ( localizeDiagnostic English
        (InvalidSyntaxControlCaptures "datra.syntax.if" 3 2)
        == LocalizedMessage
          "syntax control adapter received invalid captures"
          [ "adapter: datra.syntax.if"
          , "expected captures: 3"
          , "given captures: 2"
          ]
      && localizeDiagnostic Romanian
        (InvalidSyntaxControlCaptures "datra.syntax.if" 3 2)
        == LocalizedMessage
          "adaptorul de control sintactic a primit capturi nevalide"
          [ "adaptor: datra.syntax.if"
          , "capturi așteptate: 3"
          , "capturi primite: 2"
          ]
    )
  assert "CLI-option failures have exact bilingual localization"
    ( localizeDiagnostic English (UnsupportedEvaluationMode "fast")
        == LocalizedMessage
          "evaluation mode is not supported"
          [ "given mode: fast"
          , "expected dev, development, prod, or production"
          ]
      && localizeDiagnostic Romanian (UnsupportedEvaluationMode "fast")
        == LocalizedMessage
          "modul de evaluare nu este acceptat"
          [ "mod furnizat: fast"
          , "se așteaptă dev, development, prod sau production"
          ]
    )

assert :: String -> Bool -> IO ()
assert = assertBool

testArgumentSchemas :: IO ()
testArgumentSchemas = do
  naturalType <- expectRight "construct Nat" Types.naturalTypeValue
  integerType <- expectRight "construct Int" Types.integerTypeValue
  let naturalExpression =
        AST.IdentifierReference (AST.IdentifierString "Nat")
      evaluateNatural expression
        | expression == naturalExpression = Right naturalType
        | otherwise = Left (Types.UnknownIdentifier "unexpected test expression")
      privateOptional = AST.EitherType
        (AST.IdentifierOperation
          (AST.IdentifierString "_value") naturalExpression Nothing)
        naturalExpression
  assert "private optional parameters use a structured boundary error"
    (case Types.compileParameters evaluateNatural privateOptional of
      Left (Types.PrivateParameterCannotBeOptional "_value") -> True
      _ -> False)
  let defaultBase = Types.naturalValue 2
      exponentValue = Types.naturalValue 3
      positionalSchema = Types.orderedArgumentSchema 2
        [ Types.argumentSlotSchema
            (Just "_base") False naturalType (Just defaultBase)
        , Types.argumentSlotSchema
            (Just "_exponent") False naturalType Nothing
        ]
  skipped <- expectRight "construct skipped arguments"
    (Types.makeArgumentMap [Types.skipValue, exponentValue])
  completed <- expectRight "complete skipped default"
    (Types.argumentSchemaValuesComplete positionalSchema skipped)
  assert "a skip consumes its slot and retains that slot's default"
    (Types.interpretedCanonicalResult completed
      == Types.interpretedCanonicalResult
          (Types.makeAtlasMap 2 [defaultBase, exponentValue]))
  (_, bindings) <- expectRight "bind skipped positional arguments"
    (Types.overloadArgumentSchemaComplete positionalSchema skipped)
  assert "private positional parameters still produce body bindings"
    (map (\(name, value) -> (name, Types.interpretedCanonicalResult value)) bindings
      == [ ("_base", Types.interpretedCanonicalResult defaultBase)
         , ("_exponent", Types.interpretedCanonicalResult exponentValue)
         ])

  let requiredSchema = Types.orderedArgumentSchema 2
        [ Types.argumentSlotSchema Nothing False naturalType Nothing
        , Types.argumentSlotSchema Nothing False naturalType Nothing
        ]
  assert "a complete call rejects an explicitly skipped required slot"
    (case Types.argumentSchemaValuesComplete requiredSchema skipped of
      Left (Types.OverloadError Types.OverloadSkippedRequiredSlot) -> True
      _ -> False)

  text <- expectRight "construct ASCII string" (Types.asciiStringValue "value")
  reordered <- expectRight "construct uniquely reorderable arguments"
    (Types.makeArgumentMap [text, Types.naturalValue 7])
  let reorderSchema = Types.unorderedArgumentSchema
        [ Types.argumentSlotSchema (Just "x") False integerType Nothing
        , Types.argumentSlotSchema
            (Just "label") False Types.stringTypeValue Nothing
        ]
  (_, reorderedBindings) <- expectRight "uniquely reorder arguments"
    (Types.overloadArgumentSchemaComplete reorderSchema reordered)
  assert "an argument map uses its sole type-correct reordering"
    (map (\(name, value) -> (name, Types.interpretedCanonicalResult value))
        reorderedBindings
      == [ ("x", Types.interpretedCanonicalResult (Types.naturalValue 7))
         , ("label", Types.interpretedCanonicalResult text)
         ])

expectRight :: Show error => String -> Either error value -> IO value
expectRight label result =
  case result of
    Right value -> pure value
    Left failure -> fail (label <> ": " <> show failure)

propArgumentSchemaSkipDefault :: H.Property
propArgumentSchemaSkipDefault = H.property $ do
  defaultValue <- H.forAll (Gen.integral (Range.linear 0 10000))
  suppliedValue <- H.forAll (Gen.integral (Range.linear 0 10000))
  naturalType <- H.evalEither Types.naturalTypeValue
  let expectedDefault = Types.naturalValue defaultValue
      expectedSupplied = Types.naturalValue suppliedValue
      schema = Types.orderedArgumentSchema 2
        [ Types.argumentSlotSchema Nothing False naturalType
            (Just expectedDefault)
        , Types.argumentSlotSchema Nothing False naturalType Nothing
        ]
      supplied = Types.makeAtlasMap 2 [Types.skipValue, expectedSupplied]
  completed <- H.evalEither
    (Types.argumentSchemaValuesComplete schema supplied)
  Types.interpretedCanonicalResult completed H.===
    Types.interpretedCanonicalResult
      (Types.makeAtlasMap 2 [expectedDefault, expectedSupplied])

propAsciiStringRoundTrip :: H.Property
propAsciiStringRoundTrip = H.property $ do
  characters <- H.forAll
    (Gen.list (Range.linear 0 64) (Gen.enum '\0' '\255'))
  case AsciiString.asciiString characters AsciiString.asciiStringValue of
    Nothing -> do
      H.footnote "asciiString rejected generated byte characters"
      H.failure
    Just actual -> actual H.=== characters

propAsciiMapLookup :: H.Property
propAsciiMapLookup = H.property $ do
  value <- H.forAll (Gen.integral (Range.linear 0 255))
  asciiMap $ \ascii ->
    asciiCharacterAt ascii value H.=== Just (toEnum (fromIntegral value))

propOrdinalSequenceAppend :: H.Property
propOrdinalSequenceAppend = H.property $ do
  left <- H.forAll
    (Gen.list (Range.linear 0 30) (Gen.word8 Range.constantBounded))
  right <- H.forAll
    (Gen.list (Range.linear 0 30) (Gen.word8 Range.constantBounded))
  let makeSequence =
        foldr
          ( OrderedValues.appendOrdinalOrderedValues
              . OrderedValues.singletonOrdinalOrderedValues
          )
          OrderedValues.emptyOrdinalOrderedValues
      combined =
        OrderedValues.appendOrdinalOrderedValues
          (makeSequence left)
          (makeSequence right)
      expected = left <> right
      actual =
        map
          (OrderedValues.ordinalOrderedValueAt combined . finiteOrdinal)
          [0 .. fromIntegral (length expected)]
  OrderedValues.ordinalOrderedValuesOrderType combined
    H.=== finiteOrdinal (fromIntegral (length expected))
  actual H.=== map Just expected <> [Nothing]

testNaturalRange :: IO ()
testNaturalRange = do
  case DatraNatural.ellipsisNatural 0 $ \zero ->
      DatraNatural.ellipsisNatural 2 $ \two ->
        naturalRange zero two $ \valueRange -> do
          let federation = naturalRangeFederation valueRange
              indices = atlasFederationIndexDominion federation
              descriptions =
                fmap naturalSubrangeDescription
                  <$> traverse (unrank indices) [0 .. 6]
              first = unrank indices 1
              lastSingleton = unrank indices 6
          assert "an inclusive 0..2 range uses the exclusive boundary 3"
            ( SuperRange.superEllipsisRangeTarget
                (naturalRangeEllipsisRange valueRange)
                == SuperRange.GivenTarget (finiteOrdinal 3)
            )
          assert "0..2 federates the empty range and all directed subranges"
            ( descriptions
                == Just
                  [ EmptyNaturalSubrange
                  , FiniteNaturalSubrange 0 0
                  , FiniteNaturalSubrange 0 1
                  , FiniteNaturalSubrange 0 2
                  , FiniteNaturalSubrange 1 1
                  , FiniteNaturalSubrange 1 2
                  , FiniteNaturalSubrange 2 2
                  ]
              && isNothing (unrank indices 7)
            )
          assert "equal-sized distinct subranges have a separation witness"
            (case (first, lastSingleton) of
              (Just left, Just right) ->
                atlasFederationSeparation federation left right
                  == Just
                    (SeparatedCorrespondingPageElements
                      1 (finiteOrdinal 0))
              _ -> False)
    of
      Just (Just (Just tests)) -> tests
      _ -> fail "test setup failed: inclusive NaturalRange"

  case DatraNatural.ellipsisNatural 2 $ \two ->
      DatraNatural.ellipsisNatural 5 $ \five ->
        naturalRange two five $ \valueRange ->
          ( naturalRangeDirection valueRange
              == AscendingNaturalRange
            && naturalRangeFiniteSubrange valueRange 2 5
              /= Nothing
            && isNothing (naturalRangeFiniteSubrange valueRange 5 2)
          )
    of
      Just (Just (Just condition)) ->
        assert "ascending federations exclude backwards subranges" condition
      _ -> fail "test setup failed: ascending NaturalRange"

  case DatraNatural.ellipsisNatural 5 $ \five ->
      DatraNatural.ellipsisNatural 2 $ \two ->
        naturalRange five two $ \valueRange ->
          ( naturalRangeDirection valueRange
              == DescendingNaturalRange
            && SuperRange.superEllipsisRangeTarget
                (naturalRangeEllipsisRange valueRange)
                == SuperRange.GivenTarget (finiteOrdinal 1)
            && naturalRangeFiniteSubrange valueRange 5 2
              /= Nothing
            && isNothing (naturalRangeFiniteSubrange valueRange 2 5)
          )
    of
      Just (Just (Just condition)) ->
        assert "descending federations contain only descending subranges"
          condition
      _ -> fail "test setup failed: descending NaturalRange"

  case DatraNatural.ellipsisNatural 5 $ \five ->
      DatraNatural.ellipsisNatural 0 $ \zero ->
        naturalRange five zero $ \valueRange ->
          SuperRange.superEllipsisRangeTarget
            (naturalRangeEllipsisRange valueRange)
            == SuperRange.MinusSign
    of
      Just (Just (Just condition)) ->
        assert "a descending NaturalRange ending at zero uses ..-" condition
      _ -> fail "test setup failed: zero-target NaturalRange"

  case DatraNatural.ellipsisNatural 2 $ \two ->
      naturalRange two upwards $ \valueRange ->
        let federation = naturalRangeFederation valueRange
            indices = atlasFederationIndexDominion federation
        in ( SuperRange.superEllipsisRangeTarget
              (naturalRangeEllipsisRange valueRange)
              == SuperRange.PlusSign
            && fmap naturalSubrangeDescription (unrank indices 0)
              == Just EmptyNaturalSubrange
            && fmap naturalSubrangeDescription (unrank indices 1)
              == Just (FiniteNaturalSubrange 2 2)
            && fmap naturalSubrangeDescription (unrank indices 2)
              == Just (UpwardsNaturalSubrange 2)
            && naturalRangeUpwardsSubrange valueRange 4 /= Nothing
            && isNothing (naturalRangeFiniteSubrange valueRange 4 3)
           )
    of
      Just (Just condition) ->
        assert "upwards creates a.. and federates ascending subranges"
          condition
      _ -> fail "test setup failed: upwards NaturalRange"

testValuedNaturalRange :: IO ()
testValuedNaturalRange = do
  case DatraNatural.ellipsisNaturalTotal 2 $ \two ->
      DatraNatural.ellipsisNaturalTotal 5 $ \five ->
        valuedNaturalRange two five $ \valueRange ->
          let federation = valuedNaturalRangeFederation valueRange
              indices = atlasFederationIndexDominion federation
              values =
                fmap valuedNaturalValue
                  <$> traverse (unrank indices) [0 .. 3]
              first = unrank indices 0
              second = unrank indices 1
          in ( values == Just [2, 3, 4, 5]
              && isNothing (unrank indices 4)
              && valuedNaturalRangeContains valueRange 2
              && valuedNaturalRangeContains valueRange 5
              && not (valuedNaturalRangeContains valueRange 6)
              && case (first, second) of
                  (Just left, Just right) ->
                    atlasFederationSeparation federation left right
                      == Just
                        (SeparatedCorrespondingPageElements
                          1 (finiteOrdinal 0))
                  _ -> False
             ) of
    Just condition ->
      assert
        "ValuedNaturalRange federates exactly its EllipsisNatural values"
        condition
    Nothing -> fail "test setup failed: finite ValuedNaturalRange"

  case DatraNatural.ellipsisNaturalTotal 5 $ \five ->
      DatraNatural.ellipsisNaturalTotal 2 $ \two ->
        valuedNaturalRange five two $ \valueRange ->
          let indices =
                atlasFederationIndexDominion
                  (valuedNaturalRangeFederation valueRange)
          in fmap valuedNaturalValue
              <$> traverse (unrank indices) [0 .. 3] of
    Just (Just values) ->
      assert
        "descending ValuedNaturalRange indices follow its traversal"
        (values == [5, 4, 3, 2])
    _ -> fail "test setup failed: descending ValuedNaturalRange"

  case NaturalType.naturalType $ \valueRange ->
      let indices =
            atlasFederationIndexDominion
              (valuedNaturalRangeFederation valueRange)
      in fmap valuedNaturalValue
          <$> traverse (unrank indices) [0 .. 4] of
    Just (Just values) ->
      assert "NaturalType is from 0 upwards"
        (values == [0, 1, 2, 3, 4])
    _ -> fail "test setup failed: NaturalType"

testIntegerRanges :: IO ()
testIntegerRanges = do
  DatraInteger.ellipsisIntegerFromComplement
      5 DatraBoolean.DatraTrue $ \negative ->
    assert "integer complement flags are Datra Booleans"
      ( DatraInteger.ellipsisIntegerValue negative == -6
        && DatraBoolean.booleanNatural
          (DatraInteger.ellipsisIntegerComplement negative) == 1
      )
  DatraInteger.ellipsisInteger 5 $ \positive ->
    DatraInteger.ellipsisInteger (-6) $ \negative ->
      assert "integers use adjacent Nat x 2 complement codes"
        ( DatraInteger.ellipsisIntegerValue positive == 5
          && DatraInteger.ellipsisIntegerCode positive == 10
          && DatraInteger.ellipsisIntegerValue negative == -6
          && DatraInteger.ellipsisIntegerCode negative == 11
        )
  case DatraInteger.ellipsisInteger (-2) $ \origin ->
      DatraInteger.ellipsisInteger 2 $ \target ->
        IntegerRange.integerRange origin target $ \valueRange ->
          ( IntegerRange.integerRangeDirection valueRange
              == IntegerRange.AscendingIntegerRange
            && IntegerRange.integerRangeFiniteSubrange valueRange (-2) 2
              /= Nothing
            && IntegerRange.integerRangeFiniteSubrange valueRange 2 (-2)
              == Nothing
          ) of
    Just condition ->
      assert "finite integer ranges retain directed subranges" condition
    Nothing -> fail "test setup failed: IntegerRange"
  case DatraInteger.ellipsisInteger (-1) $ \origin ->
      IntegerRange.integerRange
        origin IntegerRange.downwards $ \valueRange ->
          ( IntegerRange.integerRangeDirection valueRange
              == IntegerRange.DescendingIntegerRange
            && IntegerRange.integerRangeDownwardsSubrange valueRange (-4)
              /= Nothing
          ) of
    Just condition ->
      assert "integer ranges support an open downward direction" condition
    Nothing -> fail "test setup failed: downward IntegerRange"
  IntegerType.integerType $ \integerValues ->
    let indices =
          atlasFederationIndexDominion
            (ValuedIntegerRange.valuedIntegerRangeFederation integerValues)
        values =
          fmap ValuedIntegerRange.valuedIntegerValue
            <$> traverse (unrank indices) [0 .. 5]
    in assert "Int enumerates the Nat x 2 product"
        (values == Just [0, -1, 1, -2, 2, -3])

atlasPageHasExactly
  :: Atlas atlasScope paginationScope cellData origin final
  -> Natural
  -> Natural
  -> Bool
atlasPageHasExactly valueAtlas pageNumber cellCount =
  let elements = atlasPageElements valueAtlas
      exists position =
        case pageElementIndex
          elements pageNumber (finiteOrdinal position) of
            Just _ -> True
            Nothing -> False
      positions = take (fromIntegral cellCount) [0 ..]
  in all exists positions && not (exists cellCount)

testDot :: IO ()
testDot =
  dot `seq`
    withAtlasMapExtent dotAtlasMap $ \_ extent coversExtent ->
      let uniqueDatum = unrank extent 0
          coveredAtOnlyCell =
            case uniqueDatum of
              Nothing -> False
              Just datum ->
                withAtlasCoveredPageElement
                  (coversExtent datum) $ \occurrence _ ->
                    pageElementPage occurrence == 0
                      && pageElementPosition occurrence == finiteOrdinal 0
      in assert
          "dot is the domanial inclusion of one terminal"
          ( atlasCardinality dotAtlas == 1
            && atlasPageHasExactly dotAtlas 0 1
            && rank dotDominion dotTerminal == 0
            && unrank dotDominion 0 == Just dotTerminal
            && isNothing (unrank dotDominion 1)
            && fmap dominionCellDataValue uniqueDatum == Just dotTerminal
            && coveredAtOnlyCell
          )

-- The hierarchy is structural: Dot is level zero, Ellipsis is level one,
-- and applying the successor once more constructs level two.
type SuperEllipsisTwo = SuperEllipsis Ellipsis

type RankOneTerminal = SuperEllipsisTerminal Ellipsis

type RankOneAtlasObject = SuperEllipsisAtlasObject Ellipsis

rankOneRank :: SuperEllipsisRank Ellipsis
rankOneRank = nextSuperEllipsisRank dotSuperEllipsisRank

rankOneTerminal :: Natural -> RankOneTerminal
rankOneTerminal value =
  fromMaybe
    (superEllipsisZeroTerminal rankOneRank)
    (superEllipsisTerminal rankOneRank (finiteOrdinal value))

rankOneTerminalRank :: RankOneTerminal -> Natural
rankOneTerminalRank =
  fromMaybe 0 . naturalAtOrdinal . superEllipsisTerminalPosition

rankOneDominion :: Dominion RankOneTerminal
rankOneDominion = superEllipsisDominion rankOneRank

rankOneAtlas :: ChainedDominionAtlas RankOneTerminal
rankOneAtlas = superEllipsisAtlas rankOneRank

rankOneAtlasMap :: AtlasMap RankOneAtlasObject
rankOneAtlasMap = superEllipsisAtlasMap rankOneRank

rankOneUnfolded
  :: StableConfederalData (ConcatOperatorValues Dot Ellipsis)
rankOneUnfolded = superEllipsisUnfolded dot

rankOneFold
  :: StableConfederalDataHom
       (ConcatOperatorValues Dot Ellipsis)
       Ellipsis
rankOneFold = superEllipsisFold dot

rankOneUnfold
  :: StableConfederalDataHom
       Ellipsis
       (ConcatOperatorValues Dot Ellipsis)
rankOneUnfold = superEllipsisUnfold dot

type RankOneConfederationScope =
  SingletonAtlasConfederationScope RankOneAtlasObject

type RankOneConfederationObject =
  AtlasConfederationObject RankOneConfederationScope ()

rankOneValue :: SuperEllipsisLayer Dot RankOneConfederationObject
rankOneValue = rollSuperEllipsisLayer
  (mapStableConfederalData
    rankOneUnfolded
    tailInclusion
    (concatValue
      dotConfederation
      rankOneConfederation
      identityAtlasConfederationHom
      rankOneValue))
  where
    dotConfederation = singletonAtlasConfederation dotAtlas
    rankOneConfederation = singletonAtlasConfederation rankOneAtlas
    tailInclusion = rightAtlasConfederationInclusion
      dotConfederation rankOneConfederation

testSuperEllipsis :: IO ()
testSuperEllipsis = do
  let levelOne :: StableConfederalData (SuperEllipsis Dot)
      levelOne = ellipsis
      levelTwo :: StableConfederalData SuperEllipsisTwo
      levelTwo = superEllipsis ellipsis
      levelTwoUnfolded = superEllipsisUnfolded ellipsis
      levelTwoFold = superEllipsisFold ellipsis
      levelTwoUnfold = superEllipsisUnfold ellipsis
      roundTripValue =
        rollSuperEllipsisLayer (unrollSuperEllipsisLayer rankOneValue)
  levelOne `seq`
    levelTwo `seq`
      levelTwoUnfolded `seq`
        levelTwoFold `seq`
          levelTwoUnfold `seq`
            roundTripValue `seq`
              assert "super rankOneData constructs Ellipsis and its successor" True

testSuperEllipsisRange :: IO ()
testSuperEllipsisRange = asciiMap $ \ascii -> do
  let rankTwo = nextSuperEllipsisRank rankOneRank
      rankTwoDominion = superEllipsisDominion rankTwo
      positions =
        [ finiteOrdinal 0
        , finiteOrdinal 65
        , omega
        , addOrdinals omega (finiteOrdinal 2)
        ]
      terminalRoundTrips position = do
        terminal <- superEllipsisTerminal rankTwo position
        unrank rankTwoDominion (rank rankTwoDominion terminal)
  assert "rank-two terminals use the canonical DatraOrdinal enumeration"
    (map terminalRoundTrips positions
      == map (superEllipsisTerminal rankTwo) positions)
  case join (superEllipsisValue rankTwo omega $ \origin ->
      join (superEllipsisValue
        rankTwo
        (addOrdinals omega (finiteOrdinal 3)) $ \target ->
          (boundedSuperEllipsisRange origin target) $ \valueRange -> do
            let insertion = SuperRange.superEllipsisRangeInsertion valueRange
                at position = do
                  sourceIndex <- chainIndex
                    (superEllipsisInsertionChain insertion)
                    (finiteOrdinal position)
                  pure
                    (superEllipsisInsertionPosition
                      insertion (chainObjectAt sourceIndex))
            assert "rank-two ranges retain transfinite ordinal positions"
              (map at [0 .. 3]
                == map Just
                  [ omega
                  , addOrdinals omega (finiteOrdinal 1)
                  , addOrdinals omega (finiteOrdinal 2)
                  ] <> [Nothing])
            assert
              "finite maps reject transfinite super-rankOneData positions"
              (case accessOperatorEither ascii insertion of
                Left (AccessPositionOutOfBounds position mapOrderType) ->
                  position == omega
                    && mapOrderType == finiteOrdinal 256
                _ -> False)))
    of
      Nothing -> fail "valid transfinite rank-two range was rejected"
      Just checks -> checks
  assert "finite values cannot be constructed above their minimal rank"
    (case superEllipsisValue rankTwo (finiteOrdinal 65) (const ()) of
      Nothing -> True
      Just () -> False)
  assert "canonical value construction chooses the minimal rank"
    (canonicalSuperEllipsisValue (finiteOrdinal 65) $ \value ->
      superEllipsisRankLevel
        (SuperRange.superEllipsisRangeRank
          (superEllipsisValueRange value)) == 1)
  case SuperRange.superEllipsisRangeEither
      rankTwo
      (finiteOrdinal 65)
      (SuperRange.GivenTarget (finiteOrdinal 68)) $ \valueRange ->
        case ascii `accessOperator` SuperRange.superEllipsisRangeInsertion valueRange of
          Nothing -> False
          Just selected ->
            orderedAtlasMapCardinality selected == finiteOrdinal 3 of
    Left rejection ->
      fail ("valid finite rank-two range was rejected: " <> show rejection)
    Right fits ->
      assert "ranges may still select finite positions in a higher rank" fits
  let omegaTimesTwo = ordinal [2, 0]
      atFiniteTail finiteTail =
        addOrdinals omegaTimesTwo (finiteOrdinal finiteTail)
      insertionAt valueRange position = do
        let insertion = SuperRange.superEllipsisRangeInsertion valueRange
        sourceIndex <- chainIndex
          (superEllipsisInsertionChain insertion)
          (finiteOrdinal position)
        pure
          (superEllipsisInsertionPosition
            insertion (chainObjectAt sourceIndex))
  case join (superEllipsisValue rankTwo (atFiniteTail 3) $ \origin ->
      (openMinusSuperEllipsisRange origin) $ \valueRange -> do
        assert "transfinite MinusSign ranges include their finite-tail base"
          ( map (insertionAt valueRange) [0 .. 4]
              == map Just
                [ atFiniteTail 3
                , atFiniteTail 2
                , atFiniteTail 1
                , omegaTimesTwo
                ] <> [Nothing]
          )
        assert "transfinite MinusSign ranges have finite order type"
          (SuperRange.superEllipsisRangeOrderType valueRange
            == finiteOrdinal 4)
        assert "transfinite MinusSign ranges do not cross their limit base"
          (isNothing (SuperRange.superEllipsisRangeElement valueRange omega)))
    of
      Nothing -> fail "valid transfinite MinusSign range was rejected"
      Just checks -> checks
  let highFiniteTail = atFiniteTail 100000
      lowFiniteTail = atFiniteTail 15
  case join (superEllipsisValue rankTwo highFiniteTail $ \origin ->
      join (superEllipsisValue rankTwo lowFiniteTail $ \target ->
        (boundedSuperEllipsisRange origin target) $ \valueRange -> do
          assert "same-base transfinite descending ranges are admitted"
            ( map (insertionAt valueRange) [0, 1, 99984, 99985]
                == [ Just highFiniteTail
                   , Just (atFiniteTail 99999)
                   , Just (atFiniteTail 16)
                   , Nothing
                   ]
            )
          assert "explicit descending targets remain exclusive"
            (SuperRange.superEllipsisRangeOrderType valueRange
              == finiteOrdinal 99985)))
    of
      Nothing -> fail "same-base transfinite descending range was rejected"
      Just checks -> checks
  assert "descending across a limit boundary reports invalid bounds"
    (case SuperRange.superEllipsisRangeEither
        rankTwo
        highFiniteTail
        (SuperRange.GivenTarget omega)
        (const ()) of
      Left
          (SuperRange.SuperEllipsisRangeInvalidDescendingBounds
            start target) ->
        start == highFiniteTail && target == omega
      _ -> False)

type EllipsisConfederationScope =
  SingletonAtlasConfederationScope RankOneAtlasObject

type EllipsisPairValues = SequentialOperatorValues Ellipsis Ellipsis

type EllipsisPairScope =
  MergedAtlasConfederationScope
    EllipsisConfederationScope
    EllipsisConfederationScope

type EllipsisPairObject =
  AtlasConfederationObject EllipsisPairScope (Either () ())

type EllipsisTripleValues =
  SequentialOperatorValues Ellipsis EllipsisPairValues

type EllipsisTripleScope =
  MergedAtlasConfederationScope
    EllipsisConfederationScope
    EllipsisPairScope

type EllipsisTripleIndex = Either () (Either () ())

type EllipsisTripleObject =
  AtlasConfederationObject EllipsisTripleScope EllipsisTripleIndex

type EllipsisLeftTripleObject =
  AtlasConfederationObject
    (MergedAtlasConfederationScope
      EllipsisPairScope
      EllipsisConfederationScope)
    (Either (Either () ()) ())

type EllipsisGroupedPairsObject =
  AtlasConfederationObject
    (MergedAtlasConfederationScope EllipsisPairScope EllipsisPairScope)
    (Either (Either () ()) (Either () ()))

type EllipsisFiveGroupValues =
  ExpansionOperatorValues EllipsisTripleValues EllipsisPairValues

type EllipsisFiveGroupScope =
  MergedAtlasConfederationScope EllipsisTripleScope EllipsisPairScope

type EllipsisFiveGroupIndex =
  Either EllipsisTripleIndex (Either () ())

type EllipsisFiveGroupObject =
  AtlasConfederationObject EllipsisFiveGroupScope EllipsisFiveGroupIndex

type EllipsisComplexObject =
  AtlasConfederationObject
    (MergedAtlasConfederationScope
      EllipsisFiveGroupScope
      EllipsisFiveGroupScope)
    (Either EllipsisFiveGroupIndex EllipsisFiveGroupIndex)

testSequentialOperator :: IO ()
testSequentialOperator = do
  let sequenced =
        sequentialOperator ellipsis (sequentialOperator ellipsis ellipsis)
      ellipsisConfederation = singletonAtlasConfederation rankOneAtlas
      pairConfederation = mergeAtlasConfederations
        ellipsisConfederation ellipsisConfederation
      pair ::
        SequentialOperatorValue Ellipsis Ellipsis EllipsisPairObject
      pair =
        sequentialValue
          ellipsisConfederation
          ellipsisConfederation
          rankOneValue
          rankOneValue
      triple ::
        SequentialOperatorValue Ellipsis EllipsisPairValues EllipsisTripleObject
      triple =
        sequentialValue
          ellipsisConfederation
          pairConfederation
          rankOneValue
          pair
      leftTriple ::
        SequentialOperatorValue EllipsisPairValues Ellipsis
          EllipsisLeftTripleObject
      leftTriple =
        sequentialValue
          pairConfederation
          ellipsisConfederation
          pair
          rankOneValue
      traversalSelectsItsCell mergedAtlas traversal =
        withSequentialAtlasTraversal traversal $
          \position sourceAtlas inclusion ->
            withPageElement (atlasOriginCell sourceAtlas) $ \extent ->
              let source = atlasTransposalElement
                    (atlasWitness sourceAtlas) extent
                  target = mapOrderedAtlasTransposalObject inclusion source
              in withAtlasTransposalElement target $ \occurrence ->
                  pageElementPage occurrence == 1
                    && pageElementPosition occurrence
                      == finiteOrdinal position
                    && orderedAtlasTransposalPreimage inclusion target
                      == Just source
                    && withAtlasMorphismImage
                      (mapOrderedAtlasTransposalData
                        (atlasWitness sourceAtlas)
                        inclusion
                        extent) (\targetCell component ->
                          case unrank (atlasDataAt sourceAtlas extent) 0 of
                            Nothing -> False
                            Just sourceDatum ->
                              let targetDatum =
                                    applyInsertion component sourceDatum
                              in rank
                                  (atlasDataAt mergedAtlas targetCell)
                                  targetDatum == position
                                && fmap
                                  (rank (atlasDataAt sourceAtlas extent))
                                  (preimage component targetDatum)
                                  == Just 0)
      verify label value =
        withSequentialAtlasTraversals value $ \mergedAtlas traversals ->
          assert label
            ( atlasCardinality mergedAtlas == 3
              && fmap sequentialAtlasTraversalPosition traversals == [0, 1, 2]
              && all (traversalSelectsItsCell mergedAtlas) traversals
              && case pageElementIndex
                  (atlasPageElements mergedAtlas) 1 (finiteOrdinal 3) of
                    Nothing -> True
                    Just _ -> False
            )
  sequenced `seq` do
    verify
      "right-associated sequence flattens three operands onto page 1"
      triple
    verify
      "left-associated sequence flattens three operands onto page 1"
      leftTriple

testConcatOperator :: IO ()
testConcatOperator = do
  let concatenated = ellipsis `concatOperands` ellipsis
      ellipsisConfederation = singletonAtlasConfederation rankOneAtlas
      pair ::
        ConcatOperatorValue Ellipsis Ellipsis EllipsisPairObject
      pair =
        concatValue
          ellipsisConfederation
          ellipsisConfederation
          rankOneValue
          rankOneValue
      mappedFinalPage sequenceAtlas concatAtlas inclusion =
        case pageElementIndex
          (atlasPageElements concatAtlas) 1 (finiteOrdinal 0) of
            Nothing -> False
            Just index ->
              withPageElement (pageElement index) $ \sourceElement ->
                let source = atlasTransposalElement
                      (atlasWitness concatAtlas) sourceElement
                    target = mapOrderedAtlasTransposalObject inclusion source
                in withAtlasTransposalElement target $ \targetElement ->
                    pageElementPage targetElement
                      == atlasCardinality sequenceAtlas - 1
                      && pageElementPosition targetElement == finiteOrdinal 0
                      && orderedAtlasTransposalPreimage inclusion target
                        == Just source
      middlePageIsForgotten sequenceAtlas inclusion =
        case pageElementIndex
          (atlasPageElements sequenceAtlas) 1 (finiteOrdinal 0) of
            Nothing -> False
            Just index ->
              withPageElement (pageElement index) $ \middleElement ->
                isNothing
                  (orderedAtlasTransposalPreimage inclusion
                    (atlasTransposalElement
                      (atlasWitness sequenceAtlas) middleElement))
  concatenated `seq`
    withConcatOrderedTransposal pair $
      \sequenceAtlas concatAtlas inclusion ->
        assert
          "concat retains only the extent and sequential final page"
          ( atlasCardinality sequenceAtlas == 3
            && atlasCardinality concatAtlas == 2
            && mappedFinalPage sequenceAtlas concatAtlas inclusion
            && middlePageIsForgotten sequenceAtlas inclusion
          )

testGroupedSequentialExpansion :: IO ()
testGroupedSequentialExpansion = do
  let groupedObject =
        expansionOperator
          (sequentialOperator ellipsis ellipsis)
          (sequentialOperator ellipsis ellipsis)
      ellipsisConfederation = singletonAtlasConfederation rankOneAtlas
      pairConfederation = mergeAtlasConfederations
        ellipsisConfederation ellipsisConfederation
      pair ::
        SequentialOperatorValue Ellipsis Ellipsis EllipsisPairObject
      pair =
        sequentialValue
          ellipsisConfederation
          ellipsisConfederation
          rankOneValue
          rankOneValue
      groupedPairs ::
        ExpansionOperatorValue
          EllipsisPairValues
          EllipsisPairValues
          EllipsisGroupedPairsObject
      groupedPairs =
        expansionValue pairConfederation pairConfederation pair pair
      mapsInnerPairToPageTwo sourceAtlas inclusion offset =
        let elements = atlasPageElements sourceAtlas
            mapsPosition position =
              case pageElementIndex
                elements 1 (finiteOrdinal position) of
                  Nothing -> False
                  Just index ->
                    withPageElement (pageElement index) $ \sourceElement ->
                      let source = atlasTransposalElement
                            (atlasWitness sourceAtlas) sourceElement
                          target = mapOrderedAtlasTransposalObject
                            inclusion source
                      in withAtlasTransposalElement target $ \targetElement ->
                          pageElementPage targetElement == 2
                            && pageElementPosition targetElement
                              == finiteOrdinal (offset + position)
        in all mapsPosition [0, 1]
  groupedObject `seq`
    withExpansionOrderedTransposals groupedPairs $
      \leftPair rightPair expanded leftTraversal rightTraversal ->
        assert
          "expansion groups two flattened pairs into pages of 2 then 4"
          ( atlasPageHasExactly expanded 1 2
            && atlasPageHasExactly expanded 2 4
            && mapsInnerPairToPageTwo leftPair leftTraversal 0
            && mapsInnerPairToPageTwo rightPair rightTraversal 2
          )

testComplexOperatorStructure :: IO ()
testComplexOperatorStructure = do
  let fiveObject =
        expansionOperator
          (sequentialOperator
            ellipsis
            (sequentialOperator ellipsis ellipsis))
          (sequentialOperator ellipsis ellipsis)
      complexObject = expansionOperator fiveObject fiveObject
      ellipsisConfederation = singletonAtlasConfederation rankOneAtlas
      pairConfederation = mergeAtlasConfederations
        ellipsisConfederation ellipsisConfederation
      tripleConfederation = mergeAtlasConfederations
        ellipsisConfederation pairConfederation
      fiveGroupConfederation = mergeAtlasConfederations
        tripleConfederation pairConfederation
      pair ::
        SequentialOperatorValue Ellipsis Ellipsis EllipsisPairObject
      pair =
        sequentialValue
          ellipsisConfederation
          ellipsisConfederation
          rankOneValue
          rankOneValue
      triple ::
        SequentialOperatorValue
          Ellipsis
          EllipsisPairValues
          EllipsisTripleObject
      triple =
        sequentialValue
          ellipsisConfederation
          pairConfederation
          rankOneValue
          pair
      fiveGroup ::
        ExpansionOperatorValue
          EllipsisTripleValues
          EllipsisPairValues
          EllipsisFiveGroupObject
      fiveGroup =
        expansionValue
          tripleConfederation
          pairConfederation
          triple
          pair
      complex ::
        ExpansionOperatorValue
          EllipsisFiveGroupValues
          EllipsisFiveGroupValues
          EllipsisComplexObject
      complex =
        expansionValue
          fiveGroupConfederation
          fiveGroupConfederation
          fiveGroup
          fiveGroup
      mapsFiveLeavesToPageThree sourceAtlas inclusion offset =
        let elements = atlasPageElements sourceAtlas
            mapsPosition position =
              case pageElementIndex
                elements 2 (finiteOrdinal position) of
                  Nothing -> False
                  Just index ->
                    withPageElement (pageElement index) $ \sourceElement ->
                      let source = atlasTransposalElement
                            (atlasWitness sourceAtlas) sourceElement
                          target = mapOrderedAtlasTransposalObject
                            inclusion source
                      in withAtlasTransposalElement target $ \targetElement ->
                          pageElementPage targetElement == 3
                            && pageElementPosition targetElement
                              == finiteOrdinal (offset + position)
        in all mapsPosition [0 .. 4]
  complexObject `seq`
    withExpansionOrderedTransposals complex $
      \leftGroup rightGroup expanded leftTraversal rightTraversal ->
        assert
          "nested sequence and expansion structure has pages 2, 4, then 10"
          ( atlasPageHasExactly expanded 1 2
            && atlasPageHasExactly expanded 2 4
            && atlasPageHasExactly expanded 3 10
            && atlasPageHasExactly leftGroup 2 5
            && atlasPageHasExactly rightGroup 2 5
            && mapsFiveLeavesToPageThree leftGroup leftTraversal 0
            && mapsFiveLeavesToPageThree rightGroup rightTraversal 5
          )

testAsciiMap :: IO ()
testAsciiMap =
  asciiMap $ \ascii -> do
    let valueAtlas = asciiAtlas ascii
    assert "ASCII map has two pages and 256 final cells"
      (asciiCardinality == 256
        && indexedAtlasCardinality ascii
          == finiteOrdinal asciiCardinality
        && atlasCardinality valueAtlas == 2
        && atlasPageHasExactly valueAtlas 1 asciiCardinality)
    assert "ASCII map positions contain matching characters"
      (map (asciiCharacterAt ascii) [0, 65, 97, 255, 256]
        == [Just '\0', Just 'A', Just 'a', Just '\255', Nothing])

testAsciiString :: IO ()
testAsciiString = do
  case AsciiString.asciiString "" $ \emptyString ->
      assert "an empty ASCII string has the canonical empty presentation"
        ( AsciiString.asciiStringLength emptyString == 0
          && AsciiString.asciiStringValue emptyString == ""
          && isNothing (AsciiString.asciiStringCharacterAt emptyString 0)
          && case orderedAtlasMap emptyString of
            EmptyOrderedAtlasMap -> True
            NonEmptyOrderedAtlasMap _ -> False
        ) of
    Nothing -> fail "an empty ASCII string was rejected"
    Just checks -> checks
  case AsciiString.asciiString "aA_0'a\255" $ \value ->
      case orderedAtlasMap value of
        EmptyOrderedAtlasMap -> fail "a nonempty ASCII string produced an empty map"
        NonEmptyOrderedAtlasMap valueMap -> do
          let valueAtlas = indexedAtlasAtlas valueMap
          assert "an ASCII string retains arbitrary and repeated characters"
            ( AsciiString.asciiStringLength value == 7
              && AsciiString.asciiStringValue value == "aA_0'a\255"
              && map (AsciiString.asciiStringCharacterAt value) [0 .. 7]
                == map Just "aA_0'a\255" <> [Nothing]
            )
          assert "a nonempty ASCII string is a finite two-page map"
            ( indexedAtlasCardinality valueMap == finiteOrdinal 7
              && atlasCardinality valueAtlas == 2
              && atlasPageHasExactly valueAtlas 1 7
            ) of
    Nothing -> fail "a valid ASCII string was rejected"
    Just checks -> checks
  assert "an out-of-map character is rejected"
    (isNothing (AsciiString.asciiString "\x100" (const ())))
  case AsciiString.asciiString "left" $ \left ->
      AsciiString.asciiString "" $ \emptyString ->
        AsciiString.asciiString "right" $ \right ->
          let unchanged = left `concatOperands` emptyString
              combined = unchanged `concatOperands` right
          in
            ( AsciiString.asciiStringValue unchanged
            , AsciiString.asciiStringValue combined
            , orderedAtlasMapCardinality (orderedAtlasMap combined)
            ) of
    Just (Just (Just (unchanged, combined, cardinality))) ->
      assert "ordinary concatenation retains ASCII-string behavior"
        ( unchanged == "left"
          && combined == "leftright"
          && cardinality == finiteOrdinal 9
        )
    _ -> fail "valid ASCII-string concatenation was rejected"
  case AsciiString.asciiString "abcd" $ \value -> do
      withEllipsisNatural 2 $ \two ->
        case AsciiString.accessAsciiString value two of
          Nothing -> fail "valid ASCII-string access was rejected"
          Just selected ->
            assert "ordinary access retains ASCII-string behavior"
              (AsciiString.asciiStringValue selected == "c")
      withEllipsisNatural 1 $ \one ->
        withEllipsisNatural 3 $ \three ->
          do
            case boundedSuperEllipsisRange one three $ \selection ->
                AsciiString.asciiStringValue
                  <$> AsciiString.accessAsciiString value selection of
              Nothing -> fail "ASCII-string access range was rejected"
              Just selected ->
                assert "range access retains ASCII-string behavior"
                  (selected == Just "bc")
            case boundedSuperEllipsisRange one one $ \selection ->
                AsciiString.asciiStringValue
                  <$> AsciiString.accessAsciiString value selection of
              Nothing -> fail "empty ASCII-string access was rejected"
              Just selected ->
                assert "empty access remains an empty ASCII string"
                  (selected == Just "")
    of
    Nothing -> fail "ASCII-string access setup was rejected"
    Just checks -> checks

testAccessOperator :: IO ()
testAccessOperator =
  asciiMap $ \ascii -> do
    case ascii `accessOperator` dot of
      Nothing -> fail "Dot's underlying range was rejected"
      Just selected ->
        assert "access interprets Dot as its full one-element range"
          ( orderedAtlasMapCardinality selected == finiteOrdinal 1
            && fmap
              (asciiCharacterValue . accessElementValue)
              (orderedAtlasMapValueAt selected 0) == Just '\0'
          )
    assert "a finite map reports Ellipsis's insertion rank mismatch"
      (case accessOperatorEither ascii ellipsis of
        Left (AccessInsertionRankExceedsMap insertionRank mapOrderType) ->
          insertionRank == omega
            && mapOrderType == finiteOrdinal 256
        _ -> False)
    let naturalDominion = dominion id Just (const ())
        omegaMap = indexedAtlasMapFromChain 0 spine naturalDominion
    case omegaMap `accessOperator` ellipsis of
      Nothing -> fail "Ellipsis's range was rejected by an omega map"
      Just selected ->
        assert "access preserves an unbounded range that fits the map"
          ( orderedAtlasMapCardinality selected == omega
            && map
              (fmap accessElementValue . orderedAtlasMapValueAt selected)
              [0, 1, 1000000]
              == map Just [0, 1, 1000000]
          )
    let rankTwo = nextSuperEllipsisRank rankOneRank
        rankTwoMap = indexedAtlasMapFromChain
          (superEllipsisZeroTerminal rankTwo)
          (superEllipsisChain rankTwo)
          (superEllipsisDominion rankTwo)
        levelTwoData :: StableConfederalData (SuperEllipsis Ellipsis)
        levelTwoData = superEllipsis ellipsis
    case rankTwoMap `accessOperator` levelTwoData of
      Nothing -> fail "level-two formulation access was rejected"
      Just selected ->
        assert "access remains ordinal-indexed above omega"
          ( orderedAtlasMapCardinality selected == ordinal [1, 0, 0]
            && fmap
              ( superEllipsisTerminalPosition
                . accessElementValue
              )
              (orderedAtlasMapValueAtOrdinal selected omega) == Just omega
          )
    withRankOneRange 10 (Just 12) $ \first ->
      withRankOneRange 2 (Just 4) $ \second ->
        let concatenated = first `concatOperands` second
        in case SuperRange.superEllipsisRangeConcatInsertion concatenated of
          Nothing ->
            fail "disjoint access ranges produced only a map"
          Just insertion ->
            case ascii `accessOperator` insertion of
              Nothing -> fail "in-bounds reordered access was rejected"
              Just selected -> do
                let selectedCharacter position =
                      asciiCharacterValue . accessElementValue
                        <$> orderedAtlasMapValueAt selected position
                assert "access follows insertion order and can reorder values"
                  (map selectedCharacter [0 .. 4]
                    == [ Just '\10', Just '\11', Just '\2', Just '\3'
                       , Nothing
                       ])
                assert "access returns a flattened two-page map"
                  (case selected of
                    EmptyOrderedAtlasMap -> False
                    NonEmptyOrderedAtlasMap valueMap ->
                      let valueAtlas = indexedAtlasAtlas valueMap
                      in atlasCardinality valueAtlas == 2
                          && atlasPageHasExactly valueAtlas 1 4)
    withRankOneRange 255 (Just 257) $ \outside ->
      let insertion = SuperRange.superEllipsisRangeInsertion outside
      in assert "access reports the first out-of-bounds position"
        (case accessOperatorEither ascii insertion of
          Left (AccessPositionOutOfBounds position mapOrderType) ->
            position == finiteOrdinal 256
              && mapOrderType == finiteOrdinal 256
          _ -> False)
    withEllipsisNatural 0 $ \zero -> do
      withEllipsisNatural 2 $ \two ->
        withEllipsisNatural 10 $ \ten ->
          case (boundedSuperEllipsisRange two ten) $ \valueRange -> do
            let selectedPosition selected =
                  SuperRange.superEllipsisRangeElementPosition
                    . accessElementValue
                    <$> orderedAtlasMapValueAt selected 0
                insertion =
                  SuperRange.superEllipsisRangeInsertion valueRange
            case valueRange `accessOperator` zero of
              Nothing -> fail "a range on the left of access was rejected"
              Just selected ->
                assert "range access at zero returns the range's first value"
                  (selectedPosition selected == Just (finiteOrdinal 2))
            case insertion `accessOperator` zero of
              Nothing ->
                fail "an insertion on the left of access was rejected"
              Just selected ->
                assert "insertion access uses its underlying Atlas map"
                  (selectedPosition selected == Just (finiteOrdinal 2))
            of
              Nothing -> fail "the bounded access range was rejected"
              Just checks -> checks
      withEllipsisNatural 3 $ \three ->
        case (boundedSuperEllipsisRange three three) $ \emptyRange -> do
          assert "an empty range converts to the empty map"
            (case SuperRange.superEllipsisRangeOrderedMap emptyRange of
              EmptyOrderedAtlasMap -> True
              NonEmptyOrderedAtlasMap _ -> False)
          assert "an empty insertion produces an empty access map"
            (case emptyRange `accessOperator` zero of
              Just EmptyOrderedAtlasMap -> True
              _ -> False)
          let emptyMap = EmptyOrderedAtlasMap :: OrderedAtlasMap Natural
          assert "access accepts an empty source map"
            (case emptyMap `accessOperator` zero of
              Just EmptyOrderedAtlasMap -> True
              _ -> False)
          of
            Nothing -> fail "valid empty range was rejected"
            Just checks -> checks
    withEllipsisNatural 2 $ \two ->
      withEllipsisNatural 3 $ \three ->
        case (openPlusSuperEllipsisRange two) $ \fromTwo ->
          case (openPlusSuperEllipsisRange three) $ \fromThree -> do
            let concatenated = fromTwo `concatOperands` fromThree
                selectedOrdinal selected =
                  either
                    SuperRange.superEllipsisRangeElementPosition
                    SuperRange.superEllipsisRangeElementPosition
                    . accessElementValue
                    <$> orderedAtlasMapValueAt selected 0
            case SuperRange.superEllipsisRangeConcatInsertionResult concatenated of
              Left (SuperRange.SuperEllipsisRangesOverlap _ _ lower upper)
                | lower == finiteOrdinal 3 && upper == omega ->
                case SuperRange.superEllipsisRangeConcatOrderedMap concatenated of
                  EmptyOrderedAtlasMap ->
                    fail "two unbounded ranges produced the empty map"
                  NonEmptyOrderedAtlasMap valueMap ->
                    assert "overlapping unbounded ranges form an Atlas map"
                      (indexedAtlasCardinality valueMap
                        == addOrdinals omega omega)
              Left rejection ->
                fail ("unbounded ranges reported the wrong rejection: " <> show rejection)
              Right _ ->
                fail "overlapping unbounded ranges produced an insertion"
            case concatenated `accessOperator` two of
              Nothing -> fail "concat-map access at finite index failed"
              Just selected ->
                assert "concat-map index 2 selects 4 from the first range"
                  (selectedOrdinal selected == Just (finiteOrdinal 4))
            case Numeric.additionOperator ellipsis two $ \omegaPlusTwo ->
                case concatenated `accessOperator` omegaPlusTwo of
                  Nothing ->
                    fail "concat-map access at omega plus 2 failed"
                  Just selected ->
                    assert
                      "concat-map index omega plus 2 selects 5 from the second range"
                      (selectedOrdinal selected == Just (finiteOrdinal 5))
              of
                Nothing -> fail "omega plus 2 index construction failed"
                Just checks -> checks
          of
            Nothing -> fail "the range from 3 was rejected"
            Just checks -> checks
        of
          Nothing -> fail "the range from 2 was rejected"
          Just checks -> checks

withRankOneRange
  :: Natural
  -> Maybe Natural
  -> (forall scope. SuperRange.SuperEllipsisRange Ellipsis scope -> IO ())
  -> IO ()
withRankOneRange lower upper useRange =
  case rankOneRange
      lower
      (maybe
        SuperRange.PlusSign
        (SuperRange.GivenTarget . finiteOrdinal)
        upper)
      useRange of
    Nothing -> fail "test setup failed: valid rankOneData range was rejected"
    Just checks -> checks

withEllipsisNatural
  :: Natural
  -> (forall scope. DatraNatural.EllipsisNatural scope -> IO ())
  -> IO ()
withEllipsisNatural value useValue =
  case DatraNatural.ellipsisNatural value useValue of
    Nothing -> fail "test setup failed: valid Ellipsis natural was rejected"
    Just checks -> checks

rankOneRange
  :: Natural
  -> SuperRange.SuperEllipsisRangeTarget
  -> (forall scope.
        SuperRange.SuperEllipsisRange Ellipsis scope -> result)
  -> Maybe result
rankOneRange start =
  \target useRange ->
    join (DatraNatural.ellipsisNatural start $ \origin ->
      case target of
        SuperRange.GivenTarget targetOrdinal -> do
          targetNatural <- naturalAtOrdinal targetOrdinal
          join (DatraNatural.ellipsisNatural targetNatural $ \targetValue ->
            (boundedSuperEllipsisRange origin targetValue) useRange)
        SuperRange.MinusSign -> (openMinusSuperEllipsisRange origin) useRange
        SuperRange.PlusSign -> (openPlusSuperEllipsisRange origin) useRange)

rankOneRangeElement
  :: SuperRange.SuperEllipsisRange Ellipsis scope
  -> Natural
  -> Maybe (SuperRange.SuperEllipsisRangeElement Ellipsis scope)
rankOneRangeElement valueRange =
  SuperRange.superEllipsisRangeElement valueRange . finiteOrdinal

rankOneElementRank
  :: SuperRange.SuperEllipsisRangeElement Ellipsis scope
  -> Natural
rankOneElementRank element =
  case naturalAtOrdinal
    (SuperRange.superEllipsisRangeElementPosition element) of
      Just value -> value
      Nothing -> 0

rankOneRangeSize
  :: SuperRange.SuperEllipsisRange Ellipsis scope
  -> Maybe Natural
rankOneRangeSize =
  naturalAtOrdinal . SuperRange.superEllipsisRangeOrderType

rankOneValueLowerBound
  :: SuperEllipsisValue Ellipsis scope
  -> Maybe Natural
rankOneValueLowerBound = naturalAtOrdinal . superEllipsisValueOrdinal

rankOneValueUpperBound
  :: SuperEllipsisValue Ellipsis scope
  -> Maybe Natural
rankOneValueUpperBound value =
  (+ 1) <$> rankOneValueLowerBound value

testEllipsis :: IO ()
testEllipsis =
  withAtlasMapExtent rankOneAtlasMap $ \_ extent coversExtent -> do
    let ranks :: [Natural]
        ranks = [0, 1, 2, 1000000]
        roundTrips valueRank =
          fmap (rank extent) (unrank extent valueRank) == Just valueRank
        covered valueRank =
          case unrank extent valueRank of
            Nothing -> False
            Just datum -> coversExtent datum `seq` True
    ellipsis `seq` pure ()
    assert "rankOneData is represented by a cardinality-two Atlas map"
      (atlasCardinality rankOneAtlas == 2)
    assert "rankOneData has one covered terminal region at every natural rank"
      (all roundTrips ranks && all covered ranks)
    let elements = atlasPageElements rankOneAtlas
        terminalRegion valueRank = do
          index <- pageElementIndex elements 1 (finiteOrdinal valueRank)
          pure $ withPageElement (pageElement index) $ \region ->
            let regionDominion = atlasDataAt rankOneAtlas region
            in fmap (rank regionDominion) (unrank regionDominion 0) == Just 0
                && isNothing (unrank regionDominion 1)
    assert "all omega final regions carry the same terminal dominion"
      (map terminalRegion ranks == map (const (Just True)) ranks)
    let unfolded =
          mapStableConfederalDataHom rankOneUnfold rankOneValue
        rerolled =
          mapStableConfederalDataHom rankOneFold unfolded
        hasRecursiveShape layer =
          withConcatOrderedTransposal layer $
            \sequenceAtlas recursiveAtlas _ ->
              atlasCardinality sequenceAtlas == 3
                && atlasPageHasExactly sequenceAtlas 1 2
                && atlasCardinality recursiveAtlas == 2
                && all
                  (\position ->
                    case pageElementIndex
                      (atlasPageElements recursiveAtlas)
                      1
                      (finiteOrdinal position) of
                        Just _ -> True
                        Nothing -> False)
                  [0, 1, 2, 100]
    assert "rankOneData unrolls as Dot concatenated with Ellipsis"
      (hasRecursiveShape unfolded)
    withSuperEllipsisLayer rerolled $ \rerolledLayer ->
      assert "rolling the Ellipsis layer restores the fixed-point value"
        (hasRecursiveShape rerolledLayer)

testSuperEllipsisInsertion :: IO ()
testSuperEllipsisInsertion = do
  let insertion :: SuperEllipsisInsertion Ellipsis RankOneTerminal
      insertion = superEllipsisInsertion rankOneRank
        (chain
          omega
          (finiteOrdinal . rankOneTerminalRank)
          (fmap rankOneTerminal . naturalAtOrdinal)
          (const ())
          (\_ _ -> ())
          (const ()))
        id
        Just
        (const ())
      terminals = map rankOneTerminal [0, 1, 1000000]
      traversalPreservesTerminal terminal =
        let sourceAtlas = dominionAtlas rankOneDominion
        in withPageElement (atlasOriginCell sourceAtlas) $ \sourceOrigin ->
          case unrank
            (atlasDataAt sourceAtlas sourceOrigin)
            (rankOneTerminalRank terminal) of
              Nothing -> False
              Just sourceDatum ->
                let sourceCovered =
                      atlasCoveredPageElement
                        sourceAtlas
                        sourceOrigin
                        sourceDatum
                        sourceOrigin
                        sourceDatum
                        ()
                    targetCovered =
                      stableAtlasTransversalPreservesCoverage
                        (superEllipsisInsertionTraversal insertion)
                        sourceCovered
                in withAtlasCoveredPageElement targetCovered $
                  \targetOccurrence targetDatum ->
                    rank
                      (atlasDataAt rankOneAtlas targetOccurrence)
                      targetDatum
                      == rankOneTerminalRank terminal
  assert "rankOneData insertion is an Atlas traversal into rankOneData"
    (all traversalPreservesTerminal terminals
      && all
      (\terminal ->
        superEllipsisInsertionPreimage insertion
          (applySuperEllipsisInsertion insertion terminal) == Just terminal)
      terminals)

testSuperEllipsisInsertionDominion :: IO ()
testSuperEllipsisInsertionDominion =
  asciiMap $ \ascii ->
    withRankOneRange 65 (Just 68) $ \valueRange -> do
      let selected = superEllipsisInsertionDominion
            (indexedAtlasDominion ascii)
            (SuperRange.superEllipsisRangeInsertion valueRange)
          selectedCharacter =
            fmap
              (asciiCharacterValue . superEllipsisInsertionElementValue)
              . unrank selected
      assert "rankOneData insertion restricts a dominion to selected ranks"
        (map selectedCharacter [64, 65, 66, 67, 68]
          == [Nothing, Just 'A', Just 'B', Just 'C', Nothing])
      assert "rankOneData insertion dominion preserves absolute ranks"
        (map (fmap (rank selected) . unrank selected) [65, 66, 67]
          == map Just [65, 66, 67])

testRankOneRange :: IO ()
testRankOneRange = do
  withEllipsisNatural 3 $ \three ->
    case (boundedSuperEllipsisRange three three) $ \valueRange -> do
      let insertion = SuperRange.superEllipsisRangeInsertion valueRange
      assert "equal endpoints form a valid empty range"
        ( all
            (\rankValue ->
              rankOneRangeElement valueRange rankValue == Nothing)
            [0 .. 6]
          && superEllipsisInsertionFirst insertion == Nothing
          && rankOneRangeSize valueRange == Just 0
          && chainOrderType (superEllipsisInsertionChain insertion)
            == finiteOrdinal 0
        )
      of
        Nothing -> fail "equal endpoints were rejected"
        Just checks -> checks
  withRankOneRange 3 (Just 3) $ \emptyRange ->
    withRankOneRange 5 (Just 7) $ \nonemptyRange ->
      let concatenated = emptyRange `concatOperands` nonemptyRange
      in case SuperRange.superEllipsisRangeConcatInsertion concatenated of
        Nothing ->
          fail "an empty range prevented insertion concatenation"
        Just insertion ->
          withConcatOrderedTransposal
              (SuperRange.superEllipsisRangeConcatValue concatenated) $
              \_ concatAtlas _ ->
            assert "an empty range contributes zero ordered cells"
              ( atlasPageHasExactly concatAtlas 1 2
                && case superEllipsisInsertionFirst insertion of
                    Just (Right element) ->
                      rankOneElementRank element == 5
                    _ -> False
              )
  withEllipsisNatural 4 $ \four ->
    withEllipsisNatural 1 $ \one ->
      case (boundedSuperEllipsisRange four one) $ \valueRange -> do
        let insertion = SuperRange.superEllipsisRangeInsertion valueRange
            at position =
              rankOneElementRank . chainObjectAt
                <$> chainIndex
                  (superEllipsisInsertionChain insertion)
                  (finiteOrdinal position)
        assert "a descending range is first-inclusive and second-exclusive"
          (map at [0 .. 3] == [Just 4, Just 3, Just 2, Nothing]
            && map
              (fmap rankOneElementRank
                . rankOneRangeElement valueRange)
              [0 .. 5]
              == [Nothing, Nothing, Just 2, Just 3, Just 4, Nothing])
        of
          Nothing -> fail "descending range was rejected"
          Just checks -> checks
  withEllipsisNatural 5 $ \five -> do
    withEllipsisNatural 0 $ \zero ->
      case (boundedSuperEllipsisRange five zero) $ \valueRange -> do
        let included rankValue =
              case rankOneRangeElement valueRange rankValue of
                Nothing -> False
                Just _ -> True
        assert "a finite zero target remains exclusive"
          (map included [0 .. 6]
            == [False, True, True, True, True, True, False])
        of
          Nothing -> fail "finite zero target was rejected"
          Just checks -> checks
    case (openMinusSuperEllipsisRange five) $ \valueRange -> do
      let insertion = SuperRange.superEllipsisRangeInsertion valueRange
          at position =
            rankOneElementRank . chainObjectAt
              <$> chainIndex
                (superEllipsisInsertionChain insertion)
                (finiteOrdinal position)
      assert "MinusSign descends through zero inclusively"
        (map at [0 .. 6]
          == [Just 5, Just 4, Just 3, Just 2, Just 1, Just 0, Nothing])
      of
        Nothing -> fail "MinusSign target was rejected"
        Just checks -> checks
  withEllipsisNatural 2 $ \two ->
    withEllipsisNatural 5 $ \five ->
      case (boundedSuperEllipsisRange two five) $ \valueRange -> do
        let insertion = SuperRange.superEllipsisRangeInsertion valueRange
            expected = [Nothing, Nothing, Just 2, Just 3, Just 4, Nothing]
            actual = map
              (fmap rankOneElementRank
                . superEllipsisInsertionPreimage insertion . rankOneTerminal)
              [0 .. 5]
        assert
          "bounded rankOneData range is lower-inclusive and upper-exclusive"
          (actual == expected)
        assert "rankOneData range insertion satisfies its left-inverse law"
          (all
            (\rankValue ->
              case rankOneRangeElement valueRange rankValue of
                Nothing -> False
                Just element ->
                  superEllipsisInsertionPreimage insertion
                    (applySuperEllipsisInsertion insertion element)
                    == Just element)
            [2 .. 4])
        of
          Nothing -> fail "valid bounded rankOneData range was rejected"
          Just checks -> checks
  withEllipsisNatural 0 $ \zero ->
    withEllipsisNatural 5 $ \five ->
      case (boundedSuperEllipsisRange zero five) $ \valueRange ->
        map
          (fmap rankOneElementRank . rankOneRangeElement valueRange)
          [0 .. 5]
        of
          Nothing -> fail "valid upper-bounded rankOneData range was rejected"
          Just actual ->
            assert "an explicit zero lower bound includes lower terminals"
              (actual == [Just 0, Just 1, Just 2, Just 3, Just 4, Nothing])
  withEllipsisNatural 2 $ \two ->
    case (openPlusSuperEllipsisRange two) $ \valueRange ->
      map
        (fmap rankOneElementRank . rankOneRangeElement valueRange)
        [1, 2, 1000000]
      of
        Nothing -> fail "valid lower-bounded rankOneData range was rejected"
        Just actual ->
          assert "missing upper bound includes every later terminal"
            (actual == [Nothing, Just 2, Just 1000000])
  withEllipsisNatural 0 $ \zero ->
    case (openPlusSuperEllipsisRange zero) $ \valueRange ->
      map
        (fmap rankOneElementRank . rankOneRangeElement valueRange)
        [0, 1, 1000000]
      of
        Nothing -> fail "unbounded rankOneData range was rejected"
        Just actual ->
          assert "zero-to-unbounded includes all terminals"
            (actual == [Just 0, Just 1, Just 1000000])

testRankOneRangeAnalysis :: IO ()
testRankOneRangeAnalysis = do
  case SuperRange.superEllipsisRangeEither
      rankOneRank omega SuperRange.PlusSign (const ()) of
    Left (SuperRange.SuperEllipsisRangeStartOutsideRank start rankLimit) ->
      assert "range construction identifies an out-of-rank start"
        (start == omega && rankLimit == omega)
    Left _ -> fail "range construction returned the wrong typed error"
    Right _ -> fail "an out-of-rank range start was accepted"

  let targetBeyondRank = addOrdinals omega (finiteOrdinal 1)
  case SuperRange.superEllipsisRangeEither
      rankOneRank
      (finiteOrdinal 0)
      (SuperRange.GivenTarget targetBeyondRank)
      (const ()) of
    Left (SuperRange.SuperEllipsisRangeTargetOutsideRank target rankLimit) ->
      assert "range construction identifies an out-of-rank target"
        (target == targetBeyondRank && rankLimit == omega)
    Left rejection ->
      fail ("range target returned the wrong rejection: " <> show rejection)
    Right _ -> fail "an out-of-rank range target was accepted"

  withRankOneRange 2 (Just 5) $ \first ->
    withRankOneRange 5 Nothing $ \second -> do
      let expected =
            SuperRange.SuperEllipsisRangeDescription
              omega
              (finiteOrdinal 2)
              SuperRange.PlusSign
      assert "adjacent ascending ranges canonicalize to one open range"
        (SuperRange.analyzeSuperEllipsisRangeConcat first second
          == SuperRange.RangeConcatCanonical expected)

  let omegaSquared = ordinal [1, 0, 0]
      finitePrefix =
        SuperRange.SuperEllipsisRangeDescription
          omega
          (finiteOrdinal 2)
          (SuperRange.GivenTarget (finiteOrdinal 5))
      transfiniteSuffix =
        SuperRange.SuperEllipsisRangeDescription
          omegaSquared
          (finiteOrdinal 5)
          (SuperRange.GivenTarget omegaSquared)
      widenedRange =
        SuperRange.SuperEllipsisRangeDescription
          omegaSquared
          (finiteOrdinal 2)
          (SuperRange.GivenTarget omegaSquared)
  assert "contiguous descriptions canonicalize across range ranks"
    (SuperRange.analyzeSuperEllipsisRangeDescriptions
      finitePrefix transfiniteSuffix
      == SuperRange.RangeConcatCanonical widenedRange)

  withRankOneRange 5 (Just 3) $ \first ->
    withRankOneRange 3 (Just 4) $ \second ->
      assert "ranges with different directions do not canonicalize"
        (case SuperRange.analyzeSuperEllipsisRangeConcat first second of
          SuperRange.RangeConcatDisjoint _ _ -> True
          _ -> False)

  withRankOneRange 5 (Just 3) $ \first ->
    withRankOneRange 3 (Just 1) $ \second ->
      assert "adjacent descending ranges canonicalize in traversal order"
        (SuperRange.analyzeSuperEllipsisRangeConcat first second
          == SuperRange.RangeConcatCanonical
              (SuperRange.SuperEllipsisRangeDescription
                omega
                (finiteOrdinal 5)
                (SuperRange.GivenTarget (finiteOrdinal 1))))

  withRankOneRange 3 Nothing $ \first ->
    withRankOneRange 4 Nothing $ \second -> do
      let analysis =
            SuperRange.analyzeSuperEllipsisRangeConcat first second
      assert "overlapping open ranges report their exact overlap"
        (case analysis of
          SuperRange.RangeConcatOverlapping _ _ lower upper ->
            lower == finiteOrdinal 4 && upper == omega
          _ -> False)
      assert "overlapping ranges have a typed insertion error"
        (case SuperRange.concatSuperEllipsisRangeInsertionEither
            first second of
          Left (SuperRange.SuperEllipsisRangesOverlap _ _ lower upper) ->
            lower == finiteOrdinal 4 && upper == omega
          Right _ -> False)

  withRankOneRange 2 (Just 2) $ \emptyRange ->
    withRankOneRange 5 Nothing $ \nonemptyRange ->
      assert "an empty range is a canonical concatenation identity"
        (SuperRange.analyzeSuperEllipsisRangeConcat
            emptyRange nonemptyRange
          == SuperRange.RangeConcatCanonical
              (SuperRange.describeSuperEllipsisRange nonemptyRange))

testRankOneRangeMerge :: IO ()
testRankOneRangeMerge = do
  withRankOneRange 2 (Just 4) $ \first ->
    withRankOneRange 10 (Just 12) $ \second ->
      let concatenated = SuperRange.mergeSuperEllipsisRanges first second
          value = SuperRange.superEllipsisRangeConcatValue concatenated
      in case SuperRange.superEllipsisRangeConcatInsertion concatenated of
        Nothing ->
          fail "disjoint ranges produced only a map"
        Just insertion -> do
          let includedRanks = map
                (fmap (either rankOneElementRank
                              rankOneElementRank)
                  . superEllipsisInsertionPreimage insertion . rankOneTerminal)
                [1, 2, 3, 4, 9, 10, 11, 12]
              extentMember combinedRank =
                withConcatOrderedTransposal value $ \_ concatAtlas _ ->
                  withPageElement (atlasOriginCell concatAtlas) $ \origin ->
                    atlasSequenceDatumMember
                      <$> unrank
                        (atlasDataAt concatAtlas origin)
                        combinedRank
          assert "concat insertion includes exactly both disjoint ranges"
            (includedRanks
              == [ Nothing, Just 2, Just 3, Nothing
                 , Nothing, Just 10, Just 11, Nothing
                 ])
          assert "range concat preserves left and right operand tags"
            (map extentMember [4, 5, 20, 21]
              == [Just 0, Nothing, Nothing, Just 1])
  withRankOneRange 2 (Just 4) $ \first ->
    withRankOneRange 4 (Just 7) $ \second ->
      let concatenated = SuperRange.mergeSuperEllipsisRanges first second
      in case SuperRange.superEllipsisRangeConcatInsertion concatenated of
        Just insertion ->
          assert "adjacent ranges retain subtype capability"
            (all
              (\rankValue ->
                case superEllipsisInsertionPreimage insertion (rankOneTerminal rankValue) of
                  Just _ -> True
                  Nothing -> False)
              [2 .. 6])
        Nothing ->
          fail "adjacent non-overlapping ranges produced only a map"
  withRankOneRange 10 (Just 12) $ \first ->
    withRankOneRange 2 (Just 4) $ \second ->
      let concatenated = SuperRange.mergeSuperEllipsisRanges first second
          value = SuperRange.superEllipsisRangeConcatValue concatenated
      in case SuperRange.superEllipsisRangeConcatInsertion concatenated of
        Nothing ->
          fail "reverse disjoint ranges produced only a map"
        Just insertion -> do
          let extentMember combinedRank =
                withConcatOrderedTransposal value $ \_ concatAtlas _ ->
                  withPageElement (atlasOriginCell concatAtlas) $ \origin ->
                    atlasSequenceDatumMember
                      <$> unrank
                        (atlasDataAt concatAtlas origin)
                        combinedRank
          assert "reverse concat preserves both insertion branches"
            (map
              (fmap (either rankOneElementRank
                            rankOneElementRank)
                . superEllipsisInsertionPreimage insertion . rankOneTerminal)
              [2, 3, 10, 11]
              == map Just [2, 3, 10, 11])
          assert "swapping ranges changes the ordered concat presentation"
            (map extentMember [4, 5, 20, 21]
              == [Nothing, Just 1, Just 0, Nothing])
  withRankOneRange 2 (Just 5) $ \first ->
    withRankOneRange 4 (Just 7) $ \second ->
      let concatenated = SuperRange.mergeSuperEllipsisRanges first second
          value = SuperRange.superEllipsisRangeConcatValue concatenated
      in case SuperRange.superEllipsisRangeConcatInsertionResult concatenated of
        Left (SuperRange.SuperEllipsisRangesOverlap _ _ lower upper)
          | lower == finiteOrdinal 4 && upper == finiteOrdinal 5 ->
          withConcatOrderedTransposal value $ \_ concatAtlas _ ->
            assert "overlapping ranges retain their ordered concat map"
              (atlasPageHasExactly concatAtlas 1 6)
        Left rejection ->
          fail ("overlapping ranges reported the wrong rejection: " <> show rejection)
        Right _ ->
          fail "overlapping ranges produced an Ellipsis insertion"
  withRankOneRange 3 Nothing $ \first ->
    withRankOneRange 5 Nothing $ \second ->
      let concatenated = first `concatOperands` second
          value = SuperRange.superEllipsisRangeConcatValue concatenated
      in case SuperRange.superEllipsisRangeConcatInsertionResult concatenated of
        Left (SuperRange.SuperEllipsisRangesOverlap _ _ lower upper)
          | lower == finiteOrdinal 5 && upper == omega ->
          withConcatOrderedTransposal value $ \_ concatAtlas _ ->
            let finalContains position =
                  case pageElementIndex
                    (atlasPageElements concatAtlas) 1 position of
                      Just _ -> True
                      Nothing -> False
            in assert "two unbounded ranges concatenate with order type omega + omega"
              ( all finalContains
                  [ finiteOrdinal 0
                  , finiteOrdinal 1000
                  , omega
                  , addOrdinals omega (finiteOrdinal 1000)
                  ]
                && not (finalContains (addOrdinals omega omega))
              )
        Left rejection ->
          fail ("unbounded ranges reported the wrong rejection: " <> show rejection)
        Right _ ->
          fail "overlapping unbounded ranges produced an Ellipsis insertion"
  withRankOneRange 3 Nothing $ \first ->
    withRankOneRange 2 (Just 20) $ \second -> do
      let concatenated = first `concatOperands` second
          value = SuperRange.superEllipsisRangeConcatValue concatenated
      case SuperRange.superEllipsisRangeConcatInsertionResult concatenated of
        Left (SuperRange.SuperEllipsisRangesOverlap _ _ lower upper)
          | lower == finiteOrdinal 3 && upper == finiteOrdinal 20 ->
          withConcatOrderedTransposal value $ \_ concatAtlas _ ->
            let finalContains position =
                  case pageElementIndex
                    (atlasPageElements concatAtlas) 1 position of
                      Just _ -> True
                      Nothing -> False
            in assert "an unbounded then finite range has order type omega + 18"
              ( all finalContains
                  [ finiteOrdinal 1000
                  , omega
                  , addOrdinals omega (finiteOrdinal 17)
                  ]
                && not
                  (finalContains
                    (addOrdinals omega (finiteOrdinal 18)))
              )
        Left rejection ->
          fail ("omega-plus-finite ranges reported the wrong rejection: " <> show rejection)
        Right _ ->
          fail "overlapping omega-plus-finite ranges produced an insertion"
      let reversed = second `concatOperands` first
          reversedValue = SuperRange.superEllipsisRangeConcatValue reversed
      case SuperRange.superEllipsisRangeConcatInsertionResult reversed of
        Left (SuperRange.SuperEllipsisRangesOverlap _ _ lower upper)
          | lower == finiteOrdinal 3 && upper == finiteOrdinal 20 ->
          withConcatOrderedTransposal reversedValue $ \_ concatAtlas _ ->
            let finalContains position =
                  case pageElementIndex
                    (atlasPageElements concatAtlas) 1 position of
                      Just _ -> True
                      Nothing -> False
            in assert "swapping omega and finite ranges changes the ordinal sum"
              ( all finalContains
                  [ finiteOrdinal 17
                  , finiteOrdinal 18
                  , finiteOrdinal 1000
                  ]
                && not (finalContains omega)
              )
        Left rejection ->
          fail ("finite-plus-omega ranges reported the wrong rejection: " <> show rejection)
        Right _ ->
          fail "overlapping finite-plus-omega ranges produced an insertion"
  withRankOneRange 4 (Just 1) $ \descending ->
    withRankOneRange 3 (Just 6) $ \ascending ->
      let concatenated = descending `concatOperands` ascending
          value = SuperRange.superEllipsisRangeConcatValue concatenated
      in case SuperRange.superEllipsisRangeConcatInsertionResult concatenated of
        Left (SuperRange.SuperEllipsisRangesOverlap _ _ lower upper)
          | lower == finiteOrdinal 3 && upper == finiteOrdinal 5 ->
          withConcatOrderedTransposal value $ \_ concatAtlas _ ->
            assert "descending ranges retain their order in overlapping maps"
              (atlasPageHasExactly concatAtlas 1 6)
        Left rejection ->
          fail ("mixed-direction ranges reported the wrong rejection: " <> show rejection)
        Right _ ->
          fail "overlapping descending and ascending ranges produced an insertion"

testEllipsisNatural :: IO ()
testEllipsisNatural = do
  case DatraNatural.ellipsisNatural 0 $ \natural ->
    map
      (fmap rankOneElementRank
        . superEllipsisInsertionPreimage (DatraNatural.ellipsisNaturalInsertion natural) . rankOneTerminal)
      [0, 1]
    of
      Nothing -> fail "zero rankOneData natural was rejected"
      Just includedRanks ->
        assert "zero rankOneData natural includes exactly zero"
          (includedRanks == [Just 0, Nothing])
  case DatraNatural.ellipsisNatural 3 $ \natural -> do
    let insertion = DatraNatural.ellipsisNaturalInsertion natural
        includedRanks = map
          (fmap rankOneElementRank
            . superEllipsisInsertionPreimage insertion . rankOneTerminal)
          [2, 3, 4]
    assert "rankOneData natural uses consecutive range bounds"
      (rankOneValueLowerBound natural == Just 3
        && rankOneValueUpperBound natural == Just 4)
    assert "rankOneData natural includes exactly its value"
      (includedRanks == [Nothing, Just 3, Nothing])
    of
      Nothing -> fail "rankOneData natural was rejected"
      Just checks -> checks

testNumericalOperators :: IO ()
testNumericalOperators = do
  assertNumericalOperator "rankOneData-natural addition" Numeric.additionOperator 2 3 5
  assertNumericalOperator "rankOneData-natural multiplication" Numeric.multiplicationOperator 4 5 20
  assertNumericalOperator "rankOneData-natural exponentiation" Numeric.exponentiationOperator 2 10 1024
  assertNumericalOperator "rankOneData-natural zero exponent" Numeric.exponentiationOperator 7 0 1
  assertNumericalOperator "rankOneData-natural zero-to-zero power" Numeric.exponentiationOperator 0 0 1
  testGenericOrdinalOperators
  testStableDatumNumericalOperands

testNumericalSemanticsAgreement :: IO ()
testNumericalSemanticsAgreement = do
  let typedProductLevel =
        Numeric.multiplicationOperator ellipsis ellipsis
          (\value -> value `seq` (2 :: Natural))
      evaluatedProduct =
        Types.interpretedCanonicalResult
          <$> Types.multiplyValues
                (Types.formulationValue 1)
                (Types.formulationValue 1)
  assert "typed and evaluated formulation multiplication share level policy"
    ( typedProductLevel == Just 2
      && evaluatedProduct == Right (Types.CanonicalFormulation 2)
    )
  case DatraNatural.ellipsisNatural 3 $ \three ->
      Numeric.exponentiationOperator
        ellipsis three Numeric.someSuperEllipsisLevel of
    Just (Just typedPowerLevel) ->
      assert "typed and evaluated formulation exponentiation share level policy"
        ((Types.interpretedCanonicalResult
          <$> Types.exponentiateValues
                (Types.formulationValue 1)
                (Types.naturalValue 3))
          == Right (Types.CanonicalFormulation typedPowerLevel))
    _ -> fail "typed formulation exponentiation setup was rejected"
  case DatraNatural.ellipsisNatural 2 $ \two ->
      Numeric.additionOperator ellipsis two superEllipsisValueOrdinal of
    Just (Just typedSum) ->
      assert "typed and evaluated addition share ordinal policy"
        ((Types.interpretedCanonicalResult
          <$> Types.addValues
                (Types.formulationValue 1)
                (Types.naturalValue 2))
          == Right (Types.CanonicalExplicit 2 typedSum))
    _ -> fail "typed addition setup was rejected"

testTypingAbstractions :: IO ()
testTypingAbstractions = do
  assert "target levels and computed levels share one rank dictionary"
    ( superEllipsisTargetLevelNatural @Dot == 0
      && superEllipsisTargetLevelNatural @Ellipsis == 1
      && superEllipsisTargetLevelNatural @(SuperEllipsis Ellipsis) == 2
      && superEllipsisRankOrderType
           (knownSuperEllipsisRank
             @('NextLevel ('NextLevel 'DotLevel)))
           == ordinal [1, 0, 0]
    )
  case DatraNatural.ellipsisNatural 7 $ \value -> do
      let valueRange = superEllipsisValueRange value
          insertion = superEllipsisInsertionOf value
          firstPosition =
            SuperRange.superEllipsisRangeElementPosition
              <$> superEllipsisInsertionFirst insertion
          presentationCardinality presentation =
            case presentation of
              EmptyOrderedAtlasMap -> Nothing
              NonEmptyOrderedAtlasMap valueMap ->
                Just (indexedAtlasCardinality valueMap)
      assert "a numerical value has a total ordinal projection"
        (superEllipsisValueOrdinal value == finiteOrdinal 7)
      assert "a numerical value retains its singleton range presentation"
        ( SuperRange.superEllipsisRangeLowerBound valueRange
            == finiteOrdinal 7
          && SuperRange.superEllipsisRangeUpperBound valueRange
            == Just (finiteOrdinal 8)
        )
      assert "value, insertion, and map capabilities agree"
        ( firstPosition == Just (finiteOrdinal 7)
          && presentationCardinality (orderedAtlasMap value)
            == Just (finiteOrdinal 1)
          && presentationCardinality (orderedAtlasMap insertion)
            == Just (finiteOrdinal 1)
        )
    of
      Nothing -> fail "typing abstraction value setup was rejected"
      Just checks -> checks
  withEllipsisNatural 3 $ \three ->
    case (boundedSuperEllipsisRange three three) $ \emptyRange ->
      assert "empty range capabilities derive emptiness from their chain"
        ( superEllipsisInsertionFirst
            (superEllipsisInsertionOf emptyRange) == Nothing
          && case orderedAtlasMap emptyRange of
              EmptyOrderedAtlasMap -> True
              NonEmptyOrderedAtlasMap _ -> False
        )
    of
      Nothing -> fail "typing abstraction empty-range setup was rejected"
      Just checks -> checks

testGenericOrdinalOperators :: IO ()
testGenericOrdinalOperators = do
  let rankTwo = nextSuperEllipsisRank rankOneRank
      omegaPlusOne = addOrdinals omega (finiteOrdinal 1)
      operatorResults =
        superEllipsisValue rankTwo omegaPlusOne $ \left ->
          superEllipsisValue rankTwo omega $ \right ->
            ( Numeric.additionOperator left right superEllipsisValueOrdinal
            , Numeric.additionOperator right left superEllipsisValueOrdinal
            , Numeric.multiplicationOperator left right superEllipsisValueOrdinal
            , Numeric.multiplicationOperator right left superEllipsisValueOrdinal
            )
  case operatorResults of
    Just (Just actual) ->
      assert "higher-rank numerical operators use ordered ordinal arithmetic"
        ( actual
          == ( Just (ordinal [2, 0])
             , Just (ordinal [2, 1])
             , Just (ordinal [1, 0, 0])
             , Just (ordinal [1, 1, 0])
             )
        )
    _ -> fail "higher-rank ordinal operator setup was rejected"

testStableDatumNumericalOperands :: IO ()
testStableDatumNumericalOperands = do
  let levelTwoData :: StableConfederalData (SuperEllipsis Ellipsis)
      levelTwoData = superEllipsis ellipsis
      omegaSquared = ordinal [1, 0, 0]
      isEllipsisFormulation
        :: StableConfederalData Ellipsis -> Bool
      isEllipsisFormulation value = value `seq` True
      isLevelTwoFormulation
        :: StableConfederalData (SuperEllipsis Ellipsis) -> Bool
      isLevelTwoFormulation value = value `seq` True
      binaryResults =
        ( Numeric.additionOperator dot dot superEllipsisValueOrdinal
        , Numeric.additionOperator dot ellipsis superEllipsisValueOrdinal
        , Numeric.additionOperator ellipsis dot superEllipsisValueOrdinal
        , Numeric.multiplicationOperator dot ellipsis isEllipsisFormulation
        , Numeric.multiplicationOperator ellipsis dot isEllipsisFormulation
        , Numeric.multiplicationOperator ellipsis ellipsis isLevelTwoFormulation
        , Numeric.additionOperator ellipsis levelTwoData superEllipsisValueOrdinal
        , Numeric.additionOperator levelTwoData ellipsis superEllipsisValueOrdinal
        )
  assert "stable data denote successive omega powers in binary operators"
    ( binaryResults
      == ( Just (finiteOrdinal 2)
         , Just omega
         , Just (addOrdinals omega (finiteOrdinal 1))
         , Just True
         , Just True
         , Just True
         , Just omegaSquared
         , Just (ordinal [1, 1, 0])
         )
    )
  case DatraNatural.ellipsisNatural 0 $ \zero ->
      Numeric.additionOperator ellipsis zero superEllipsisValueOrdinal of
    Just (Just result) ->
      assert "adding zero soft-casts a formulation to an explicit value"
        (result == omega)
    _ -> fail "formulation soft cast was rejected"
  case DatraNatural.ellipsisNatural 3 $ \three ->
      Numeric.exponentiationOperator dot three Numeric.someSuperEllipsisLevel of
    Just (Just result) ->
      assert "Dot exponentiation returns Dot"
        (result == 0)
    _ -> fail "Dot exponentiation was rejected"
  case DatraNatural.ellipsisNatural 2 $ \two ->
      Numeric.exponentiationOperator ellipsis two Numeric.someSuperEllipsisLevel of
    Just (Just result) ->
      assert "Ellipsis squared returns the level-two formulation"
        (result == 2)
    _ -> fail "Ellipsis squared was rejected"
  case DatraNatural.ellipsisNatural 0 $ \zero ->
      Numeric.exponentiationOperator ellipsis zero Numeric.someSuperEllipsisLevel of
    Just (Just result) ->
      assert "Ellipsis to zero returns Dot"
        (result == 0)
    _ -> fail "Ellipsis to zero was rejected"
  let rankTwo = nextSuperEllipsisRank rankOneRank
      explicitOmegaSquared =
        superEllipsisValue rankTwo omega $ \omegaValue ->
          DatraNatural.ellipsisNatural 2 $ \two ->
            Numeric.exponentiationOperator omegaValue two superEllipsisValueOrdinal
  case explicitOmegaSquared of
    Just (Just Nothing) -> pure ()
    _ ->
      fail "rank-specific exponentiation constructed a non-minimal value"

assertNumericalOperator
  :: String
  -> (forall leftScope rightScope result.
        DatraNatural.EllipsisNatural leftScope
        -> DatraNatural.EllipsisNatural rightScope
        -> (forall resultScope. DatraNatural.EllipsisNatural resultScope -> result)
        -> Maybe result)
  -> Natural
  -> Natural
  -> Natural
  -> IO ()
assertNumericalOperator label operator leftValue rightValue expected =
  case DatraNatural.ellipsisNatural leftValue $ \left ->
    DatraNatural.ellipsisNatural rightValue $ \right ->
      operator left right $ \result ->
        rankOneValueLowerBound result == Just expected
          && rankOneValueUpperBound result == Just (expected + 1)
  of
    Just (Just (Just matches)) -> assert label matches
    _ -> fail ("test setup failed: " <> label)
