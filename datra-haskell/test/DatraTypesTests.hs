{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}

module Main (main) where

import AsciiMap
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
  , mergeAtlasConfederations
  , singletonAtlasConfederation
  )
import AtlasCoveredPageElement
  ( atlasCoveredPageElement
  , withAtlasCoveredPageElement
  )
import AtlasMap (withAtlasMapExtent)
import AtlasTransposal
  ( atlasTransposalElement
  , withAtlasTransposalElement
  )
import AtlasSequence (atlasSequenceDatumMember)
import CanonicalCharsMap
import Dominion
import Chain
  ( chain
  , chainIndex
  , chainObjectAt
  , chainOrderType
  )
import DatraOrdinal
  ( addOrdinals
  , finiteOrdinal
  , naturalAtOrdinal
  , omega
  )
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
import Ellipsis
import EllipsisInsertion
import Natural qualified as DatraNatural
import NaturalRange
import FiniteDominion
import MapOperators
import Numeric.Natural (Natural)
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
  , mapStableConfederalDataHom
  )
import SuperEllipsis
import SuperEllipsisInsertion
  ( superEllipsisInsertionChain
  , superEllipsisInsertionPosition
  )
import qualified SuperEllipsisRange as SuperRange

import Data.Maybe (isNothing)
import qualified Data.Set as Set
import qualified NumericalOperators as Numeric

main :: IO ()
main = do
  testAsciiMap
  testCanonicalCharsMap
  testAccessOperator
  testDot
  testSequentialOperator
  testConcatOperator
  testGroupedSequentialExpansion
  testComplexOperatorStructure
  testEllipsis
  testSuperEllipsis
  testSuperEllipsisRange
  testEllipsisInsertion
  testEllipsisInsertionDominion
  testNaturalRange
  testNaturalRangeMerge
  testNatural
  testNumericalOperators
  testFiniteDominion

assert :: String -> Bool -> IO ()
assert label condition
  | condition = pure ()
  | otherwise = fail ("test failed: " <> label)

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
        rollSuperEllipsisLayer (unrollSuperEllipsisLayer ellipsisValue)
  levelOne `seq`
    levelTwo `seq`
      levelTwoUnfolded `seq`
        levelTwoFold `seq`
          levelTwoUnfold `seq`
            roundTripValue `seq`
              assert "super ellipsis constructs Ellipsis and its successor" True

testSuperEllipsisRange :: IO ()
testSuperEllipsisRange = asciiMap $ \ascii -> do
  let rankTwo = nextSuperEllipsisRank ellipsisRank
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
  case SuperRange.superEllipsisRange
      rankTwo
      (Just omega)
      (SuperRange.FiniteTarget
        (addOrdinals omega (finiteOrdinal 3))) $ \valueRange -> do
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
    assert "finite maps reject transfinite super-ellipsis positions"
      (case ascii <@> insertion of
        Nothing -> True
        Just _ -> False)
    of
      Nothing -> fail "valid transfinite rank-two range was rejected"
      Just checks -> checks
  case SuperRange.superEllipsisRange
      rankTwo
      (Just (finiteOrdinal 65))
      (SuperRange.FiniteTarget (finiteOrdinal 68)) $ \valueRange ->
    case ascii <@> SuperRange.superEllipsisRangeInsertion valueRange of
      Nothing -> False
      Just selected -> indexedAtlasCardinality selected == 3
    of
      Nothing -> fail "valid finite rank-two range was rejected"
      Just fits ->
        assert "access accepts a higher-rank insertion that fits the map" fits

type EllipsisConfederationScope =
  SingletonAtlasConfederationScope EllipsisAtlasObject

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
  let sequenced = ellipsis <:> ellipsis <:> ellipsis
      ellipsisConfederation = singletonAtlasConfederation ellipsisAtlas
      pairConfederation = mergeAtlasConfederations
        ellipsisConfederation ellipsisConfederation
      pair ::
        SequentialOperatorValue Ellipsis Ellipsis EllipsisPairObject
      pair =
        sequentialValue
          ellipsisConfederation
          ellipsisConfederation
          ellipsisValue
          ellipsisValue
      triple ::
        SequentialOperatorValue Ellipsis EllipsisPairValues EllipsisTripleObject
      triple =
        sequentialValue
          ellipsisConfederation
          pairConfederation
          ellipsisValue
          pair
      leftTriple ::
        SequentialOperatorValue EllipsisPairValues Ellipsis
          EllipsisLeftTripleObject
      leftTriple =
        sequentialValue
          pairConfederation
          ellipsisConfederation
          pair
          ellipsisValue
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
  let concatenated = ellipsis <.> ellipsis
      ellipsisConfederation = singletonAtlasConfederation ellipsisAtlas
      pair ::
        ConcatOperatorValue Ellipsis Ellipsis EllipsisPairObject
      pair =
        concatValue
          ellipsisConfederation
          ellipsisConfederation
          ellipsisValue
          ellipsisValue
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
        ellipsis <:> ellipsis <+> ellipsis <:> ellipsis
      ellipsisConfederation = singletonAtlasConfederation ellipsisAtlas
      pairConfederation = mergeAtlasConfederations
        ellipsisConfederation ellipsisConfederation
      pair ::
        SequentialOperatorValue Ellipsis Ellipsis EllipsisPairObject
      pair =
        sequentialValue
          ellipsisConfederation
          ellipsisConfederation
          ellipsisValue
          ellipsisValue
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
        ellipsis <:> ellipsis <:> ellipsis
          <+> ellipsis <:> ellipsis
      complexObject = fiveObject <+> fiveObject
      ellipsisConfederation = singletonAtlasConfederation ellipsisAtlas
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
          ellipsisValue
          ellipsisValue
      triple ::
        SequentialOperatorValue
          Ellipsis
          EllipsisPairValues
          EllipsisTripleObject
      triple =
        sequentialValue
          ellipsisConfederation
          pairConfederation
          ellipsisValue
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
        && indexedAtlasCardinality ascii == asciiCardinality
        && atlasCardinality valueAtlas == 2
        && atlasPageHasExactly valueAtlas 1 asciiCardinality)
    assert "ASCII map positions contain matching characters"
      (map (asciiCharacterAt ascii) [0, 65, 97, 255, 256]
        == [Just '\0', Just 'A', Just 'a', Just '\255', Nothing])

testCanonicalCharsMap :: IO ()
testCanonicalCharsMap =
  case canonicalCharsMap (\canonical -> do
      let valueAtlas = indexedAtlasAtlas canonical
          positions = [0, 1, 10, 11, 36, 37, 38, 63, 64]
          expected =
            [ Just '\'', Just '0', Just '9', Just 'A', Just 'Z'
            , Just '_', Just 'a', Just 'z', Nothing
            ]
      assert "canonical characters retain their ASCII order under access"
        (map (canonicalCharacterAt canonical) positions == expected)
      assert "canonical character access produces a two-page 64-cell map"
        ( indexedAtlasCardinality canonical == canonicalCharsCardinality
          && atlasCardinality valueAtlas == 2
          && atlasPageHasExactly valueAtlas 1 canonicalCharsCardinality
        )) of
    Nothing -> fail "canonical character insertion did not fit ASCII"
    Just checks -> checks

testAccessOperator :: IO ()
testAccessOperator =
  asciiMap $ \ascii -> do
    withNaturalRange (Just 10) (Just 12) $ \first ->
      withNaturalRange (Just 2) (Just 4) $ \second ->
        case concatNaturalRanges first second of
          SomeNaturalRangeConcat
              (ConcatenatedNaturalMap _ _) ->
            fail "disjoint access ranges produced only a map"
          SomeNaturalRangeConcat
              (ConcatenatedNaturalInsertion _ _ insertion) ->
            case ascii <@> insertion of
              Nothing -> fail "in-bounds reordered access was rejected"
              Just selected -> do
                let selectedCharacter position =
                      asciiCharacterValue . accessElementValue
                        <$> indexedAtlasValueAt selected position
                    valueAtlas = indexedAtlasAtlas selected
                assert "access follows insertion order and can reorder values"
                  (map selectedCharacter [0 .. 4]
                    == [ Just '\10', Just '\11', Just '\2', Just '\3'
                       , Nothing
                       ])
                assert "access returns a flattened two-page map"
                  (atlasCardinality valueAtlas == 2
                    && atlasPageHasExactly valueAtlas 1 4)
    withNaturalRange (Just 255) (Just 257) $ \outside ->
      assert "access rejects an insertion exceeding final cardinality"
        (case ascii <@> naturalRangeInsertion outside of
          Nothing -> True
          Just _ -> False)

withNaturalRange
  :: Maybe Natural
  -> Maybe Natural
  -> (forall scope. NaturalRange scope -> IO ())
  -> IO ()
withNaturalRange lower upper useRange =
  case naturalRange
      lower
      (maybe UnboundedTarget FiniteTarget upper)
      useRange of
    Nothing -> fail "test setup failed: valid ellipsis range was rejected"
    Just checks -> checks

testEllipsis :: IO ()
testEllipsis =
  withAtlasMapExtent ellipsisAtlasMap $ \_ extent coversExtent -> do
    let ranks :: [Natural]
        ranks = [0, 1, 2, 1000000]
        roundTrips valueRank =
          fmap (rank extent) (unrank extent valueRank) == Just valueRank
        covered valueRank =
          case unrank extent valueRank of
            Nothing -> False
            Just datum -> coversExtent datum `seq` True
    ellipsis `seq` pure ()
    assert "ellipsis is represented by a cardinality-two Atlas map"
      (atlasCardinality ellipsisAtlas == 2)
    assert "ellipsis has one covered terminal region at every natural rank"
      (all roundTrips ranks && all covered ranks)
    let elements = atlasPageElements ellipsisAtlas
        terminalRegion valueRank = do
          index <- pageElementIndex elements 1 (finiteOrdinal valueRank)
          pure $ withPageElement (pageElement index) $ \region ->
            let regionDominion = atlasDataAt ellipsisAtlas region
            in fmap (rank regionDominion) (unrank regionDominion 0) == Just 0
                && isNothing (unrank regionDominion 1)
    assert "all omega final regions carry the same terminal dominion"
      (map terminalRegion ranks == map (const (Just True)) ranks)
    let unfolded =
          mapStableConfederalDataHom ellipsisUnfold ellipsisValue
        rerolled =
          mapStableConfederalDataHom ellipsisFold unfolded
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
    assert "ellipsis unrolls as Dot concatenated with Ellipsis"
      (hasRecursiveShape unfolded)
    withEllipsisValue rerolled $ \rerolledLayer ->
      assert "rolling the Ellipsis layer restores the fixed-point value"
        (hasRecursiveShape rerolledLayer)

testEllipsisInsertion :: IO ()
testEllipsisInsertion = do
  let insertion :: EllipsisInsertion EllipsisTerminal
      insertion = ellipsisInsertion
        (Just (Terminal 0))
        (chain
          omega
          (finiteOrdinal . terminalRank)
          (fmap Terminal . naturalAtOrdinal)
          (const ())
          (\_ _ -> ())
          (const ()))
        id
        Just
        (const ())
      terminals = map Terminal [0, 1, 1000000]
      traversalPreservesTerminal terminal =
        let sourceAtlas = dominionAtlas ellipsisDominion
        in withPageElement (atlasOriginCell sourceAtlas) $ \sourceOrigin ->
          case unrank
            (atlasDataAt sourceAtlas sourceOrigin)
            (terminalRank terminal) of
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
                        (ellipsisInsertionTraversal insertion)
                        sourceCovered
                in withAtlasCoveredPageElement targetCovered $
                  \targetOccurrence targetDatum ->
                    rank
                      (atlasDataAt ellipsisAtlas targetOccurrence)
                      targetDatum
                      == terminalRank terminal
  assert "ellipsis insertion is an Atlas traversal into ellipsis"
    (all traversalPreservesTerminal terminals
      && all
      (\terminal ->
        ellipsisInsertionPreimage insertion
          (applyEllipsisInsertion insertion terminal) == Just terminal)
      terminals)

testEllipsisInsertionDominion :: IO ()
testEllipsisInsertionDominion =
  asciiMap $ \ascii ->
    withNaturalRange (Just 65) (Just 68) $ \valueRange -> do
      let selected = ellipsisInsertionDominion
            (indexedAtlasDominion ascii)
            (naturalRangeInsertion valueRange)
          selectedCharacter =
            fmap
              (asciiCharacterValue . ellipsisInsertionElementValue)
              . unrank selected
      assert "ellipsis insertion restricts a dominion to selected ranks"
        (map selectedCharacter [64, 65, 66, 67, 68]
          == [Nothing, Just 'A', Just 'B', Just 'C', Nothing])
      assert "ellipsis insertion dominion preserves absolute ranks"
        (map (fmap (rank selected) . unrank selected) [65, 66, 67]
          == map Just [65, 66, 67])

testNaturalRange :: IO ()
testNaturalRange = do
  assert "an omitted first endpoint cannot descend from infinity"
    (case naturalRange Nothing NegativeOne (const ()) of
      Nothing -> True
      Just () -> False)
  case naturalRange (Just 3) (FiniteTarget 3) $ \valueRange -> do
    let insertion = naturalRangeInsertion valueRange
    assert "equal endpoints form a valid empty range"
      ( all
          (\rankValue ->
            naturalRangeElement valueRange rankValue == Nothing)
          [0 .. 6]
        && ellipsisInsertionFirst insertion == Nothing
        && naturalRangeSize valueRange == Just 0
        && chainOrderType (ellipsisInsertionChain insertion)
          == finiteOrdinal 0
      )
    of
      Nothing -> fail "equal endpoints were rejected"
      Just checks -> checks
  withNaturalRange (Just 3) (Just 3) $ \emptyRange ->
    withNaturalRange (Just 5) (Just 7) $ \nonemptyRange ->
      case emptyRange <.> nonemptyRange of
        SomeNaturalRangeConcat
            (ConcatenatedNaturalMap _ _) ->
          fail "an empty range prevented insertion concatenation"
        SomeNaturalRangeConcat
            (ConcatenatedNaturalInsertion _ value insertion) ->
          withConcatOrderedTransposal value $ \_ concatAtlas _ ->
            assert "an empty range contributes zero ordered cells"
              ( atlasPageHasExactly concatAtlas 1 2
                && case ellipsisInsertionFirst insertion of
                    Just (Right element) ->
                      naturalRangeElementRank element == 5
                    _ -> False
              )
  case naturalRange (Just 4) (FiniteTarget 1) $ \valueRange -> do
    let insertion = naturalRangeInsertion valueRange
        at position =
          naturalRangeElementRank . chainObjectAt
            <$> chainIndex
              (ellipsisInsertionChain insertion)
              (finiteOrdinal position)
    assert "a descending range is first-inclusive and second-exclusive"
      (map at [0 .. 3] == [Just 4, Just 3, Just 2, Nothing]
        && map
          (fmap naturalRangeElementRank
            . naturalRangeElement valueRange)
          [0 .. 5]
          == [Nothing, Nothing, Just 2, Just 3, Just 4, Nothing])
    of
      Nothing -> fail "descending range was rejected"
      Just checks -> checks
  case naturalRange (Just 5) (FiniteTarget 0) $ \valueRange -> do
    let included rankValue =
          case naturalRangeElement valueRange rankValue of
            Nothing -> False
            Just _ -> True
    assert "a finite zero target remains exclusive"
      (map included [0 .. 6]
        == [False, True, True, True, True, True, False])
    of
      Nothing -> fail "finite zero target was rejected"
      Just checks -> checks
  case naturalRange (Just 5) NegativeOne $ \valueRange -> do
    let insertion = naturalRangeInsertion valueRange
        at position =
          naturalRangeElementRank . chainObjectAt
            <$> chainIndex
              (ellipsisInsertionChain insertion)
              (finiteOrdinal position)
    assert "NegativeOne descends through zero inclusively"
      (map at [0 .. 6]
        == [Just 5, Just 4, Just 3, Just 2, Just 1, Just 0, Nothing])
    of
      Nothing -> fail "NegativeOne target was rejected"
      Just checks -> checks
  case naturalRange (Just 2) (FiniteTarget 5) $ \valueRange -> do
    let insertion = naturalRangeInsertion valueRange
        expected = [Nothing, Nothing, Just 2, Just 3, Just 4, Nothing]
        actual = map
          (fmap naturalRangeElementRank
            . ellipsisInsertionPreimage insertion . Terminal)
          [0 .. 5]
    assert "bounded ellipsis range is lower-inclusive and upper-exclusive"
      (actual == expected)
    assert "ellipsis range insertion satisfies its left-inverse law"
      (all
        (\rankValue ->
          case naturalRangeElement valueRange rankValue of
            Nothing -> False
            Just element ->
              ellipsisInsertionPreimage insertion (applyEllipsisInsertion insertion element)
                == Just element)
        [2 .. 4])
    of
      Nothing -> fail "valid bounded ellipsis range was rejected"
      Just checks -> checks
  case naturalRange Nothing (FiniteTarget 5) $ \valueRange ->
    map
      (fmap naturalRangeElementRank . naturalRangeElement valueRange)
      [0 .. 5]
    of
      Nothing -> fail "valid upper-bounded ellipsis range was rejected"
      Just actual ->
        assert "missing lower bound includes all lower terminals"
          (actual == [Just 0, Just 1, Just 2, Just 3, Just 4, Nothing])
  case naturalRange (Just 2) UnboundedTarget $ \valueRange ->
    map
      (fmap naturalRangeElementRank . naturalRangeElement valueRange)
      [1, 2, 1000000]
    of
      Nothing -> fail "valid lower-bounded ellipsis range was rejected"
      Just actual ->
        assert "missing upper bound includes every later terminal"
          (actual == [Nothing, Just 2, Just 1000000])
  case naturalRange Nothing UnboundedTarget $ \valueRange ->
    map
      (fmap naturalRangeElementRank . naturalRangeElement valueRange)
      [0, 1, 1000000]
    of
      Nothing -> fail "unbounded ellipsis range was rejected"
      Just actual ->
        assert "missing bounds include all terminals"
          (actual == [Just 0, Just 1, Just 1000000])

testNaturalRangeMerge :: IO ()
testNaturalRangeMerge = do
  withNaturalRange (Just 2) (Just 4) $ \first ->
    withNaturalRange (Just 10) (Just 12) $ \second ->
      case mergeNaturalRanges first second of
        SomeNaturalRangeConcat (ConcatenatedNaturalMap _ _) ->
          fail "disjoint ranges produced only a map"
        SomeNaturalRangeConcat
            (ConcatenatedNaturalInsertion _ value insertion) -> do
          let includedRanks = map
                (fmap (either naturalRangeElementRank
                              naturalRangeElementRank)
                  . ellipsisInsertionPreimage insertion . Terminal)
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
  withNaturalRange (Just 2) (Just 4) $ \first ->
    withNaturalRange (Just 4) (Just 7) $ \second ->
      case mergeNaturalRanges first second of
        SomeNaturalRangeConcat
            (ConcatenatedNaturalInsertion _ _ insertion) ->
          assert "adjacent ranges retain subtype capability"
            (all
              (\rankValue ->
                case ellipsisInsertionPreimage insertion (Terminal rankValue) of
                  Just _ -> True
                  Nothing -> False)
              [2 .. 6])
        SomeNaturalRangeConcat (ConcatenatedNaturalMap _ _) ->
          fail "adjacent non-overlapping ranges produced only a map"
  withNaturalRange (Just 10) (Just 12) $ \first ->
    withNaturalRange (Just 2) (Just 4) $ \second ->
      case mergeNaturalRanges first second of
        SomeNaturalRangeConcat (ConcatenatedNaturalMap _ _) ->
          fail "reverse disjoint ranges produced only a map"
        SomeNaturalRangeConcat
            (ConcatenatedNaturalInsertion _ value insertion) -> do
          let extentMember combinedRank =
                withConcatOrderedTransposal value $ \_ concatAtlas _ ->
                  withPageElement (atlasOriginCell concatAtlas) $ \origin ->
                    atlasSequenceDatumMember
                      <$> unrank
                        (atlasDataAt concatAtlas origin)
                        combinedRank
          assert "reverse concat preserves both insertion branches"
            (map
              (fmap (either naturalRangeElementRank
                            naturalRangeElementRank)
                . ellipsisInsertionPreimage insertion . Terminal)
              [2, 3, 10, 11]
              == map Just [2, 3, 10, 11])
          assert "swapping ranges changes the ordered concat presentation"
            (map extentMember [4, 5, 20, 21]
              == [Nothing, Just 1, Just 0, Nothing])
  withNaturalRange (Just 2) (Just 5) $ \first ->
    withNaturalRange (Just 4) (Just 7) $ \second ->
      case mergeNaturalRanges first second of
        SomeNaturalRangeConcat
            (ConcatenatedNaturalInsertion _ _ _) ->
          fail "overlapping ranges produced an Ellipsis insertion"
        SomeNaturalRangeConcat (ConcatenatedNaturalMap _ value) ->
          withConcatOrderedTransposal value $ \_ concatAtlas _ ->
            assert "overlapping ranges retain their ordered concat map"
              (atlasPageHasExactly concatAtlas 1 6)
  withNaturalRange (Just 3) Nothing $ \first ->
    withNaturalRange (Just 5) Nothing $ \second ->
      case concatNaturalRanges first second of
        SomeNaturalRangeConcat
            (ConcatenatedNaturalInsertion _ _ _) ->
          fail "overlapping unbounded ranges produced an Ellipsis insertion"
        SomeNaturalRangeConcat (ConcatenatedNaturalMap _ value) ->
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
  withNaturalRange (Just 3) Nothing $ \first ->
    withNaturalRange (Just 2) (Just 20) $ \second -> do
      case first <.> second of
        SomeNaturalRangeConcat
            (ConcatenatedNaturalInsertion _ _ _) ->
          fail "overlapping omega-plus-finite ranges produced an insertion"
        SomeNaturalRangeConcat (ConcatenatedNaturalMap _ value) ->
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
      case second <.> first of
        SomeNaturalRangeConcat
            (ConcatenatedNaturalInsertion _ _ _) ->
          fail "overlapping finite-plus-omega ranges produced an insertion"
        SomeNaturalRangeConcat (ConcatenatedNaturalMap _ value) ->
          withConcatOrderedTransposal value $ \_ concatAtlas _ ->
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
  withNaturalRange (Just 4) (Just 1) $ \descending ->
    withNaturalRange (Just 3) (Just 6) $ \ascending ->
      case descending <.> ascending of
        SomeNaturalRangeConcat
            (ConcatenatedNaturalInsertion _ _ _) ->
          fail "overlapping descending and ascending ranges produced an insertion"
        SomeNaturalRangeConcat (ConcatenatedNaturalMap _ value) ->
          withConcatOrderedTransposal value $ \_ concatAtlas _ ->
            assert "descending ranges retain their order in overlapping maps"
              (atlasPageHasExactly concatAtlas 1 6)

testNatural :: IO ()
testNatural = do
  case DatraNatural.natural 0 $ \natural ->
    map
      (fmap naturalRangeElementRank
        . ellipsisInsertionPreimage (DatraNatural.naturalInsertion natural) . Terminal)
      [0, 1]
    of
      Nothing -> fail "zero ellipsis natural was rejected"
      Just includedRanks ->
        assert "zero ellipsis natural includes exactly zero"
          (includedRanks == [Just 0, Nothing])
  case DatraNatural.natural 3 $ \natural -> do
    let insertion = DatraNatural.naturalInsertion natural
        includedRanks = map
          (fmap naturalRangeElementRank
            . ellipsisInsertionPreimage insertion . Terminal)
          [2, 3, 4]
    assert "ellipsis natural uses consecutive range bounds"
      (naturalRangeLowerBound natural == Just 3
        && naturalRangeUpperBound natural == Just 4)
    assert "ellipsis natural includes exactly its value"
      (includedRanks == [Nothing, Just 3, Nothing])
    of
      Nothing -> fail "ellipsis natural was rejected"
      Just checks -> checks

testNumericalOperators :: IO ()
testNumericalOperators = do
  assertNumericalOperator "ellipsis-natural addition" (Numeric.+) 2 3 5
  assertNumericalOperator "ellipsis-natural multiplication" (Numeric.*) 4 5 20
  assertNumericalOperator "ellipsis-natural exponentiation" (Numeric.^) 2 10 1024
  assertNumericalOperator "ellipsis-natural zero exponent" (Numeric.^) 7 0 1
  assertNumericalOperator "ellipsis-natural zero-to-zero power" (Numeric.^) 0 0 1

assertNumericalOperator
  :: String
  -> (forall leftScope rightScope result.
        DatraNatural.Natural leftScope
        -> DatraNatural.Natural rightScope
        -> (forall resultScope. DatraNatural.Natural resultScope -> result)
        -> Maybe result)
  -> Natural
  -> Natural
  -> Natural
  -> IO ()
assertNumericalOperator label operator leftValue rightValue expected =
  case DatraNatural.natural leftValue $ \left ->
    DatraNatural.natural rightValue $ \right ->
      operator left right $ \result ->
        naturalRangeLowerBound result == Just expected
          && naturalRangeUpperBound result == Just (expected + 1)
  of
    Just (Just (Just matches)) -> assert label matches
    _ -> fail ("test setup failed: " <> label)

testFiniteDominion :: IO ()
testFiniteDominion =
  finiteSetDominion (Set.fromList ['a', 'b', 'c']) $ \finite -> do
    let members = traverse (finiteMember finite) ['a', 'b', 'c']
    case members of
      Nothing -> fail "test setup failed: carrier member was rejected"
      Just carrier -> do
        let valueDominion = finiteAsDominion finite
            valueRanks :: [Natural]
            valueRanks = map (rank valueDominion) carrier
        assert "finite dominion ranks its carrier"
          (valueRanks == [0, 1, 2])
        assert "finite dominion rejects values outside its carrier"
          (isNothing (finiteMember finite 'z'))
        assert "finite bounded rank unrank is total"
          (all
            (\value -> finiteUnrank (finiteRank value) == value)
            carrier)
        assert "finite dominion rank round-trips every carrier value"
          (all
            (\value ->
              unrank valueDominion (rank valueDominion value) == Just value)
            carrier)
        assert "finite dominion only constructs bounded indices"
          (map (fmap finiteIndexValue . finiteIndex finite) [0, 1, 2, 3]
            == [Just 0, Just 1, Just 2, Nothing])
        assert "finite dominion unrank is inverse"
          (map (fmap finiteValue . unrank valueDominion) [0, 1, 2, 3]
            == [Just 'a', Just 'b', Just 'c', Nothing])
