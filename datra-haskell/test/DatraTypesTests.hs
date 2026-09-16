{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}

module Main (main) where

import AsciiDominion
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
import CanonicalCharsDominion
import Dominion
import DatraOrdinal (addOrdinals, finiteOrdinal, omega)
import DomanialInclusion (dominionAtlas, dominionCellDataValue)
import Dot
  ( dot
  , dotAtlas
  , dotAtlasMap
  , dotDominion
  , dotTerminal
  )
import DomanialInsertion (applyInsertion, preimage)
import Ellipsis
import EllipsisInsertion
import EllipsisNatural
import EllipsisNaturalRange
import FiniteDominion
import MapMakingOperators
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
import StableConfederalData (mapStableConfederalDataHom)

import Data.Maybe (isNothing)
import qualified Data.Set as Set

main :: IO ()
main = do
  testAsciiDominion
  testCanonicalCharsDominion
  testDot
  testSequentialOperator
  testConcatOperator
  testGroupedSequentialExpansion
  testComplexOperatorStructure
  testEllipsis
  testEllipsisInsertion
  testEllipsisInsertionDominion
  testEllipsisNaturalRange
  testEllipsisNaturalRangeMerge
  testEllipsisNatural
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

testAsciiDominion :: IO ()
testAsciiDominion =
  asciiDominion $ \ascii -> do
    assert "ASCII dominion has 256 ranks"
      (asciiCardinality == 256
        && finiteCardinality ascii == asciiCardinality)
    assert "ASCII dominion maps ranks to matching characters"
      (map (asciiCharacterAt ascii) [0, 65, 97, 255, 256]
        == [Just '\0', Just 'A', Just 'a', Just '\255', Nothing])

testCanonicalCharsDominion :: IO ()
testCanonicalCharsDominion =
  canonicalCharsDominion $ \canonical -> do
    let boundaryRanks =
          [38, 39, 40, 47, 48, 57, 58, 64, 65, 90, 91, 94, 95, 96, 97, 122, 123]
        expected =
          [ Nothing, Just '\'', Nothing
          , Nothing, Just '0', Just '9', Nothing
          , Nothing, Just 'A', Just 'Z', Nothing
          , Nothing, Just '_', Nothing
          , Just 'a', Just 'z', Nothing
          ]
        included = filter
          (\valueRank -> case canonicalCharacterAt canonical valueRank of
            Nothing -> False
            Just _ -> True)
          [0 .. 255]
    assert "canonical character dominion uses exact ASCII ranks"
      (map (canonicalCharacterAt canonical) boundaryRanks == expected)
    assert "canonical character dominion contains exactly 64 characters"
      (fromIntegral (length included) == canonicalCharsCardinality)

withEllipsisNaturalRange
  :: Maybe Natural
  -> Maybe Natural
  -> (forall scope. EllipsisNaturalRange scope -> IO ())
  -> IO ()
withEllipsisNaturalRange lower upper useRange =
  case ellipsisNaturalRange lower upper useRange of
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
      insertion = ellipsisInsertion id Just (const ())
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
  asciiDominion $ \ascii ->
    withEllipsisNaturalRange (Just 65) (Just 68) $ \valueRange -> do
      let selected = ellipsisInsertionDominion
            (finiteAsDominion ascii)
            (ellipsisNaturalRangeInsertion valueRange)
          selectedCharacter =
            fmap
              (finiteValue . ellipsisInsertionElementValue)
              . unrank selected
      assert "ellipsis insertion restricts a dominion to selected ranks"
        (map selectedCharacter [64, 65, 66, 67, 68]
          == [Nothing, Just 'A', Just 'B', Just 'C', Nothing])
      assert "ellipsis insertion dominion preserves absolute ranks"
        (map (fmap (rank selected) . unrank selected) [65, 66, 67]
          == map Just [65, 66, 67])

testEllipsisNaturalRange :: IO ()
testEllipsisNaturalRange = do
  case ellipsisNaturalRange (Just 0) Nothing $ \valueRange ->
    map
      (fmap ellipsisNaturalRangeElementRank . ellipsisNaturalRangeElement valueRange)
      [0, 1]
    of
      Nothing -> fail "zero lower bound was rejected"
      Just actual ->
        assert "zero is a valid lower bound"
          (actual == [Just 0, Just 1])
  assert "ellipsis range rejects an empty implicit-lower range"
    (case ellipsisNaturalRange Nothing (Just 0) (const ()) of
      Nothing -> True
      Just () -> False)
  assert "ellipsis range rejects an empty zero-bounded range"
    (case ellipsisNaturalRange (Just 0) (Just 0) (const ()) of
      Nothing -> True
      Just () -> False)
  assert "ellipsis range rejects equal bounds"
    (case ellipsisNaturalRange (Just 3) (Just 3) (const ()) of
      Nothing -> True
      Just () -> False)
  assert "ellipsis range rejects descending bounds"
    (case ellipsisNaturalRange (Just 5) (Just 2) (const ()) of
      Nothing -> True
      Just () -> False)
  case ellipsisNaturalRange (Just 2) (Just 5) $ \valueRange -> do
    let insertion = ellipsisNaturalRangeInsertion valueRange
        expected = [Nothing, Nothing, Just 2, Just 3, Just 4, Nothing]
        actual = map
          (fmap ellipsisNaturalRangeElementRank
            . ellipsisInsertionPreimage insertion . Terminal)
          [0 .. 5]
    assert "bounded ellipsis range is lower-inclusive and upper-exclusive"
      (actual == expected)
    assert "ellipsis range insertion satisfies its left-inverse law"
      (all
        (\rankValue ->
          case ellipsisNaturalRangeElement valueRange rankValue of
            Nothing -> False
            Just element ->
              ellipsisInsertionPreimage insertion (applyEllipsisInsertion insertion element)
                == Just element)
        [2 .. 4])
    of
      Nothing -> fail "valid bounded ellipsis range was rejected"
      Just checks -> checks
  case ellipsisNaturalRange Nothing (Just 5) $ \valueRange ->
    map
      (fmap ellipsisNaturalRangeElementRank . ellipsisNaturalRangeElement valueRange)
      [0 .. 5]
    of
      Nothing -> fail "valid upper-bounded ellipsis range was rejected"
      Just actual ->
        assert "missing lower bound includes all lower terminals"
          (actual == [Just 0, Just 1, Just 2, Just 3, Just 4, Nothing])
  case ellipsisNaturalRange (Just 2) Nothing $ \valueRange ->
    map
      (fmap ellipsisNaturalRangeElementRank . ellipsisNaturalRangeElement valueRange)
      [1, 2, 1000000]
    of
      Nothing -> fail "valid lower-bounded ellipsis range was rejected"
      Just actual ->
        assert "missing upper bound includes every later terminal"
          (actual == [Nothing, Just 2, Just 1000000])
  case ellipsisNaturalRange Nothing Nothing $ \valueRange ->
    map
      (fmap ellipsisNaturalRangeElementRank . ellipsisNaturalRangeElement valueRange)
      [0, 1, 1000000]
    of
      Nothing -> fail "unbounded ellipsis range was rejected"
      Just actual ->
        assert "missing bounds include all terminals"
          (actual == [Just 0, Just 1, Just 1000000])

testEllipsisNaturalRangeMerge :: IO ()
testEllipsisNaturalRangeMerge = do
  withEllipsisNaturalRange (Just 2) (Just 4) $ \first ->
    withEllipsisNaturalRange (Just 10) (Just 12) $ \second ->
      case mergeEllipsisNaturalRanges first second of
        SomeEllipsisNaturalRangeConcat (ConcatenatedEllipsisMap _ _) ->
          fail "disjoint ranges produced only a map"
        SomeEllipsisNaturalRangeConcat
            (ConcatenatedEllipsisInsertion _ value insertion) -> do
          let includedRanks = map
                (fmap (either ellipsisNaturalRangeElementRank
                              ellipsisNaturalRangeElementRank)
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
  withEllipsisNaturalRange (Just 2) (Just 4) $ \first ->
    withEllipsisNaturalRange (Just 4) (Just 7) $ \second ->
      case mergeEllipsisNaturalRanges first second of
        SomeEllipsisNaturalRangeConcat
            (ConcatenatedEllipsisInsertion _ _ insertion) ->
          assert "adjacent ranges retain subtype capability"
            (all
              (\rankValue ->
                case ellipsisInsertionPreimage insertion (Terminal rankValue) of
                  Just _ -> True
                  Nothing -> False)
              [2 .. 6])
        SomeEllipsisNaturalRangeConcat (ConcatenatedEllipsisMap _ _) ->
          fail "adjacent non-overlapping ranges produced only a map"
  withEllipsisNaturalRange (Just 10) (Just 12) $ \first ->
    withEllipsisNaturalRange (Just 2) (Just 4) $ \second ->
      case mergeEllipsisNaturalRanges first second of
        SomeEllipsisNaturalRangeConcat (ConcatenatedEllipsisMap _ _) ->
          fail "reverse disjoint ranges produced only a map"
        SomeEllipsisNaturalRangeConcat
            (ConcatenatedEllipsisInsertion _ value insertion) -> do
          let extentMember combinedRank =
                withConcatOrderedTransposal value $ \_ concatAtlas _ ->
                  withPageElement (atlasOriginCell concatAtlas) $ \origin ->
                    atlasSequenceDatumMember
                      <$> unrank
                        (atlasDataAt concatAtlas origin)
                        combinedRank
          assert "reverse concat preserves both insertion branches"
            (map
              (fmap (either ellipsisNaturalRangeElementRank
                            ellipsisNaturalRangeElementRank)
                . ellipsisInsertionPreimage insertion . Terminal)
              [2, 3, 10, 11]
              == map Just [2, 3, 10, 11])
          assert "swapping ranges changes the ordered concat presentation"
            (map extentMember [4, 5, 20, 21]
              == [Nothing, Just 1, Just 0, Nothing])
  withEllipsisNaturalRange (Just 2) (Just 5) $ \first ->
    withEllipsisNaturalRange (Just 4) (Just 7) $ \second ->
      case mergeEllipsisNaturalRanges first second of
        SomeEllipsisNaturalRangeConcat
            (ConcatenatedEllipsisInsertion _ _ _) ->
          fail "overlapping ranges produced an Ellipsis insertion"
        SomeEllipsisNaturalRangeConcat (ConcatenatedEllipsisMap _ value) ->
          withConcatOrderedTransposal value $ \_ concatAtlas _ ->
            assert "overlapping ranges retain their ordered concat map"
              (atlasPageHasExactly concatAtlas 1 6)
  withEllipsisNaturalRange (Just 3) Nothing $ \first ->
    withEllipsisNaturalRange (Just 5) Nothing $ \second ->
      case concatEllipsisNaturalRanges first second of
        SomeEllipsisNaturalRangeConcat
            (ConcatenatedEllipsisInsertion _ _ _) ->
          fail "overlapping unbounded ranges produced an Ellipsis insertion"
        SomeEllipsisNaturalRangeConcat (ConcatenatedEllipsisMap _ value) ->
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
  withEllipsisNaturalRange (Just 3) Nothing $ \first ->
    withEllipsisNaturalRange (Just 2) (Just 20) $ \second -> do
      case first <.> second of
        SomeEllipsisNaturalRangeConcat
            (ConcatenatedEllipsisInsertion _ _ _) ->
          fail "overlapping omega-plus-finite ranges produced an insertion"
        SomeEllipsisNaturalRangeConcat (ConcatenatedEllipsisMap _ value) ->
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
        SomeEllipsisNaturalRangeConcat
            (ConcatenatedEllipsisInsertion _ _ _) ->
          fail "overlapping finite-plus-omega ranges produced an insertion"
        SomeEllipsisNaturalRangeConcat (ConcatenatedEllipsisMap _ value) ->
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

testEllipsisNatural :: IO ()
testEllipsisNatural = do
  case ellipsisNatural 0 $ \natural ->
    map
      (fmap ellipsisNaturalRangeElementRank
        . ellipsisInsertionPreimage (ellipsisNaturalInsertion natural) . Terminal)
      [0, 1]
    of
      Nothing -> fail "zero ellipsis natural was rejected"
      Just includedRanks ->
        assert "zero ellipsis natural includes exactly zero"
          (includedRanks == [Just 0, Nothing])
  case ellipsisNatural 3 $ \natural -> do
    let insertion = ellipsisNaturalInsertion natural
        includedRanks = map
          (fmap ellipsisNaturalRangeElementRank
            . ellipsisInsertionPreimage insertion . Terminal)
          [2, 3, 4]
    assert "ellipsis natural uses consecutive range bounds"
      (ellipsisNaturalRangeLowerBound natural == Just 3
        && ellipsisNaturalRangeUpperBound natural == Just 4)
    assert "ellipsis natural includes exactly its value"
      (includedRanks == [Nothing, Just 3, Nothing])
    of
      Nothing -> fail "ellipsis natural was rejected"
      Just checks -> checks

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
