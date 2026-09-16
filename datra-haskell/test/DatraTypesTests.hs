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
  , identityAtlasConfederationHom
  , mergeAtlasConfederations
  , rightAtlasConfederationInclusion
  , singletonAtlasConfederation
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
import CanonicalCharsMap
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
import EllipsisNatural qualified as DatraNatural
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
  , StableConfederalDataHom
  , mapStableConfederalData
  , mapStableConfederalDataHom
  )
import SuperEllipsis
import SuperEllipsisInsertion
import qualified SuperEllipsisRange as SuperRange
import SuperEllipsisValue

import Data.Maybe (fromMaybe, isNothing)
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
  testSuperEllipsisInsertion
  testSuperEllipsisInsertionDominion
  testRankOneRange
  testRankOneRangeMerge
  testEllipsisNatural
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

rankOneData :: StableConfederalData Ellipsis
rankOneData = superEllipsis dot

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
      levelOne = rankOneData
      levelTwo :: StableConfederalData SuperEllipsisTwo
      levelTwo = superEllipsis rankOneData
      levelTwoUnfolded = superEllipsisUnfolded rankOneData
      levelTwoFold = superEllipsisFold rankOneData
      levelTwoUnfold = superEllipsisUnfold rankOneData
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
  case SuperRange.superEllipsisRange
      rankTwo
      omega
      (SuperRange.GivenTarget
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
    assert "finite maps reject transfinite super-rankOneData positions"
      (case ascii <@> insertion of
        Nothing -> True
        Just _ -> False)
    of
      Nothing -> fail "valid transfinite rank-two range was rejected"
      Just checks -> checks
  case SuperRange.superEllipsisRange
      rankTwo
      (finiteOrdinal 65)
      (SuperRange.GivenTarget (finiteOrdinal 68)) $ \valueRange ->
    case ascii <@> SuperRange.superEllipsisRangeInsertion valueRange of
      Nothing -> False
      Just selected ->
        indexedAtlasCardinality selected == finiteOrdinal 3
    of
      Nothing -> fail "valid finite rank-two range was rejected"
      Just fits ->
        assert "access accepts a higher-rank insertion that fits the map" fits

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
  let sequenced = rankOneData <:> rankOneData <:> rankOneData
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
  let concatenated = rankOneData <.> rankOneData
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
        rankOneData <:> rankOneData <+> rankOneData <:> rankOneData
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
        rankOneData <:> rankOneData <:> rankOneData
          <+> rankOneData <:> rankOneData
      complexObject = fiveObject <+> fiveObject
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
        ( indexedAtlasCardinality canonical
            == finiteOrdinal canonicalCharsCardinality
          && atlasCardinality valueAtlas == 2
          && atlasPageHasExactly valueAtlas 1 canonicalCharsCardinality
        )) of
    Nothing -> fail "canonical character insertion did not fit ASCII"
    Just checks -> checks

testAccessOperator :: IO ()
testAccessOperator =
  asciiMap $ \ascii -> do
    case ascii <@> dot of
      Nothing -> fail "Dot's underlying range was rejected"
      Just selected ->
        assert "access interprets Dot as its full one-element range"
          ( indexedAtlasCardinality selected == finiteOrdinal 1
            && fmap
              (asciiCharacterValue . accessElementValue)
              (indexedAtlasValueAt selected 0) == Just '\0'
          )
    assert "a finite map rejects Ellipsis's unbounded underlying range"
      (case ascii <@> rankOneData of
        Nothing -> True
        Just _ -> False)
    let naturalDominion = dominion id Just (const ())
        omegaMap = indexedAtlasMapFromChain 0 spine naturalDominion
    case omegaMap <@> rankOneData of
      Nothing -> fail "Ellipsis's range was rejected by an omega map"
      Just selected ->
        assert "access preserves an unbounded range that fits the map"
          ( indexedAtlasCardinality selected == omega
            && map
              (fmap accessElementValue . indexedAtlasValueAt selected)
              [0, 1, 1000000]
              == map Just [0, 1, 1000000]
          )
    let rankTwo = nextSuperEllipsisRank rankOneRank
        rankTwoMap = indexedAtlasMapFromChain
          (superEllipsisZeroTerminal rankTwo)
          (superEllipsisChain rankTwo)
          (superEllipsisDominion rankTwo)
        levelTwoData :: StableConfederalData (SuperEllipsis Ellipsis)
        levelTwoData = superEllipsis rankOneData
    case rankTwoMap <@> levelTwoData of
      Nothing -> fail "level-two formulation access was rejected"
      Just selected ->
        assert "access remains ordinal-indexed above omega"
          ( indexedAtlasCardinality selected == ordinal [1, 0, 0]
            && fmap
              ( superEllipsisTerminalPosition
                . accessElementValue
              )
              (indexedAtlasValueAtOrdinal selected omega) == Just omega
          )
    withRankOneRange 10 (Just 12) $ \first ->
      withRankOneRange 2 (Just 4) $ \second ->
        case SuperRange.concatSuperEllipsisRanges first second of
          SuperRange.SomeSuperEllipsisRangeConcat
              (SuperRange.ConcatenatedSuperEllipsisMap _ _) ->
            fail "disjoint access ranges produced only a map"
          SuperRange.SomeSuperEllipsisRangeConcat
              (SuperRange.ConcatenatedSuperEllipsisInsertion _ _ insertion) ->
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
    withRankOneRange 255 (Just 257) $ \outside ->
      assert "access rejects an insertion exceeding final cardinality"
        (case ascii <@> SuperRange.superEllipsisRangeInsertion outside of
          Nothing -> True
          Just _ -> False)

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

rankOneRange
  :: Natural
  -> SuperRange.SuperEllipsisRangeTarget
  -> (forall scope.
        SuperRange.SuperEllipsisRange Ellipsis scope -> result)
  -> Maybe result
rankOneRange start =
  SuperRange.superEllipsisRange rankOneRank (finiteOrdinal start)

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

rankOneRangeLowerBound
  :: SuperRange.SuperEllipsisRange Ellipsis scope
  -> Maybe Natural
rankOneRangeLowerBound valueRange =
  naturalAtOrdinal (SuperRange.superEllipsisRangeLowerBound valueRange)

rankOneRangeUpperBound
  :: SuperRange.SuperEllipsisRange Ellipsis scope
  -> Maybe Natural
rankOneRangeUpperBound valueRange =
  SuperRange.superEllipsisRangeUpperBound valueRange >>= naturalAtOrdinal

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
    rankOneData `seq` pure ()
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
        (Just (rankOneTerminal 0))
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
  case rankOneRange
      3 (SuperRange.GivenTarget (finiteOrdinal 3)) $ \valueRange -> do
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
      case emptyRange <.> nonemptyRange of
        SuperRange.SomeSuperEllipsisRangeConcat
            (SuperRange.ConcatenatedSuperEllipsisMap _ _) ->
          fail "an empty range prevented insertion concatenation"
        SuperRange.SomeSuperEllipsisRangeConcat
            (SuperRange.ConcatenatedSuperEllipsisInsertion _ value insertion) ->
          withConcatOrderedTransposal value $ \_ concatAtlas _ ->
            assert "an empty range contributes zero ordered cells"
              ( atlasPageHasExactly concatAtlas 1 2
                && case superEllipsisInsertionFirst insertion of
                    Just (Right element) ->
                      rankOneElementRank element == 5
                    _ -> False
              )
  case rankOneRange
      4 (SuperRange.GivenTarget (finiteOrdinal 1)) $ \valueRange -> do
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
  case rankOneRange
      5 (SuperRange.GivenTarget (finiteOrdinal 0)) $ \valueRange -> do
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
  case rankOneRange 5 SuperRange.MinusSign $ \valueRange -> do
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
  case rankOneRange
      2 (SuperRange.GivenTarget (finiteOrdinal 5)) $ \valueRange -> do
    let insertion = SuperRange.superEllipsisRangeInsertion valueRange
        expected = [Nothing, Nothing, Just 2, Just 3, Just 4, Nothing]
        actual = map
          (fmap rankOneElementRank
            . superEllipsisInsertionPreimage insertion . rankOneTerminal)
          [0 .. 5]
    assert "bounded rankOneData range is lower-inclusive and upper-exclusive"
      (actual == expected)
    assert "rankOneData range insertion satisfies its left-inverse law"
      (all
        (\rankValue ->
          case rankOneRangeElement valueRange rankValue of
            Nothing -> False
            Just element ->
              superEllipsisInsertionPreimage insertion (applySuperEllipsisInsertion insertion element)
                == Just element)
        [2 .. 4])
    of
      Nothing -> fail "valid bounded rankOneData range was rejected"
      Just checks -> checks
  case rankOneRange
      0 (SuperRange.GivenTarget (finiteOrdinal 5)) $ \valueRange ->
    map
      (fmap rankOneElementRank . rankOneRangeElement valueRange)
      [0 .. 5]
    of
      Nothing -> fail "valid upper-bounded rankOneData range was rejected"
      Just actual ->
        assert "an explicit zero lower bound includes lower terminals"
          (actual == [Just 0, Just 1, Just 2, Just 3, Just 4, Nothing])
  case rankOneRange 2 SuperRange.PlusSign $ \valueRange ->
    map
      (fmap rankOneElementRank . rankOneRangeElement valueRange)
      [1, 2, 1000000]
    of
      Nothing -> fail "valid lower-bounded rankOneData range was rejected"
      Just actual ->
        assert "missing upper bound includes every later terminal"
          (actual == [Nothing, Just 2, Just 1000000])
  case rankOneRange 0 SuperRange.PlusSign $ \valueRange ->
    map
      (fmap rankOneElementRank . rankOneRangeElement valueRange)
      [0, 1, 1000000]
    of
      Nothing -> fail "unbounded rankOneData range was rejected"
      Just actual ->
        assert "zero-to-unbounded includes all terminals"
          (actual == [Just 0, Just 1, Just 1000000])

testRankOneRangeMerge :: IO ()
testRankOneRangeMerge = do
  withRankOneRange 2 (Just 4) $ \first ->
    withRankOneRange 10 (Just 12) $ \second ->
      case SuperRange.mergeSuperEllipsisRanges first second of
        SuperRange.SomeSuperEllipsisRangeConcat (SuperRange.ConcatenatedSuperEllipsisMap _ _) ->
          fail "disjoint ranges produced only a map"
        SuperRange.SomeSuperEllipsisRangeConcat
            (SuperRange.ConcatenatedSuperEllipsisInsertion _ value insertion) -> do
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
      case SuperRange.mergeSuperEllipsisRanges first second of
        SuperRange.SomeSuperEllipsisRangeConcat
            (SuperRange.ConcatenatedSuperEllipsisInsertion _ _ insertion) ->
          assert "adjacent ranges retain subtype capability"
            (all
              (\rankValue ->
                case superEllipsisInsertionPreimage insertion (rankOneTerminal rankValue) of
                  Just _ -> True
                  Nothing -> False)
              [2 .. 6])
        SuperRange.SomeSuperEllipsisRangeConcat (SuperRange.ConcatenatedSuperEllipsisMap _ _) ->
          fail "adjacent non-overlapping ranges produced only a map"
  withRankOneRange 10 (Just 12) $ \first ->
    withRankOneRange 2 (Just 4) $ \second ->
      case SuperRange.mergeSuperEllipsisRanges first second of
        SuperRange.SomeSuperEllipsisRangeConcat (SuperRange.ConcatenatedSuperEllipsisMap _ _) ->
          fail "reverse disjoint ranges produced only a map"
        SuperRange.SomeSuperEllipsisRangeConcat
            (SuperRange.ConcatenatedSuperEllipsisInsertion _ value insertion) -> do
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
      case SuperRange.mergeSuperEllipsisRanges first second of
        SuperRange.SomeSuperEllipsisRangeConcat
            (SuperRange.ConcatenatedSuperEllipsisInsertion _ _ _) ->
          fail "overlapping ranges produced an Ellipsis insertion"
        SuperRange.SomeSuperEllipsisRangeConcat (SuperRange.ConcatenatedSuperEllipsisMap _ value) ->
          withConcatOrderedTransposal value $ \_ concatAtlas _ ->
            assert "overlapping ranges retain their ordered concat map"
              (atlasPageHasExactly concatAtlas 1 6)
  withRankOneRange 3 Nothing $ \first ->
    withRankOneRange 5 Nothing $ \second ->
      case SuperRange.concatSuperEllipsisRanges first second of
        SuperRange.SomeSuperEllipsisRangeConcat
            (SuperRange.ConcatenatedSuperEllipsisInsertion _ _ _) ->
          fail "overlapping unbounded ranges produced an Ellipsis insertion"
        SuperRange.SomeSuperEllipsisRangeConcat (SuperRange.ConcatenatedSuperEllipsisMap _ value) ->
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
  withRankOneRange 3 Nothing $ \first ->
    withRankOneRange 2 (Just 20) $ \second -> do
      case first <.> second of
        SuperRange.SomeSuperEllipsisRangeConcat
            (SuperRange.ConcatenatedSuperEllipsisInsertion _ _ _) ->
          fail "overlapping omega-plus-finite ranges produced an insertion"
        SuperRange.SomeSuperEllipsisRangeConcat (SuperRange.ConcatenatedSuperEllipsisMap _ value) ->
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
        SuperRange.SomeSuperEllipsisRangeConcat
            (SuperRange.ConcatenatedSuperEllipsisInsertion _ _ _) ->
          fail "overlapping finite-plus-omega ranges produced an insertion"
        SuperRange.SomeSuperEllipsisRangeConcat (SuperRange.ConcatenatedSuperEllipsisMap _ value) ->
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
  withRankOneRange 4 (Just 1) $ \descending ->
    withRankOneRange 3 (Just 6) $ \ascending ->
      case descending <.> ascending of
        SuperRange.SomeSuperEllipsisRangeConcat
            (SuperRange.ConcatenatedSuperEllipsisInsertion _ _ _) ->
          fail "overlapping descending and ascending ranges produced an insertion"
        SuperRange.SomeSuperEllipsisRangeConcat (SuperRange.ConcatenatedSuperEllipsisMap _ value) ->
          withConcatOrderedTransposal value $ \_ concatAtlas _ ->
            assert "descending ranges retain their order in overlapping maps"
              (atlasPageHasExactly concatAtlas 1 6)

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
      (rankOneRangeLowerBound natural == Just 3
        && rankOneRangeUpperBound natural == Just 4)
    assert "rankOneData natural includes exactly its value"
      (includedRanks == [Nothing, Just 3, Nothing])
    of
      Nothing -> fail "rankOneData natural was rejected"
      Just checks -> checks

testNumericalOperators :: IO ()
testNumericalOperators = do
  assertNumericalOperator "rankOneData-natural addition" (Numeric.+) 2 3 5
  assertNumericalOperator "rankOneData-natural multiplication" (Numeric.*) 4 5 20
  assertNumericalOperator "rankOneData-natural exponentiation" (Numeric.^) 2 10 1024
  assertNumericalOperator "rankOneData-natural zero exponent" (Numeric.^) 7 0 1
  assertNumericalOperator "rankOneData-natural zero-to-zero power" (Numeric.^) 0 0 1
  testGenericOrdinalOperators
  testStableDatumNumericalOperands

testGenericOrdinalOperators :: IO ()
testGenericOrdinalOperators = do
  let rankThree =
        nextSuperEllipsisRank (nextSuperEllipsisRank rankOneRank)
      omegaPlusOne = addOrdinals omega (finiteOrdinal 1)
      operatorResults =
        superEllipsisValue rankThree omegaPlusOne $ \left ->
          superEllipsisValue rankThree omega $ \right ->
            DatraNatural.ellipsisNatural 2 $ \two ->
              ( join ((Numeric.+) left right superEllipsisValueOrdinal)
              , join ((Numeric.+) right left superEllipsisValueOrdinal)
              , join ((Numeric.*) left right superEllipsisValueOrdinal)
              , join ((Numeric.*) right left superEllipsisValueOrdinal)
              , join ((Numeric.^) left two superEllipsisValueOrdinal)
              )
  case operatorResults of
    Just (Just (Just actual)) ->
      assert "higher-rank numerical operators use ordered ordinal arithmetic"
        ( actual
          == ( Just (ordinal [2, 0])
             , Just (ordinal [2, 1])
             , Just (ordinal [1, 0, 0])
             , Just (ordinal [1, 1, 0])
             , Just (ordinal [1, 1, 1])
             )
        )
    _ -> fail "higher-rank ordinal operator setup was rejected"

testStableDatumNumericalOperands :: IO ()
testStableDatumNumericalOperands = do
  let levelTwoData :: StableConfederalData (SuperEllipsis Ellipsis)
      levelTwoData = superEllipsis rankOneData
      omegaSquared = ordinal [1, 0, 0]
      isEllipsisFormulation
        :: StableConfederalData Ellipsis -> Bool
      isEllipsisFormulation value = value `seq` True
      isLevelTwoFormulation
        :: StableConfederalData (SuperEllipsis Ellipsis) -> Bool
      isLevelTwoFormulation value = value `seq` True
      binaryResults =
        ( join ((Numeric.+) dot dot superEllipsisValueOrdinal)
        , join ((Numeric.+) dot rankOneData superEllipsisValueOrdinal)
        , join ((Numeric.+) rankOneData dot superEllipsisValueOrdinal)
        , (Numeric.*) dot rankOneData isEllipsisFormulation
        , (Numeric.*) rankOneData dot isEllipsisFormulation
        , (Numeric.*) rankOneData rankOneData
            isLevelTwoFormulation
        , join ((Numeric.+) rankOneData levelTwoData
            superEllipsisValueOrdinal)
        , join ((Numeric.+) levelTwoData rankOneData
            superEllipsisValueOrdinal)
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
      join ((Numeric.+) rankOneData zero superEllipsisValueOrdinal) of
    Just (Just result) ->
      assert "adding zero soft-casts a formulation to an explicit value"
        (result == omega)
    _ -> fail "formulation soft cast was rejected"
  case DatraNatural.ellipsisNatural 3 $ \three ->
      (Numeric.^) dot three Numeric.someSuperEllipsisLevel of
    Just (Just result) ->
      assert "Dot exponentiation returns Dot"
        (result == 0)
    _ -> fail "Dot exponentiation was rejected"
  case DatraNatural.ellipsisNatural 2 $ \two ->
      (Numeric.^) rankOneData two Numeric.someSuperEllipsisLevel of
    Just (Just result) ->
      assert "Ellipsis squared returns the level-two formulation"
        (result == 2)
    _ -> fail "Ellipsis squared was rejected"
  case DatraNatural.ellipsisNatural 0 $ \zero ->
      (Numeric.^) rankOneData zero Numeric.someSuperEllipsisLevel of
    Just (Just result) ->
      assert "Ellipsis to zero returns Dot"
        (result == 0)
    _ -> fail "Ellipsis to zero was rejected"
  let rankThree =
        nextSuperEllipsisRank (nextSuperEllipsisRank rankOneRank)
      explicitOmegaSquared =
        superEllipsisValue rankThree omega $ \omegaValue ->
          DatraNatural.ellipsisNatural 2 $ \two ->
            join ((Numeric.^) omegaValue two superEllipsisValueOrdinal)
  case explicitOmegaSquared of
    Just (Just (Just result)) ->
      assert "an explicit omega base returns an explicit omega-squared value"
        (result == omegaSquared)
    _ -> fail "explicit omega exponentiation was rejected"

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
        rankOneRangeLowerBound result == Just expected
          && rankOneRangeUpperBound result == Just (expected + 1)
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
