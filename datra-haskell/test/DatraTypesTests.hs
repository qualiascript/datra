{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}

module Main (main) where

import AsciiDominion
import CanonicalCharsDominion
import DomanialInsertion
import Dominion
import Ellipsis
import EllipsisInsertion
import EllipsisNatural
import EllipsisRange
import FiniteDominion
import Numeric.Natural (Natural)

import Data.Maybe (isNothing)
import qualified Data.Set as Set

main :: IO ()
main = do
  testAsciiDominion
  testCanonicalCharsDominion
  testEllipsis
  testEllipsisInsertion
  testEllipsisInsertionDominion
  testEllipsisRange
  testEllipsisRangeMerge
  testEllipsisNatural
  testFiniteDominion

assert :: String -> Bool -> IO ()
assert label condition
  | condition = pure ()
  | otherwise = fail ("test failed: " <> label)

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

withEllipsisRange
  :: Maybe Natural
  -> Maybe Natural
  -> (forall scope. EllipsisRange scope -> IO ())
  -> IO ()
withEllipsisRange lower upper useRange =
  case ellipsisRange lower upper useRange of
    Nothing -> fail "test setup failed: valid ellipsis range was rejected"
    Just checks -> checks

testEllipsis :: IO ()
testEllipsis = do
  let ranks :: [Natural]
      ranks = [0, 1, 2, 1000000]
      terminals = map Terminal ranks
  assert "ellipsis contains a terminal at every natural rank"
    (map (fmap terminalRank . unrank ellipsis) ranks == map Just ranks)
  assert "ellipsis ranks and unranks every terminal"
    (all
      (\terminal -> unrank ellipsis (rank ellipsis terminal) == Just terminal)
      terminals)

testEllipsisInsertion :: IO ()
testEllipsisInsertion = do
  let insertion :: EllipsisInsertion Ellipsis
      insertion = ellipsisInsertion id Just (const ())
      terminals = map Terminal [0, 1, 1000000]
  assert "ellipsis insertion specializes a domanial insertion into ellipsis"
    (all
      (\terminal ->
        preimage insertion (applyInsertion insertion terminal)
          == Just terminal)
      terminals)

testEllipsisInsertionDominion :: IO ()
testEllipsisInsertionDominion =
  asciiDominion $ \ascii ->
    withEllipsisRange (Just 65) (Just 68) $ \valueRange -> do
      let selected = ellipsisInsertionDominion
            (finiteAsDominion ascii)
            (ellipsisRangeInsertion valueRange)
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

testEllipsisRange :: IO ()
testEllipsisRange = do
  case ellipsisRange (Just 0) Nothing $ \valueRange ->
    map
      (fmap ellipsisRangeElementRank . ellipsisRangeElement valueRange)
      [0, 1]
    of
      Nothing -> fail "zero lower bound was rejected"
      Just actual ->
        assert "zero is a valid lower bound"
          (actual == [Just 0, Just 1])
  assert "ellipsis range rejects an empty implicit-lower range"
    (case ellipsisRange Nothing (Just 0) (const ()) of
      Nothing -> True
      Just () -> False)
  assert "ellipsis range rejects an empty zero-bounded range"
    (case ellipsisRange (Just 0) (Just 0) (const ()) of
      Nothing -> True
      Just () -> False)
  assert "ellipsis range rejects equal bounds"
    (case ellipsisRange (Just 3) (Just 3) (const ()) of
      Nothing -> True
      Just () -> False)
  assert "ellipsis range rejects descending bounds"
    (case ellipsisRange (Just 5) (Just 2) (const ()) of
      Nothing -> True
      Just () -> False)
  case ellipsisRange (Just 2) (Just 5) $ \valueRange -> do
    let insertion = ellipsisRangeInsertion valueRange
        expected = [Nothing, Nothing, Just 2, Just 3, Just 4, Nothing]
        actual = map
          (fmap ellipsisRangeElementRank
            . preimage insertion . Terminal)
          [0 .. 5]
    assert "bounded ellipsis range is lower-inclusive and upper-exclusive"
      (actual == expected)
    assert "ellipsis range insertion satisfies its left-inverse law"
      (all
        (\rankValue ->
          case ellipsisRangeElement valueRange rankValue of
            Nothing -> False
            Just element ->
              preimage insertion (applyInsertion insertion element)
                == Just element)
        [2 .. 4])
    of
      Nothing -> fail "valid bounded ellipsis range was rejected"
      Just checks -> checks
  case ellipsisRange Nothing (Just 5) $ \valueRange ->
    map
      (fmap ellipsisRangeElementRank . ellipsisRangeElement valueRange)
      [0 .. 5]
    of
      Nothing -> fail "valid upper-bounded ellipsis range was rejected"
      Just actual ->
        assert "missing lower bound includes all lower terminals"
          (actual == [Just 0, Just 1, Just 2, Just 3, Just 4, Nothing])
  case ellipsisRange (Just 2) Nothing $ \valueRange ->
    map
      (fmap ellipsisRangeElementRank . ellipsisRangeElement valueRange)
      [1, 2, 1000000]
    of
      Nothing -> fail "valid lower-bounded ellipsis range was rejected"
      Just actual ->
        assert "missing upper bound includes every later terminal"
          (actual == [Nothing, Just 2, Just 1000000])
  case ellipsisRange Nothing Nothing $ \valueRange ->
    map
      (fmap ellipsisRangeElementRank . ellipsisRangeElement valueRange)
      [0, 1, 1000000]
    of
      Nothing -> fail "unbounded ellipsis range was rejected"
      Just actual ->
        assert "missing bounds include all terminals"
          (actual == [Just 0, Just 1, Just 1000000])

testEllipsisRangeMerge :: IO ()
testEllipsisRangeMerge = do
  withEllipsisRange (Just 2) (Just 4) $ \first ->
    withEllipsisRange (Just 10) (Just 12) $ \second ->
      case nonOverlappingEllipsisRanges first second of
        Nothing -> fail "disjoint ranges were reported as overlapping"
        Just disjoint ->
          case mergeEllipsisRanges disjoint of
            SomeEllipsisRangeMerge (MergedEllipsisRange _) ->
              fail "ranges separated by a gap produced a range"
            SomeEllipsisRangeMerge (MergedEllipsisInsertion insertion) -> do
              let includedRanks = map
                    (fmap (either ellipsisRangeElementRank
                                  ellipsisRangeElementRank)
                      . preimage insertion . Terminal)
                    [1, 2, 3, 4, 9, 10, 11, 12]
              assert "merge insertion includes exactly both disjoint ranges"
                (includedRanks
                  == [ Nothing, Just 2, Just 3, Nothing
                     , Nothing, Just 10, Just 11, Nothing
                     ])
  withEllipsisRange (Just 2) (Just 4) $ \first ->
    withEllipsisRange (Just 4) (Just 7) $ \second ->
      case nonOverlappingEllipsisRanges first second of
        Nothing -> fail "adjacent ranges were reported as overlapping"
        Just adjacent ->
          case mergeEllipsisRanges adjacent of
            SomeEllipsisRangeMerge (MergedEllipsisInsertion _) ->
              fail "adjacent ranges did not produce a range"
            SomeEllipsisRangeMerge result@(MergedEllipsisRange _) ->
              withMergedEllipsisRange result $ \combined ->
                assert "adjacent range merge spans both inputs"
                  (ellipsisRangeLowerBound combined == Just 2
                    && ellipsisRangeUpperBound combined == Just 7)
  withEllipsisRange (Just 10) (Just 12) $ \first ->
    withEllipsisRange (Just 2) (Just 4) $ \second ->
      case nonOverlappingEllipsisRanges first second of
        Nothing -> fail "reverse disjoint ranges were reported as overlapping"
        Just disjoint ->
          case mergeEllipsisRanges disjoint of
            SomeEllipsisRangeMerge (MergedEllipsisRange _) ->
              fail "reverse ranges separated by a gap produced a range"
            SomeEllipsisRangeMerge (MergedEllipsisInsertion insertion) ->
              assert "reverse merge preserves both original range branches"
                (map
                  (fmap (either ellipsisRangeElementRank
                                ellipsisRangeElementRank)
                    . preimage insertion . Terminal)
                  [2, 3, 10, 11]
                  == map Just [2, 3, 10, 11])
  withEllipsisRange (Just 4) (Just 7) $ \first ->
    withEllipsisRange (Just 2) (Just 4) $ \second ->
      case nonOverlappingEllipsisRanges first second of
        Nothing -> fail "reverse adjacent ranges were reported as overlapping"
        Just adjacent ->
          case mergeEllipsisRanges adjacent of
            SomeEllipsisRangeMerge (MergedEllipsisInsertion _) ->
              fail "reverse adjacent ranges did not produce a range"
            SomeEllipsisRangeMerge result@(MergedEllipsisRange _) ->
              withMergedEllipsisRange result $ \combined ->
                assert "reverse adjacent merge orders and spans both inputs"
                  (ellipsisRangeLowerBound combined == Just 2
                    && ellipsisRangeUpperBound combined == Just 7)
  withEllipsisRange (Just 2) (Just 5) $ \first ->
    withEllipsisRange (Just 4) (Just 7) $ \second ->
      assert "overlapping ranges cannot produce non-overlap evidence"
        (case nonOverlappingEllipsisRanges first second of
          Nothing -> True
          Just _ -> False)

testEllipsisNatural :: IO ()
testEllipsisNatural = do
  case ellipsisNatural 0 $ \natural ->
    map
      (fmap ellipsisRangeElementRank
        . preimage (ellipsisNaturalInsertion natural) . Terminal)
      [0, 1]
    of
      Nothing -> fail "zero ellipsis natural was rejected"
      Just includedRanks ->
        assert "zero ellipsis natural includes exactly zero"
          (includedRanks == [Just 0, Nothing])
  case ellipsisNatural 3 $ \natural -> do
    let insertion = ellipsisNaturalInsertion natural
        includedRanks = map
          (fmap ellipsisRangeElementRank
            . preimage insertion . Terminal)
          [2, 3, 4]
    assert "ellipsis natural uses consecutive range bounds"
      (ellipsisRangeLowerBound natural == Just 3
        && ellipsisRangeUpperBound natural == Just 4)
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
