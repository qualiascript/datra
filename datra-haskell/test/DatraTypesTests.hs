module Main (main) where

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
  testEllipsis
  testEllipsisInsertion
  testEllipsisRange
  testEllipsisNatural
  testFiniteDominion

assert :: String -> Bool -> IO ()
assert label condition
  | condition = pure ()
  | otherwise = fail ("test failed: " <> label)

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
