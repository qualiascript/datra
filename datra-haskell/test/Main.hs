module Main (main) where

import Chains
import DatraOrdinal
import DomanialInsertion
import Dominion
import Numeric.Natural (Natural)

import qualified Data.Set as Set

main :: IO ()
main = do
  testFiniteDominion
  testIdentityInsertion
  testSpine
  testChainSum

checkedIdentity :: DomanialInsertion Bool Bool
checkedIdentity = domanialInsertion (\value -> value) Just (\_ -> ())

assert :: String -> Bool -> IO ()
assert label condition
  | condition = pure ()
  | otherwise = fail ("test failed: " <> label)

testFiniteDominion :: IO ()
testFiniteDominion = do
  let values = Set.fromList ['a', 'b', 'c']
      valueDominion = finiteSetDominion values
  assert "finite dominion ranks its carrier"
    (map (rank valueDominion) ['a', 'b', 'c']
      == map Just [0, 1, 2])
  assert "finite dominion unrank is inverse"
    (map (unrank valueDominion) [0, 1, 2, 3]
      == [Just 'a', Just 'b', Just 'c', Nothing])

testIdentityInsertion :: IO ()
testIdentityInsertion = do
  let insertion = identityInsertion :: DomanialInsertion Natural Natural
  assert "identity insertion applies forward"
    (map (applyInsertion insertion) [0, 1, 2] == [0, 1, 2])
  assert "identity insertion computes preimages"
    (map (preimage insertion) [0, 1, 2]
      == map Just [0, 1, 2])
  assert "checked smart constructor applies forward"
    (applyInsertion checkedIdentity True)

testSpine :: IO ()
testSpine = do
  let values = [0 .. 8]
  assert "spine positions are below omega"
    (all (\value -> ordinalLT (chainPosition spine value) omega) values)
  assert "spine lookup inverts positions"
    (all
      (\value ->
        chainObjectAt spine (chainPosition spine value) == Just value)
      values)

testChainSum :: IO ()
testChainSum = do
  let doubledSpine = sumChains spine spine
      leftValues = map Left [0 .. 4]
      rightValues = map Right [0 .. 4]
      roundTrips value =
        chainObjectAt doubledSpine (chainPosition doubledSpine value)
          == Just value
  assert "ordinal sum lookup inverts both summands"
    (all roundTrips (leftValues <> rightValues))
