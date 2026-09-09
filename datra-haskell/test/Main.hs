module Main (main) where

import Chains
import Consolidation
import DatraOrdinal
import DomanialInsertion
import Dominion
import FiniteDominion
import Numeric.Natural (Natural)

import qualified Data.Set as Set

main :: IO ()
main = do
  testFiniteDominion
  testIdentityInsertion
  testSpine
  testChainSum
  testConsolidation
  testConsolidationSum

checkedIdentity :: DomanialInsertion Bool Bool
checkedIdentity = domanialInsertion (\value -> value) Just (\_ -> ())

assert :: String -> Bool -> IO ()
assert label condition
  | condition = pure ()
  | otherwise = fail ("test failed: " <> label)

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
          (finiteMember finite 'z' == Nothing)
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
  assert "ordinal construction removes leading zero coefficients"
    (ordinal [0, 0, 1, 2] == ordinal [1, 2])

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

halve :: Consolidation Natural Natural
halve =
  consolidation
    (`div` 2)
    (* 2)
    (\_ _ right -> right `div` 2)
    (const ())

testConsolidation :: IO ()
testConsolidation = do
  let values = [0 .. 8]
      doubledHalve = composeConsolidations halve halve
      identity = identityConsolidation :: Consolidation Natural Natural
  assert "consolidation applies its object map"
    (map (applyConsolidation halve) values
      == [0, 0, 1, 1, 2, 2, 3, 3, 4])
  assert "consolidation object map is monotone on the spine"
    (all
      (\(left, right) ->
        not (hasArrow spine left right)
          || hasArrow spine
            (applyConsolidation halve left)
            (applyConsolidation halve right))
      [(left, right) | left <- values, right <- values])
  assert "consolidation chosen preimages witness point-surjectivity"
    (all
      (\value ->
        applyConsolidation halve (consolidationPreimage halve value)
          == value)
      values)
  assert "consolidation composition follows categorical order"
    (map (applyConsolidation doubledHalve) values
      == [0, 0, 0, 0, 1, 1, 1, 1, 2])
  assert "identity consolidation preserves objects"
    (map (applyConsolidation identity) values == values)
  assert "coconsolidation retains the underlying map"
    (map
      (applyConsolidation (Consolidation.unop (Consolidation.op halve)))
      values
      == map (applyConsolidation halve) values)

testConsolidationSum :: IO ()
testConsolidationSum = do
  let summed = sumConsolidations halve halve
      targets = map Left [0 .. 4] <> map Right [0 .. 4]
  assert "sum consolidation maps within each summand"
    (map (applyConsolidation summed)
      [Left 3, Left 4, Right 5, Right 6]
      == [Left 1, Left 2, Right 2, Right 3])
  assert "sum consolidation is point-surjective in both summands"
    (all
      (\value ->
        applyConsolidation summed (consolidationPreimage summed value)
          == value)
      targets)
