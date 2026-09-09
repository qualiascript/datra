module Main (main) where

import Chain
import Consolidation
import ConsolidationTransport
import DatraOrdinal
import DomanialInsertion
import Dominion
import FiniteDominion
import Folio
import Numeric.Natural (Natural)

import Data.Maybe (isNothing)
import qualified Data.Set as Set

main :: IO ()
main = do
  testFiniteDominion
  testIdentityInsertion
  testSpine
  testChainSum
  testConsolidation
  testConsolidationSum
  testConsolidationTransport
  testFolio

checkedIdentity :: DomanialInsertion Bool Bool
checkedIdentity = domanialInsertion id Just (const ())

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
  assert "coconsolidation composition follows opposite categorical order"
    (map
      (applyConsolidation
        (Consolidation.unop
          (Consolidation.composeCoconsolidations
            (Consolidation.op halve)
            (Consolidation.op halve))))
      values
      == map (applyConsolidation doubledHalve) values)

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

unitChain :: Chain ()
unitChain =
  chain
    (finiteOrdinal 1)
    (const (finiteOrdinal 0))
    (\position ->
      if position == finiteOrdinal 0 then Just () else Nothing)
    (const ())
    (\_ _ -> ())
    (const ())

boolChain :: Chain Bool
boolChain =
  chain
    (finiteOrdinal 2)
    (\value -> finiteOrdinal (if value then 1 else 0))
    (\position ->
      if position == finiteOrdinal 0
        then Just False
        else if position == finiteOrdinal 1 then Just True else Nothing)
    (const ())
    (\_ _ -> ())
    (const ())

collapseBool :: Consolidation Bool ()
collapseBool =
  consolidation
    (const ())
    (const False)
    (\_ _ _ -> ())
    (const ())

nonzero :: Consolidation Natural Bool
nonzero =
  consolidation
    (> 0)
    (\value -> if value then 1 else 0)
    (\_ _ right -> right > 0)
    (const ())

threePageFolio :: Folio () Natural
threePageFolio =
  appendPage
    (appendPage
      (singletonFolio unitChain)
      boolChain
      (Consolidation.op collapseBool))
    spine
    (Consolidation.op nonzero)

testConsolidationTransport :: IO ()
testConsolidationTransport = do
  let values = [0 .. 8]
      transported = runConsolidationTransport (consolidationTransport halve)
      transportedTwice =
        runConsolidationTransport
          (consolidationTransport (composeConsolidations halve halve))
      identity =
        runConsolidationTransport
          (consolidationTransport
            (identityConsolidation :: Consolidation Natural Natural))
  consolidationTransportIdentity (0 :: Natural) `seq`
    consolidationTransportComposition halve halve 7 `seq` pure ()
  assert "consolidation transport exposes a consolidation's carrier map"
    (map transported values == map (applyConsolidation halve) values)
  assert "consolidation transport preserves identity"
    (map identity values == values)
  assert "consolidation transport preserves composition"
    (map transportedTwice values
      == map (transported . transported) values)

testFolio :: IO ()
testFolio = do
  originUnique threePageFolio () `seq`
    folioMapIdentity False `seq`
      folioMapComposition
        (Consolidation.op nonzero)
        (Consolidation.op collapseBool)
        7 `seq` pure ()
  assert "folio counts its genuine pages"
    (folioLength threePageFolio == 3)
  assert "folio padded indices repeat the final page"
    (map (paddedIndex threePageFolio) [0, 1, 2, 3, 100]
      == [0, 1, 2, 2, 2])
  assert "folio retrieves each heterogeneous page"
    (withPageAt threePageFolio 1 chainOrderType
      == Just (finiteOrdinal 2))
  assert "folio rejects an index outside its finite core"
    (isNothing (withPageAt threePageFolio 3 (const True)))
  assert "folio's padded presentation repeats its final chain"
    (withPaddedPage threePageFolio 100 chainOrderType == omega)
  assert "folio composes adjacent maps coherently"
    (withFolioMap threePageFolio 1 2
      (\sourcePage targetPage pageMap -> do
        value <- chainObjectAt targetPage (finiteOrdinal 2)
        let transported =
              runConsolidationTransport (transportCoconsolidation pageMap) value
        pure (chainPosition sourcePage transported == finiteOrdinal 1))
      == Just (Just True))
  assert "folio transports from a later page to its origin"
    (withFolioMap threePageFolio 0 2
      (\sourcePage targetPage pageMap -> do
        value <- chainObjectAt targetPage (finiteOrdinal 5)
        let transported =
              runConsolidationTransport (transportCoconsolidation pageMap) value
        pure (chainPosition sourcePage transported == finiteOrdinal 0))
      == Just (Just True))
  assert "folio pads maps along the full spine"
    (withPaddedFolioMap threePageFolio 1 100
      (\sourcePage targetPage pageMap -> do
        value <- chainObjectAt targetPage (finiteOrdinal 8)
        let transported =
              runConsolidationTransport (transportCoconsolidation pageMap) value
        pure (chainPosition sourcePage transported == finiteOrdinal 1))
      == Just (Just True))
  assert "folio has no map against the spine order"
    (isNothing (withFolioMap threePageFolio 2 1 (\_ _ _ -> True)))
