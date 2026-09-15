{-# LANGUAGE QualifiedDo #-}
{-# LANGUAGE TypeFamilies #-}

module Main (main) where

import Atlas
import AtlasExtent
import AtlasConfederation
import AtlasFederation
import AtlasHorizontalSum
import EmptyAtlas
import AtlasCoveredPageElement
import AtlasMap
import AtlasMerge
import AtlasTransposal
import AtlasTransversal
import AtlasTransversalMap
import AtlasTerritory
import Chain
import Charter
import Coalition
import Consolidation
import qualified Control.Category as Category
import DataTransformation
import DataTransformationMap
import DataTransposal
import DataTransversal
import DatraOrdinal
import DomanialInclusion
import DomanialInsertion
import Dominion
import Expedition
import FiniteDominion
import Folio
import HorizontalSum
import Navigation
import PageElements
import Pagination
import Numeric.Natural (Natural)
import OrderedAtlasTransposal
import OrderedDataTransposal
import StableAtlasTransversal
import StableConfederalDataTransversal
import StableConfederalDataTransversalKleisli
import qualified StableConfederalDataTransversalKleisli.Syntax as Kleisli
import StableConfederalDataTransversalMonoidal
import StableDataTransversal

import Data.Maybe (isJust, isNothing)
import qualified Data.Set as Set
import Data.Void (Void, absurd)

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
  testPageElements
  testPagination
  testAtlas
  testEmptyAtlas
  testAtlasMerge
  testAtlasConfederation
  testAtlasFederation
  testAtlasMap
  testNavigationAndExpedition
  testDataTransformationMap
  testRestrictedDataTransformations
  testStableConfederalKleisliSyntax
  testCharter
  testOrderedAtlasTransposal
  testAtlasTransversal
  testStableAtlasTransversal
  testCoalition
  testDomanialInclusion

checkedIdentity :: DomanialInsertion Bool Bool
checkedIdentity = domanialInsertion id Just (const ())

assert :: String -> Bool -> IO ()
assert label condition
  | condition = pure ()
  | otherwise = fail ("test failed: " <> label)

testEmptyAtlas :: IO ()
testEmptyAtlas =
  emptyAtlas $ \valueAtlas ->
    assert "the empty Atlas has one empty page"
      (atlasCardinality valueAtlas == 1)

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
        chainObjectAt (chainIndexOf spine value) == value)
      values)
  assert "spine rejects an index at its order type"
    (isNothing (chainIndex spine omega))
  assert "ordinal construction removes leading zero coefficients"
    (ordinal [0, 0, 1, 2] == ordinal [1, 2])

testChainSum :: IO ()
testChainSum = do
  let doubledSpine = sumChains spine spine
      leftValues = map Left [0 .. 4]
      rightValues = map Right [0 .. 4]
      roundTrips value =
        chainObjectAt (chainIndexOf doubledSpine value)
          == value
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
testFolio =
  case (pageOrder 1 2, pageOrder 0 2, pageOrder 1 100) of
    (Just oneToTwo, Just zeroToTwo, Just oneToHundred) -> do
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
          == finiteOrdinal 2)
      assert "folio page lookup pads beyond its finite presentation"
        (withPageAt threePageFolio 100 chainOrderType == omega)
      assert "folio map order retains its certified endpoints"
        ( pageOrderSource oneToTwo == 1
          && pageOrderTarget oneToTwo == 2
        )
      assert "folio composes adjacent maps coherently"
        (withFolioMap threePageFolio oneToTwo
          (\sourcePage targetPage pageMap -> do
            index <- chainIndex targetPage (finiteOrdinal 2)
            let value = chainObjectAt index
            let transported =
                  runConsolidationTransport
                    (transportCoconsolidation pageMap)
                    value
            pure (chainPosition sourcePage transported == finiteOrdinal 1))
          == Just True)
      assert "folio transports from a later page to its origin"
        (withFolioMap threePageFolio zeroToTwo
          (\sourcePage targetPage pageMap -> do
            index <- chainIndex targetPage (finiteOrdinal 5)
            let value = chainObjectAt index
            let transported =
                  runConsolidationTransport
                    (transportCoconsolidation pageMap)
                    value
            pure (chainPosition sourcePage transported == finiteOrdinal 0))
          == Just True)
      assert "folio pads maps along the full spine"
        (withFolioMap threePageFolio oneToHundred
          (\sourcePage targetPage pageMap -> do
            index <- chainIndex targetPage (finiteOrdinal 8)
            let value = chainObjectAt index
            let transported =
                  runConsolidationTransport
                    (transportCoconsolidation pageMap)
                    value
            pure (chainPosition sourcePage transported == finiteOrdinal 1))
          == Just True)
      assert "folio rejects an interval against the spine order"
        (isNothing (pageOrder 2 1))
    _ -> fail "test setup failed: valid page order was rejected"

testPageElements :: IO ()
testPageElements =
  pageElements threePageFolio $ \elements ->
    let at page position =
          pageElement
            <$> pageElementIndex elements page (finiteOrdinal position)
    in case (at 0 0, at 1 0, at 1 1, at 2 5, at 100 5) of
      ( Just someOrigin
        , Just someFalseCell
        , Just someTrueCell
        , Just someFive
        , Just somePaddedFive
        ) ->
        withPageElement someOrigin $ \origin ->
          withPageElement someFalseCell $ \falseCell ->
            withPageElement someTrueCell $ \trueCell ->
              withPageElement someFive $ \five ->
                withPageElement somePaddedFive $ \paddedFive -> do
                  assert "cell occurrence rejects a position outside its page"
                    (isNothing (at 1 2))
                  assert "cell occurrence exposes its page and position"
                    ( pageElementPage five == 2
                      && pageElementPosition five == finiteOrdinal 5
                    )
                  assert "cell occurrence eliminates its hidden carrier safely"
                    (withPageElementValue trueCell
                      chainPosition
                      == finiteOrdinal 1)
                  assert "page element traces encode exact folio transport"
                    ( pageElementTransported five trueCell
                      && not (pageElementTransported five falseCell)
                      && pageElementTransported trueCell origin
                    )
                  assert "page elements retain their infinite-spine page"
                    ( pageElementPage paddedFive == 100
                      && pageElementPosition paddedFive == finiteOrdinal 5
                      && pageElementTransported paddedFive five
                    )
                  let fiveToTrue = pageElementArrow five trueCell
                      trueToOrigin = pageElementArrow trueCell origin
                      fiveToOrigin =
                        composePageElementArrows trueToOrigin fiveToTrue
                      directFiveToOrigin = pageElementArrow five origin
                  pageElementArrowEndpoints five trueCell `seq`
                    pageElementArrowThin fiveToOrigin directFiveToOrigin `seq`
                      pageElementArrowLeftIdentity fiveToTrue `seq`
                        pageElementArrowRightIdentity fiveToTrue `seq`
                          pageElementArrowAssociativity
                            (identityPageElementArrow origin)
                            trueToOrigin
                            fiveToTrue `seq` pure ()
                  assert "page element arrows retain their typed endpoints"
                    ( arrowSource fiveToTrue == five
                      && arrowTarget fiveToTrue == trueCell
                    )
                  assert "page element identities retain their object"
                    ( arrowSource (identityPageElementArrow five) == five
                      && arrowTarget (identityPageElementArrow five) == five
                    )
                  assert
                    "page element arrows compose totally through a typed boundary"
                    (fiveToOrigin == directFiveToOrigin)
      _ -> fail "test setup failed: expected cell occurrences"

testPagination :: IO ()
testPagination =
  pagination threePageFolio $ \sourcePagination ->
    pagination threePageFolio $ \targetPagination ->
      let sourceElements = paginationPageElements sourcePagination
          targetElements = paginationPageElements targetPagination
      in case
        ( pageElement <$> pageElementIndex sourceElements 2 (finiteOrdinal 5)
        , pageElement <$> pageElementIndex sourceElements 1 (finiteOrdinal 1)
        , pageElement <$> pageElementIndex sourceElements 100 (finiteOrdinal 5)
        , pageElement <$> pageElementIndex targetElements 0 (finiteOrdinal 0)
        ) of
          ( Just someFive
            , Just someTrueCell
            , Just somePaddedFive
            , Just targetOrigin
            ) ->
            withPageElement someFive $ \five ->
              withPageElement someTrueCell $ \trueCell ->
                withPageElement somePaddedFive $ \paddedFive -> do
                assert "pagination retains its source folio"
                  (folioLength (paginationFolio sourcePagination) == 3)
                assert "pagination exposes its genuine cardinality"
                  (paginationCardinality sourcePagination == 3)
                let normalizedFive =
                      normalizePaginationElement sourcePagination paddedFive
                paginationCoherenceIdempotent
                  sourcePagination paddedFive `seq` pure ()
                assert "pagination normalization collapses padded pages"
                  ( pageElementPage normalizedFive == 2
                    && pageElementPosition normalizedFive == finiteOrdinal 5
                  )
                assert "pagination normalization fixes genuine pages"
                  ( normalizePaginationElement sourcePagination five == five
                  )
                assert "pagination normalization is idempotent"
                  ( normalizePaginationElement
                      sourcePagination normalizedFive == normalizedFive
                  )
                let paddedToFinal = pageElementArrow paddedFive five
                    normalizedArrow =
                      normalizePaginationArrow
                        sourcePagination paddedToFinal
                assert "pagination normalization preserves arrows"
                  ( pageElementPage (arrowSource normalizedArrow) == 2
                    && pageElementPage (arrowTarget normalizedArrow) == 2
                    && pageElementPosition (arrowSource normalizedArrow)
                      == finiteOrdinal 5
                    && pageElementPosition (arrowTarget normalizedArrow)
                      == finiteOrdinal 5
                  )
                withPageElement
                  (mapPaginationElement
                    (paginationCoherence sourcePagination)
                    paddedFive) $ \coherentFive -> do
                    assert "pagination coherence acts by normalization"
                      ( pageElementPage coherentFive == 2
                        && pageElementPosition coherentFive == finiteOrdinal 5
                      )
                    withPageElement
                      (mapPaginationElement
                        (paginationCoherence sourcePagination)
                        coherentFive) $ \coherentTwice ->
                          assert "pagination coherence is operationally idempotent"
                            ( pageElementPage coherentTwice
                                == pageElementPage coherentFive
                              && pageElementPosition coherentTwice
                                == pageElementPosition coherentFive
                            )
                withPageElementArrow
                  (mapPaginationArrow
                    (paginationCoherence sourcePagination)
                    paddedToFinal) $ \coherentArrow ->
                      assert "pagination coherence normalizes arrow endpoints"
                        ( pageElementPage (arrowSource coherentArrow) == 2
                          && pageElementPage (arrowTarget coherentArrow) == 2
                        )
                let constantMorphism =
                      paginationMorphism
                        (const targetOrigin)
                        (\_ _ ->
                          somePageElementTransportedReflexive targetOrigin)
                    sourceArrow = pageElementArrow five trueCell
                withPageElement
                  (mapPaginationElement constantMorphism five) $ \mapped ->
                    assert "pagination morphisms map page elements"
                      ( pageElementPage mapped == 0
                        && pageElementPosition mapped == finiteOrdinal 0
                      )
                withPageElementArrow
                  (mapPaginationArrow constantMorphism sourceArrow) $
                    \mappedArrow ->
                      assert
                        "pagination morphisms map arrows between mapped endpoints"
                        ( pageElementPage (arrowSource mappedArrow) == 0
                          && pageElementPage (arrowTarget mappedArrow) == 0
                        )
                withPageElement
                  (mapPaginationElement identityPaginationMorphism five) $
                    \mapped ->
                      assert "the identity pagination morphism fixes objects"
                        ( pageElementPage mapped == pageElementPage five
                          && pageElementPosition mapped == pageElementPosition five
                        )
                let composed =
                      composePaginationMorphisms
                        identityPaginationMorphism
                        constantMorphism
                withPageElement
                  (mapPaginationElement composed five) $ \mapped ->
                    assert "pagination morphisms compose in categorical order"
                      ( pageElementPage mapped == 0
                        && pageElementPosition mapped == finiteOrdinal 0
                      )
          _ -> fail "test setup failed: expected pagination elements"

newtype TestCellData object = TestCellData Natural
  deriving (Eq, Show)

newtype TestDataTransformationValue atlas =
  TestDataTransformationValue Natural
  deriving (Eq, Show)

data TestDataTransformationValues

type instance
  DataTransformationValue TestDataTransformationValues atlas =
    TestDataTransformationValue atlas

testDataTransformation
  :: DataTransformation TestDataTransformationValues
testDataTransformation =
  dataTransformation
    (\_ (TestDataTransformationValue value) ->
      TestDataTransformationValue value)
    (const ())
    (\_ _ _ -> ())

incrementDataTransformation
  :: DataTransformationHom
       TestDataTransformationValues
       TestDataTransformationValues
incrementDataTransformation =
  dataTransformationHom
    testDataTransformation
    testDataTransformation
    (\(TestDataTransformationValue value) ->
      TestDataTransformationValue (value + 1))
    (\_ _ -> ())

-- The initial presheaf has no navigations: evaluating a purported navigation
-- on the represented Atlas's identity would produce a 'Void'. Consequently
-- it satisfies Lean's IsDaTraMap property vacuously.
data EmptyDataTransformationValues

newtype EmptyDataTransformationValue atlas =
  EmptyDataTransformationValue Void

type instance
  DataTransformationValue EmptyDataTransformationValues atlas =
    EmptyDataTransformationValue atlas

emptyDataTransformation
  :: DataTransformation EmptyDataTransformationValues
emptyDataTransformation =
  dataTransformation
    (\_ (EmptyDataTransformationValue impossible) -> absurd impossible)
    (\(EmptyDataTransformationValue impossible) -> absurd impossible)
    (\_ _ (EmptyDataTransformationValue impossible) -> absurd impossible)

emptyDataTransformationMap
  :: DataTransformationMap EmptyDataTransformationValues
emptyDataTransformationMap =
  dataTransformationMap emptyDataTransformation $ \valueNavigation ->
    case mapNavigation valueNavigation (Yoneda Category.id) of
      EmptyDataTransformationValue impossible -> absurd impossible

newtype TestRestrictedDataValue atlas =
  TestRestrictedDataValue Natural
  deriving (Eq, Show)

data TestRestrictedDataValues

type instance
  DataTransposalValue TestRestrictedDataValues atlas =
    TestRestrictedDataValue atlas

type instance
  OrderedDataTransposalValue TestRestrictedDataValues atlas =
    TestRestrictedDataValue atlas

type instance
  DataTransversalValue TestRestrictedDataValues atlas =
    TestRestrictedDataValue atlas

type instance
  StableDataTransversalValue TestRestrictedDataValues atlas =
    TestRestrictedDataValue atlas

type instance
  StableConfederalDataTransversalValue
    TestRestrictedDataValues confederation =
      TestRestrictedDataValue confederation

testDataTransposal :: DataTransposal TestRestrictedDataValues
testDataTransposal =
  dataTransposal
    (\_ (TestRestrictedDataValue value) ->
      TestRestrictedDataValue value)
    (const ())
    (\_ _ _ -> ())

incrementDataTransposal
  :: DataTransposalHom TestRestrictedDataValues TestRestrictedDataValues
incrementDataTransposal =
  dataTransposalHom
    testDataTransposal
    testDataTransposal
    (\(TestRestrictedDataValue value) ->
      TestRestrictedDataValue (value + 1))
    (\_ _ -> ())

testOrderedDataTransposal
  :: OrderedDataTransposal TestRestrictedDataValues
testOrderedDataTransposal =
  orderedDataTransposal
    (\_ (TestRestrictedDataValue value) ->
      TestRestrictedDataValue value)
    (const ())
    (\_ _ _ -> ())

incrementOrderedDataTransposal
  :: OrderedDataTransposalHom
       TestRestrictedDataValues TestRestrictedDataValues
incrementOrderedDataTransposal =
  orderedDataTransposalHom
    testOrderedDataTransposal
    testOrderedDataTransposal
    (\(TestRestrictedDataValue value) ->
      TestRestrictedDataValue (value + 1))
    (\_ _ -> ())

testDataTransversal :: DataTransversal TestRestrictedDataValues
testDataTransversal =
  dataTransversal
    (\_ (TestRestrictedDataValue value) ->
      TestRestrictedDataValue value)
    (const ())
    (\_ _ _ -> ())

incrementDataTransversal
  :: DataTransversalHom TestRestrictedDataValues TestRestrictedDataValues
incrementDataTransversal =
  dataTransversalHom
    testDataTransversal
    testDataTransversal
    (\(TestRestrictedDataValue value) ->
      TestRestrictedDataValue (value + 1))
    (\_ _ -> ())

testStableDataTransversal
  :: StableDataTransversal TestRestrictedDataValues
testStableDataTransversal =
  stableDataTransversal
    (\_ (TestRestrictedDataValue value) ->
      TestRestrictedDataValue value)
    (const ())
    (\_ _ _ -> ())

incrementStableDataTransversal
  :: StableDataTransversalHom
       TestRestrictedDataValues TestRestrictedDataValues
incrementStableDataTransversal =
  stableDataTransversalHom
    testStableDataTransversal
    testStableDataTransversal
    (\(TestRestrictedDataValue value) ->
      TestRestrictedDataValue (value + 1))
    (\_ _ -> ())

testStableConfederalDataTransversal
  :: StableConfederalDataTransversal TestRestrictedDataValues
testStableConfederalDataTransversal =
  stableConfederalDataTransversal
    (\_ (TestRestrictedDataValue value) ->
      TestRestrictedDataValue value)
    (const ())
    (\_ _ _ -> ())

incrementStableConfederalDataTransversal
  :: StableConfederalDataTransversalHom
       TestRestrictedDataValues TestRestrictedDataValues
incrementStableConfederalDataTransversal =
  stableConfederalDataTransversalHom
    testStableConfederalDataTransversal
    testStableConfederalDataTransversal
    (\(TestRestrictedDataValue value) ->
      TestRestrictedDataValue (value + 1))
    (\_ _ -> ())

horizontalSumComponents
  :: HorizontalSumValue
       TestRestrictedDataValues TestRestrictedDataValues object
  -> (Natural, Natural)
horizontalSumComponents
  (HorizontalSumValue
    _ _ _
    (TestRestrictedDataValue left)
    (TestRestrictedDataValue right)) =
      (left, right)

data IdentityStableConfederalValues values

newtype IdentityStableConfederalValue values object =
  IdentityStableConfederalValue
    (StableConfederalDataTransversalValue values object)

type instance
  StableConfederalDataTransversalValue
    (IdentityStableConfederalValues values) object =
      IdentityStableConfederalValue values object

identityStableConfederalObject
  :: StableConfederalDataTransversal values
  -> StableConfederalDataTransversal
       (IdentityStableConfederalValues values)
identityStableConfederalObject source =
  stableConfederalDataTransversal
    (\arrow (IdentityStableConfederalValue value) ->
      IdentityStableConfederalValue
        (mapStableConfederalDataTransversal source arrow value))
    (\(IdentityStableConfederalValue value) ->
      stableConfederalDataTransversalIdentity source value)
    (\second first (IdentityStableConfederalValue value) ->
      stableConfederalDataTransversalComposition
        source second first value)

identityStableConfederalArrow
  :: StableConfederalDataTransversal source
  -> StableConfederalDataTransversal target
  -> StableConfederalDataTransversalHom source target
  -> StableConfederalDataTransversalHom
       (IdentityStableConfederalValues source)
       (IdentityStableConfederalValues target)
identityStableConfederalArrow source target arrow =
  stableConfederalDataTransversalHom
    (identityStableConfederalObject source)
    (identityStableConfederalObject target)
    (\(IdentityStableConfederalValue value) ->
      IdentityStableConfederalValue
        (mapStableConfederalDataTransversalHom arrow value))
    (\confederationArrow (IdentityStableConfederalValue value) ->
      stableConfederalDataTransversalHomNaturality
        arrow confederationArrow value)

identityStableConfederalEndofunctor
  :: StableConfederalDataTransversalEndofunctor
       IdentityStableConfederalValues
identityStableConfederalEndofunctor =
  stableConfederalDataTransversalEndofunctor
    identityStableConfederalObject
    identityStableConfederalArrow
    (const ())
    (\_ _ _ _ _ -> ())

identityStableConfederalUnit
  :: StableConfederalDataTransversal values
  -> StableConfederalDataTransversalHom
       values (IdentityStableConfederalValues values)
identityStableConfederalUnit source =
  stableConfederalDataTransversalHom
    source
    (identityStableConfederalObject source)
    IdentityStableConfederalValue
    (\_ _ -> ())

identityStableConfederalMultiplication
  :: StableConfederalDataTransversal values
  -> StableConfederalDataTransversalHom
       (IdentityStableConfederalValues
         (IdentityStableConfederalValues values))
       (IdentityStableConfederalValues values)
identityStableConfederalMultiplication source =
  stableConfederalDataTransversalHom
    (identityStableConfederalObject
      (identityStableConfederalObject source))
    (identityStableConfederalObject source)
    (\(IdentityStableConfederalValue
        (IdentityStableConfederalValue value)) ->
          IdentityStableConfederalValue value)
    (\_ _ -> ())

identityStableConfederalFubini
  :: StableConfederalDataTransversal left
  -> StableConfederalDataTransversal right
  -> StableConfederalDataTransversalHom
       (HorizontalSumValues
         (IdentityStableConfederalValues left)
         (IdentityStableConfederalValues right))
       (IdentityStableConfederalValues
         (HorizontalSumValues left right))
identityStableConfederalFubini left right =
  stableConfederalDataTransversalHom
    (horizontalSum
      (identityStableConfederalObject left)
      (identityStableConfederalObject right))
    (identityStableConfederalObject (horizontalSum left right))
    (\(HorizontalSumValue
        leftConfederation
        rightConfederation
        represented
        (IdentityStableConfederalValue leftValue)
        (IdentityStableConfederalValue rightValue)) ->
          IdentityStableConfederalValue
            (HorizontalSumValue
              leftConfederation
              rightConfederation
              represented
              leftValue
              rightValue))
    (\_ _ -> ())

identityStableConfederalMonad
  :: CommutativeStableConfederalDataTransversalMonad
       IdentityStableConfederalValues
identityStableConfederalMonad =
  commutativeStableConfederalDataTransversalMonad
    identityStableConfederalEndofunctor
    identityStableConfederalUnit
    identityStableConfederalMultiplication
    identityStableConfederalFubini
    (const ())
    (const ())
    (const ())
    (\_ _ -> ())

incrementIdentityStableConfederalKleisli
  :: StableConfederalDataTransversalKleisliHom
       IdentityStableConfederalValues
       TestRestrictedDataValues
       TestRestrictedDataValues
incrementIdentityStableConfederalKleisli =
  stableConfederalKleisliHom
    (stableConfederalDataTransversalHom
      testStableConfederalDataTransversal
      (identityStableConfederalObject
        testStableConfederalDataTransversal)
      (\(TestRestrictedDataValue value) ->
        IdentityStableConfederalValue
          (TestRestrictedDataValue (value + 1)))
      (\_ _ -> ()))

identityStableConfederalNatural
  :: IdentityStableConfederalValue TestRestrictedDataValues object
  -> Natural
identityStableConfederalNatural
  (IdentityStableConfederalValue (TestRestrictedDataValue value)) = value

identityHorizontalSumComponents
  :: IdentityStableConfederalValue
       (HorizontalSumValues
         TestRestrictedDataValues TestRestrictedDataValues)
       object
  -> (Natural, Natural)
identityHorizontalSumComponents
  (IdentityStableConfederalValue value) = horizontalSumComponents value

testStableConfederalKleisliSyntax :: IO ()
testStableConfederalKleisliSyntax = do
  let object = testStableConfederalDataTransversal
      identityProgram = Kleisli.return object
      stepProgram =
        Kleisli.step object incrementIdentityStableConfederalKleisli
      liftedProgram =
        Kleisli.lift object incrementStableConfederalDataTransversal
      qualifiedDoProgram = Kleisli.do
        identityProgram
        stepProgram
        liftedProgram
      forwardComposition =
        identityProgram Kleisli.>=> stepProgram Kleisli.>=> liftedProgram
      reverseComposition =
        liftedProgram Kleisli.<=< stepProgram Kleisli.<=< identityProgram
      leftAssociated =
        (identityProgram Kleisli.>=> stepProgram)
          Kleisli.>=> liftedProgram
      rightAssociated =
        identityProgram
          Kleisli.>=> (stepProgram Kleisli.>=> liftedProgram)
      evaluate
        :: Kleisli.Program
             IdentityStableConfederalValues
             TestRestrictedDataValues
             TestRestrictedDataValues
        -> Natural
      evaluate program =
        identityStableConfederalNatural
          (mapStableConfederalKleisliHom
            (Kleisli.run identityStableConfederalMonad program)
            (TestRestrictedDataValue 29 :: TestRestrictedDataValue ()))
  assert "Kleisli syntax return is the identity"
    (evaluate identityProgram == 29)
  assert "Kleisli syntax introduces an existing Kleisli arrow"
    (evaluate stepProgram == 30)
  assert "Kleisli syntax lifts a base-category arrow"
    (evaluate liftedProgram == 30)
  assert "qualified do sequences Kleisli arrows from left to right"
    (evaluate qualifiedDoProgram == 31)
  assert "forward Kleisli composition agrees with qualified do"
    (evaluate forwardComposition == evaluate qualifiedDoProgram)
  assert "reverse Kleisli composition agrees with qualified do"
    (evaluate reverseComposition == evaluate qualifiedDoProgram)
  assert "Kleisli syntax composition is associative"
    (evaluate leftAssociated == evaluate rightAssociated)

-- The page offset makes it observable whether 'atlasDataAt' normalized its
-- input before consulting the canonical data assignment.
testAtlasDataAt
  :: PageElement scope object
  -> Dominion (TestCellData object)
testAtlasDataAt occurrence =
  dominion
    (\(TestCellData value) -> pageElementPage occurrence + value)
    (\value ->
      if value < pageElementPage occurrence
        then Nothing
        else Just
          (TestCellData (value - pageElementPage occurrence)))
    (const ())

-- Likewise, this action would visibly shift a value if it were ever called on
-- an unnormalized padded arrow.  On the one-page test atlas every canonical
-- arrow is an identity, so the documented functor and disjointness laws hold.
testAtlasMapData
  :: PageElementArrow scope source target
  -> DomanialInsertion
       (TestCellData source)
       (TestCellData target)
testAtlasMapData pageArrow =
  domanialInsertion
    (\(TestCellData value) ->
      TestCellData (pageElementPage (arrowSource pageArrow) + value))
    (\(TestCellData value) ->
      if value < pageElementPage (arrowSource pageArrow)
        then Nothing
        else Just
          (TestCellData
            (value - pageElementPage (arrowSource pageArrow))))
    (const ())

doubleTestCellData
  :: DomanialInsertion
       (TestCellData source)
       (TestCellData target)
doubleTestCellData =
  domanialInsertion
    (\(TestCellData value) -> TestCellData (value * 2))
    (\(TestCellData value) ->
      if even value
        then Just (TestCellData (value `div` 2))
        else Nothing)
    (const ())

testAtlasIdentityLaw
  :: PageElement scope object
  -> TestCellData object
  -> ()
testAtlasIdentityLaw _ _ = ()

testAtlasCompositionLaw
  :: PageElementArrow scope middle target
  -> PageElementArrow scope source middle
  -> ()
  -> TestCellData source
  -> ()
testAtlasCompositionLaw _ _ _ _ = ()

testAtlasCoherenceLaw
  :: PageElement scope object
  -> PageElementArrow scope object object
  -> ()
  -> TestCellData object
  -> ()
testAtlasCoherenceLaw _ _ _ _ = ()

testAtlasDisjointLaw
  :: PageElement scope leftObject
  -> PageElement scope rightObject
  -> PageElementArrow scope leftObject originObject
  -> PageElementArrow scope rightObject originObject
  -> ()
  -> TestCellData leftObject
  -> TestCellData rightObject
  -> ()
testAtlasDisjointLaw _ _ _ _ _ _ _ = ()

testAtlas :: IO ()
testAtlas =
  pagination (singletonFolio unitChain) $ \valuePagination ->
    let dataAction = atlasDataAction testAtlasDataAt testAtlasMapData
    in atlas
      valuePagination
      dataAction
      testAtlasIdentityLaw
      testAtlasCompositionLaw
      testAtlasCoherenceLaw
      testAtlasDisjointLaw $ \valueAtlas ->
        let elements = atlasPageElements valueAtlas
        in case
          ( pageElement <$> pageElementIndex elements 0 (finiteOrdinal 0)
          , pageElement <$> pageElementIndex elements 100 (finiteOrdinal 0)
          ) of
            (Just someOrigin, Just somePadded) ->
              withPageElement someOrigin $ \origin ->
                withPageElement somePadded $ \padded -> do
                  assert "atlas retains its pagination and cardinality"
                    ( atlasCardinality valueAtlas == 1
                      && folioLength (atlasFolio valueAtlas) == 1
                      && paginationCardinality
                        (atlasPagination valueAtlas) == 1
                    )
                  let normalized = normalizeAtlasElement valueAtlas padded
                  assert "atlas element observation uses the padded spine"
                    ( pageElementPage padded == 100
                      && pageElementPage normalized == 0
                    )
                  assert "atlas data lookup uses the canonical representative"
                    (rank
                      (atlasDataAt valueAtlas padded)
                      (TestCellData 7) == 7)
                  let paddedToOrigin = pageElementArrow padded origin
                      normalizedArrow =
                        normalizeAtlasArrow valueAtlas paddedToOrigin
                      mappedDatum =
                        applyInsertion
                          (mapAtlasData valueAtlas paddedToOrigin)
                          (TestCellData 11)
                  assert "atlas arrow action uses canonical endpoints"
                    ( pageElementPage (arrowSource normalizedArrow) == 0
                      && pageElementPage (arrowTarget normalizedArrow) == 0
                      && mappedDatum == TestCellData 11
                    )
                  assert "atlas data coherence is operationally identity"
                    ( normalizeAtlasDatum
                        valueAtlas padded (TestCellData 13)
                        == TestCellData 13
                    )
                  withAtlasPageChain valueAtlas 100 $ \pageChain ->
                    assert "atlas pages expose the padded final chain"
                      (chainOrderType pageChain == chainOrderType unitChain)
                  case pageElementIndex elements 100 (finiteOrdinal 0) of
                    Nothing ->
                      fail "test setup failed: expected an atlas cell index"
                    Just paddedCellIndex ->
                      withPageElement
                        (atlasPageCell valueAtlas paddedCellIndex) $ \cell ->
                        assert "atlas page cells retain their spine page"
                          (pageElementPage cell == 100)
                  withPageElement (atlasOriginCell valueAtlas) $ \originCell ->
                    assert "atlas origin cell is on page zero"
                      ( pageElementPage originCell == 0
                        && pageElementPosition originCell == finiteOrdinal 0
                      )
                  withAtlasCellDominion (atlasExtent valueAtlas) $
                    \extentCell extentDominion ->
                      assert "atlas extent is the origin dominion"
                        ( pageElementPage extentCell == 0
                          && rank extentDominion (TestCellData 5) == 5
                        )
                  case chainIndex
                    (atlasTerritoryChain valueAtlas)
                    (finiteOrdinal 0) of
                    Nothing ->
                      fail "test setup failed: expected a territory index"
                    Just territoryIndex -> do
                      withAtlasCellDominion
                        (atlasTerritory valueAtlas territoryIndex) $
                          \territoryCell territoryDominion ->
                            assert "atlas territory uses the final genuine page"
                              ( pageElementPage territoryCell == 0
                                && rank territoryDominion (TestCellData 5) == 5
                              )
                      withAtlasCellDominion
                        (atlasRegion valueAtlas territoryIndex) $
                          \regionCell regionDominion ->
                            assert "atlas regions are territory members"
                              ( pageElementPage regionCell == 0
                                && rank regionDominion (TestCellData 5) == 5
                              )
                  assert "atlas element ordering compares canonical cells"
                    (not (atlasElementLT valueAtlas padded origin))
                  atlasCoherenceIdempotent valueAtlas padded `seq`
                    assert "atlas coherence is pointwise idempotent"
                      ( normalizeAtlasElement valueAtlas
                          (normalizeAtlasElement valueAtlas padded)
                        == normalizeAtlasElement valueAtlas padded
                      )
                  withPageElement
                    (mapPaginationElement (atlasCoherence valueAtlas) padded) $
                      \coherent ->
                        assert "atlas exposes pagination coherence"
                          (pageElementPage coherent == 0)
                  let coherentIdentity = identityAtlasMorphism valueAtlas
                  withPageElement
                    (mapAtlasMorphismElement coherentIdentity padded) $
                      \coherent ->
                        assert "atlas identity is its coherence map"
                          (pageElementPage coherent == 0)
                  withPageElement
                    (mapAtlasHomElement
                      (atlasWitness valueAtlas)
                      Category.id
                      padded) $ \coherent ->
                        assert
                          "Control.Category identity materializes as Atlas coherence"
                          (pageElementPage coherent == 0)
                  atlas
                    valuePagination
                    dataAction
                    testAtlasIdentityLaw
                    testAtlasCompositionLaw
                    testAtlasCoherenceLaw
                    testAtlasDisjointLaw $ \targetAtlas -> do
                      let valueMorphism =
                            atlasMorphism
                              (atlasMorphismAction
                                identityAtlasObjectMap
                                valueAtlas
                                targetAtlas
                                id
                                (const identityInsertion)
                                (\_ _ -> ())
                                (\_ _ -> ()))
                          valueHom = atlasHom valueMorphism
                          valueWitness = atlasWitness valueAtlas
                          valueTransposal =
                            atlasTransposal
                              valueWitness
                              valueHom
                              (\targetElement ->
                                withAtlasTransposalElement targetElement $
                                  \targetOccurrence ->
                                    Just
                                      (atlasTransposalElement
                                        valueWitness
                                        targetOccurrence))
                              (const ())
                          includedIdentityTransposal =
                            Category.id Category.. valueTransposal
                          leftHom = Category.id Category.. valueHom
                          rightHom = valueHom Category.. Category.id
                          associatedLeftHom =
                            Category.id Category.. rightHom
                          associatedRightHom =
                            leftHom Category.. Category.id
                          incrementedTwice =
                            incrementDataTransformation
                              Category.. incrementDataTransformation
                      withPageElement
                        (mapAtlasMorphismElement valueMorphism padded) $
                          \mapped ->
                            assert
                              "atlas morphisms normalize their page action"
                              (pageElementPage mapped == 0)
                      let sourceElement =
                            atlasTransposalElement valueWitness padded
                          mappedElement =
                            mapAtlasTransposalObject
                              includedIdentityTransposal
                              sourceElement
                      atlasTransposalLeftInverse
                        includedIdentityTransposal
                        sourceElement `seq` pure ()
                      assert
                        "atlas transposals retain a left inverse under identity"
                        ( atlasTransposalPreimage
                            includedIdentityTransposal
                            mappedElement
                            == Just sourceElement
                        )
                      withAtlasTransposalElement mappedElement $ \mapped ->
                        assert
                          "atlas transposals act on genuine Atlas elements"
                          (pageElementPage mapped == 0)
                      withPageElement
                        (mapAtlasTransposalElement
                          valueWitness
                          includedIdentityTransposal
                          padded) $ \mapped ->
                            assert
                              "the transposal inclusion retains the Atlas action"
                              (pageElementPage mapped == 0)
                      withAtlasMorphismImage
                        (mapAtlasMorphismData valueMorphism padded) $
                          \mapped insertion ->
                            assert
                              "atlas morphisms retain dependent data targets"
                              ( pageElementPage mapped == 0
                                && applyInsertion insertion (TestCellData 17)
                                  == TestCellData 17
                              )
                      withPageElementArrow
                        (mapAtlasMorphismArrow
                          valueMorphism paddedToOrigin) $ \mappedArrow ->
                            assert "atlas morphisms map page arrows"
                              ( pageElementPage (arrowSource mappedArrow) == 0
                                && pageElementPage (arrowTarget mappedArrow) == 0
                              )
                      withPageElement
                        (mapAtlasHomElement
                          (atlasWitness valueAtlas)
                          leftHom
                          padded) $ \mapped ->
                            assert
                              "Control.Category AtlasHom left identity"
                              (pageElementPage mapped == 0)
                      withPageElement
                        (mapAtlasHomElement
                          (atlasWitness valueAtlas)
                          rightHom
                          padded) $ \mapped ->
                            assert
                              "Control.Category AtlasHom right identity"
                              (pageElementPage mapped == 0)
                      withAtlasMorphismImage
                        (mapAtlasHomData
                          (atlasWitness valueAtlas)
                          associatedLeftHom
                          padded) $ \_ leftInsertion ->
                            withAtlasMorphismImage
                              (mapAtlasHomData
                                (atlasWitness valueAtlas)
                                associatedRightHom
                                padded) $ \_ rightInsertion ->
                                  case
                                    ( applyInsertion leftInsertion
                                        (TestCellData 23)
                                    , applyInsertion rightInsertion
                                        (TestCellData 23)
                                    ) of
                                    (TestCellData left, TestCellData right) ->
                                      assert
                                        "Control.Category AtlasHom associativity"
                                        (left == right)
                      assert "DaTra presheaves act contravariantly on AtlasHom"
                        ( mapDataTransformation
                            testDataTransformation
                            valueHom
                            (TestDataTransformationValue 29)
                          == TestDataTransformationValue 29
                        )
                      dataTransformationIdentity
                        testDataTransformation
                        (TestDataTransformationValue 29) `seq`
                          dataTransformationComposition
                            testDataTransformation
                            Category.id
                            valueHom
                            (TestDataTransformationValue 29) `seq`
                              dataTransformationHomNaturality
                                incrementDataTransformation
                                valueHom
                                (TestDataTransformationValue 29) `seq`
                                  pure ()
                      assert
                        "DaTra natural transformations compose pointwise"
                        ( mapDataTransformationHom
                            incrementedTwice
                            (TestDataTransformationValue 29)
                          == TestDataTransformationValue 31
                        )
                      case mapDataTransformation
                        yoneda
                        valueHom
                        (Yoneda Category.id) of
                          Yoneda representedArrow ->
                            withPageElement
                              (mapAtlasHomElement
                                (atlasWitness valueAtlas)
                                representedArrow
                                padded) $ \mapped ->
                                  assert
                                    "Yoneda acts by presheaf precomposition"
                                    (pageElementPage mapped == 0)
                      case mapDataTransformationHom
                        (yonedaMap valueHom)
                        (Yoneda Category.id) of
                          Yoneda representedArrow ->
                            withPageElement
                              (mapAtlasHomElement
                                (atlasWitness valueAtlas)
                                representedArrow
                                padded) $ \mapped ->
                                  assert
                                    "Yoneda embeds AtlasHom by postcomposition"
                                    (pageElementPage mapped == 0)
            _ -> fail "test setup failed: expected atlas elements"

testAtlasMerge :: IO ()
testAtlasMerge = do
  testSingletonAtlasMerge
  testDeepAtlasMerge

testSingletonAtlasMerge :: IO ()
testSingletonAtlasMerge =
  pagination (singletonFolio unitChain) $ \leftPagination ->
    atlas
      leftPagination
      (atlasDataAction testAtlasDataAt testAtlasMapData)
      testAtlasIdentityLaw
      testAtlasCompositionLaw
      testAtlasCoherenceLaw
      testAtlasDisjointLaw $ \leftAtlas ->
        pagination (singletonFolio unitChain) $ \rightPagination ->
          atlas
            rightPagination
            (atlasDataAction testAtlasDataAt testAtlasMapData)
            testAtlasIdentityLaw
            testAtlasCompositionLaw
            testAtlasCoherenceLaw
            testAtlasDisjointLaw $ \rightAtlas ->
              atlasMerge leftAtlas rightAtlas $ \mergedAtlas -> do
                let elements = atlasPageElements mergedAtlas
                    at pageNumber position =
                      pageElement <$>
                        pageElementIndex
                          elements pageNumber (finiteOrdinal position)
                assert "Atlas merge adds one page to the greatest input depth"
                  ( atlasMergeLength leftAtlas rightAtlas == 2
                    && atlasCardinality mergedAtlas == 2
                  )
                case (at 0 0, at 1 0, at 1 1, at 50 0) of
                  (Just someOrigin, Just someLeft, Just someRight, Just padded) ->
                    withPageElement someOrigin $ \origin ->
                      withPageElement someLeft $ \leftCell ->
                        withPageElement someRight $ \rightCell ->
                          withPageElement padded $ \paddedLeft -> do
                            let originDominion = atlasDataAt mergedAtlas origin
                                leftDominion = atlasDataAt mergedAtlas leftCell
                                rightDominion = atlasDataAt mergedAtlas rightCell
                                paddedDominion =
                                  atlasDataAt mergedAtlas paddedLeft
                            assert "Atlas merge interleaves its extent ranks"
                              ( case (unrank originDominion 0,
                                      unrank originDominion 1) of
                                  (Just leftDatum, Just rightDatum) ->
                                    atlasMergeDatumSide leftDatum
                                      == AtlasMergeLeft
                                      && atlasMergeDatumRank leftDatum == 0
                                      && atlasMergeDatumSide rightDatum
                                        == AtlasMergeRight
                                      && atlasMergeDatumRank rightDatum == 1
                                  _ -> False
                              )
                            assert "Atlas merge cells retain their tagged image"
                              ( isJust (unrank leftDominion 0)
                                && isNothing (unrank leftDominion 1)
                                && isNothing (unrank rightDominion 0)
                                && isJust (unrank rightDominion 1)
                              )
                            assert "Atlas merge is stable on the padded spine"
                              ( isJust (unrank paddedDominion 0)
                                && isNothing (unrank paddedDominion 1)
                              )
                  _ -> fail "test setup failed: expected Atlas merge cells"

testDeepAtlasMerge :: IO ()
testDeepAtlasMerge =
  pagination threePageFolio $ \leftPagination ->
    atlas
      leftPagination
      (atlasDataAction testAtlasDataAt testAtlasMapData)
      testAtlasIdentityLaw
      testAtlasCompositionLaw
      testAtlasCoherenceLaw
      testAtlasDisjointLaw $ \leftAtlas ->
        pagination (singletonFolio unitChain) $ \rightPagination ->
          atlas
            rightPagination
            (atlasDataAction testAtlasDataAt testAtlasMapData)
            testAtlasIdentityLaw
            testAtlasCompositionLaw
            testAtlasCoherenceLaw
            testAtlasDisjointLaw $ \rightAtlas ->
              atlasMerge leftAtlas rightAtlas $ \mergedAtlas -> do
                let elements = atlasPageElements mergedAtlas
                    at pageNumber position =
                      pageElement <$>
                        pageElementIndex
                          elements pageNumber (finiteOrdinal position)
                assert "Atlas merge follows the deeper input folio"
                  (atlasCardinality mergedAtlas == 4)
                case (at 2 2, at 3 5, at 100 5) of
                  (Just someRight, Just someLeft, Just somePaddedLeft) ->
                    withPageElement someRight $ \rightCell ->
                      withPageElement someLeft $ \leftCell ->
                        withPageElement somePaddedLeft $ \paddedLeft -> do
                          assert "Atlas merge pads the shallower input"
                            ( isJust
                                (unrank (atlasDataAt mergedAtlas rightCell) 1)
                              && isNothing
                                (unrank (atlasDataAt mergedAtlas rightCell) 0)
                            )
                          assert "Atlas merge transports deeper component data"
                            ( isJust
                                (unrank (atlasDataAt mergedAtlas leftCell) 4)
                              && isJust
                                (unrank (atlasDataAt mergedAtlas paddedLeft) 4)
                            )
                  _ -> fail "test setup failed: expected deep Atlas merge cells"

testAtlasConfederation :: IO ()
testAtlasConfederation =
  pagination (singletonFolio unitChain) $ \leftPagination ->
    atlas
      leftPagination
      (atlasDataAction testAtlasDataAt testAtlasMapData)
      testAtlasIdentityLaw
      testAtlasCompositionLaw
      testAtlasCoherenceLaw
      testAtlasDisjointLaw $ \leftAtlas ->
        pagination (singletonFolio unitChain) $ \rightPagination ->
          atlas
            rightPagination
            (atlasDataAction testAtlasDataAt testAtlasMapData)
            testAtlasIdentityLaw
            testAtlasCompositionLaw
            testAtlasCoherenceLaw
            testAtlasDisjointLaw $ \rightAtlas ->
              let leftAtom = singletonAtlasConfederation leftAtlas
                  rightAtom = singletonAtlasConfederation rightAtlas
              in do
                  let leftWitness = atlasConfederationWitness leftAtom
                      identityHom = Category.id
                      primitiveHom =
                        singletonAtlasConfederationHom
                          leftAtlas leftAtlas identityStableAtlasTransversal
                      rightPrimitiveHom =
                        singletonAtlasConfederationHom
                          rightAtlas rightAtlas identityStableAtlasTransversal
                      composedHom = primitiveHom Category.. primitiveHom
                      componentCount :: Natural
                      componentCount =
                        foldAtlasConfederationComponentHom
                          (const 0)
                          (\_ _ _ -> 1)
                          (+)
                          (mapAtlasConfederationComponent
                            leftWitness composedHom ())
                  assert "Atlas-confederation identity preserves tags"
                    (mapAtlasConfederationIndex leftWitness identityHom () == ())
                  atlasConfederationComponentHomStable
                    (mapAtlasConfederationComponent
                      leftWitness composedHom ()) `seq` pure ()
                  assert "Atlas-confederation component maps compose"
                    (componentCount == 2)
                  let merged = atlasHorizontalSum leftAtom rightAtom
                      lemmaResult = horizontalLemma leftAtom rightAtom
                  do
                    let indices = atlasConfederationIndexDominion merged
                        presentation = atlasConfederationPresentation merged
                        mergedWitness = atlasConfederationWitness merged
                        mergedHom = atlasHorizontalSumHom
                          leftAtom rightAtom leftAtom rightAtom
                          primitiveHom rightPrimitiveHom
                    assert "Atlas-confederation merge retains disjoint tags"
                      ( unrank indices 0 == Just (Left ())
                        && unrank indices 1 == Just (Right ())
                      )
                    assert "Atlas-confederation merge retains its presentation"
                      (atlasMergePresentationSize presentation == 2)
                    assert "the horizontal lemma creates horizontal sum"
                      ( atlasMergePresentationSize
                          (atlasConfederationPresentation lemmaResult) == 2
                      )
                    assert "merged Atlas-confederation morphisms map both tags"
                      ( mapAtlasConfederationIndex
                          mergedWitness mergedHom (Left ()) == Left ()
                        && mapAtlasConfederationIndex
                          mergedWitness mergedHom (Right ()) == Right ()
                      )
                    let braided = atlasHorizontalSum rightAtom leftAtom
                        braidedWitness = atlasConfederationWitness braided
                        (braiderHom, braiderInv) =
                          atlasBraider leftAtom rightAtom
                    assert "the Atlas braider swaps tags in both directions"
                      ( mapAtlasConfederationIndex
                          mergedWitness braiderHom (Left ()) == Right ()
                        && mapAtlasConfederationIndex
                          braidedWitness braiderInv (Right ()) == Left ()
                      )
                    let associatedLeft =
                          atlasHorizontalSum
                            (atlasHorizontalSum leftAtom rightAtom)
                            leftAtom
                        associatedRight =
                          atlasHorizontalSum
                            leftAtom
                            (atlasHorizontalSum rightAtom leftAtom)
                        associatedLeftWitness =
                          atlasConfederationWitness associatedLeft
                        associatedRightWitness =
                          atlasConfederationWitness associatedRight
                        (associatorHom, associatorInv) =
                          atlasAssociator leftAtom rightAtom leftAtom
                    assert "the Atlas associator reassociates tags"
                      ( mapAtlasConfederationIndex
                          associatedLeftWitness associatorHom
                          (Left (Right ())) == Right (Left ())
                        && mapAtlasConfederationIndex
                          associatedRightWitness associatorInv
                          (Right (Left ())) == Left (Right ())
                      )
                    let leftUnitSource =
                          atlasHorizontalSum emptyAtlasConfederation leftAtom
                        rightUnitSource =
                          atlasHorizontalSum leftAtom emptyAtlasConfederation
                        leftUnitSourceWitness =
                          atlasConfederationWitness leftUnitSource
                        rightUnitSourceWitness =
                          atlasConfederationWitness rightUnitSource
                        (leftUnitorHom, leftUnitorInv) =
                          atlasLeftUnitor leftAtom
                        (rightUnitorHom, rightUnitorInv) =
                          atlasRightUnitor leftAtom
                    assert "the Atlas unitors delete and restore empty tags"
                      ( mapAtlasConfederationIndex
                          leftUnitSourceWitness leftUnitorHom (Right ()) == ()
                        && mapAtlasConfederationIndex
                          leftWitness leftUnitorInv () == Right ()
                        && mapAtlasConfederationIndex
                          rightUnitSourceWitness rightUnitorHom (Left ()) == ()
                        && mapAtlasConfederationIndex
                          leftWitness rightUnitorInv () == Left ()
                      )
                    withAtlasConfederationResultingAtlas merged $ \result ->
                      assert "Atlas-confederation presentation evaluates"
                        (atlasCardinality result == 2)
                  let empty = emptyAtlasConfederation
                  do
                    assert "the empty Atlas confederation has no tags"
                      (isNothing
                        (unrank (atlasConfederationIndexDominion empty) 0))
                    forgetAtlasConfederationTags empty $ \result ->
                        assert "the empty presentation evaluates to an Atlas"
                          (atlasCardinality result == 1)

testAtlasFederation :: IO ()
testAtlasFederation = do
  let emptyFederation =
        atlasFederation
          emptyAtlasConfederation
          (\impossible _ -> absurd impossible)
  assert "the empty Atlas federation has no tags"
    (isNothing (unrank (atlasFederationIndexDominion emptyFederation) 0))
  forgetAtlasFederationTags emptyFederation $ \result ->
    assert "forgetting empty federation tags produces the empty Atlas"
      (atlasCardinality result == 1)
  emptyAtlas $ \valueAtlas ->
    let component = atlasConfederationComponentWitness (atlasWitness valueAtlas)
        atom = AtlasMergeAtom (atlasWitness valueAtlas)
        correspondingPosition = finiteOrdinal 0
        twoTagDominion =
          dominion
            (\tag -> if tag then 1 else 0)
            (\tagRank -> case tagRank of
              0 -> Just False
              1 -> Just True
              _ -> Nothing)
            (const ())
    in atlasConfederation
        twoTagDominion
        (const component)
        (AtlasMergeNode atom atom) $ \confederation -> do
          let federation =
                atlasFederation confederation $ \_ _ ->
                  SeparatedCorrespondingRegions correspondingPosition
          assert "a federation does not separate a tag from itself"
            (isNothing (atlasFederationSeparation federation False False))
          assert "a federation retains separation evidence for distinct tags"
            ( atlasFederationSeparation federation False True
                == Just
                  (SeparatedCorrespondingRegions correspondingPosition)
            )

testAtlasMap :: IO ()
testAtlasMap =
  pagination (singletonFolio unitChain) $ \valuePagination ->
    atlas
      valuePagination
      (atlasDataAction testAtlasDataAt testAtlasMapData)
      testAtlasIdentityLaw
      testAtlasCompositionLaw
      testAtlasCoherenceLaw
      testAtlasDisjointLaw $ \valueAtlas ->
        let valueMap =
              atlasMap valueAtlas $ \extent extentDatum ->
                atlasCoverageWitness
                  valueAtlas
                  extent
                  extentDatum
                  extent
                  extentDatum
                  ()
            identityMapHom = identityAtlasMapHom
        in withAtlasMapExtent valueMap $ \extent extentDominion covers -> do
          withAtlasCoveredPageElement (covers (TestCellData 7)) $ \coveredElement datum ->
            assert "Atlas maps cover every extent datum"
              ( pageElementPage coveredElement == 0
                && rank (atlasDataAt valueAtlas coveredElement) datum == 7
                && rank extentDominion (TestCellData 7) == 7
              )
          withPageElement
            (mapAtlasMapHomElement valueMap identityMapHom extent) $ \mapped ->
              assert "the Atlas-map category inherits Atlas identity"
                (pageElementPage mapped == 0)
          withPageElement
            (mapAtlasHomElement
              (atlasMapInclusionObject atlasMapInclusionFunctor valueMap)
              (atlasMapInclusionHom
                atlasMapInclusionFunctor
                (identityMapHom Category.. identityMapHom))
              extent) $ \mapped ->
                assert "the Atlas Map Inclusion Functor preserves composition"
                  (pageElementPage mapped == 0)
          let mapWitness = atlasMapAtlas valueMap
              transposal =
                atlasTransposal
                  mapWitness
                  identityAtlasHom
                  Just
                  (const ())
              ordered = orderedAtlasTransposal transposal (\_ _ -> ())
              transversal =
                atlasTransversal
                  valueAtlas
                  valueAtlas
                  ordered
                  (\_ targetOccurrence targetDatum ->
                    atlasCoverageWitness
                      valueAtlas
                      targetOccurrence
                      targetDatum
                      targetOccurrence
                      targetDatum
                      ())
              transversalMap = atlasTransversalMap transversal
              composedTransversalMap =
                Category.id Category.. transversalMap
          withPageElement
            (mapAtlasTransversalMapElement
              valueMap
              composedTransversalMap
              extent) $ \mapped ->
                assert "Atlas transversal maps inherit transversal actions"
                  (pageElementPage mapped == 0)
          withAtlasCoveredPageElement
            (mapAtlasTransversalMapCoveredPageElement
              composedTransversalMap
              (covers (TestCellData 11))) $ \mapped datum ->
                assert "Atlas transversal maps preserve covered page elements"
                  ( pageElementPage mapped == 0
                    && rank (atlasDataAt valueAtlas mapped) datum == 11
                  )
          withPageElement
            (mapAtlasTransversalElement
              (atlasTransversalMapInclusionObject
                atlasTransversalMapInclusionFunctor
                valueMap)
              (atlasTransversalMapInclusionHom
                atlasTransversalMapInclusionFunctor
                (composedTransversalMap Category.. Category.id))
              extent) $ \mapped ->
                assert
                  "Atlas Transversal Map inclusion preserves composition"
                  (pageElementPage mapped == 0)

testNavigationAndExpedition :: IO ()
testNavigationAndExpedition =
  pagination (singletonFolio unitChain) $ \valuePagination ->
    atlas
      valuePagination
      (atlasDataAction testAtlasDataAt testAtlasMapData)
      testAtlasIdentityLaw
      testAtlasCompositionLaw
      testAtlasCoherenceLaw
      testAtlasDisjointLaw $ \valueAtlas ->
        let witness = atlasWitness valueAtlas
            valueMap =
              atlasMap valueAtlas $ \extent extentDatum ->
                atlasCoverageWitness
                  valueAtlas
                  extent
                  extentDatum
                  extent
                  extentDatum
                  ()
            valueNavigation =
              navigation witness Category.id Just (const ())
            valueExpedition =
              expedition valueMap Category.id Just (const ())
            refinedExpedition =
              expeditionFromNavigation valueMap valueNavigation
            source = Yoneda identityAtlasHom
        in do
          navigationLeftInverse valueNavigation source `seq`
            expeditionLeftInverse valueExpedition source `seq`
              pure ()
          case navigationPreimage valueNavigation
            (mapNavigation valueNavigation source) of
              Nothing -> fail "navigation left inverse rejected its image"
              Just (Yoneda recovered) ->
                withPageElement
                  (atlasOriginCell valueAtlas) $ \origin ->
                    withPageElement
                      (mapAtlasHomElement witness recovered origin) $ \mapped ->
                        assert "navigations are componentwise monomorphisms"
                          (pageElementPage mapped == 0)
          case expeditionPreimage refinedExpedition
            (mapExpedition refinedExpedition source) of
              Nothing -> fail "expedition left inverse rejected its image"
              Just _ ->
                withAtlasMapExtent
                  (expeditionAtlasMap valueExpedition) $ \extent _ _ ->
                    withPageElement
                      (mapAtlasHomElement
                        (expeditionAtlas valueExpedition)
                        identityAtlasHom
                        extent) $ \mapped ->
                          assert
                            "expeditions retain their Atlas-map representation"
                            (pageElementPage mapped == 0)

testDataTransformationMap :: IO ()
testDataTransformationMap = do
  let valueHom = dataTransformationMapHom incrementDataTransformation
      identityHom =
        identityDataTransformationMapHom
          :: DataTransformationMapHom
               TestDataTransformationValues
               TestDataTransformationValues
      composedHom = composeDataTransformationMapHoms valueHom valueHom
      categoryComposed = valueHom Category.. valueHom
      includedHom =
        dataTransformationMapInclusionHom
          dataTransformationMapInclusionFunctor
          (Category.id Category.. valueHom Category.. Category.id)
      input = TestDataTransformationValue 29
  dataTransformationMapHomNaturality valueHom Category.id input `seq`
    dataTransformationMapInclusionObject
      dataTransformationMapInclusionFunctor
      emptyDataTransformationMap `seq`
        pure ()
  assert "Data Transformation Map identity acts pointwise"
    (mapDataTransformationMapHom identityHom input == input)
  assert "Data Transformation Map composition follows categorical order"
    ( mapDataTransformationMapHom composedHom input
        == TestDataTransformationValue 31
      && mapDataTransformationMapHom categoryComposed input
        == TestDataTransformationValue 31
    )
  assert "the full-subcategory inclusion preserves morphism components"
    ( mapDataTransformationHom includedHom input
        == TestDataTransformationValue 30
    )

testRestrictedDataTransformations :: IO ()
testRestrictedDataTransformations = do
  let input = TestRestrictedDataValue 29 :: TestRestrictedDataValue ()
      emptyConfederationIdentity =
        identityAtlasConfederationHom
          :: AtlasConfederationHom
               (AtlasConfederationObject EmptyAtlasConfederationScope Void)
               (AtlasConfederationObject EmptyAtlasConfederationScope Void)
      reindexedEmptyMapIdentity =
        mapStableConfederalDataTransversal
          emptyMap
          emptyConfederationIdentity
          emptyConfederationIdentity
      summedTransformation =
        testStableConfederalDataTransversal
          |+| testStableConfederalDataTransversal
      summedValue =
        horizontalSumValue
          emptyAtlasConfederation
          emptyAtlasConfederation
          (TestRestrictedDataValue 11)
          (TestRestrictedDataValue 17)
      reindexedSummedValue =
        mapStableConfederalDataTransversal
          summedTransformation
          identityAtlasConfederationHom
          summedValue
      summedHom =
        horizontalSumHom
          testStableConfederalDataTransversal
          testStableConfederalDataTransversal
          testStableConfederalDataTransversal
          testStableConfederalDataTransversal
          incrementStableConfederalDataTransversal
          incrementStableConfederalDataTransversal
      identityKleisliReturn =
        stableConfederalKleisliReturn
          identityStableConfederalMonad
          testStableConfederalDataTransversal
      boundIdentityKleisli =
        stableConfederalKleisliBind
          identityStableConfederalMonad
          testStableConfederalDataTransversal
          testStableConfederalDataTransversal
          incrementIdentityStableConfederalKleisli
          incrementIdentityStableConfederalKleisli
      joinedIdentityValue =
        mapStableConfederalDataTransversalHom
          (stableConfederalJoin
            identityStableConfederalMonad
            testStableConfederalDataTransversal)
          (IdentityStableConfederalValue
            (IdentityStableConfederalValue input))
      mappedIdentityValue =
        mapStableConfederalDataTransversalHom
          (stableConfederalFmap
            identityStableConfederalMonad
            testStableConfederalDataTransversal
            testStableConfederalDataTransversal
            incrementStableConfederalDataTransversal)
          (IdentityStableConfederalValue input)
      identityFubiniValue =
        mapStableConfederalDataTransversalHom
          (stableConfederalFubini
            identityStableConfederalMonad
            testStableConfederalDataTransversal
            testStableConfederalDataTransversal)
          (horizontalSumValue
            emptyAtlasConfederation
            emptyAtlasConfederation
            (IdentityStableConfederalValue (TestRestrictedDataValue 11))
            (IdentityStableConfederalValue (TestRestrictedDataValue 17)))
  dataTransposalIdentity testDataTransposal input `seq`
    dataTransposalComposition
      testDataTransposal
      identityAtlasTransposal
      identityAtlasTransposal
      input `seq`
        dataTransposalHomNaturality
          incrementDataTransposal identityAtlasTransposal input `seq`
            pure ()
  orderedDataTransposalIdentity testOrderedDataTransposal input `seq`
    orderedDataTransposalComposition
      testOrderedDataTransposal
      identityOrderedAtlasTransposal
      identityOrderedAtlasTransposal
      input `seq`
        orderedDataTransposalHomNaturality
          incrementOrderedDataTransposal
          identityOrderedAtlasTransposal
          input `seq`
            pure ()
  dataTransversalIdentity testDataTransversal input `seq`
    dataTransversalComposition
      testDataTransversal
      identityAtlasTransversal
      identityAtlasTransversal
      input `seq`
        dataTransversalHomNaturality
          incrementDataTransversal identityAtlasTransversal input `seq`
            pure ()
  stableDataTransversalIdentity testStableDataTransversal input `seq`
    stableDataTransversalComposition
      testStableDataTransversal
      identityStableAtlasTransversal
      identityStableAtlasTransversal
      input `seq`
        stableDataTransversalHomNaturality
          incrementStableDataTransversal
          identityStableAtlasTransversal
          input `seq`
            pure ()
  stableConfederalDataTransversalIdentity
      testStableConfederalDataTransversal input `seq`
    stableConfederalDataTransversalComposition
      testStableConfederalDataTransversal
      identityAtlasConfederationHom
      identityAtlasConfederationHom
      input `seq`
        stableConfederalDataTransversalHomNaturality
          incrementStableConfederalDataTransversal
          identityAtlasConfederationHom
          input `seq`
            pure ()
  stableConfederalDataTransversalIdentity
      emptyMap emptyConfederationIdentity `seq`
    stableConfederalDataTransversalComposition
      emptyMap
      emptyConfederationIdentity
      emptyConfederationIdentity
      emptyConfederationIdentity `seq`
        targetAtlasConfederationWitness
          (atlasConfederationWitness emptyAtlasConfederation)
          reindexedEmptyMapIdentity `seq`
            pure ()
  stableConfederalDataTransversalIdentity
      summedTransformation summedValue `seq`
    stableConfederalDataTransversalComposition
      summedTransformation
      identityAtlasConfederationHom
      identityAtlasConfederationHom
      summedValue `seq`
        stableConfederalDataTransversalHomNaturality
          summedHom identityAtlasConfederationHom summedValue `seq`
            pure ()
  stableConfederalEndofunctorIdentity
      identityStableConfederalEndofunctor
      testStableConfederalDataTransversal `seq`
    stableConfederalEndofunctorComposition
      identityStableConfederalEndofunctor
      testStableConfederalDataTransversal
      testStableConfederalDataTransversal
      testStableConfederalDataTransversal
      incrementStableConfederalDataTransversal
      incrementStableConfederalDataTransversal `seq`
        stableConfederalMonadLeftIdentity
          identityStableConfederalMonad
          testStableConfederalDataTransversal `seq`
            stableConfederalMonadRightIdentity
              identityStableConfederalMonad
              testStableConfederalDataTransversal `seq`
                stableConfederalMonadAssociativity
                  identityStableConfederalMonad
                  testStableConfederalDataTransversal `seq`
                    stableConfederalMonadCommutativity
                      identityStableConfederalMonad
                      testStableConfederalDataTransversal
                      testStableConfederalDataTransversal `seq`
                        pure ()
  assert "restricted data presheaves act contravariantly"
    ( mapDataTransposal
        testDataTransposal identityAtlasTransposal input == input
      && mapOrderedDataTransposal
        testOrderedDataTransposal identityOrderedAtlasTransposal input == input
      && mapDataTransversal
        testDataTransversal identityAtlasTransversal input == input
      && mapStableDataTransversal
        testStableDataTransversal identityStableAtlasTransversal input == input
      && mapStableConfederalDataTransversal
        testStableConfederalDataTransversal
        identityAtlasConfederationHom
        input == input
      && horizontalSumComponents reindexedSummedValue == (11, 17)
      && identityStableConfederalNatural mappedIdentityValue == 30
      && identityStableConfederalNatural joinedIdentityValue == 29
      && identityHorizontalSumComponents identityFubiniValue == (11, 17)
    )
  assert "restricted natural transformations compose pointwise"
    ( mapDataTransposalHom
        (incrementDataTransposal Category.. incrementDataTransposal)
        input == TestRestrictedDataValue 31
      && mapOrderedDataTransposalHom
        (incrementOrderedDataTransposal
          Category.. incrementOrderedDataTransposal)
        input == TestRestrictedDataValue 31
      && mapDataTransversalHom
        (incrementDataTransversal Category.. incrementDataTransversal)
        input == TestRestrictedDataValue 31
      && mapStableDataTransversalHom
        (incrementStableDataTransversal
          Category.. incrementStableDataTransversal)
        input == TestRestrictedDataValue 31
      && mapStableConfederalDataTransversalHom
        (incrementStableConfederalDataTransversal
          Category.. incrementStableConfederalDataTransversal)
        input == TestRestrictedDataValue 31
      && horizontalSumComponents
        (mapStableConfederalDataTransversalHom summedHom summedValue)
          == (12, 18)
      && identityStableConfederalNatural
        (mapStableConfederalKleisliHom identityKleisliReturn input) == 29
      && identityStableConfederalNatural
        (mapStableConfederalKleisliHom boundIdentityKleisli input) == 31
    )

testCharter :: IO ()
testCharter =
  pagination (singletonFolio unitChain) $ \valuePagination ->
    atlas
      valuePagination
      (atlasDataAction testAtlasDataAt testAtlasMapData)
      testAtlasIdentityLaw
      testAtlasCompositionLaw
      testAtlasCoherenceLaw
      testAtlasDisjointLaw $ \valueAtlas ->
        let witness = atlasWitness valueAtlas
            valueMap =
              atlasMap valueAtlas $ \extent extentDatum ->
                atlasCoverageWitness
                  valueAtlas extent extentDatum extent extentDatum ()
            transposal =
              atlasTransposal witness identityAtlasHom Just (const ())
            ordered = orderedAtlasTransposal transposal (\_ _ -> ())
            transversal =
              atlasTransversal
                valueAtlas
                valueAtlas
                ordered
                (\_ targetOccurrence targetDatum ->
                  atlasCoverageWitness
                    valueAtlas
                    targetOccurrence
                    targetDatum
                    targetOccurrence
                    targetDatum
                    ())
            chartedMap = charterFunctorObject valueAtlas
            mapped = charterFunctorHom witness witness transversal
            lifted = chartLift valueMap witness transversal
            lowered = chartLower valueAtlas lifted
        in withAtlasMapExtent chartedMap $ \extent chartedDom covers ->
          case
            [ candidate
            | index <- [0 .. 100]
            , Just candidate <- [unrank chartedDom index]
            , let TestCellData candidateValue =
                    chartedCellDataValue candidate
            , candidateValue == 7
            ] of
            [] -> fail "Charter lost a covered extent page element"
            charted : _ -> do
              let TestCellData value = chartedCellDataValue charted
              assert "Charter retains covered cell data" (value == 7)
              case unrank chartedDom (rank chartedDom charted) of
                Nothing -> fail "charted Dominion rank did not round-trip"
                Just roundTripped ->
                  let TestCellData roundTrippedValue =
                        chartedCellDataValue roundTripped
                  in assert "charted Dominion rank round-trips"
                      (roundTrippedValue == 7)
              withAtlasCoveredPageElement (covers charted) $ \coveredElement datum ->
                let TestCellData coveredValue = chartedCellDataValue datum
                in assert "charted objects are Atlas maps"
                    (pageElementPage coveredElement == 0 && coveredValue == 7)
              withAtlasMorphismImage
                (mapAtlasTransversalData
                  (atlasWitness (chartAtlas valueAtlas))
                  (chartCounit valueAtlas)
                  extent) $ \target component ->
                    let TestCellData counitValue =
                          applyInsertion component charted
                    in assert "the chart counit forgets only coverage"
                        (pageElementPage target == 0 && counitValue == 7)
              withAtlasMorphismImage
                (mapAtlasTransversalMapData chartedMap mapped extent) $
                  \_ component ->
                    let TestCellData mappedValue =
                          chartedCellDataValue
                            (applyInsertion component charted)
                    in assert "the Charter functor maps covered page elements"
                        (mappedValue == 7)
              withAtlasMorphismImage
                (mapAtlasTransversalMapData
                  valueMap lifted extent) $ \_ component ->
                    let TestCellData liftedValue =
                          chartedCellDataValue
                            (applyInsertion component (TestCellData 7))
                    in assert "chartLift realizes the forward hom equivalence"
                        (liftedValue == 7)
              withAtlasMorphismImage
                (mapAtlasTransversalData witness lowered extent) $
                  \_ component ->
                    let TestCellData loweredValue =
                          applyInsertion component (TestCellData 7)
                    in assert "chartLower is inverse to chartLift on data"
                        (loweredValue == 7)
testOrderedAtlasTransposal :: IO ()
testOrderedAtlasTransposal =
  pagination threePageFolio $ \valuePagination ->
    atlas
      valuePagination
      (atlasDataAction testAtlasDataAt testAtlasMapData)
      testAtlasIdentityLaw
      testAtlasCompositionLaw
      testAtlasCoherenceLaw
      testAtlasDisjointLaw $ \valueAtlas ->
        let elements = atlasPageElements valueAtlas
            at position =
              pageElement
                <$> pageElementIndex elements 1 (finiteOrdinal position)
        in case (at 0, at 1) of
          (Just someLeft, Just someRight) ->
            withPageElement someLeft $ \left ->
              withPageElement someRight $ \right -> do
                let witness = atlasWitness valueAtlas
                    transposal =
                      atlasTransposal
                        witness
                        identityAtlasHom
                        Just
                        (const ())
                    ordered =
                      orderedAtlasTransposal transposal (\_ _ -> ())
                    composed = ordered Category.. ordered
                    includedIdentity = Category.id Category.. composed
                    leftElement = atlasTransposalElement witness left
                    rightElement = atlasTransposalElement witness right
                    mappedLeft =
                      mapOrderedAtlasTransposalObject
                        includedIdentity leftElement
                    mappedRight =
                      mapOrderedAtlasTransposalObject
                        includedIdentity rightElement
                assert "ordered transposal test source is strictly ordered"
                  (atlasTransposalElementLT leftElement rightElement)
                orderedAtlasTransposalPreservesOrder
                  includedIdentity leftElement rightElement `seq` pure ()
                assert "ordered transposals preserve strict Atlas order"
                  (atlasTransposalElementLT mappedLeft mappedRight)
                assert "ordered transposals retain transposal injectivity"
                  ( orderedAtlasTransposalPreimage includedIdentity mappedLeft
                      == Just leftElement
                  )
          _ -> fail "test setup failed: expected two ordered Atlas elements"

testAtlasTransversal :: IO ()
testAtlasTransversal =
  pagination threePageFolio $ \valuePagination ->
    atlas
      valuePagination
      (atlasDataAction testAtlasDataAt testAtlasMapData)
      testAtlasIdentityLaw
      testAtlasCompositionLaw
      testAtlasCoherenceLaw
      testAtlasDisjointLaw $ \valueAtlas ->
        let elements = atlasPageElements valueAtlas
        in case
          pageElement <$> pageElementIndex elements 2 (finiteOrdinal 5) of
            Nothing ->
              fail "test setup failed: expected a final-region element"
            Just someRegion ->
              withPageElement someRegion $ \region -> do
                let witness = atlasWitness valueAtlas
                    transposal =
                      atlasTransposal
                        witness
                        identityAtlasHom
                        Just
                        (const ())
                    ordered =
                      orderedAtlasTransposal transposal (\_ _ -> ())
                    transversal =
                      atlasTransversal
                        valueAtlas
                        valueAtlas
                        ordered
                        (\_ targetOccurrence targetDatum ->
                          atlasCoverageWitness
                            valueAtlas
                            targetOccurrence
                            targetDatum
                            targetOccurrence
                            targetDatum
                            ())
                    composed = transversal Category.. transversal
                    covered =
                      atlasCoveredPageElement
                        valueAtlas
                        region
                        (TestCellData 7)
                        region
                        (TestCellData 7)
                        ()
                    mappedCovered =
                      mapAtlasTransversalCoveredPageElement composed covered
                withAtlasCoveredPageElement mappedCovered $ \mapped datum ->
                  assert "transversals preserve covered final-region page elements"
                    ( pageElementPage mapped == 2
                      && rank (atlasDataAt valueAtlas mapped) datum == 9
                    )

testStableAtlasTransversal :: IO ()
testStableAtlasTransversal =
  pagination threePageFolio $ \valuePagination ->
    atlas
      valuePagination
      (atlasDataAction testAtlasDataAt testAtlasMapData)
      testAtlasIdentityLaw
      testAtlasCompositionLaw
      testAtlasCoherenceLaw
      testAtlasDisjointLaw $ \valueAtlas ->
        withPageElement (atlasOriginCell valueAtlas) $ \origin -> do
          let witness = atlasWitness valueAtlas
              transposal =
                atlasTransposal witness identityAtlasHom Just (const ())
              ordered = orderedAtlasTransposal transposal (\_ _ -> ())
              transversal =
                atlasTransversal
                  valueAtlas
                  valueAtlas
                  ordered
                  (\_ targetOccurrence targetDatum ->
                    atlasCoverageWitness
                      valueAtlas
                      targetOccurrence
                      targetDatum
                      targetOccurrence
                      targetDatum
                      ())
              stable =
                stableAtlasTransversal
                  valueAtlas valueAtlas transversal ()
              composed = stable Category.. stable
              originElement = atlasTransposalElement witness origin
              mappedOrigin =
                mapStableAtlasTransversalObject composed originElement
          stableAtlasTransversalPreservesExtent composed `seq`
            assert "stable Atlas transversals send extent to extent"
              (mappedOrigin == originElement)

testCoalition :: IO ()
testCoalition =
  pagination (singletonFolio unitChain) $ \valuePagination ->
    atlas
      valuePagination
      (atlasDataAction testAtlasDataAt testAtlasMapData)
      testAtlasIdentityLaw
      testAtlasCompositionLaw
      testAtlasCoherenceLaw
      testAtlasDisjointLaw $ \valueAtlas ->
        let witness = atlasWitness valueAtlas
            transposal =
              atlasTransposal witness identityAtlasHom Just (const ())
            ordered = orderedAtlasTransposal transposal (\_ _ -> ())
            transversal =
              atlasTransversal
                valueAtlas
                valueAtlas
                ordered
                (\_ targetOccurrence targetDatum ->
                  atlasCoverageWitness
                    valueAtlas
                    targetOccurrence
                    targetDatum
                    targetOccurrence
                    targetDatum
                    ())
            stable =
              stableAtlasTransversal
                valueAtlas valueAtlas transversal ()
            doublingAction =
              atlasMorphismAction
                identityAtlasObjectMap
                valueAtlas
                valueAtlas
                id
                (const doubleTestCellData)
                (\_ _ -> ())
                (\_ _ -> ())
            doublingTransposal =
              atlasTransposal
                witness
                (atlasHom (atlasMorphism doublingAction))
                Just
                (const ())
            doublingTransversal =
              atlasTransversal
                valueAtlas
                valueAtlas
                (orderedAtlasTransposal
                  doublingTransposal (\_ _ -> ()))
                (\_ targetOccurrence targetDatum ->
                  atlasCoverageWitness
                    valueAtlas
                    targetOccurrence
                    targetDatum
                    targetOccurrence
                    targetDatum
                    ())
            doublingStable =
              stableAtlasTransversal
                valueAtlas valueAtlas doublingTransversal ()
            valueCoalition = coalition valueAtlas
        in case
          [ candidate
          | index <- [0 .. 100]
          , Just candidate <- [unrank valueCoalition index]
          , coalitionElementRank candidate == 7
          ] of
            [] -> fail "Coalition lost a covered extent page element"
            element : _ -> do
              let decoded =
                    withCoalitionElement element $ \origin datum ->
                      ( pageElementPage origin
                      , rank (atlasDataAt valueAtlas origin) datum
                      )
              assert "a coalition is the covered chart extent"
                (decoded == (0, 7))
              let mapped =
                    applyInsertion
                      (coalizingFunctorHom witness witness stable)
                      element
                  composed =
                    coalizingFunctorHom
                      witness
                      witness
                      (stable Category.. stable)
              assert "the Coalizing functor maps the stable origin component"
                (coalitionElementRank mapped == 7)
              assert "the Coalizing arrow has the inherited partial inverse"
                (preimage
                  (coalizingFunctorHom witness witness stable)
                  mapped == Just element)
              assert "a coalition preimage outside the arrow image is total"
                (isNothing (preimage
                  (coalizingFunctorHom
                    witness witness doublingStable)
                  element))
              assert "the coalition dominion rank round-trips"
                (unrank valueCoalition (rank valueCoalition element)
                  == Just element)
              coalizingFunctorIdentity witness element `seq`
                coalizingFunctorComposition
                  witness witness witness stable stable element `seq`
                    assert "the Coalizing functor preserves composition"
                      (coalitionElementRank
                        (applyInsertion composed element) == 7)

testDomanialInclusion :: IO ()
testDomanialInclusion = do
  let naturals = dominion id Just (const ())
      successor :: Natural -> Natural
      successor = (+ 1)
      twice :: Natural -> Natural
      twice = (* 2)
      included = dominionAtlas naturals
      includedWitness = atlasWitness included
      (fromCoalition, intoCoalition) = coaDomIncIso naturals
      seven = applyInsertion intoCoalition 7

  assert "Coa (DomInc X) is isomorphic to X"
    (applyInsertion fromCoalition seven == 7)
  assert "the Coa-DomInc counit has a total inverse"
    (preimage fromCoalition 7 == Just seven)
  assert "the Coa-DomInc unit has a total inverse"
    (preimage intoCoalition seven == Just 7)

  coaDomIncIsoLeftInverse naturals seven `seq`
    coaDomIncIsoRightInverse naturals 7 `seq` pure ()

  let includedIdentity =
        dominionMap naturals naturals
          (identityInsertion :: DomanialInsertion Natural Natural)
      adjointArrow =
        domIncCoaHomEquivTo naturals includedWitness includedIdentity
      restoredArrow =
        domIncCoaHomEquivFrom naturals includedWitness adjointArrow
      mappedSeven = applyInsertion adjointArrow 7

  assert "the forward adjunction map lands in the target coalition"
    (applyInsertion fromCoalition mappedSeven == 7)
  assert "the forward adjunction map retains its inverse witness"
    (preimage adjointArrow mappedSeven == Just 7)

  withPageElement (atlasOriginCell included) $ \origin ->
    case unrank (atlasDataAt included origin) 7 of
      Nothing -> fail "Domanial Inclusion lost its constant cell datum"
      Just sourceDatum ->
        withAtlasMorphismImage
          (mapStableAtlasTransversalData
            includedWitness restoredArrow origin) $ \_ component -> do
              let restoredDatum = applyInsertion component sourceDatum
              assert "the two adjunction maps are inverse on data"
                (dominionCellDataValue restoredDatum == 7)
              assert "the reconstructed component inverse is total on images"
                (preimage component restoredDatum == Just sourceDatum)

              let observe datum = dominionCellDataValue datum + 1
              domIncCoaHomEquivLeftInverse observe sourceDatum `seq`
                domIncCoaHomEquivRightInverse successor 7 `seq`
                  domIncCoaHomEquivNaturalityLeft
                    successor observe 7 `seq`
                      domIncCoaHomEquivNaturalityRight
                        observe twice 7 `seq` pure ()

  let double =
        domanialInsertion
          twice
          (\value ->
            if even value then Just (value `div` 2) else Nothing)
          (const ())
      increment =
        domanialInsertion
          successor
          (\value ->
            if value == 0 then Nothing else Just (value - 1))
          (const ())
      direct = dominionMap naturals naturals
        (composeInsertions increment double)
      staged =
        composeStableAtlasTransversals
          (dominionMap naturals naturals increment)
          (dominionMap naturals naturals double)

  withPageElement (atlasOriginCell included) $ \origin ->
    case unrank (atlasDataAt included origin) 4 of
      Nothing -> fail "Domanial Inclusion failed to decode a source datum"
      Just sourceDatum ->
        withAtlasMorphismImage
          (mapStableAtlasTransversalData includedWitness direct origin) $
            \_ directComponent ->
              withAtlasMorphismImage
                (mapStableAtlasTransversalData includedWitness staged origin) $
                  \_ stagedComponent -> do
                    assert "the Domanial Inclusion preserves composition"
                      ( dominionCellDataValue
                          (applyInsertion directComponent sourceDatum)
                        == dominionCellDataValue
                          (applyInsertion stagedComponent sourceDatum)
                      )
                    domanialInclusionFunctorIdentity sourceDatum `seq`
                      domanialInclusionFunctorComposition
                        twice successor sourceDatum `seq` pure ()
