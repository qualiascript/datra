module Main (main) where

import Atlas
import Chain
import Consolidation
import qualified Control.Category as Category
import DatraOrdinal
import DomanialInsertion
import Dominion
import FiniteDominion
import Folio
import PageElements
import Pagination
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
  testPageElements
  testPagination
  testAtlas

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
                          composedMorphism =
                            atlasCategoryCompose atlasCategory
                              (atlasCategoryIdentity atlasCategory targetAtlas)
                              valueMorphism
                          rightIdentityMorphism =
                            atlasCategoryCompose atlasCategory
                              valueMorphism
                              (atlasCategoryIdentity atlasCategory valueAtlas)
                          associatedLeft =
                            atlasCategoryCompose atlasCategory
                              (atlasCategoryIdentity atlasCategory targetAtlas)
                              rightIdentityMorphism
                          associatedRight =
                            atlasCategoryCompose atlasCategory
                              composedMorphism
                              (atlasCategoryIdentity atlasCategory valueAtlas)
                          valueHom = atlasHom valueMorphism
                          leftHom = Category.id Category.. valueHom
                          rightHom = valueHom Category.. Category.id
                          associatedLeftHom =
                            Category.id Category.. rightHom
                          associatedRightHom =
                            leftHom Category.. Category.id
                      withPageElement
                        (mapAtlasMorphismElement valueMorphism padded) $
                          \mapped ->
                            assert
                              "atlas morphisms normalize their page action"
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
                        (mapAtlasMorphismElement composedMorphism padded) $
                          \mapped ->
                            assert
                              "atlas category left identity retains coherence"
                              (pageElementPage mapped == 0)
                      withPageElement
                        (mapAtlasMorphismElement rightIdentityMorphism padded) $
                          \mapped ->
                            assert
                              "atlas category right identity retains coherence"
                              (pageElementPage mapped == 0)
                      withAtlasMorphismImage
                        (mapAtlasMorphismData associatedLeft padded) $
                          \leftPage leftInsertion ->
                            withAtlasMorphismImage
                              (mapAtlasMorphismData associatedRight padded) $
                                \rightPage rightInsertion ->
                                  case
                                    ( applyInsertion leftInsertion
                                        (TestCellData 19)
                                    , applyInsertion rightInsertion
                                        (TestCellData 19)
                                    ) of
                                    (TestCellData left, TestCellData right) ->
                                      assert
                                        "atlas category composition is associative pointwise"
                                        ( pageElementPage leftPage
                                            == pageElementPage rightPage
                                          && left == right
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
            _ -> fail "test setup failed: expected atlas elements"
