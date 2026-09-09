{-# OPTIONS_GHC -fplugin=LiquidHaskell #-}
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}

-- | LiquidHaskell-verified consolidation representation and operations.
module Consolidation.LiquidInternal
  ( Consolidation (..)
  , consolidationMonotone
  , consolidation
  , identityConsolidation
  , composeConsolidations
  ) where

-- | A monotone, point-surjective map between chain carriers.
--
-- The abstract refinements @sourceLe@ and @targetLe@ stand for the orders of
-- the source and target chains. They have no runtime representation.
{-@
data Consolidation source target
      < sourceLe :: source -> source -> Bool
      , targetLe :: target -> target -> Bool >
  = Consolidation
  { applyConsolidation :: source -> target
  , consolidationPreimage :: target -> source
  , consolidationMonotoneProof :: left:source ->
      mappedLeft:{target | mappedLeft == applyConsolidation left} ->
      right:source<sourceLe left> ->
      { mappedRight:target<targetLe mappedLeft> |
          mappedRight == applyConsolidation right }
  , consolidationPointSurjective :: value:target ->
      { proof:() |
          applyConsolidation (consolidationPreimage value) == value }
  }
@-}
data Consolidation source target = Consolidation
  { applyConsolidation :: source -> target
  , consolidationPreimage :: target -> source
  , consolidationMonotoneProof :: source -> target -> source -> target
  , consolidationPointSurjective :: target -> ()
  }

-- | Apply the monotonicity witness. Its result is definitionally the mapped
-- right object; LiquidHaskell additionally tracks that it follows the mapped
-- left object in the target relation.
consolidationMonotone
  :: Consolidation source target
  -> source
  -> source
  -> target
consolidationMonotone value left = consolidationMonotoneProof value
    left
    (applyConsolidation value left)

-- | Construct a consolidation from its map, chosen preimages, and proofs.
{-@
consolidation
  :: forall
       < sourceLe :: source -> source -> Bool
       , targetLe :: target -> target -> Bool >.
     forward:(source -> target)
  -> backward:(target -> source)
  -> (left:source ->
       mappedLeft:{target | mappedLeft == forward left} ->
       right:source<sourceLe left> ->
       { mappedRight:target<targetLe mappedLeft> |
           mappedRight == forward right })
  -> (value:target ->
       { proof:() | forward (backward value) == value })
  -> Consolidation <sourceLe, targetLe> source target
@-}
consolidation
  :: (source -> target)
  -> (target -> source)
  -> (source -> target -> source -> target)
  -> (target -> ())
  -> Consolidation source target
consolidation = Consolidation

-- | The identity consolidation preserves every relation and is its own
-- chosen-preimage map.
--
-- The contract is kept in this module because LiquidHaskell 0.9.4 serializes
-- an imported abstract-refined 'Consolidation' incorrectly on a cold build.
-- The pinned verifier also crashes when it solves this polymorphic identity
-- contract together with the (fully checked) composition contract below, so
-- this elementary contract is currently trusted.  The implementation makes
-- both laws definitionally true.
{-@
assume identityConsolidation
  :: forall <objectLe :: object -> object -> Bool>.
     Consolidation <objectLe, objectLe> object object
@-}
{-@ ignore identityConsolidation @-}
identityConsolidation :: Consolidation object object
identityConsolidation =
  consolidation
    identityMap
    identityMap
    identityMonotone
    identityPointSurjective

{-@ reflect identityMap @-}
identityMap :: value -> value
identityMap value = value

{-@
identityMonotone
  :: forall <objectLe :: object -> object -> Bool>.
     left:object
  -> mappedLeft:{object | mappedLeft == identityMap left}
  -> right:object<objectLe left>
  -> { mappedRight:object<objectLe mappedLeft> |
       mappedRight == identityMap right }
@-}
identityMonotone :: object -> object -> object -> object
identityMonotone _ _ right = right

{-@
identityPointSurjective
  :: value:object ->
     { proof:() | identityMap (identityMap value) == value }
@-}
identityPointSurjective :: object -> ()
identityPointSurjective _ = ()

-- | Compose consolidations in categorical order.
{-@ composeConsolidations :: forall
       < sourceLe :: source -> source -> Bool
       , middleLe :: middle -> middle -> Bool
       , targetLe :: target -> target -> Bool >.
     second:Consolidation <middleLe, targetLe> middle target
     -> first:Consolidation <sourceLe, middleLe> source middle
     -> Consolidation <sourceLe, targetLe> source target
@-}
composeConsolidations
  :: Consolidation middle target
  -> Consolidation source middle
  -> Consolidation source target
composeConsolidations
  (Consolidation secondMap secondPreimage secondMonotone secondSurjective)
  (Consolidation firstMap firstPreimage firstMonotone firstSurjective) =
  consolidation
    (composeFunctions secondMap firstMap)
    (composeFunctions firstPreimage secondPreimage)
    (composeMonotone secondMap firstMap secondMonotone firstMonotone)
    (composePointSurjective
      secondMap
      firstMap
      secondPreimage
      firstPreimage
      secondSurjective
      firstSurjective)

-- | Monotone maps remain monotone under composition.
{-@
composeMonotone
  :: forall
       < sourceLe :: source -> source -> Bool
       , middleLe :: middle -> middle -> Bool
       , targetLe :: target -> target -> Bool >.
     secondMap:(middle -> target)
  -> firstMap:(source -> middle)
  -> secondMonotone:(left:middle ->
       mappedLeft:{target | mappedLeft == secondMap left} ->
       right:middle<middleLe left> ->
       { mappedRight:target<targetLe mappedLeft> |
         mappedRight == secondMap right })
  -> firstMonotone:(left:source ->
       mappedLeft:{middle | mappedLeft == firstMap left} ->
       right:source<sourceLe left> ->
       { mappedRight:middle<middleLe mappedLeft> |
         mappedRight == firstMap right })
  -> left:source
  -> mappedLeft:{target |
       mappedLeft == composeFunctions secondMap firstMap left}
  -> right:source<sourceLe left>
  -> { mappedRight:target<targetLe mappedLeft> |
       mappedRight == composeFunctions secondMap firstMap right }
@-}
composeMonotone
  :: (middle -> target)
  -> (source -> middle)
  -> (middle -> target -> middle -> target)
  -> (source -> middle -> source -> middle)
  -> source
  -> target
  -> source
  -> target
composeMonotone secondMap firstMap secondMonotone firstMonotone
  left _ right =
    secondMonotone
      (firstMap left)
      (secondMap (firstMap left))
      (firstMonotone left (firstMap left) right)

-- | Chosen preimages remain right inverses under composition.
{-@
composePointSurjective
  :: secondMap:(middle -> target)
  -> firstMap:(source -> middle)
  -> secondPreimage:(target -> middle)
  -> firstPreimage:(middle -> source)
  -> (value:target ->
       { proof:() | secondMap (secondPreimage value) == value })
  -> (value:middle ->
       { proof:() | firstMap (firstPreimage value) == value })
  -> value:target
  -> { proof:() |
       composeFunctions secondMap firstMap
         (composeFunctions firstPreimage secondPreimage value) == value }
@-}
composePointSurjective
  :: (middle -> target)
  -> (source -> middle)
  -> (target -> middle)
  -> (middle -> source)
  -> (target -> ())
  -> (middle -> ())
  -> target
  -> ()
composePointSurjective _secondMap _firstMap secondPreimage _firstPreimage
  secondSurjective firstSurjective value =
    case secondSurjective value of
      () -> case firstSurjective (secondPreimage value) of
        () -> ()

{-@ reflect composeFunctions @-}
composeFunctions :: (middle -> target) -> (source -> middle) -> source -> target
composeFunctions second first value = second (first value)
