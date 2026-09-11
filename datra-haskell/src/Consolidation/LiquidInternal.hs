{-# LANGUAGE CPP #-}
#include "../LiquidPlugin.h"
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}

-- | LiquidHaskell-verified consolidation representation, operations, and
-- carrier transport.
module Consolidation.LiquidInternal
  ( Consolidation (..)
  , consolidationMonotone
  , consolidation
  , identityConsolidation
  , identityConsolidationApply
  , identityMap
  , identityMonotone
  , identityPointSurjective
  , composeConsolidations
  , composeConsolidationsApply
  , composeFunctions
  , composeMonotone
  , composePointSurjective
  , Coconsolidation (..)
  , op
  , unop
  , composeCoconsolidations
  , coconsolidationIdentity
  , coconsolidationComposition
  , ConsolidationTransport (..)
  , consolidationTransport
  , consolidationTransportIdentity
  , consolidationTransportComposition
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
-- The constructor is used directly so reflection can expose the carrier map
-- while LiquidHaskell checks the abstract order refinements.
{-@
identityConsolidation
  :: forall <objectLe :: object -> object -> Bool>.
     Consolidation <objectLe, objectLe> object object
@-}
{-@ reflect identityConsolidation @-}
identityConsolidation :: Consolidation object object
identityConsolidation =
  Consolidation
    identityMap
    identityMap
    identityMonotone
    identityPointSurjective

-- | The identity consolidation's carrier map is the identity function.
{-@
identityConsolidationApply
  :: value:object ->
     { proof:() | applyConsolidation identityConsolidation value == value }
@-}
identityConsolidationApply :: object -> ()
identityConsolidationApply _ = ()

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
{-@ reflect identityMonotone @-}
identityMonotone :: object -> object -> object -> object
identityMonotone _ _ right = right

{-@
identityPointSurjective
  :: value:object ->
     { proof:() | identityMap (identityMap value) == value }
@-}
{-@ reflect identityPointSurjective @-}
identityPointSurjective :: object -> ()
identityPointSurjective _ = ()

-- | Compose consolidations in categorical order.
{-@ reflect composeConsolidations @-}
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
  Consolidation
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

-- | Consolidation composition composes the underlying carrier maps.
{-@
composeConsolidationsApply
  :: second:Consolidation middle target
  -> first:Consolidation source middle
  -> value:source
  -> { proof:() |
       applyConsolidation (composeConsolidations second first) value
         == applyConsolidation second (applyConsolidation first value) }
@-}
composeConsolidationsApply
  :: Consolidation middle target
  -> Consolidation source middle
  -> source
  -> ()
composeConsolidationsApply
  (Consolidation {})
  (Consolidation {})
  _ = ()

-- | The opposite category of consolidations (@CoCon@ in @datra.lean@).
{-@
data Coconsolidation source target = Coconsolidation
  { getOppositeConsolidation :: Consolidation target source }
@-}
data Coconsolidation source target = Coconsolidation
  { getOppositeConsolidation :: Consolidation target source
  }

-- | Reverse the categorical direction of a consolidation.
{-@ reflect op @-}
op :: Consolidation source target -> Coconsolidation target source
op = Coconsolidation

-- | Recover the underlying consolidation.
{-@ reflect unop @-}
unop :: Coconsolidation target source -> Consolidation source target
unop (Coconsolidation value) = value

-- | Compose coconsolidations in categorical order.
{-@ reflect composeCoconsolidations @-}
composeCoconsolidations
  :: Coconsolidation middle target
  -> Coconsolidation source middle
  -> Coconsolidation source target
composeCoconsolidations second first =
  op (composeConsolidations (unop first) (unop second))

-- | The underlying map of the identity coconsolidation is identity.
{-@
coconsolidationIdentity
  :: value:object ->
     { proof:() |
       applyConsolidation (unop (op identityConsolidation)) value
         == value }
@-}
coconsolidationIdentity :: object -> ()
coconsolidationIdentity = identityConsolidationApply

-- | Coconsolidation composition coheres with reversed carrier-map
-- composition.
{-@
coconsolidationComposition
  :: second:Coconsolidation middle target
  -> first:Coconsolidation source middle
  -> value:target
  -> { proof:() |
       applyConsolidation
         (unop (composeCoconsolidations second first)) value
         == applyConsolidation (unop first)
              (applyConsolidation (unop second) value) }
@-}
coconsolidationComposition
  :: Coconsolidation middle target
  -> Coconsolidation source middle
  -> target
  -> ()
coconsolidationComposition second first =
  composeConsolidationsApply (unop first) (unop second)

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
{-@ reflect composeMonotone @-}
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
{-@ reflect composePointSurjective @-}
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

-- | A morphism in the target of the consolidation-transport functor.
--
-- Haskell already represents the object part of @Tra : Con -> Type@ with the
-- carrier type parameters @source@ and @target@. This wrapper makes its
-- morphism part explicit without discarding those types.
{-@
data ConsolidationTransport source target = ConsolidationTransport
  { runConsolidationTransport :: source -> target }
@-}
data ConsolidationTransport source target = ConsolidationTransport
  { runConsolidationTransport :: source -> target
  }

-- | The morphism action of the consolidation-transport functor.
{-@ reflect consolidationTransport @-}
consolidationTransport
  :: Consolidation source target
  -> ConsolidationTransport source target
consolidationTransport value = ConsolidationTransport (applyConsolidation value)

-- | Consolidation transport preserves identity pointwise.
{-@
consolidationTransportIdentity
  :: value:object ->
     { proof:() |
       runConsolidationTransport (consolidationTransport identityConsolidation) value
         == value }
@-}
consolidationTransportIdentity :: object -> ()
consolidationTransportIdentity = identityConsolidationApply

-- | Consolidation transport preserves composition pointwise.
{-@
consolidationTransportComposition
  :: second:Consolidation middle target
  -> first:Consolidation source middle
  -> value:source
  -> { proof:() |
       runConsolidationTransport
         (consolidationTransport (composeConsolidations second first)) value
         == runConsolidationTransport (consolidationTransport second)
              (runConsolidationTransport (consolidationTransport first) value) }
@-}
consolidationTransportComposition
  :: Consolidation middle target
  -> Consolidation source middle
  -> source
  -> ()
consolidationTransportComposition = composeConsolidationsApply
