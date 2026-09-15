{-# LANGUAGE CPP #-}
#include "../../../LiquidPlugin.h"
{-@ LIQUID "--ple" @-}
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--prune-unsorted" @-}

-- | Hidden chain representation and proof-bearing operations.
module Chain.Internal
  ( Chain
  , ChainIndex (..)
  , chainOrdinalLT
  , positionMatches
  , chainOrderType
  , chainPosition
  , chainLookup
  , chainIndex
  , chainIndexOf
  , chainObjectAt
  , chainPositionBelow
  , chainPositionInjective
  , chainPositionSurjective
  , chain
  , compareInChain
  , hasArrow
  , spine
  ) where

import Numeric.Natural (Natural)

import DatraOrdinal.Internal
  ( Ordinal(..)
  , canonicalCoefficients
  , ordinalLT
  )
import DatraOrdinal.LiquidInternal (ordinalLongNotBelowOmega)

{-@ embed Natural as int @-}
{-@ invariant { value:Natural | value >= 0 } @-}

{-@ reflect chainOrdinalLT @-}
{-@
chainOrdinalLT
  :: left:Ordinal
  -> right:Ordinal
  -> { resultValue:Bool | resultValue == ordinalLT left right }
@-}
chainOrdinalLT :: Ordinal -> Ordinal -> Bool
chainOrdinalLT left right = ordinalLT left right

{-@ reflect chainListLength @-}
{-@ chainListLength :: values:[a] -> { lengthValue:Int | lengthValue == len values } @-}
chainListLength :: [a] -> Int
chainListLength [] = 0
chainListLength (_ : values) = 1 + chainListLength values

{-@ reflect positionMatches @-}
positionMatches :: (object -> Ordinal) -> Ordinal -> Maybe object -> Bool
positionMatches _ _ Nothing = False
positionMatches position expected (Just object) = position object == expected

{-@
data Chain object = Chain
  { chainOrderType :: Ordinal
  , chainPosition :: object -> Ordinal
  , chainLookup :: Ordinal -> Maybe object
  , chainPositionBelow :: objectValue:object ->
      { proof:() |
          chainOrdinalLT (chainPosition objectValue) chainOrderType }
  , chainPositionInjective :: left:object -> right:object ->
      { proof:() |
          chainPosition left == chainPosition right => left == right }
  , chainPositionSurjective :: position:Ordinal ->
      { proof:() |
          chainOrdinalLT position chainOrderType
            => positionMatches chainPosition position
                 (chainLookup position) }
  }
@-}
data Chain object = Chain
  { chainOrderType :: Ordinal
  , chainPosition :: object -> Ordinal
  , chainLookup :: Ordinal -> Maybe object
  , chainPositionBelow :: object -> ()
  , chainPositionInjective :: object -> object -> ()
  , chainPositionSurjective :: Ordinal -> ()
  }

-- | An ordinal certified to index an object of a chain.  Its constructor is
-- hidden by the public module; retaining the object makes elimination total.
{-@
data ChainIndex object = ChainIndex
  { chainIndexOrderType :: Ordinal
  , chainIndexPosition :: {
      position:Ordinal |
      chainOrdinalLT position chainIndexOrderType }
  , chainIndexObject :: object
  }
@-}
data ChainIndex object = ChainIndex
  { chainIndexOrderType :: Ordinal
  , chainIndexPosition :: Ordinal
  , chainIndexObject :: object
  }
  deriving (Eq, Show)

-- | Construct a chain from its indexing equivalence and proofs.
{-@
chain
  :: orderType:Ordinal
  -> position:(object -> Ordinal)
  -> objectAt:(Ordinal -> Maybe object)
  -> (objectValue:object ->
       { proof:() | chainOrdinalLT (position objectValue) orderType })
  -> (left:object -> right:object ->
       { proof:() | position left == position right => left == right })
  -> (ordinalValue:Ordinal ->
       { proof:() |
           chainOrdinalLT ordinalValue orderType
             => positionMatches position ordinalValue
                  (objectAt ordinalValue) })
  -> Chain object
@-}
chain
  :: Ordinal
  -> (object -> Ordinal)
  -> (Ordinal -> Maybe object)
  -> (object -> ())
  -> (object -> object -> ())
  -> (Ordinal -> ())
  -> Chain object
chain = Chain

-- | Refine an arbitrary ordinal to an in-bounds chain index.
{-@
chainIndex
  :: valueChain:Chain object
  -> position:Ordinal
  -> Maybe ({ index:ChainIndex object |
       chainIndexOrderType index == chainOrderType valueChain
       && chainIndexPosition index == position
       && chainOrdinalLT position (chainOrderType valueChain)
       && chainPosition valueChain (chainIndexObject index) == position })
@-}
chainIndex :: Chain object -> Ordinal -> Maybe (ChainIndex object)
chainIndex valueChain position
  | not (chainOrdinalLT position (chainOrderType valueChain)) = Nothing
  | otherwise = case chainPositionSurjective valueChain position of
      () -> case chainLookup valueChain position of
        Nothing -> Nothing
        Just object ->
          Just (ChainIndex (chainOrderType valueChain) position object)

-- | The certified index occupied by an existing chain object.
{-@
chainIndexOf
  :: valueChain:Chain object
  -> objectValue:object
  -> { index:ChainIndex object |
       chainIndexOrderType index == chainOrderType valueChain
       && chainIndexPosition index == chainPosition valueChain objectValue
       && chainIndexObject index == objectValue
       && chainOrdinalLT
            (chainIndexPosition index)
            (chainOrderType valueChain) }
@-}
chainIndexOf :: Chain object -> object -> ChainIndex object
chainIndexOf valueChain objectValue =
  chainPositionBelow valueChain objectValue `seq`
    ChainIndex
      (chainOrderType valueChain)
      (chainPosition valueChain objectValue)
      objectValue

-- | Retrieve the object at a certified chain index.
chainObjectAt :: ChainIndex object -> object
chainObjectAt = chainIndexObject

compareInChain :: Chain object -> object -> object -> Ordering
compareInChain valueChain left right =
  compare (chainPosition valueChain left) (chainPosition valueChain right)

hasArrow :: Chain object -> object -> object -> Bool
hasArrow valueChain source target =
  compareInChain valueChain source target /= GT

spine :: Chain Natural
spine =
  Chain
    spineOmega
    spineOrdinal
    spineNatural
    spinePositionBelow
    spinePositionInjective
    spinePositionSurjective

{-@
spinePositionBelow
  :: value:Natural
  -> { proof:() |
       chainOrdinalLT (spineOrdinal value) spineOmega }
@-}
spinePositionBelow :: Natural -> ()
spinePositionBelow value
  | value > 0 = ()
  | otherwise = ()

{-@
spinePositionInjective
  :: left:Natural
  -> right:Natural
  -> { proof:() |
       spineOrdinal left == spineOrdinal right => left == right }
@-}
spinePositionInjective :: Natural -> Natural -> ()
spinePositionInjective left right
  | left == right = ()
  | left > 0 && right > 0 =
      spineOrdinal left `seq` spineOrdinal right `seq` ()
  | left > 0 = spineOrdinal left `seq` spineOrdinal right `seq` ()
  | right > 0 = spineOrdinal left `seq` spineOrdinal right `seq` ()
  | otherwise = spineOrdinal left `seq` spineOrdinal right `seq` ()

{-@
spinePositionSurjective
  :: position:Ordinal
  -> { proof:() |
       chainOrdinalLT position spineOmega
         => positionMatches spineOrdinal position
              (spineNatural position) }
@-}
spinePositionSurjective :: Ordinal -> ()
spinePositionSurjective position@(Ordinal []) =
  spineNatural position `seq` spineOrdinal 0 `seq` ()
spinePositionSurjective position@(Ordinal [value]) =
  spineNatural position `seq` spineOrdinal value `seq` ()
spinePositionSurjective (Ordinal coefficients@(_ : _ : _))
  | canonicalCoefficients coefficients =
      spineListAtLeastTwo coefficients `seq`
        spineLongNotBelow coefficients
  | otherwise = ()

{-@ inline spineOmega @-}
spineOmega :: Ordinal
spineOmega = Ordinal [1, 0]

{-@ reflect spineOrdinal @-}
{-@
spineOrdinal
  :: value:Natural
  -> { position:Ordinal |
       chainOrdinalLT position spineOmega
       && spineNatural position == Just value }
@-}
spineOrdinal :: Natural -> Ordinal
spineOrdinal value
  | value > 0 = Ordinal [value]
  | otherwise = Ordinal []

{-@ reflect spineNatural @-}
{-@
spineNatural
  :: position:Ordinal
  -> { result:Maybe Natural |
       chainOrdinalLT position spineOmega
         => positionMatches spineOrdinal position result }
@-}
spineNatural :: Ordinal -> Maybe Natural
spineNatural (Ordinal []) = Just 0
spineNatural (Ordinal [value]) = Just value
spineNatural (Ordinal coefficients@(_ : _ : _))
  | canonicalCoefficients coefficients =
      spineListAtLeastTwo coefficients `seq`
        spineLongNotBelow coefficients `seq` Nothing
  | otherwise = Nothing

{-@
spineLongNotBelow
  :: coefficients:{ [Natural] |
       chainListLength coefficients >= 2
       && canonicalCoefficients coefficients }
  -> { proof:() |
       not (chainOrdinalLT (Ordinal coefficients) spineOmega) }
@-}
{-@ ple spineLongNotBelow @-}
spineLongNotBelow :: [Natural] -> ()
spineLongNotBelow coefficients@(_ : _ : _) =
  ordinalLongNotBelowOmega coefficients
spineLongNotBelow _ = ()

{-@
spineListAtLeastTwo
  :: coefficients:{ [Natural] | len coefficients >= 2 }
  -> { proof:() | chainListLength coefficients >= 2 }
@-}
spineListAtLeastTwo :: [Natural] -> ()
spineListAtLeastTwo coefficients@(_ : _ : _) =
  chainListLength coefficients `seq` ()
spineListAtLeastTwo _ = ()
