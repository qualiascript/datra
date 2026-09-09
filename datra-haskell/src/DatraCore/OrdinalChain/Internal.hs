{-# OPTIONS_GHC -fplugin=LiquidHaskell #-}
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}

-- | The shared proof kernel for ordinals and chains. Keeping the ordinal
-- representation and every reflected chain predicate in this one module
-- avoids LiquidHaskell 0.9.4's cross-module reflection limitation.
module OrdinalChain.Internal
  ( Ordinal
  , ordinal
  , finiteOrdinal
  , omega
  , ordinalLT
  , addOrdinals
  , subtractOrdinal
  , naturalAtOrdinal
  , Chain
  , chainOrdinalLT
  , positionMatches
  , chainOrderType
  , chainPosition
  , chainObjectAt
  , chainPositionBelow
  , chainPositionInjective
  , chainPositionSurjective
  , chain
  , compareInChain
  , hasArrow
  , sumChains
  , spine
  ) where

import Numeric.Natural (Natural)

{-@ embed Natural as int @-}

-- | An ordinal strictly below omega^omega in canonical Cantor normal form.
-- The constructor never leaves this proof kernel.
newtype Ordinal = Ordinal
  { coefficients :: [Natural]
  }
  deriving (Eq, Show)

-- | Construct a canonical ordinal from descending coefficients.
ordinal :: [Natural] -> Ordinal
ordinal = Ordinal . dropWhile (== 0)

-- | Embed a natural number as a finite ordinal.
finiteOrdinal :: Natural -> Ordinal
finiteOrdinal value = ordinal [value]

-- | The first infinite ordinal.
omega :: Ordinal
omega = ordinal [1, 0]

instance Ord Ordinal where
  compare (Ordinal left) (Ordinal right) =
    compare (length left) (length right)
      <> compare left right

-- | A reflected strict comparison that agrees with the 'Ord' instance.
{-@ reflect ordinalLT @-}
ordinalLT :: Ordinal -> Ordinal -> Bool
ordinalLT (Ordinal left) (Ordinal right) =
  listLength left < listLength right
    || listLength left == listLength right && lexicographicLT left right

{-@ reflect listLength @-}
listLength :: [a] -> Int
listLength [] = 0
listLength (_ : values) = 1 + listLength values

{-@ reflect lexicographicLT @-}
lexicographicLT :: [Natural] -> [Natural] -> Bool
lexicographicLT [] _ = False
lexicographicLT _ [] = False
lexicographicLT (left : lefts) (right : rights)
  | left < right = True
  | left > right = False
  | otherwise = lexicographicLT lefts rights

-- | Ordinal addition. This is generally not commutative.
addOrdinals :: Ordinal -> Ordinal -> Ordinal
addOrdinals left (Ordinal []) = left
addOrdinals (Ordinal leftCoefficients)
  right@(Ordinal (rightLeadingCoefficient : rightLowerCoefficients))
  | length leftCoefficients < length rightCoefficients = right
  | otherwise = case matchingAndLowerLeftCoefficients of
      matchingLeftCoefficient : _ ->
        Ordinal
          (higherLeftCoefficients
            ++ (matchingLeftCoefficient + rightLeadingCoefficient)
              : rightLowerCoefficients)
      [] -> right
  where
    rightCoefficients = rightLeadingCoefficient : rightLowerCoefficients

    numberOfHigherLeftCoefficients =
      length leftCoefficients - length rightCoefficients

    (higherLeftCoefficients, matchingAndLowerLeftCoefficients) =
      splitAt numberOfHigherLeftCoefficients leftCoefficients

-- | Remove a left ordinal prefix when the value lies at or after it.
subtractOrdinal :: Ordinal -> Ordinal -> Maybe Ordinal
subtractOrdinal (Ordinal left) (Ordinal value)
  | listLength value < listLength left = Nothing
  | listLength value > listLength left = Just (Ordinal value)
  | otherwise = Ordinal <$> subtractCoefficients left value

subtractCoefficients
  :: [Natural]
  -> [Natural]
  -> Maybe [Natural]
subtractCoefficients [] [] = Just []
subtractCoefficients (left : lefts) (value : values)
  | value < left = Nothing
  | value == left = subtractCoefficients lefts values
  | otherwise = Just ((value - left) : values)
subtractCoefficients _ _ = Nothing

-- | Decode a finite ordinal as a natural number.
naturalAtOrdinal :: Ordinal -> Maybe Natural
naturalAtOrdinal (Ordinal []) = Just 0
naturalAtOrdinal (Ordinal [value]) = Just value
naturalAtOrdinal _ = Nothing

-- The alias and the reflected implementation it calls are deliberately local
-- to the same module, so LiquidHaskell can resolve the logical symbol.
{-@ reflect chainOrdinalLT @-}
chainOrdinalLT :: Ordinal -> Ordinal -> Bool
chainOrdinalLT = ordinalLT

{-@ reflect positionMatches @-}
positionMatches :: (object -> Ordinal) -> Ordinal -> Maybe object -> Bool
positionMatches _ _ Nothing = False
positionMatches position expected (Just object) = position object == expected

{-@
data Chain object = Chain
  { chainOrderType :: Ordinal
  , chainPosition :: object -> Ordinal
  , chainObjectAt :: Ordinal -> Maybe object
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
                 (chainObjectAt position) }
  }
@-}
data Chain object = Chain
  { chainOrderType :: Ordinal
  , chainPosition :: object -> Ordinal
  , chainObjectAt :: Ordinal -> Maybe object
  , chainPositionBelow :: object -> ()
  , chainPositionInjective :: object -> object -> ()
  , chainPositionSurjective :: Ordinal -> ()
  }

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

compareInChain :: Chain object -> object -> object -> Ordering
compareInChain valueChain left right =
  compare (chainPosition valueChain left) (chainPosition valueChain right)

hasArrow :: Chain object -> object -> object -> Bool
hasArrow valueChain source target =
  compareInChain valueChain source target /= GT

{-@ assume sumChains :: Chain left -> Chain right -> Chain (Either left right) @-}
{-@ ignore sumChains @-}
sumChains :: Chain left -> Chain right -> Chain (Either left right)
sumChains left right =
  Chain
    { chainOrderType =
        addOrdinals (chainOrderType left) (chainOrderType right)
    , chainPosition = positionInSum
    , chainObjectAt = objectInSum
    , chainPositionBelow = const ()
    , chainPositionInjective = \_ _ -> ()
    , chainPositionSurjective = const ()
    }
  where
    positionInSum (Left object) = chainPosition left object
    positionInSum (Right object) =
      addOrdinals (chainOrderType left) (chainPosition right object)

    objectInSum position
      | chainOrdinalLT position (chainOrderType left) =
          Left <$> chainObjectAt left position
      | otherwise =
          subtractOrdinal (chainOrderType left) position
            >>= fmap Right . chainObjectAt right

{-@ assume spine :: Chain Natural @-}
{-@ ignore spine @-}
spine :: Chain Natural
spine =
  Chain
    omega
    finiteOrdinal
    naturalAtOrdinal
    (const ())
    (\_ _ -> ())
    (const ())
