{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE RoleAnnotations #-}

-- | Integers represented by a natural and a complement flag.
--
-- The complemented natural @n@ denotes @-n-1@.  This is the usual infinite
-- two's-complement convention: for example, direct @5@ denotes @5@ and
-- complemented @5@ denotes @-6@.  The pair is embedded in @Nat x 2@ by
-- assigning the codes @2*n@ and @2*n+1@ respectively.
module EllipsisInteger
  ( EllipsisInteger
  , IntegerComplement (..)
  , ellipsisInteger
  , ellipsisIntegerFromComplement
  , ellipsisIntegerValue
  , ellipsisIntegerNatural
  , ellipsisIntegerComplement
  , ellipsisIntegerCode
  , integerFromComplement
  , integerCode
  , integerAtCode
  ) where

import Numeric.Natural (Natural)

data IntegerComplement = Direct | Complemented
  deriving (Eq, Show)

type role EllipsisInteger nominal
data EllipsisInteger scope = EllipsisInteger
  { ellipsisIntegerNatural :: Natural
  , ellipsisIntegerComplement :: IntegerComplement
  }
  deriving (Eq, Show)

ellipsisInteger
  :: Integer
  -> (forall scope. EllipsisInteger scope -> result)
  -> result
ellipsisInteger value useInteger =
  case value of
    _ | value >= 0 ->
        useInteger (EllipsisInteger (fromInteger value) Direct)
      | otherwise ->
        useInteger
          (EllipsisInteger (fromInteger (negate value - 1)) Complemented)

ellipsisIntegerFromComplement
  :: Natural
  -> IntegerComplement
  -> (forall scope. EllipsisInteger scope -> result)
  -> result
ellipsisIntegerFromComplement natural complement useInteger =
  useInteger (EllipsisInteger natural complement)

ellipsisIntegerValue :: EllipsisInteger scope -> Integer
ellipsisIntegerValue (EllipsisInteger natural complement) =
  integerFromComplement natural complement

ellipsisIntegerCode :: EllipsisInteger scope -> Natural
ellipsisIntegerCode (EllipsisInteger natural complement) =
  integerCode natural complement

integerFromComplement :: Natural -> IntegerComplement -> Integer
integerFromComplement natural Direct = toInteger natural
integerFromComplement natural Complemented = negate (toInteger natural) - 1

integerCode :: Natural -> IntegerComplement -> Natural
integerCode natural Direct = 2 * natural
integerCode natural Complemented = 2 * natural + 1

integerAtCode :: Natural -> Integer
integerAtCode code =
  integerFromComplement
    (code `div` 2)
    (if even code then Direct else Complemented)
