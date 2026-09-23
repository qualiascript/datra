{-# LANGUAGE RankNTypes #-}

-- | The integer type, canonically written @Int@.
module IntegerType
  ( IntegerType
  , integerType
  ) where

import ValuedIntegerRange
  ( ValuedIntegerRange
  , valuedAllIntegers
  )

type IntegerType = ValuedIntegerRange

integerType
  :: (forall rangeScope federationScope.
       IntegerType rangeScope federationScope
       -> result)
  -> result
integerType = valuedAllIntegers
