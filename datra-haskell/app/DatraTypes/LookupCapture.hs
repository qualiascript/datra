module DatraTypes.LookupCapture
  ( LookupCapture (..)
  ) where

import DatraTypes (InterpretedValue)
import Numeric.Natural (Natural)

data LookupCapture = LookupCapture
  { captureIndex :: Natural
  , captureSchema :: InterpretedValue
  , captureBound :: InterpretedValue
  }
