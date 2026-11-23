module DatraTypes.Lookup
  ( lookupKeyFieldName
  , lookupValueFieldName
  , lookupKeyFieldPosition
  , lookupValueFieldPosition
  ) where

import DatraLanguage.AST (SimpleIdentifierString (SimpleIdentifierString))
import DatraLanguage.AST.Reserved
  ( LookupField (LookupKeyField, LookupValueField)
  , lookupFieldIdentifierString
  )
import Numeric.Natural (Natural)

lookupKeyFieldName :: SimpleIdentifierString
lookupKeyFieldName =
  SimpleIdentifierString (lookupFieldIdentifierString LookupKeyField)

lookupValueFieldName :: SimpleIdentifierString
lookupValueFieldName =
  SimpleIdentifierString (lookupFieldIdentifierString LookupValueField)

lookupKeyFieldPosition :: Natural
lookupKeyFieldPosition = 0

lookupValueFieldPosition :: Natural
lookupValueFieldPosition = 1
