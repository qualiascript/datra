-- | Temporary host definitions for reserved identifiers that do not yet come
-- from a Datra standard library. Parsers consume this table generically; the
-- remaining reserved identifiers are implemented as parser special forms.
module DatraLanguage.AST.Reserved.Bootstrap
  ( reservedSymbolReplacements
  ) where

import Data.Maybe (mapMaybe)
import DatraLanguage.AST
  ( Expression
      ( BooleanLiteral
      , BooleanType
      , IntegerType
      , IdentifierValueType
      , NaturalType
      , NothingLiteral
      , StringType
      )
  )
import DatraLanguage.AST.Reserved
  ( ReservedSymbol (..)
  , reservedSymbols
  )

-- | Current context bindings supplied by the host. A future standard-library
-- loader can replace this table without teaching the parser individual names.
reservedSymbolReplacements :: [(ReservedSymbol, Expression)]
reservedSymbolReplacements = mapMaybe replacement reservedSymbols
  where
    replacement BooleanTypeSymbol = Just (BooleanTypeSymbol, BooleanType)
    replacement StringTypeSymbol = Just (StringTypeSymbol, StringType)
    replacement IdentifierValueTypeSymbol =
      Just (IdentifierValueTypeSymbol, IdentifierValueType)
    replacement IntegerTypeSymbol = Just (IntegerTypeSymbol, IntegerType)
    replacement NaturalTypeSymbol = Just (NaturalTypeSymbol, NaturalType)
    replacement FalseSymbol = Just (FalseSymbol, BooleanLiteral False)
    replacement TrueSymbol = Just (TrueSymbol, BooleanLiteral True)
    replacement NothingSymbol = Just (NothingSymbol, NothingLiteral)
    replacement IfSymbol = Nothing
    replacement RangeSymbol = Nothing
    replacement FromSymbol = Nothing
