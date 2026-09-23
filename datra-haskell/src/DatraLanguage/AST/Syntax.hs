{-# LANGUAGE PostfixOperators #-}

-- | Symbolic Haskell constructors for Datra ASTs.
module DatraLanguage.AST.Syntax
  ( natural
  , identifierType
  , assignment
  , asciiString
  , emptyMap
  , (...)
  , (<:>)
  , (<+>)
  , (<..>)
  , (..+)
  , (..-)
  , fromTo
  , fromUpwards
  , withinTo
  , withinUpwards
  , naturalType
  , integerFromTo
  , integerFromUpwards
  , integerFromDownwards
  , integerWithinTo
  , integerWithinUpwards
  , integerWithinDownwards
  , integerType
  , minus
  , (-)
  , (+)
  , (*)
  , (^)
  , (<.>)
  , (<@>)
  , (~>)
  ) where

import DatraLanguage.AST
  ( Expression (..)
  , IdentifierString (IdentifierString)
  )
import Numeric.Natural (Natural)
import Prelude hiding ((+), (-), (*), (^))

natural :: Natural -> Expression
natural = EllipsisNatural

identifierType :: String -> Expression -> Expression
identifierType identifierString typeAnnotation =
  IdentifierOperation
    (IdentifierString identifierString)
    typeAnnotation
    Nothing

assignment :: String -> Expression -> Expression -> Expression
assignment identifierString typeAnnotation givenValue =
  IdentifierOperation
    (IdentifierString identifierString)
    typeAnnotation
    (Just givenValue)

asciiString :: String -> Expression
asciiString = AsciiStringLiteral

emptyMap :: Expression
emptyMap = AtlasMap []

(...) :: Expression
(...) = EllipsisLiteral

infixr 7 <:>

(<:>) :: Expression -> Expression -> Expression
left <:> right = MapSequence (sequenceMembers left <> sequenceMembers right)
  where
    sequenceMembers (MapSequence members) = members
    sequenceMembers expressionValue = [expressionValue]

infix 6 <+>

(<+>) :: Expression -> Expression -> Expression
(<+>) = MapExpansion

infix 5 <..>

(<..>) :: Expression -> Expression -> Expression
(<..>) = SuperEllipsisRange

infixl 5 ..+, ..-

(..+) :: Expression -> Expression
(..+) = SuperEllipsisRangePlus

(..-) :: Expression -> Expression
(..-) = SuperEllipsisRangeMinus

fromTo :: Natural -> Natural -> Expression
fromTo = NaturalRange

fromUpwards :: Natural -> Expression
fromUpwards = NaturalRangeUpwards

withinTo :: Natural -> Natural -> Expression
withinTo = ValuedNaturalRange

withinUpwards :: Natural -> Expression
withinUpwards = ValuedNaturalRangeUpwards

naturalType :: Expression
naturalType = NaturalType

integerFromTo :: Integer -> Integer -> Expression
integerFromTo = IntegerRange

integerFromUpwards :: Integer -> Expression
integerFromUpwards = IntegerRangeUpwards

integerFromDownwards :: Integer -> Expression
integerFromDownwards = IntegerRangeDownwards

integerWithinTo :: Integer -> Integer -> Expression
integerWithinTo = ValuedIntegerRange

integerWithinUpwards :: Integer -> Expression
integerWithinUpwards = ValuedIntegerRangeUpwards

integerWithinDownwards :: Integer -> Expression
integerWithinDownwards = ValuedIntegerRangeDownwards

integerType :: Expression
integerType = IntegerType

minus :: Expression -> Expression
minus = Minus

infixl 6 +

(+) :: Expression -> Expression -> Expression
(+) = Addition

infixl 6 -

(-) :: Expression -> Expression -> Expression
(-) = Subtraction

infixl 7 *

(*) :: Expression -> Expression -> Expression
(*) = Multiplication

infixr 8 ^

(^) :: Expression -> Expression -> Expression
(^) = Exponentiation

infixr 7 <.>

(<.>) :: Expression -> Expression -> Expression
(<.>) = MapConcatenation

infixl 8 <@>

(<@>) :: Expression -> Expression -> Expression
(<@>) = MapAccess

infixl 4 ~>

(~>) :: Expression -> Expression -> Expression
(~>) = MapSpecification
