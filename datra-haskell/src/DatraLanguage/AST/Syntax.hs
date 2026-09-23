{-# LANGUAGE PostfixOperators #-}

-- | Symbolic Haskell constructors for Datra ASTs.
module DatraLanguage.AST.Syntax
  ( natural
  , identifierType
  , assignment
  , asciiString
  , nothing
  , stringTemplate
  , stringType
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
  , boolean
  , booleanType
  , eitherType
  , optional
  , conditional
  , conditionalWithoutElse
  , subfederation
  , equal
  , and
  , or
  , not
  , extract
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
  , StringTemplatePart
  )
import Numeric.Natural (Natural)
import Prelude hiding (and, not, or, (+), (-), (*), (^))

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

nothing :: Expression
nothing = NothingLiteral

stringTemplate :: [StringTemplatePart Expression] -> Expression
stringTemplate = StringTemplate

stringType :: Expression
stringType = StringType

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

boolean :: Bool -> Expression
boolean = BooleanLiteral

booleanType :: Expression
booleanType = BooleanType

eitherType :: Expression -> Expression -> Expression
eitherType = EitherType

optional :: Expression -> Expression
optional = OptionalType

conditional :: Expression -> Expression -> Expression -> Expression
conditional = Conditional

conditionalWithoutElse :: Expression -> Expression -> Expression
conditionalWithoutElse condition consequent =
  Conditional condition consequent (AtlasMap [])

equal :: Expression -> Expression -> Expression
equal = Equality

subfederation :: Expression -> Expression -> Expression
subfederation = Subfederation

and :: Expression -> Expression -> Expression
and = BooleanAnd

or :: Expression -> Expression -> Expression
or = BooleanOr

not :: Expression -> Expression
not = BooleanNot

extract :: Expression -> Expression
extract = Extract

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
