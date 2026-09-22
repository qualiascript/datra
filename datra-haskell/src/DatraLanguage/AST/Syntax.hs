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
  , (+)
  , (*)
  , (^)
  , (<.>)
  , (<@>)
  , (<~>)
  ) where

import DatraLanguage.AST (Expression (..), Identifier (Identifier))
import Numeric.Natural (Natural)
import Prelude hiding ((+), (*), (^))

natural :: Natural -> Expression
natural = EllipsisNatural

identifierType :: String -> Expression -> Expression
identifierType name typeExpression =
  IdentifierOperation (Identifier name) typeExpression Nothing

assignment :: String -> Expression -> Expression -> Expression
assignment name typeExpression assignedExpression =
  IdentifierOperation
    (Identifier name)
    typeExpression
    (Just assignedExpression)

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

infixl 6 +

(+) :: Expression -> Expression -> Expression
(+) = Addition

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

infixl 4 <~>

(<~>) :: Expression -> Expression -> Expression
(<~>) = MapSpecification
