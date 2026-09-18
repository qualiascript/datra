{-# LANGUAGE PostfixOperators #-}

-- | Symbolic Haskell constructors for Datra ASTs.
module DatraLanguage.AST.Syntax
  ( natural
  , emptyMap
  , (...)
  , (<:>)
  , (<+>)
  , (<..>)
  , (..+)
  , (..-)
  , (+)
  , (*)
  , (^)
  , (<.>)
  , (<@>)
  ) where

import DatraLanguage.AST (Expression (..))
import Numeric.Natural (Natural)
import Prelude hiding ((+), (*), (^))

natural :: Natural -> Expression
natural = EllipsisNatural

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
