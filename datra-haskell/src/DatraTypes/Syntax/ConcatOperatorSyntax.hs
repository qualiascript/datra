{-# LANGUAGE TypeFamilies #-}

-- | Infix syntax for two-page concatenation.
module Syntax.ConcatOperatorSyntax
  ( (<.>)
  ) where

import MapOperators.ConcatOperator
  ( Concat (ConcatResult, concatOperands)
  )

-- | Legal Haskell spelling of the requested @<,>@ operation. ASCII comma is
-- punctuation rather than an operator character in Haskell's lexer. The
-- operation is ordered: swapping its operands changes the ordinal sum.
infixr 7 <.>

(<.>) :: Concat left right => left -> right -> ConcatResult left right
(<.>) = concatOperands
