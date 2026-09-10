{-# LANGUAGE CPP #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE RoleAnnotations #-}
#include "../LiquidPlugin.h"
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}

-- | LiquidHaskell-verified page-element objects and category operations.
module PageElements.LiquidInternal
  ( PageElement (..)
  , PageElementArrow (..)
  , pageElementAt
  , pageElementPrecedes
  , pageElementPrecedesTransitive
  , pageElementArrow
  , identityPageElementArrow
  , composePageElementArrows
  , pageElementArrowEndpoints
  , pageElementArrowThin
  , pageElementArrowLeftIdentity
  , pageElementArrowRightIdentity
  , pageElementArrowAssociativity
  ) where

import Data.Kind (Type)
import DatraOrdinal (Ordinal)
import Numeric.Natural (Natural)

{-@ embed Natural as int @-}

-- | One object of the category of elements.  The phantom @object@ identifies
-- this particular dependent pair at the type level.
{-@
data PageElement scope object = PageElement
  { pageElementPage :: Natural
  , pageElementPosition :: Ordinal
  }
@-}
type role PageElement nominal nominal
data PageElement (scope :: Type) (object :: Type) = PageElement
  { pageElementPage :: Natural
  , pageElementPosition :: Ordinal
  }
  deriving (Eq, Show)

-- | Construct a page element with exactly the supplied runtime coordinates.
{-@ reflect pageElementAt @-}
{-@
pageElementAt
  :: page:Natural
  -> position:Ordinal
  -> { elementValue:PageElement scope object |
       pageElementPage elementValue == page
       && pageElementPosition elementValue == position }
@-}
pageElementAt
  :: Natural
  -> Ordinal
  -> PageElement scope object
pageElementAt = PageElement

-- | The base-arrow condition in the opposite finite spine: a source page is
-- the same as or later than its target page.
{-@ reflect pageElementPrecedes @-}
pageElementPrecedes
  :: PageElement scope source
  -> PageElement scope target
  -> Bool
pageElementPrecedes source target =
  pageElementPage source >= pageElementPage target

-- | Transitivity of the opposite-spine page order.
{-@
pageElementPrecedesTransitive
  :: sourceValue:PageElement scope source
  -> middleValue:{PageElement scope middle |
       pageElementPrecedes sourceValue middleValue}
  -> targetValue:{PageElement scope target |
       pageElementPrecedes middleValue targetValue}
  -> { proof:() |
       pageElementPrecedes sourceValue targetValue }
@-}
pageElementPrecedesTransitive
  :: PageElement scope source
  -> PageElement scope middle
  -> PageElement scope target
  -> ()
pageElementPrecedesTransitive
  (PageElement _ _)
  (PageElement _ _)
  (PageElement _ _) = ()

-- | A type-indexed arrow between page elements.  LiquidHaskell checks the
-- existence of its underlying opposite-spine arrow; exact cell transport is
-- the additional proof obligation documented on 'pageElementArrow'.
{-@
data PageElementArrow scope source target = PageElementArrow
  { arrowSource :: PageElement scope source
  , arrowTarget :: targetValue:{PageElement scope target |
      pageElementPrecedes arrowSource targetValue}
  }
@-}
type role PageElementArrow nominal nominal nominal
data PageElementArrow
  (scope :: Type)
  (source :: Type)
  (target :: Type) = PageElementArrow
  { arrowSource :: PageElement scope source
  , arrowTarget :: PageElement scope target
  }
  deriving (Eq, Show)

-- | Total arrow constructor.  Its refined input requires the underlying base
-- arrow.  The remaining category-of-elements premise is that folio transport
-- sends @source@'s cell exactly to @target@'s cell; that premise will become a
-- refinement once heterogeneous folio transport is exposed to LiquidHaskell.
{-@ reflect pageElementArrow @-}
{-@
pageElementArrow
  :: sourceValue:PageElement scope source
  -> targetValue:{PageElement scope target |
       pageElementPrecedes sourceValue targetValue}
  -> { arrowValue:PageElementArrow scope source target |
       arrowSource arrowValue == sourceValue
       && arrowTarget arrowValue == targetValue }
@-}
pageElementArrow
  :: PageElement scope source
  -> PageElement scope target
  -> PageElementArrow scope source target
pageElementArrow = PageElementArrow

-- | The identity arrow, including its endpoint and base-order guarantees.
{-@ reflect identityPageElementArrow @-}
identityPageElementArrow
  :: PageElement scope object
  -> PageElementArrow scope object object
identityPageElementArrow occurrence =
  PageElementArrow occurrence occurrence

-- | Total categorical composition.  The Haskell indices align the middle
-- object; LiquidHaskell proves closure of the underlying page order.
{-@ reflect composePageElementArrows @-}
{-@
composePageElementArrows
  :: second:PageElementArrow scope middle target
  -> first:{PageElementArrow scope source middle |
       arrowTarget first == arrowSource second}
  -> { composite:PageElementArrow scope source target |
       arrowSource composite == arrowSource first
       && arrowTarget composite == arrowTarget second }
@-}
composePageElementArrows
  :: PageElementArrow scope middle target
  -> PageElementArrow scope source middle
  -> PageElementArrow scope source target
composePageElementArrows second first =
  case pageElementPrecedesTransitive
    (arrowSource first)
    (arrowTarget first)
    (arrowTarget second) of
      () -> PageElementArrow (arrowSource first) (arrowTarget second)

-- | The smart constructor stores exactly its two arguments.
{-@
pageElementArrowEndpoints
  :: sourceValue:PageElement scope source
  -> targetValue:{PageElement scope target |
       pageElementPrecedes sourceValue targetValue}
  -> { proof:() |
       arrowSource (pageElementArrow sourceValue targetValue) == sourceValue
       && arrowTarget (pageElementArrow sourceValue targetValue) == targetValue }
@-}
pageElementArrowEndpoints
  :: PageElement scope source
  -> PageElement scope target
  -> ()
pageElementArrowEndpoints _ _ = ()

-- | A hom-set is a subsingleton: arrows with equal endpoints are equal.
{-@
pageElementArrowThin
  :: first:PageElementArrow scope source target
  -> second:{PageElementArrow scope source target |
       arrowSource second == arrowSource first
       && arrowTarget second == arrowTarget first}
  -> { proof:() | first == second }
@-}
pageElementArrowThin
  :: PageElementArrow scope source target
  -> PageElementArrow scope source target
  -> ()
pageElementArrowThin (PageElementArrow _ _) (PageElementArrow _ _) = ()

-- | Left identity for total arrow composition.
{-@
pageElementArrowLeftIdentity
  :: arrowValue:PageElementArrow scope source target
  -> { proof:() |
       composePageElementArrows
         (identityPageElementArrow (arrowTarget arrowValue))
         arrowValue
       == arrowValue }
@-}
pageElementArrowLeftIdentity
  :: PageElementArrow scope source target
  -> ()
pageElementArrowLeftIdentity (PageElementArrow _ _) = ()

-- | Right identity for total arrow composition.
{-@
pageElementArrowRightIdentity
  :: arrowValue:PageElementArrow scope source target
  -> { proof:() |
       composePageElementArrows
         arrowValue
         (identityPageElementArrow (arrowSource arrowValue))
       == arrowValue }
@-}
pageElementArrowRightIdentity
  :: PageElementArrow scope source target
  -> ()
pageElementArrowRightIdentity (PageElementArrow _ _) = ()

-- | Associativity for three aligned arrows.
{-@
pageElementArrowAssociativity
  :: third:PageElementArrow scope secondMiddle target
  -> second:PageElementArrow scope firstMiddle secondMiddle
  -> first:PageElementArrow scope source firstMiddle
  -> { proof:() |
       composePageElementArrows third
         (composePageElementArrows second first)
       == composePageElementArrows
            (composePageElementArrows third second) first }
@-}
pageElementArrowAssociativity
  :: PageElementArrow scope secondMiddle target
  -> PageElementArrow scope firstMiddle secondMiddle
  -> PageElementArrow scope source firstMiddle
  -> ()
pageElementArrowAssociativity
  (PageElementArrow _ _)
  (PageElementArrow _ _)
  (PageElementArrow _ _) = ()
