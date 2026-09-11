{-# LANGUAGE CPP #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE RoleAnnotations #-}
#include "../LiquidPlugin.h"
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}

-- | LiquidHaskell-verified page-element objects and category operations.
module PageElements.LiquidInternal
  ( PageElementCell (..)
  , pageElementCellPosition
  , PageElement (..)
  , SomePageElement (..)
  , PageElementArrow (..)
  , SomePageElementArrow (..)
  , pageElementAt
  , somePageElement
  , pageElementPrecedes
  , somePageElementPrecedes
  , somePageElementPrecedesReflexive
  , pageElementPrecedesTransitive
  , pageElementTransported
  , somePageElementTransported
  , somePageElementTransportedReflexive
  , pageElementTransportedReflexive
  , pageElementTransportedTransitive
  , pageElementArrow
  , somePageElementArrow
  , withPageElementArrow
  , identityPageElementArrow
  , composePageElementArrows
  , pageElementArrowEndpoints
  , pageElementArrowThin
  , pageElementArrowLeftIdentity
  , pageElementArrowRightIdentity
  , pageElementArrowAssociativity
  , normalizePageElementAt
  , normalizeSomePageElementAt
  , normalizePageElementArrowAt
  , normalizePageElementIdempotentAt
  , normalizePageElementPreservesArrowAt
  , normalizeSomePageElementPreservesArrowAt
  , clampPage
  , trimTrace
  , trimTraceIdempotent
  , trimTracePreservesSuffix
  , traceSuffix
  , traceTail
  ) where

import Chain
  ( Chain
  , chainPosition
  )
import Data.Kind (Type)
import DatraOrdinal (Ordinal)
import Numeric.Natural (Natural)

{-@ embed Natural as int @-}

-- | The heterogeneous chain and value represented by a page element.
data PageElementCell where
  PageElementCell :: Chain cell -> cell -> PageElementCell

instance Eq PageElementCell where
  _ == _ = True

instance Show PageElementCell where
  show _ = "<page-element-cell>"

-- | Compute the stored value's position in its chain.
{-@ reflect pageElementCellPosition @-}
pageElementCellPosition :: PageElementCell -> Ordinal
pageElementCellPosition (PageElementCell pageChain value) =
  chainPosition pageChain value

-- | One object of the category of elements.  The phantom @object@ identifies
-- this particular dependent pair at the type level.
{-@
data PageElement scope object = PageElement
  { pageElementPage :: Natural
  , pageElementPosition :: Ordinal
  , pageElementTrace :: [Ordinal]
  , pageElementCell :: PageElementCell
  }
@-}
type role PageElement nominal nominal
data PageElement (scope :: Type) (object :: Type) = PageElement
  { pageElementPage :: Natural
  , pageElementPosition :: Ordinal
  , pageElementTrace :: [Ordinal]
  , pageElementCell :: PageElementCell
  }
  deriving (Eq, Show)

-- | A page element whose dependent object identity is existentially hidden.
type role SomePageElement nominal
data SomePageElement (scope :: Type) where
  SomePageElement :: PageElement scope object -> SomePageElement scope

-- | Hide a page element's dependent object identity.
{-@ reflect somePageElement @-}
somePageElement :: PageElement scope object -> SomePageElement scope
somePageElement = SomePageElement

-- | Construct a page element from its current position followed by its
-- transported positions on every preceding page.
{-@ reflect pageElementAt @-}
{-@
pageElementAt
  :: page:Natural
  -> earlierPositions:[Ordinal]
  -> cell:PageElementCell
  -> { elementValue:PageElement scope object |
       pageElementPage elementValue == page
       && pageElementPosition elementValue == pageElementCellPosition cell }
@-}
pageElementAt
  :: Natural
  -> [Ordinal]
  -> PageElementCell
  -> PageElement scope object
pageElementAt page earlierPositions cell =
  PageElement
    page
    (pageElementCellPosition cell)
    (pageElementCellPosition cell : earlierPositions)
    cell

-- | The base-arrow condition in the opposite finite spine: a source page is
-- the same as or later than its target page.
{-@ reflect pageElementPrecedes @-}
pageElementPrecedes
  :: PageElement scope source
  -> PageElement scope target
  -> Bool
pageElementPrecedes source target =
  pageElementPage source >= pageElementPage target

-- | Lift the opposite-spine order relation to existential page elements.
{-@ reflect somePageElementPrecedes @-}
somePageElementPrecedes
  :: SomePageElement scope
  -> SomePageElement scope
  -> Bool
somePageElementPrecedes
  (SomePageElement source)
  (SomePageElement target) =
    pageElementPrecedes source target

-- | The lifted opposite-spine order is reflexive.
{-@
somePageElementPrecedesReflexive
  :: value:SomePageElement scope
  -> { proof:() | somePageElementPrecedes value value }
@-}
somePageElementPrecedesReflexive :: SomePageElement scope -> ()
somePageElementPrecedesReflexive (SomePageElement _) = ()

-- | Whether the target is exactly one of the source cell's transported
-- occurrences.  Traces are stored from the current page back to the origin,
-- so this is precisely the suffix relation.
{-@ reflect pageElementTransported @-}
pageElementTransported
  :: PageElement scope source
  -> PageElement scope target
  -> Bool
pageElementTransported source target =
  traceSuffix (pageElementTrace source) (pageElementTrace target)

-- | Lift exact folio transport to existential page elements.
{-@ reflect somePageElementTransported @-}
somePageElementTransported
  :: SomePageElement scope
  -> SomePageElement scope
  -> Bool
somePageElementTransported
  (SomePageElement source)
  (SomePageElement target) =
    pageElementTransported source target

-- | The lifted exact-transport relation is reflexive.
{-@
somePageElementTransportedReflexive
  :: value:SomePageElement scope
  -> { proof:() | somePageElementTransported value value }
@-}
somePageElementTransportedReflexive :: SomePageElement scope -> ()
somePageElementTransportedReflexive (SomePageElement value) =
  pageElementTransportedReflexive value

{-@ reflect traceSuffix @-}
traceSuffix :: [Ordinal] -> [Ordinal] -> Bool
traceSuffix source target
  | source == target = True
traceSuffix [] _ = False
traceSuffix (_ : rest) target = traceSuffix rest target

-- | A reflected trace-length counter used by the verified suffix-trimming
-- operation below.
{-@ reflect traceLength @-}
traceLength :: [a] -> Int
traceLength [] = 0
traceLength (_ : rest) = 1 + traceLength rest

-- | Retain at most the requested number of entries at the end of a transport
-- trace.  A page-element trace runs from its current page back to the origin,
-- so this removes repeated final-page occurrences from the front.
{-@ reflect trimTrace @-}
trimTrace :: Int -> [Ordinal] -> [Ordinal]
trimTrace limit values
  | traceLength values <= limit = values
trimTrace _ [] = []
trimTrace limit (_ : rest) = trimTrace limit rest

-- | Trimming an already trimmed trace has no further effect.
{-@
trimTraceIdempotent
  :: limit:Int
  -> values:[Ordinal]
  -> { proof:() |
       trimTrace limit (trimTrace limit values) == trimTrace limit values }
@-}
trimTraceIdempotent :: Int -> [Ordinal] -> ()
trimTraceIdempotent limit values
  | traceLength values <= limit = ()
trimTraceIdempotent _ [] = ()
trimTraceIdempotent limit (_ : rest) =
  trimTraceIdempotent limit rest

-- | A suffix cannot be longer than the trace containing it.
{-@
traceSuffixLength
  :: source:[Ordinal]
  -> target:{[Ordinal] | traceSuffix source target}
  -> { proof:() | traceLength target <= traceLength source }
@-}
traceSuffixLength :: [Ordinal] -> [Ordinal] -> ()
traceSuffixLength source target
  | source == target = ()
traceSuffixLength [] _ = ()
traceSuffixLength (_ : rest) target = traceSuffixLength rest target

-- | Taking equally bounded suffixes preserves the suffix relation.
{-@
trimTracePreservesSuffix
  :: limit:Int
  -> source:[Ordinal]
  -> target:{[Ordinal] | traceSuffix source target}
  -> { proof:() |
       traceSuffix (trimTrace limit source) (trimTrace limit target) }
@-}
trimTracePreservesSuffix :: Int -> [Ordinal] -> [Ordinal] -> ()
trimTracePreservesSuffix _ source target
  | source == target = ()
trimTracePreservesSuffix _ [] _ = ()
trimTracePreservesSuffix limit source@(_ : rest) target
  | traceLength source <= limit =
      case traceSuffixLength source target of
        () -> ()
  | otherwise = trimTracePreservesSuffix limit rest target

-- | Clamp a page coordinate to the final genuine page.  This named helper is
-- reflected because LiquidHaskell 0.9.4 does not reflect the overloaded
-- Prelude 'min' method.
{-@ reflect clampPage @-}
clampPage :: Natural -> Natural -> Natural
clampPage page finalPage
  | page <= finalPage = page
  | otherwise = finalPage

-- | Clamping a page twice has no further effect.
{-@
clampPageIdempotent
  :: page:Natural
  -> finalPage:Natural
  -> { proof:() |
       clampPage (clampPage page finalPage) finalPage
         == clampPage page finalPage }
@-}
clampPageIdempotent :: Natural -> Natural -> ()
clampPageIdempotent page finalPage
  | page <= finalPage = ()
  | otherwise = ()

-- | Clamping both sides preserves the reversed page order used by arrows.
{-@
clampPagePreservesPrecedes
  :: finalPage:Natural
  -> sourcePage:Natural
  -> targetPage:{Natural | sourcePage >= targetPage}
  -> { proof:() |
       clampPage sourcePage finalPage >= clampPage targetPage finalPage }
@-}
clampPagePreservesPrecedes :: Natural -> Natural -> Natural -> ()
clampPagePreservesPrecedes finalPage sourcePage targetPage
  | sourcePage <= finalPage = ()
  | targetPage <= finalPage = ()
  | otherwise = ()

-- | Collapse a page-element occurrence to the coherent representative whose
-- page is at most the final genuine page.  Traces keep only the suffix from
-- that page back to the origin.
{-@ reflect normalizePageElementAt @-}
normalizePageElementAt
  :: Natural
  -> Int
  -> PageElement scope object
  -> PageElement scope object
normalizePageElementAt finalPage traceLimit value =
  PageElement
    { pageElementPage = clampPage (pageElementPage value) finalPage
    , pageElementPosition = pageElementPosition value
    , pageElementTrace = trimTrace traceLimit (pageElementTrace value)
    , pageElementCell = pageElementCell value
    }

-- | Normalize an existential page element without exposing its object token.
{-@ reflect normalizeSomePageElementAt @-}
normalizeSomePageElementAt
  :: Natural
  -> Int
  -> SomePageElement scope
  -> SomePageElement scope
normalizeSomePageElementAt finalPage traceLimit (SomePageElement value) =
  SomePageElement (normalizePageElementAt finalPage traceLimit value)

-- | Page-element normalization is idempotent.
{-@
normalizePageElementIdempotentAt
  :: finalPage:Natural
  -> traceLimit:Int
  -> value:PageElement scope object
  -> { proof:() |
       normalizePageElementAt finalPage traceLimit
         (normalizePageElementAt finalPage traceLimit value)
       == normalizePageElementAt finalPage traceLimit value }
@-}
normalizePageElementIdempotentAt
  :: Natural
  -> Int
  -> PageElement scope object
  -> ()
normalizePageElementIdempotentAt finalPage traceLimit value =
  case clampPageIdempotent (pageElementPage value) finalPage of
    () -> trimTraceIdempotent traceLimit (pageElementTrace value)

-- | Normalization preserves both parts of the page-element arrow relation.
{-@
normalizePageElementPreservesArrowAt
  :: finalPage:Natural
  -> traceLimit:Int
  -> sourceValue:PageElement scope source
  -> targetValue:{PageElement scope target |
       pageElementPrecedes sourceValue targetValue
       && pageElementTransported sourceValue targetValue}
  -> { proof:() |
       pageElementPrecedes
         (normalizePageElementAt finalPage traceLimit sourceValue)
         (normalizePageElementAt finalPage traceLimit targetValue)
       && pageElementTransported
         (normalizePageElementAt finalPage traceLimit sourceValue)
         (normalizePageElementAt finalPage traceLimit targetValue) }
@-}
normalizePageElementPreservesArrowAt
  :: Natural
  -> Int
  -> PageElement scope source
  -> PageElement scope target
  -> ()
normalizePageElementPreservesArrowAt finalPage traceLimit source target =
  case clampPagePreservesPrecedes
    finalPage
    (pageElementPage source)
    (pageElementPage target) of
      () -> trimTracePreservesSuffix
        traceLimit
        (pageElementTrace source)
        (pageElementTrace target)

-- | Existential form of arrow preservation, suitable for constructing a
-- pagination morphism without exposing endpoint object tokens.
{-@
normalizeSomePageElementPreservesArrowAt
  :: finalPage:Natural
  -> traceLimit:Int
  -> sourceValue:SomePageElement scope
  -> targetValue:{SomePageElement scope |
       somePageElementPrecedes sourceValue targetValue
       && somePageElementTransported sourceValue targetValue}
  -> { proof:() |
       somePageElementPrecedes
         (normalizeSomePageElementAt finalPage traceLimit sourceValue)
         (normalizeSomePageElementAt finalPage traceLimit targetValue)
       && somePageElementTransported
         (normalizeSomePageElementAt finalPage traceLimit sourceValue)
         (normalizeSomePageElementAt finalPage traceLimit targetValue) }
@-}
normalizeSomePageElementPreservesArrowAt
  :: Natural
  -> Int
  -> SomePageElement scope
  -> SomePageElement scope
  -> ()
normalizeSomePageElementPreservesArrowAt
  finalPage
  traceLimit
  (SomePageElement source)
  (SomePageElement target) =
    normalizePageElementPreservesArrowAt finalPage traceLimit source target

-- | Apply normalization to both endpoints of a typed page-element arrow.
{-@ reflect normalizePageElementArrowAt @-}
normalizePageElementArrowAt
  :: Natural
  -> Int
  -> PageElementArrow scope source target
  -> PageElementArrow scope source target
normalizePageElementArrowAt finalPage traceLimit sourceArrow =
  case normalizePageElementPreservesArrowAt
    finalPage
    traceLimit
    (arrowSource sourceArrow)
    (arrowTarget sourceArrow) of
      () -> PageElementArrow
        (normalizePageElementAt finalPage traceLimit (arrowSource sourceArrow))
        (normalizePageElementAt finalPage traceLimit (arrowTarget sourceArrow))

-- | Every transport trace is a suffix of itself.
{-@
pageElementTransportedReflexive
  :: value:PageElement scope object
  -> { proof:() | pageElementTransported value value }
@-}
pageElementTransportedReflexive
  :: PageElement scope object
  -> ()
pageElementTransportedReflexive _ = ()

-- | Exact transport is transitive because suffixes of suffixes are suffixes.
{-@
pageElementTransportedTransitive
  :: sourceValue:PageElement scope source
  -> middleValue:{PageElement scope middle |
       pageElementTransported sourceValue middleValue}
  -> targetValue:{PageElement scope target |
       pageElementTransported middleValue targetValue}
  -> { proof:() |
       pageElementTransported sourceValue targetValue }
@-}
pageElementTransportedTransitive
  :: PageElement scope source
  -> PageElement scope middle
  -> PageElement scope target
  -> ()
pageElementTransportedTransitive source middle target =
  traceSuffixTransitive
    (pageElementTrace source)
    (pageElementTrace middle)
    (pageElementTrace target)

{-@
traceSuffixTransitive
  :: source:[Ordinal]
  -> middle:{[Ordinal] | traceSuffix source middle}
  -> target:{[Ordinal] | traceSuffix middle target}
  -> { proof:() | traceSuffix source target }
@-}
traceSuffixTransitive :: [Ordinal] -> [Ordinal] -> [Ordinal] -> ()
traceSuffixTransitive source middle _target
  | source == middle = ()
traceSuffixTransitive [] _ _ = ()
traceSuffixTransitive source@(_ : rest) middle target =
  case traceSuffixTransitive rest middle target of
    () -> traceSuffixLift source target

{-@ reflect traceTail @-}
traceTail :: [Ordinal] -> [Ordinal]
traceTail [] = []
traceTail (_ : rest) = rest

-- | Lift a suffix fact across one additional leading trace entry.
{-@
traceSuffixLift
  :: source:{[Ordinal] | 0 < len source}
  -> target:{[Ordinal] | traceSuffix (traceTail source) target}
  -> { proof:() | traceSuffix source target }
@-}
traceSuffixLift :: [Ordinal] -> [Ordinal] -> ()
traceSuffixLift source target
  | source == target = ()
traceSuffixLift [] _ = ()
traceSuffixLift (_ : _) _ = ()

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
  PageElement {}
  PageElement {}
  PageElement {} = ()

-- | A type-indexed arrow between page elements. LiquidHaskell checks both the
-- underlying opposite-spine arrow and exact cell transport through the stored
-- transport traces.
{-@
data PageElementArrow scope source target = PageElementArrow
  { arrowSource :: PageElement scope source
  , arrowTarget :: targetValue:{PageElement scope target |
      pageElementPrecedes arrowSource targetValue
      && pageElementTransported arrowSource targetValue}
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

-- | A page-element arrow whose endpoint identities are existentially hidden.
type role SomePageElementArrow nominal
data SomePageElementArrow (scope :: Type) where
  SomePageElementArrow
    :: PageElementArrow scope source target
    -> SomePageElementArrow scope

-- | Total arrow constructor. Its refined input requires both the underlying
-- opposite-spine arrow and the category-of-elements condition that the source
-- cell's transport trace lands exactly on the target occurrence.
{-@ reflect pageElementArrow @-}
{-@
pageElementArrow
  :: sourceValue:PageElement scope source
  -> targetValue:{PageElement scope target |
       pageElementPrecedes sourceValue targetValue
       && pageElementTransported sourceValue targetValue}
  -> { arrowValue:PageElementArrow scope source target |
       arrowSource arrowValue == sourceValue
       && arrowTarget arrowValue == targetValue }
@-}
pageElementArrow
  :: PageElement scope source
  -> PageElement scope target
  -> PageElementArrow scope source target
pageElementArrow = PageElementArrow

-- | Package the unique arrow between existential page elements once its two
-- defining conditions have been established.
{-@
somePageElementArrow
  :: sourceValue:SomePageElement scope
  -> targetValue:{SomePageElement scope |
       somePageElementPrecedes sourceValue targetValue
       && somePageElementTransported sourceValue targetValue}
  -> SomePageElementArrow scope
@-}
somePageElementArrow
  :: SomePageElement scope
  -> SomePageElement scope
  -> SomePageElementArrow scope
somePageElementArrow
  (SomePageElement source)
  (SomePageElement target) =
    SomePageElementArrow (pageElementArrow source target)

-- | Eliminate the hidden endpoint identities of an existential arrow.
withPageElementArrow
  :: SomePageElementArrow scope
  -> (forall source target.
        PageElementArrow scope source target -> result)
  -> result
withPageElementArrow (SomePageElementArrow pageArrow) useArrow =
  useArrow pageArrow

-- | The identity arrow, including its endpoint and base-order guarantees.
{-@ reflect identityPageElementArrow @-}
identityPageElementArrow
  :: PageElement scope object
  -> PageElementArrow scope object object
identityPageElementArrow occurrence =
  case pageElementTransportedReflexive occurrence of
    () -> PageElementArrow occurrence occurrence

-- | Total categorical composition. The Haskell indices align the middle
-- object; the refinement additionally requires its two runtime representations
-- to agree. LiquidHaskell proves that both reversed page order and exact trace
-- transport are preserved from the first arrow's source to the second arrow's
-- target.
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
      () -> case pageElementTransportedTransitive
        (arrowSource first)
        (arrowTarget first)
        (arrowTarget second) of
          () -> PageElementArrow (arrowSource first) (arrowTarget second)

-- | The smart constructor stores exactly its two arguments.
{-@
pageElementArrowEndpoints
  :: sourceValue:PageElement scope source
  -> targetValue:{PageElement scope target |
       pageElementPrecedes sourceValue targetValue
       && pageElementTransported sourceValue targetValue}
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
