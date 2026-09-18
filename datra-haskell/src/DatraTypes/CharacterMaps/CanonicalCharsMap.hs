{-# LANGUAGE RankNTypes #-}

-- | Canonical identifier characters obtained by ordered access into ASCII.
module CanonicalCharsMap
  ( CanonicalCharsMap
  , CanonicalChar
  , canonicalCharsCardinality
  , canonicalCharsMap
  , canonicalCharValue
  , canonicalCharacterAt
  ) where

import AsciiMap
  ( AsciiCharacter
  , asciiCharacterValue
  , asciiMap
  )
import Chain (Chain, chain)
import Control.Arrow ((&&&))
import Control.Monad ((>=>))
import DatraOrdinal (finiteOrdinal, naturalAtOrdinal)
import Ellipsis (Ellipsis)
import MapOperators.AccessOperator
  ( AccessElement
  , IndexedAtlasMap
  , accessOperator
  , accessElementValue
  , indexedAtlasValueAt
  )
import MapOperators.OrderedAtlasMap (orderedAtlasMapIndexed)
import Numeric.Natural (Natural)
import SuperEllipsisInsertion
  ( SuperEllipsisInsertion
  , superEllipsisInsertion
  )
import SuperEllipsis
  ( dotSuperEllipsisRank
  , nextSuperEllipsisRank
  , superEllipsisTerminal
  , superEllipsisTerminalPosition
  , superEllipsisZeroTerminal
  )

import qualified Data.Map.Strict as Map

-- | One request in the canonical-character access order.
data CanonicalCharIndex = CanonicalCharIndex
  { canonicalPosition :: Natural
  , canonicalAsciiRank :: Natural
  }
  deriving (Eq, Show)

-- | A selected ASCII character, retaining its access witness.
type CanonicalChar scope =
  AccessElement CanonicalCharIndex (AsciiCharacter scope)

-- | The two-page map produced by accessing the ASCII map.
type CanonicalCharsMap scope = IndexedAtlasMap (CanonicalChar scope)

canonicalCharsCardinality :: Natural
canonicalCharsCardinality = 64

canonicalAsciiRanks :: [Natural]
canonicalAsciiRanks =
  [39]
    <> [48 .. 57]
    <> [65 .. 90]
    <> [95]
    <> [97 .. 122]

canonicalIndices :: [CanonicalCharIndex]
canonicalIndices =
  zipWith CanonicalCharIndex [0 ..] canonicalAsciiRanks

canonicalIndicesByPosition :: Map.Map Natural CanonicalCharIndex
canonicalIndicesByPosition =
  Map.fromList
    (map (canonicalPosition &&& id) canonicalIndices)

canonicalIndicesByAsciiRank :: Map.Map Natural CanonicalCharIndex
canonicalIndicesByAsciiRank =
  Map.fromList
    (map (canonicalAsciiRank &&& id) canonicalIndices)

canonicalIndexChain :: Chain CanonicalCharIndex
canonicalIndexChain =
  chain
    (finiteOrdinal canonicalCharsCardinality)
    (finiteOrdinal . canonicalPosition)
    (naturalAtOrdinal >=> (`Map.lookup` canonicalIndicesByPosition))
    (const ())
    (\_ _ -> ())
    (const ())

canonicalCharsInsertion
  :: SuperEllipsisInsertion Ellipsis CanonicalCharIndex
canonicalCharsInsertion =
  superEllipsisInsertion
    rankOne
    canonicalIndexChain
    terminalAt
    (naturalAtOrdinal . superEllipsisTerminalPosition
      >=> (`Map.lookup` canonicalIndicesByAsciiRank))
    (const ())
  where
    rankOne = nextSuperEllipsisRank dotSuperEllipsisRank
    terminalAt index =
      case superEllipsisTerminal
        rankOne (finiteOrdinal (canonicalAsciiRank index)) of
          Just terminal -> terminal
          Nothing -> superEllipsisZeroTerminal rankOne

-- | Construct the canonical-character map by selecting from the ASCII map.
-- The result is 'Nothing' only if the internal insertion ever ceases to fit
-- the 256-element ASCII page.
canonicalCharsMap
  :: (forall scope. CanonicalCharsMap scope -> result)
  -> Maybe result
canonicalCharsMap useCanonical =
  asciiMap
    (\ascii -> do
      selected <- accessOperator ascii canonicalCharsInsertion
      useCanonical <$> orderedAtlasMapIndexed selected)

canonicalCharValue :: CanonicalChar scope -> Char
canonicalCharValue = asciiCharacterValue . accessElementValue

-- | Look up one character by its new page-1 position, from 0 through 63.
canonicalCharacterAt
  :: CanonicalCharsMap scope
  -> Natural
  -> Maybe Char
canonicalCharacterAt valueMap valueRank =
  canonicalCharValue <$> indexedAtlasValueAt valueMap valueRank
