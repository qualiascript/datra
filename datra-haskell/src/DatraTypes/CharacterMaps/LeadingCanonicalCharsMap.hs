{-# LANGUAGE RankNTypes #-}

-- | Canonical identifier-leading characters obtained by ordered access into
-- the canonical-character map.
module LeadingCanonicalCharsMap
  ( LeadingCanonicalCharsMap
  , LeadingCanonicalChar
  , leadingCanonicalCharsCardinality
  , leadingCanonicalCharsMap
  , leadingCanonicalCharValue
  , leadingCanonicalCharacterAt
  ) where

import CanonicalCharsMap
  ( CanonicalChar
  , canonicalCharValue
  , canonicalCharsMap
  )
import Chain (Chain, chain)
import Control.Arrow ((&&&))
import Control.Monad ((>=>), join)
import DatraOrdinal (finiteOrdinal, naturalAtOrdinal)
import Ellipsis (Ellipsis)
import MapOperators.AccessOperator
  ( AccessElement
  , IndexedAtlasMap
  , accessElementValue
  , accessOperator
  , indexedAtlasValueAt
  )
import MapOperators.OrderedAtlasMap (orderedAtlasMapIndexed)
import Numeric.Natural (Natural)
import SuperEllipsis
  ( dotSuperEllipsisRank
  , nextSuperEllipsisRank
  , superEllipsisTerminal
  , superEllipsisTerminalPosition
  , superEllipsisZeroTerminal
  )
import SuperEllipsisInsertion
  ( SuperEllipsisInsertion
  , superEllipsisInsertion
  )

import qualified Data.Map.Strict as Map

-- | One request in the leading-canonical-character access order.
data LeadingCanonicalCharIndex = LeadingCanonicalCharIndex
  { leadingCanonicalPosition :: Natural
  , leadingCanonicalSourceRank :: Natural
  }
  deriving (Eq, Show)

-- | A selected canonical character, retaining both access witnesses.
type LeadingCanonicalChar scope =
  AccessElement LeadingCanonicalCharIndex (CanonicalChar scope)

-- | The two-page map of characters permitted at the start of an identifier.
type LeadingCanonicalCharsMap scope = IndexedAtlasMap (LeadingCanonicalChar scope)

leadingCanonicalCharsCardinality :: Natural
leadingCanonicalCharsCardinality = 53

-- CanonicalCharsMap positions 11 through 63 are A-Z, _, and a-z.
leadingCanonicalIndices :: [LeadingCanonicalCharIndex]
leadingCanonicalIndices =
  zipWith LeadingCanonicalCharIndex [0 ..] [11 .. 63]

leadingCanonicalIndicesByPosition
  :: Map.Map Natural LeadingCanonicalCharIndex
leadingCanonicalIndicesByPosition =
  Map.fromList
    (map (leadingCanonicalPosition &&& id) leadingCanonicalIndices)

leadingCanonicalIndicesBySourceRank
  :: Map.Map Natural LeadingCanonicalCharIndex
leadingCanonicalIndicesBySourceRank =
  Map.fromList
    (map (leadingCanonicalSourceRank &&& id) leadingCanonicalIndices)

leadingCanonicalIndexChain :: Chain LeadingCanonicalCharIndex
leadingCanonicalIndexChain =
  chain
    (finiteOrdinal leadingCanonicalCharsCardinality)
    (finiteOrdinal . leadingCanonicalPosition)
    (naturalAtOrdinal >=> (`Map.lookup` leadingCanonicalIndicesByPosition))
    (const ())
    (\_ _ -> ())
    (const ())

leadingCanonicalCharsInsertion
  :: SuperEllipsisInsertion Ellipsis LeadingCanonicalCharIndex
leadingCanonicalCharsInsertion =
  superEllipsisInsertion
    rankOne
    leadingCanonicalIndexChain
    terminalAt
    (naturalAtOrdinal . superEllipsisTerminalPosition
      >=> (`Map.lookup` leadingCanonicalIndicesBySourceRank))
    (const ())
  where
    rankOne = nextSuperEllipsisRank dotSuperEllipsisRank
    terminalAt index =
      case superEllipsisTerminal
        rankOne (finiteOrdinal (leadingCanonicalSourceRank index)) of
          Just terminal -> terminal
          Nothing -> superEllipsisZeroTerminal rankOne

-- | Construct the leading-canonical-character map by selecting letters and
-- underscore from the canonical-character map.
leadingCanonicalCharsMap
  :: (forall scope. LeadingCanonicalCharsMap scope -> result)
  -> Maybe result
leadingCanonicalCharsMap useLeadingCanonical =
  join
    (canonicalCharsMap
      (\canonical -> do
        selected <- accessOperator canonical leadingCanonicalCharsInsertion
        useLeadingCanonical <$> orderedAtlasMapIndexed selected))

leadingCanonicalCharValue :: LeadingCanonicalChar scope -> Char
leadingCanonicalCharValue = canonicalCharValue . accessElementValue

-- | Look up one character by its new page-1 position, from 0 through 52.
leadingCanonicalCharacterAt
  :: LeadingCanonicalCharsMap scope
  -> Natural
  -> Maybe Char
leadingCanonicalCharacterAt valueMap valueRank =
  leadingCanonicalCharValue <$> indexedAtlasValueAt valueMap valueRank
