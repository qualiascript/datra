{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE RoleAnnotations #-}

-- | The two-page Atlas map of the 256 ASCII code points.
module AsciiMap
  ( AsciiMap
  , AsciiCharacter
  , asciiCardinality
  , asciiMap
  , asciiAtlas
  , asciiAtlasMap
  , asciiCharacterRank
  , asciiCharacterValue
  , asciiCharacterAt
  ) where

import AtlasMap (AtlasMap)
import ChainedDominionAtlas
  ( ChainedDominionAtlas
  , ChainedDominionAtlasObject
  )
import Data.Char (chr)
import Dominion (Dominion, dominion)
import MapOperators.AccessOperator
  ( IndexedAtlasMap
  , indexedAtlasAtlas
  , indexedAtlasAtlasMap
  , indexedAtlasMap
  , indexedAtlasValueAt
  )
import Numeric.Natural (Natural)

-- | An ASCII character carrying its final-page index.
type role AsciiCharacter nominal
data AsciiCharacter scope = AsciiCharacter
  { asciiCharacterRank :: Natural
  , asciiCharacterValue :: Char
  }
  deriving (Eq, Show)

-- | A two-page map whose page 1 is the 256-element ASCII chain.
type AsciiMap scope = IndexedAtlasMap (AsciiCharacter scope)

asciiCardinality :: Natural
asciiCardinality = 256

asciiCharacterDominion :: Dominion (AsciiCharacter scope)
asciiCharacterDominion =
  dominion
    asciiCharacterRank
    (\valueRank ->
      if valueRank < asciiCardinality
        then Just
          (AsciiCharacter valueRank (chr (fromIntegral valueRank)))
        else Nothing)
    (const ())

-- | Introduce the ASCII map with a fresh abstract membership scope.
asciiMap
  :: (forall scope. AsciiMap scope -> result)
  -> result
asciiMap useAscii =
  useAscii
    (indexedAtlasMap
      asciiCardinality
      (AsciiCharacter 0 '\0')
      asciiCharacterDominion)

asciiAtlas :: AsciiMap scope -> ChainedDominionAtlas (AsciiCharacter scope)
asciiAtlas = indexedAtlasAtlas

-- | The underlying chained Atlas map.
asciiAtlasMap
  :: AsciiMap scope
  -> AtlasMap (ChainedDominionAtlasObject (AsciiCharacter scope))
asciiAtlasMap = indexedAtlasAtlasMap

-- | Look up the character at one page-1 position.
asciiCharacterAt
  :: AsciiMap scope
  -> Natural
  -> Maybe Char
asciiCharacterAt valueMap valueRank =
  asciiCharacterValue <$> indexedAtlasValueAt valueMap valueRank
