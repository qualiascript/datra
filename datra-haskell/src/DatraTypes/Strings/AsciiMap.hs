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

import Atlas (Atlas)
import AtlasMap (AtlasMap)
import ChainedDominionAtlas
  ( ChainedDominionCellData
  , chainedDominionAtlas
  , chainedDominionAtlasMap
  , ChainedDominionAtlasObject
  )
import Data.Char (chr)
import Dominion (Dominion, dominion)
import MapOperators.AccessOperator
  ( IndexedAtlasMap
  , withIndexedAtlas
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

asciiAtlas :: AsciiMap scope
  -> (forall owner pages. Atlas owner pages (ChainedDominionCellData (AsciiCharacter scope)) () (AsciiCharacter scope) -> result)
  -> result
asciiAtlas valueMap useAtlas = withIndexedAtlas valueMap (useAtlas . chainedDominionAtlas)

-- | Observe the underlying map while retaining its owning scopes.
asciiAtlasMap :: AsciiMap scope
  -> (forall owner pages. AtlasMap (ChainedDominionAtlasObject owner pages (AsciiCharacter scope)) -> result)
  -> result
asciiAtlasMap valueMap useMap = withIndexedAtlas valueMap (useMap . chainedDominionAtlasMap)

-- | Look up the character at one page-1 position.
asciiCharacterAt
  :: AsciiMap scope
  -> Natural
  -> Maybe Char
asciiCharacterAt valueMap valueRank =
  asciiCharacterValue <$> indexedAtlasValueAt valueMap valueRank
