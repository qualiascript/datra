-- | Rank-one specialization of 'SuperEllipsisInsertion'.
module EllipsisInsertion
  ( EllipsisInsertion
  , EllipsisInsertionElement
  , ellipsisInsertion
  , ellipsisInsertionFirst
  , ellipsisInsertionChain
  , ellipsisInsertionTraversal
  , applyEllipsisInsertion
  , ellipsisInsertionPreimage
  , ellipsisInsertionLeftInverse
  , mergeDisjointEllipsisInsertions
  , ellipsisInsertionDominion
  , ellipsisInsertionElementSource
  , ellipsisInsertionElementValue
  ) where

import Chain (Chain)
import DomanialInclusion (DominionAtlasObject)
import Dominion (Dominion)
import Ellipsis
  ( Ellipsis
  , EllipsisAtlasObject
  , EllipsisTerminal
  , ellipsisRank
  )
import StableAtlasTransversal (StableAtlasTransversal)
import SuperEllipsisInsertion
  ( SuperEllipsisInsertion
  , SuperEllipsisInsertionElement
  , applySuperEllipsisInsertion
  , mergeDisjointSuperEllipsisInsertions
  , superEllipsisInsertion
  , superEllipsisInsertionChain
  , superEllipsisInsertionDominion
  , superEllipsisInsertionElementSource
  , superEllipsisInsertionElementValue
  , superEllipsisInsertionFirst
  , superEllipsisInsertionLeftInverse
  , superEllipsisInsertionPreimage
  , superEllipsisInsertionTraversal
  )

type EllipsisInsertion = SuperEllipsisInsertion Ellipsis

type EllipsisInsertionElement = SuperEllipsisInsertionElement Ellipsis

ellipsisInsertion
  :: Maybe source
  -> Chain source
  -> (source -> EllipsisTerminal)
  -> (EllipsisTerminal -> Maybe source)
  -> (source -> ())
  -> EllipsisInsertion source
ellipsisInsertion = superEllipsisInsertion ellipsisRank

ellipsisInsertionFirst :: EllipsisInsertion source -> Maybe source
ellipsisInsertionFirst = superEllipsisInsertionFirst

ellipsisInsertionChain :: EllipsisInsertion source -> Chain source
ellipsisInsertionChain = superEllipsisInsertionChain

ellipsisInsertionTraversal
  :: EllipsisInsertion source
  -> StableAtlasTransversal
       (DominionAtlasObject source)
       EllipsisAtlasObject
ellipsisInsertionTraversal = superEllipsisInsertionTraversal

applyEllipsisInsertion
  :: EllipsisInsertion source
  -> source
  -> EllipsisTerminal
applyEllipsisInsertion = applySuperEllipsisInsertion

ellipsisInsertionPreimage
  :: EllipsisInsertion source
  -> EllipsisTerminal
  -> Maybe source
ellipsisInsertionPreimage = superEllipsisInsertionPreimage

ellipsisInsertionLeftInverse
  :: EllipsisInsertion source
  -> source
  -> ()
ellipsisInsertionLeftInverse = superEllipsisInsertionLeftInverse

mergeDisjointEllipsisInsertions
  :: EllipsisInsertion left
  -> EllipsisInsertion right
  -> EllipsisInsertion (Either left right)
mergeDisjointEllipsisInsertions = mergeDisjointSuperEllipsisInsertions

ellipsisInsertionDominion
  :: Dominion value
  -> EllipsisInsertion source
  -> Dominion (EllipsisInsertionElement source value)
ellipsisInsertionDominion = superEllipsisInsertionDominion

ellipsisInsertionElementSource
  :: EllipsisInsertionElement source value
  -> source
ellipsisInsertionElementSource = superEllipsisInsertionElementSource

ellipsisInsertionElementValue
  :: EllipsisInsertionElement source value
  -> value
ellipsisInsertionElementValue = superEllipsisInsertionElementValue
