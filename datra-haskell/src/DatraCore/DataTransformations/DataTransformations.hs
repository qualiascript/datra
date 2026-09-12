{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE MultiParamTypeClasses #-}

-- | The complete public API for Datra data transformations.
--
-- This supermodule collects the formerly separate DatraCore entry points into
-- one import.  The overloaded 'op' and 'unop' operations cover both kinds of
-- opposite morphism that previously lived in separate modules.
module DataTransformations
  ( module Atlas
  , module Chain
  , module Consolidation
  , module DataTransformation
  , module DatraOrdinal
  , module DomanialInsertion
  , module Dominion
  , module FiniteDominion
  , module Folio
  , module PageElements
  , module Pagination
  , Opposite (..)
  ) where

import Atlas
import Chain
import Consolidation hiding (op, unop)
import qualified Consolidation
import DataTransformation
import DatraOrdinal
import DomanialInsertion hiding (op, unop)
import qualified DomanialInsertion
import Dominion
import FiniteDominion
import Folio
import PageElements
import Pagination

-- | A pair of representations related by passage to the opposite category.
class Opposite morphism opposite | morphism -> opposite, opposite -> morphism where
  op :: morphism source target -> opposite target source
  unop :: opposite target source -> morphism source target

instance Opposite Consolidation Coconsolidation where
  op = Consolidation.op
  unop = Consolidation.unop

instance Opposite DomanialInsertion CodomanialInsertion where
  op = DomanialInsertion.op
  unop = DomanialInsertion.unop
