-- | Backwards-compatible diagnostics import. Evaluation owns these domain
-- errors; diagnostics modules only render them.
module DatraLanguage.Diagnostics.Interpreter
  ( module Evaluation.Error
  ) where

import Evaluation.Error
