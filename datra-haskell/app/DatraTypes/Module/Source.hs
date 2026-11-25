module DatraTypes.Module.Source
  ( ModuleSource (..)
  ) where

import DatraLanguage.AST (Expression)

data ModuleSource = ModuleSource FilePath Expression
