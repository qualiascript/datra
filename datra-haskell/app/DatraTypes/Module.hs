module DatraTypes.Module
  ( PreparedModule (..)
  , PreparedModules (..)
  , emptyPreparedModules
  , preparedModuleContains
  , StandardLibraryVisibility (..)
  , ModuleExport (..)
  , moduleExportName
  ) where

import DatraTypes (InterpretedValue)
import DatraTypes.Scope (DependentDeclarationLayer)

data PreparedModule = PreparedModule
  { preparedModuleIdentity :: FilePath
  , preparedModuleNamespaces :: DependentDeclarationLayer
  }

newtype PreparedModules = PreparedModules [PreparedModule]

emptyPreparedModules :: PreparedModules
emptyPreparedModules = PreparedModules []

preparedModuleContains :: FilePath -> PreparedModules -> Bool
preparedModuleContains identity (PreparedModules modules) = any
  ((== identity) . preparedModuleIdentity)
  modules

data StandardLibraryVisibility
  = NoStandardLibrary
  | QualifiedStandardLibrary
  | AllStandardLibrary
  deriving (Eq, Show)

data ModuleExport = ModuleExport
  String Bool InterpretedValue

moduleExportName :: ModuleExport -> String
moduleExportName (ModuleExport name _ _) = name
