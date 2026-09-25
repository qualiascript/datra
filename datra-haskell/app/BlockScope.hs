-- | Declaration and projection rules shared by evaluation, inference and
-- canonical reconstruction. The caller supplies how binding values are read.
module BlockScope
  ( Declaration (..)
  , blockDeclaration
  , bindingNames
  , buildScopeBindings
  , declarationMap
  , projectDeclaration
  , selectedDeclarationName
  ) where

import DatraLanguage.AST
import DatraOrdinal (naturalAtOrdinal)
import DatraTypes

data Declaration = Declaration
  { declarationName :: String
  , declarationIsLet :: Bool
  , declarationAnnotation :: Maybe Expression
  , declarationValue :: Expression
  }

blockDeclaration :: Expression -> Maybe Declaration
blockDeclaration = declaration False
  where
    declaration _ (Let value) = declaration True value
    declaration strict (IdentifierOperation (IdentifierString name) annotation given) =
      Just (Declaration name strict (annotationToCheck annotation given)
        (maybe annotation (\value -> if value == annotation then value
          else MapSpecification value annotation) given))
    declaration strict (EitherType named@(IdentifierOperation _ annotation _) missing)
      | annotation == missing = declaration strict named
    declaration _ _ = Nothing

    annotationToCheck annotation (Just implementation)
      | annotation == implementation = Nothing
    annotationToCheck FunctionType {} (Just FunctionBody {}) = Nothing
    annotationToCheck SyntaxType {} (Just _) = Nothing
    annotationToCheck annotation _ = Just annotation

bindingNames :: Expression -> [String]
bindingNames = maybe [] ((: []) . declarationName) . blockDeclaration

-- Ordinary declarations capture earlier ordinary bindings; let declarations
-- are predeclared in every captured scope. Evaluation order is left to callers.
buildScopeBindings :: ([binding] -> Declaration -> binding)
  -> [binding] -> [Declaration] -> [binding]
buildScopeBindings makeBinding enclosing declarations = foldl addOrdinary initial declarations
  where
    initial = recursiveLets <> enclosing
    recursiveLets =
      [makeBinding (scopeBefore position) value
      | (position, value) <- zip [0..] declarations, declarationIsLet value]
    scopeBefore position = foldl addOrdinary initial (take position declarations)
    addOrdinary scope value
      | declarationIsLet value = scope
      | otherwise = makeBinding scope value : scope

declarationMap :: [String] -> (String -> Either InterpretingError InterpretedValue)
  -> Either InterpretingError InterpretedValue
declarationMap names resolve = makeAtlasMap 2 <$>
  traverse (\name -> simpleIdentifierTypeValue name <$> resolve name) names

-- Validate against the map shape before asking for any declaration values.
-- This also bounds the Natural-to-Int conversion used to select the list entry.
selectedDeclarationName :: [String] -> InterpretedValue
  -> Either InterpretingError (Maybe String)
selectedDeclarationName names index = do
  shape <- declarationMap names (const (Right (naturalValue 0)))
  _ <- accessValues shape index
  pure $ do
    ordinal <- interpretedExplicitOrdinal index >>= (naturalAtOrdinal . snd)
    case drop (fromIntegral ordinal) names of
      name : _ -> Just name
      [] -> Nothing

projectDeclaration :: [String] -> (String -> Either InterpretingError InterpretedValue)
  -> InterpretedValue -> Either InterpretingError InterpretedValue
projectDeclaration names resolve index = do
  selected <- selectedDeclarationName names index
  case selected of
    Just name -> simpleIdentifierTypeValue name <$> resolve name
    Nothing -> declarationMap names resolve >>= (`accessValues` index)
