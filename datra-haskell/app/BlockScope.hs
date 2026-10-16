-- | Declaration and projection rules shared by evaluation, inference and
-- canonical reconstruction. The caller supplies how binding values are read.
module BlockScope
  ( Declaration (..)
  , ScopeMember (..)
  , blockDeclaration
  , isBlockDeclaration
  , isDependentDeclaration
  , bindingNames
  , buildScopeBindings
  , declarationScopeMember
  , declarationMap
  , projectDeclaration
  , selectedDeclarationName
  , scopeMemberNames
  ) where

import DatraLanguage.AST
import DatraOrdinal (naturalAtOrdinal)
import DatraTypes

data Declaration = Declaration
  { declarationName :: String
  , declarationIsLet :: Bool
  , declarationIsCanonicalValue :: Bool
  , declarationAnnotation :: Maybe Expression
  , declarationValue :: Expression
  }

data ScopeMember = ScopeMember
  { scopeMemberName :: String
  , scopeMemberIsCanonicalValue :: Bool
  }
  deriving (Eq, Show)

blockDeclaration :: Expression -> Maybe Declaration
blockDeclaration = declaration False False
  where
    declaration _ True (Let _) = Nothing
    declaration _ canonical (Let value) = declaration True canonical value
    declaration _ True (Val _) = Nothing
    declaration strict _ (Val value) = declaration strict True value
    declaration strict canonical
        (IdentifierOperation (IdentifierString name) annotation given) =
      Just (Declaration name strict canonical (annotationToCheck annotation given)
        (maybe annotation (\value -> if value == annotation then value
          else MapSpecification value annotation) given))
    declaration strict canonical optional
      | Just (named@IdentifierOperation {}, _) <-
          optionalIdentifierExpression optional =
          declaration strict canonical named
    declaration strict canonical (In value body) = do
      declared <- declaration strict canonical body
      pure declared
        { declarationAnnotation = In value <$> declarationAnnotation declared
        , declarationValue = In value (declarationValue declared)
        }
    declaration _ _ _ = Nothing

    annotationToCheck annotation (Just implementation)
      | annotation == implementation = Nothing
    annotationToCheck FunctionTypeExpression {} (Just FunctionBody {}) = Nothing
    annotationToCheck SyntaxType {} (Just _) = Nothing
    annotationToCheck annotation _ = Just annotation

-- A dependent declaration exists only as a block entry and contributes a
-- family of names rather than one finite binding. It is therefore recognized
-- here without being coerced into the fixed-name 'Declaration' record.
isBlockDeclaration :: Expression -> Bool
isBlockDeclaration expressionValue =
  case blockDeclaration expressionValue of
    Just _ -> True
    Nothing -> isDependentDeclaration expressionValue

isDependentDeclaration :: Expression -> Bool
isDependentDeclaration expressionValue = case expressionValue of
  IdentifierTemplateOperation _ annotation (Just given) ->
    annotation == given
  Let value -> isDependentDeclaration value
  Val value -> isDependentDeclaration value
  In _ value -> isDependentDeclaration value
  _ -> False

bindingNames :: Expression -> [String]
bindingNames = maybe [] ((: []) . declarationName) . blockDeclaration

declarationScopeMember :: Declaration -> ScopeMember
declarationScopeMember declaration = ScopeMember
  (declarationName declaration)
  (declarationIsCanonicalValue declaration)

scopeMemberNames :: [ScopeMember] -> [String]
scopeMemberNames = map scopeMemberName

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

declarationMap :: [ScopeMember] -> (String -> Either InterpretingError InterpretedValue)
  -> Either InterpretingError InterpretedValue
declarationMap members resolve = makeAtlasMap 2 <$> traverse memberValue members
  where
    memberValue member = do
      value <- simpleIdentifierTypeValue name <$> resolve name
      pure (if scopeMemberIsCanonicalValue member
        then withTrailingIdentifierMarker canonicalValueMarker value
        else value)
      where name = scopeMemberName member

-- Validate against the map shape before asking for any declaration values.
-- This also bounds the Natural-to-Int conversion used to select the list entry.
selectedDeclarationName :: [ScopeMember] -> InterpretedValue
  -> Either InterpretingError (Maybe String)
selectedDeclarationName members index =
  fmap (fmap scopeMemberName) (selectedDeclarationMember members index)

selectedDeclarationMember :: [ScopeMember] -> InterpretedValue
  -> Either InterpretingError (Maybe ScopeMember)
selectedDeclarationMember members index = do
  shape <- declarationMap members (const (Right (naturalValue 0)))
  _ <- accessValues shape index
  pure $ do
    ordinal <- interpretedExplicitOrdinal index >>= (naturalAtOrdinal . snd)
    case drop (fromIntegral ordinal) members of
      member : _ -> Just member
      [] -> Nothing

projectDeclaration :: [ScopeMember] -> (String -> Either InterpretingError InterpretedValue)
  -> InterpretedValue -> Either InterpretingError InterpretedValue
projectDeclaration members resolve index = do
  selected <- selectedDeclarationMember members index
  case selected of
    Just member -> do
      let name = scopeMemberName member
      value <- simpleIdentifierTypeValue name
        . withoutCanonicalPresentation <$> resolve name
      pure (if scopeMemberIsCanonicalValue member
        then withTrailingIdentifierMarker canonicalValueMarker value
        else value)
    Nothing -> declarationMap members resolve >>= (`accessValues` index)
