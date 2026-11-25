module Evaluation.Scope.Syntax
  ( ScopeSyntaxRule (..)
  , scopeSyntaxRules
  , enterSyntaxFrame
  , enterSyntaxScope
  , publishSyntaxDeclaration
  , predeclareSyntaxLets
  , openSyntaxScope
  ) where

import Control.Applicative ((<|>))
import DatraLanguage.AST
import DatraLanguage.DependentDeclaration
import DatraTypes.Scope
import Evaluation.Scope
import Evaluation.Scope.GenericProtection (genericContinuationHandoff)
import StringInterpolation

data ScopeSyntaxRule = ScopeSyntaxRule
  { scopeSyntaxRuleNames :: [String]
  , scopeSyntaxRuleBranch :: Int
  , scopeSyntaxRuleValue :: SyntaxRule
  , scopeSyntaxRuleFamilyScope :: Scope
  , scopeSyntaxRuleImportPolicy :: DeclarationLayerImportPolicy
  , scopeSyntaxRuleLayer :: Int
  }

scopeSyntaxRules :: Scope -> [ScopeSyntaxRule]
scopeSyntaxRules scope =
  [ ScopeSyntaxRule
      { scopeSyntaxRuleNames = bindingNames expressionValue
      , scopeSyntaxRuleBranch = branch
      , scopeSyntaxRuleValue = rule
      , scopeSyntaxRuleFamilyScope = scopedDependentDeclarationFamilyScope scoped
      , scopeSyntaxRuleImportPolicy =
          dependentDeclarationLayerImportPolicy layer
      , scopeSyntaxRuleLayer = layerIndex
      }
  | (layerIndex, layer) <- zip [0 ..]
      (scopeDependentDeclarationLayers scope)
  , scoped <- dependentDeclarationLayerMembers layer
  , Just declaration <- [scopedDependentDeclarationValue scoped]
  , let expressionValue = DeclarationExpression declaration
  , (_, branch, rule) <- declarationRuleBranches expressionValue
  ]

enterSyntaxFrame :: Scope -> Scope
enterSyntaxFrame scope = scope
  { scopeDependentDeclarationLayers =
      dependentDeclarationLayer [] : scopeDependentDeclarationLayers scope }

enterSyntaxScope :: salt -> Scope -> Scope
enterSyntaxScope salt = enterSyntaxFrame
  . enterScope salt genericContinuationHandoff

publishSyntaxDeclaration :: Expression -> Scope -> Maybe Scope
publishSyntaxDeclaration expressionValue scope = do
  declaration <- dependentDeclaration expressionValue
  let names = bindingNames expressionValue
      retained = filter (not . declarationMatchesAny names)
      scoped = ScopedDatraDependentDeclaration scope scope declaration Nothing
      publish layer = layer
        { dependentDeclarationLayerMembers =
            retained (dependentDeclarationLayerMembers layer) <> [scoped] }
  pure scope
    { scopeDependentDeclarationLayers =
        case scopeDependentDeclarationLayers scope of
          layer : outer
            | dependentDeclarationLayerOrigin layer == SourceDeclarationLayer
            , dependentDeclarationLayerImportPolicy layer ==
                LocalDeclarationLayer -> publish layer : outer
          layers -> publish (dependentDeclarationLayer []) : layers
    }
  where
    declarationMatchesAny names scoped =
      case scopedDependentDeclarationValue scoped of
        Nothing -> False
        Just declaration -> not (null
          (filter (`elem` names)
            (bindingNames (DeclarationExpression declaration))))

predeclareSyntaxLets :: [Expression] -> Scope -> Scope
predeclareSyntaxLets entries scope = foldl publish scope entries
  where
    publish current entry
      | maybe False dependentDeclarationIsLet (dependentDeclaration entry) =
          maybe current id (publishSyntaxDeclaration entry current)
      | otherwise = current

openSyntaxScope
  :: DeclarationLayerImportPolicy
  -> Scope
  -> Expression
  -> Scope
openSyntaxScope policy enclosing source =
  case source of
    IdentifierReference (SimpleIdentifierString name) ->
      maybe enclosing (installOpenedLayers policy enclosing)
        (openedIdentifier name)
    SyntaxBoundary inner -> openSyntaxScope policy enclosing inner
    _ -> enclosing
  where
    openedIdentifier name = moduleScopeFor name <|> definitionScopeFor name
    moduleScopeFor name = do
      runtime <- runtimeDeclarationByName name enclosing
      runtimeDeclarationPublicScope runtime
    definitionScopeFor name = do
      (captured, _, implementation) <- declarationDefinitionByName enclosing name
      entries <- blockEntries implementation
      pure (foldl publish (enterSyntaxFrame captured) entries)
    blockEntries value = case value of
      Begin declarations _ -> Just (map DeclarationExpression declarations)
      FunctionBody declarations _ -> Just (map DeclarationExpression declarations)
      SyntaxBoundary inner -> blockEntries inner
      _ -> Nothing
    publish scope entry = maybe scope id (publishSyntaxDeclaration entry scope)

installOpenedLayers
  :: DeclarationLayerImportPolicy
  -> Scope
  -> Scope
  -> Scope
installOpenedLayers policy enclosing opened = enclosing
  { scopeDependentDeclarationLayers =
      map (withDeclarationLayerImportPolicy policy) publicLayers
        <> scopeDependentDeclarationLayers enclosing
  }
  where
    publicLayers = take 1
      [ layer
      | layer <- scopeDependentDeclarationLayers opened
      , dependentDeclarationLayerOrigin layer == SourceDeclarationLayer
      ]
