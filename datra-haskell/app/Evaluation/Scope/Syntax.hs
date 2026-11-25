module Evaluation.Scope.Syntax
  ( ScopeSyntaxRule (..)
  , scopeSyntaxRules
  , enterSyntaxFrame
  , enterSyntaxScope
  , publishSyntaxDeclaration
  , predeclareSyntaxLets
  , openSyntaxScope
  ) where

import DatraLanguage.AST
import DatraLanguage.DependentDeclaration
import DatraTypes (InterpretedValue)
import DatraTypes.Scope
import Evaluation.Scope
import Evaluation.Scope.GenericProtection (genericContinuationHandoff)
import StringInterpolation

data ScopeSyntaxRule = ScopeSyntaxRule
  { scopeSyntaxRuleBranch :: Int
  , scopeSyntaxRuleValue :: SyntaxRule
  , scopeSyntaxRuleFamilyScope :: Scope
  , scopeSyntaxRuleImportPolicy :: DeclarationLayerImportPolicy
  , scopeSyntaxRuleLayer :: Int
  }

scopeSyntaxRules :: Scope -> [ScopeSyntaxRule]
scopeSyntaxRules scope =
  [ ScopeSyntaxRule
      { scopeSyntaxRuleBranch = branch
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
  :: (Scope -> Expression -> Maybe InterpretedValue)
  -> DeclarationLayerImportPolicy
  -> Scope
  -> Expression
  -> Scope
openSyntaxScope evaluate policy enclosing source =
  case evaluate enclosing source >>= (`runtimePublicScopeForValue` enclosing) of
    Just public -> installOpenedLayers policy enclosing public
    Nothing -> enclosing

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
