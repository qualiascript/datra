module Interpreting.Obsolete.SyntaxEnvironment
  ( ObsoleteSyntaxEvaluation (..)
  , obsoleteSyntaxContext
  ) where

import Data.Maybe (mapMaybe)
import DatraLanguage.AST
import DatraLanguage.DependentDeclaration
import DatraTypes
import DatraTypes.Module.Source
import DatraTypes.Resolution
import DatraTypes.Scope
import Evaluation.Scope
import Evaluation.Scope.GenericProtection (genericContinuationHandoff)
import Interpreting.Syntax (assembleImplicitSyntaxResource)
import StringInterpolation
import SyntaxRewriting

-- | OBSOLETE compatibility capabilities for the parallel SyntaxContext model.
-- Delete this record together with this module once syntax rules are indexed by
-- the dependent declaration layers in Scope.
data ObsoleteSyntaxEvaluation = ObsoleteSyntaxEvaluation
  { obsoleteDeclareSyntaxScope
      :: Scope -> [Expression] -> Either InterpretingError Scope
  , obsoleteEvaluateInScope
      :: Scope -> ResolutionStack -> Expression
      -> Either InterpretingError InterpretedValue
  , obsoletePrepareSyntaxValidationDeclaration :: Expression -> Expression
  }

moduleSyntaxRules
  :: [(String, String, [SyntaxRule])]
  -> [Expression]
  -> Expression
  -> [SyntaxRule]
moduleSyntaxRules availableRules =
  scopeSyntaxRules
    (\_ kind -> kind)
    [ (namespace, rules)
    | (_, namespace, rules) <- availableRules
    ]

scopeSyntaxNamespaces :: Expression -> [String]
scopeSyntaxNamespaces source = case source of
  IdentifierReference (SimpleIdentifierString selected) -> [selected]
  _ -> []

scopeSyntaxRules
  :: ([Expression] -> DeclarativeCapture -> DeclarativeCapture)
  -> [(String, [SyntaxRule])]
  -> [Expression]
  -> Expression
  -> [SyntaxRule]
scopeSyntaxRules classify availableRules declarations source =
  localSyntaxRules classify declarations source <>
  concat
    [ rules
    | selected <- scopeSyntaxNamespaces source
    , (namespace, rules) <- availableRules
    , namespace == selected
    ]

ruleHasAnyName :: [String] -> SyntaxRule -> Bool
ruleHasAnyName names = any (`elem` names) . syntaxRuleLiteralHeads

syntaxRuleLiteralHeads :: SyntaxRule -> [String]
syntaxRuleLiteralHeads rule = case declarativeMatcherPlan rule of
  IdentifierApplicationMatcher patternValue ->
    expressionHead (identifierApplicationHead patternValue)
  LiteralExpressionMatcher (LiteralExpressionPattern parts) -> take 1
    [ literal
    | LiteralExpressionPatternLiteral literal <- parts
    , not (null literal)
    ]
  where
    expressionHead expressionValue = case expressionValue of
      IdentifierReference (SimpleIdentifierString name) -> [name]
      _ -> []

-- A lexical map can introduce syntax in exactly the same way as an installed
-- module.  Its rules are visible only on the right side of an access to that
-- map, and are specialized against the declarations visible both outside and
-- inside the map.
localSyntaxRules
  :: ([Expression] -> DeclarativeCapture -> DeclarativeCapture)
  -> [Expression]
  -> Expression
  -> [SyntaxRule]
localSyntaxRules classify declarations source =
  case localScopeDeclarations declarations source of
    [] -> []
    local -> snd (foldl introduce (enclosingDeclarations, []) local)
  where
    enclosingDeclarations = case localScopeName source of
      Nothing -> declarations
      Just name -> filter (notElem name . bindingNames) declarations
    introduce (visible, rules) declaration =
      (retainedDeclarations <> [declaration], retainedRules <> introduced)
      where
        names = bindingNames declaration
        retainedDeclarations = filter
          (null . filter (`elem` names) . bindingNames)
          visible
        retainedRules = filter (not . ruleHasAnyName names) rules
        introduced = map (specialize visible)
          (declarationRules declaration)
    specialize visible = mapSyntaxRuleCaptures (specializeCapture visible)
    specializeCapture visible kind = case kind of
      StringExpressionCapture LiteralString {} -> kind
      _ -> classify visible kind

localScopeName :: Expression -> Maybe String
localScopeName source = case source of
  IdentifierReference (SimpleIdentifierString name) -> Just name
  SyntaxBoundary inner -> localScopeName inner
  _ -> Nothing

localScopeDeclarations :: [Expression] -> Expression -> [Expression]
localScopeDeclarations declarations source = case source of
  IdentifierReference (SimpleIdentifierString name) ->
    case
        [ dependentDeclarationImplementation binding
        | declaration <- reverse declarations
        , Just binding <- [dependentDeclaration declaration]
        , name `elem` bindingNames declaration
        ] of
      value : _ -> mapScopeEntries value
      [] -> []
  SyntaxBoundary inner -> localScopeDeclarations declarations inner
  _ -> []

mapScopeEntries :: Expression -> [Expression]
mapScopeEntries value = case value of
  AtlasMap entries -> entries
  MapSequence entries -> entries
  MapConcatenation left right ->
    mapScopeEntries left <> mapScopeEntries right
  SyntaxBoundary inner -> mapScopeEntries inner
  _ -> []

classifySyntaxHoles
  :: ObsoleteSyntaxEvaluation
  -> Scope
  -> [(String, ModuleSource)]
  -> [Expression]
  -> [DeclarativeCapture]
  -> [(DeclarativeCapture, Maybe InterpretedValue)]
classifySyntaxHoles evaluation base modules declarations = map classify
  where
    enclosing = extendModuleCatalog modules base
    declared = obsoleteDeclareSyntaxScope evaluation enclosing
      (map (obsoletePrepareSyntaxValidationDeclaration evaluation) declarations)
    classify kind = case kind of
      StringExpressionCapture valueKind@(ValueString target) ->
        case declared >>= \scope ->
            obsoleteEvaluateInScope evaluation scope [] target of
          Left _ -> (kind, Nothing)
          Right value ->
            ( StringExpressionCapture
                (specializeStringExpression value valueKind)
            , Just value
            )
      _ -> (kind, Nothing)

evaluateSyntaxValue
  :: ObsoleteSyntaxEvaluation
  -> Scope
  -> [(String, ModuleSource)]
  -> [Expression]
  -> Expression
  -> Maybe InterpretedValue
evaluateSyntaxValue evaluation base modules declarations expressionValue = do
  let enclosing = extendModuleCatalog modules base
  scope <- either (const Nothing) Just
    (obsoleteDeclareSyntaxScope evaluation enclosing
      (map (obsoletePrepareSyntaxValidationDeclaration evaluation) declarations))
  either (const Nothing) Just
    (obsoleteEvaluateInScope evaluation scope [] expressionValue)

syntaxResultType
  :: ObsoleteSyntaxEvaluation
  -> Scope
  -> [(String, ModuleSource)]
  -> [Expression]
  -> Expression
  -> Maybe InterpretedValue
syntaxResultType evaluation base modules declarations expressionValue =
  case expressionValue of
    Equality {} -> booleanType
    Inequality {} -> booleanType
    LessThan {} -> booleanType
    LessThanOrEqual {} -> booleanType
    GreaterThan {} -> booleanType
    GreaterThanOrEqual {} -> booleanType
    _ -> evaluateSyntaxValue evaluation base modules declarations expressionValue
  where
    booleanType = evaluateSyntaxValue evaluation base modules declarations BooleanType

-- OBSOLETE: parser scope contains a second, structural-only view of rule
-- visibility and nominal types.  Scope-owned declaration families replace it.
obsoleteSyntaxContext
  :: ObsoleteSyntaxEvaluation
  -> Scope
  -> [(String, ModuleSource)]
  -> [(String, String, [SyntaxRule])]
  -> [SyntaxRule]
  -> [Expression]
  -> SyntaxContext
obsoleteSyntaxContext evaluation base modules availableRules initialRules
    initialDeclarations =
  make base initialDeclarations initialFamilies
  where
    initialFamilies =
      externalFamily base initialDeclarations initialRules
        : declarationFamilies base initialDeclarations

    make currentBase declarations families = context
      where
        context = SyntaxContext
          { contextSourceSpan = Nothing
          , contextRuleFamilies = filter
              (not . null . syntaxRuleFamilyRules)
              families
          , contextClassify = classifySyntaxHoles evaluation
              currentBase modules declarations
          , contextResultType = syntaxResultType evaluation
              currentBase modules declarations
          , contextAssembleImplicitResource = assembleImplicitSyntaxResource
          , contextRewriteScope = rewriteScope context
          , contextPublish = publish currentBase declarations families
          , contextRecursive = recursive currentBase declarations families
          , contextScope = scoped currentBase declarations families
          , contextEnter = enter currentBase declarations families
          }
    rewriteScope environment locus = case locus of
      RewriteExpression expressionValue ->
        expressionScope environment expressionValue
      RewriteChild parent cursor child ->
        expressionScope (scopeAt cursor (childScopes parent)) child
      where
        childScopes expressionValue = case expressionValue of
          MaybeThen _ _ ->
            [ environment
            , contextEnter environment Nothing
            ]
          ScopeAccess source _ ->
            [ environment
            , (contextEnter (contextScope environment source) Nothing)
                { contextSourceSpan = contextSourceSpan environment }
            ]
          ScopedExpression source _ ->
            [ environment
            , (contextEnter (contextScope environment source) Nothing)
                { contextSourceSpan = contextSourceSpan environment }
            ]
          WithScopes sources _ ->
            replicate (length sources) environment <>
              [ (contextEnter
                    (foldl contextScope environment sources)
                    Nothing)
                  { contextSourceSpan = contextSourceSpan environment }
              ]
          _ -> map (const environment)
            (expressionChildren expressionValue)
        scopeAt selected = maybe environment id
          . listHead . drop selected
        listHead [] = Nothing
        listHead (selected : _) = Just selected

    expressionScope environment expressionValue = case expressionValue of
      AtlasMap entries -> contextRecursive environment entries
      Begin declarations result -> contextRecursive
        (contextEnter environment Nothing)
        (map DeclarationExpression declarations <> [result])
      FunctionBody declarations result -> contextRecursive
        (contextEnter environment Nothing)
        (map DeclarationExpression declarations <> [result])
      _ -> environment

    publish currentBase declarations families entry = do
      let resolved = entry
      _ <- dependentDeclaration resolved
      let names = bindingNames entry
          retainedDeclarations = retainDeclarations names declarations
          retainedFamilies = retainFamilies names families
          nextDeclarations = retainedDeclarations <> [entry]
          introduced = declarationFamily currentBase retainedDeclarations
            entry resolved
      pure (make currentBase nextDeclarations
        (retainedFamilies <> [introduced]))

    recursive currentBase declarations families entries =
      foldl publishLet (make currentBase declarations families)
        [ entry
        | entry <- entries
        , maybe False dependentDeclarationIsLet
            (dependentDeclaration entry)
        ]
      where
        publishLet context entry =
          case contextPublish context entry of
            Just next -> next
            Nothing -> context

    scoped currentBase declarations families source =
      make currentBase declarations
        (families <> [externalFamily currentBase declarations rules])
      where
        rules = moduleSyntaxRules availableRules declarations source

    enter currentBase declarations families input =
      make child [] families
      where
        enclosing = extendModuleCatalog modules currentBase
        declared = obsoleteDeclareSyntaxScope evaluation enclosing
          (map (obsoletePrepareSyntaxValidationDeclaration evaluation) declarations)
        parent = either (const enclosing) id declared
        child = enterScope input genericContinuationHandoff parent

    declarationFamilies currentBase = snd . foldl introduce ([], [])
      where
        introduce (visible, families) entry =
          case dependentDeclaration resolved of
            Nothing -> (visible, families)
            Just _ ->
              let names = bindingNames entry
                  retained = retainDeclarations names visible
                  next = retained <> [entry]
              in ( next
                 , retainFamilies names families <>
                    [declarationFamily currentBase retained entry resolved]
                 )
          where
            resolved = entry

    declarationFamily currentBase visible entry resolved = SyntaxRuleFamily
      { syntaxRuleFamilyNames = bindingNames entry
      , syntaxRuleFamilyRules =
          [ (branch, specialize rule)
          | (_, branch, rule) <-
              declarationRuleBranches resolved
          ]
      , syntaxRuleFamilyEvaluate = evaluateSyntaxValue evaluation
          currentBase modules visible
      }
      where
        specialize = id

    externalFamily currentBase declarations rules = SyntaxRuleFamily
      { syntaxRuleFamilyNames = concatMap syntaxRuleLiteralHeads rules
      , syntaxRuleFamilyRules = map (0,) rules
      , syntaxRuleFamilyEvaluate = evaluateSyntaxValue evaluation
          currentBase modules declarations
      }

    retainDeclarations names = filter
      (null . filter (`elem` names) . bindingNames)
    retainFamilies names = mapMaybe retain
      where
        retain family =
          let retained = filter
                (not . ruleHasAnyName names . snd)
                (syntaxRuleFamilyRules family)
          in if null retained
              then Nothing
              else Just family { syntaxRuleFamilyRules = retained }

