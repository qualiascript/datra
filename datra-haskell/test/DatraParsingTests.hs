{-# LANGUAGE PostfixOperators #-}
{-# LANGUAGE PatternSynonyms #-}

module DatraParsingTests (main) where

import Data.Char (chr, toUpper)
import DatraLanguage.AST
  ( Expression (..)
  , DependentDeclaration (..)
  , DependentDeclarationHead (..)
  , GenericBinder (..)
  , GenericBinderId (..)
  , GenericIdentifier (..)
  , GenericIntroduction (..)
  , GenericPolarity (..)
  , GenericReference (..)
  , GenericReferenceRole (..)
  , IdentifierString (IdentifierString)
  , StringTemplatePart (..)
  , pattern FunctionType
  , pattern GenericFunctionType
  , expressionChildren
  , normalizeExpression
  , renderExpression
  , toOperatorExpression
  )
import DatraLanguage.DependentDeclaration (dependentDeclaration)
import DatraLanguage.AST.Syntax
  ( natural
  , (...)
  , (<:>)
  , (<+>)
  , (<..>)
  , (..+)
  , (..-)
  , (<.>)
  , (<@>)
  , (~>)
  )
import DatraLanguage.AST.Syntax qualified as AST
import DatraLanguage.AST.Reserved qualified as Reserved
import DatraLanguage.AST.Source (renderSourceExpression)
import DatraLanguage.SyntaxTemplate qualified as SyntaxTemplate
import DatraLanguage.SyntaxTemplate (TemplateSelection (..))
import DatraLanguage.Diagnostics
  ( Located (Located, locatedValue)
  , SourcePosition (SourcePosition)
  , SourceSpan (SourceSpan)
  , withoutSourceSpan
  )
import DatraLanguage.Diagnostics.Application
  ( ParseFailure )
import DatraLanguage.Diagnostics.Localization
  ( Locale (English)
  , renderDatraError
  )
import DatraLanguage.Identifier qualified as Identifier
import Interpreting
  ( StandardLibraryVisibility (NoStandardLibrary, QualifiedStandardLibrary)
  , parseDatraSourceLocatedWithImportsAndStandardLibrary
  , parseDatraSourceLocatedWithImportsAndStandardLibraryVisibility
  )
import Parsing
  ( FunctionTypeIdentifier (..)
  , PreparedFunctionDomain (..)
  , PreparedFunctionDomainKind (..)
  , PreparedFunctionDomainMember (..)
  , ResourceEnvelope (..)
  , functionTypeIdentifiers
  , neutralExpressionWitnessSources
  , prepareFunctionDomain
  , prepareFunctionDomainExpression
  , parseDatra
  , parseDatraAst
  , parseDatraRawLocatedWithSourceName
  , parseNeutralPhrase
  )
import SyntaxDefinitions
  ( SyntaxHoleKind (..)
  , SyntaxPiece (..)
  , SyntaxRule (..)
  , SyntaxRuleSemantics (..)
  , SyntaxTemplate (..)
  , declarationRuleBranches
  , declarationRules
  , expandSyntax
  )
import SyntaxTemplateAdmissibility (validateSyntaxTemplate)
import SyntaxTemplateMatching
  ( SyntaxTemplateMatchFailure (..)
  , matchSyntaxRules
  )
import Numeric (showHex)
import Hedgehog qualified as H
import Hedgehog.Gen qualified as Gen
import Hedgehog.Range qualified as Range
import Test.Tasty (TestTree, defaultMain, testGroup)
import Test.Tasty.Hedgehog (testProperty)
import Test.Tasty.HUnit (assertBool, assertEqual, assertFailure, testCase)

main :: IO ()
main = defaultMain testTree

renderParseFailure :: ParseFailure -> String
renderParseFailure = renderDatraError English . withoutSourceSpan

testTree :: TestTree
testTree =
  testGroup "Datra parser"
    [ testCase "brace separator semantics" testBraceSeparatorSemantics
    , testCase "bundled module block shape" assertBundledModuleBlockShape
    , testCase "standard syntax declarations are admissible"
        assertStandardSyntaxDeclarationsAdmissible
    , testCase "generic AST representation" testGenericAstRepresentation
    , testCase "generic source parsing" testGenericSourceParsing
    , testCase "dependent declaration precedence"
        testDependentDeclarationPrecedence
    , testCase "dependent arguments and argumentative maps"
        testRenamedArgumentConcepts
    , testCase "syntax regressions" regressionTests
    , testGroup "properties"
        [ testProperty "rendered ASTs parse canonically" propAstRoundTrip
        , testProperty "natural maps parse in order" propNaturalMapParsing
        ]
    ]

testRenamedArgumentConcepts :: IO ()
testRenamedArgumentConcepts = do
  assertParsed "dependent argument source form"
    "value : Int"
    (AST.dependentArgumentType "value" (ref "Int"))
  assertParsed "argumentative map source form"
    "{value : Int; 2}"
    (ArgumentativeMap
      [ AST.dependentArgumentType "value" (ref "Int")
      , natural 2
      ])

testGenericAstRepresentation :: IO ()
testGenericAstRepresentation = do
  let binderIdentity = GenericBinderId 0
      binder = GenericBinder
        { genericBinderId = binderIdentity
        , genericBinderPolarity = GenericProduct
        , genericBinderIdentifier = genericIdentifier "_T" False
        , genericBinderBound = ref "IntLimit"
        , genericBinderSource = Nothing
        }
      declaration = GenericReferenceExpression (GenericReference
        binderIdentity
        GenericDeclarationReference)
      reference = GenericReferenceExpression (GenericReference
        binderIdentity
        GenericUseReference)
      signature = GenericFunctionType
        [binder]
        (FunctionApplication (ref "Args") declaration)
        reference
      rawIntroduction = GenericIntroductionExpression (GenericIntroduction
        GenericSum
        (genericIdentifier "T" True)
          (ref "Any")
          Nothing)
  assert "raw generic introductions retain polarity and optional public names"
    (renderSourceExpression rawIntroduction == "^T?")
  assert "resolved function types reconstruct the declaration anchor"
    (renderSourceExpression signature == "(Args (&_T :: IntLimit)) -> _T")
  assert "function types own binder bounds as immediate AST children"
    (expressionChildren signature
      == [ ref "IntLimit"
         , FunctionApplication (ref "Args") declaration
         , reference
         ])
  assert "normalization preserves the ordered generic prefix"
    (normalizeExpression signature == signature)
  assertEqual
    "canonical AST rendering preserves binder identity and occurrence role"
    "(generic-function-type (generic-prefix (generic-binder 0 & (ref $_T) (ref $IntLimit))) (apply-func (ref $Args) (generic-reference 0 declaration)) (generic-reference 0 use))"
    (renderExpression signature)
  assertAstRoundTrip "generic function AST" (renderExpression signature)

testGenericSourceParsing :: IO ()
testGenericSourceParsing = do
  unowned <- parseGenericSource "&T?"
  case unowned of
    GenericIntroductionExpression introduction ->
      assert "an unowned introduction remains a raw AST node"
        ( genericIntroductionPolarity introduction == GenericProduct
          && genericIntroductionIdentifier introduction
            == genericIdentifier "T" True
        )
    other -> fail ("unexpected raw generic introduction: " <> show other)

  parsed <- parseGenericSource
    "{value? : &T? :: Any} -> T"
  case parsed of
    FunctionTypeExpression [binder]
        (ArgumentativeMap
          [OptionalType
            (IdentifierOperation (IdentifierString "value") declaration Nothing)])
        reference -> do
      assert "optional generic name is stored on the simple identifier"
        ( genericBinderPolarity binder == GenericProduct
          && genericBinderIdentifier binder == genericIdentifier "T" True
        )
      assert "the marked occurrence becomes the declaration reference"
        (declaration == genericReference binder GenericDeclarationReference)
      assert "the codomain occurrence becomes a use reference"
        (reference == genericReference binder GenericUseReference)
      assert "optional naming does not wrap the declaration as an optional value"
        (case declaration of OptionalType {} -> False; _ -> True)
    other -> fail ("unexpected optional generic AST: " <> show other)

  privateParsed <- parseGenericSource
    "{Args (&_T :: IntLimit),} -> _T"
  case privateParsed of
    FunctionTypeExpression [binder] domain reference -> do
      assert "private generic identifiers retain ordinary privacy spelling"
        (genericBinderIdentifier binder == genericIdentifier "_T" False)
      assert "private generic codomain references use binder identity"
        (reference == genericReference binder GenericUseReference)
      case prepareFunctionDomain [binder] domain of
        PreparedFunctionDomain PreparedArgumentFunctionDomain
            [ PreparedGenericFunctionDomainMember preparedBinder
            , PreparedOrdinaryFunctionDomainMember _
            ] ->
          assert "argument domains expose generic binders as real prefix members"
            (preparedBinder == binder)
        prepared -> fail ("unexpected prepared argument domain: " <> show prepared)
    other -> fail ("unexpected private generic AST: " <> show other)

  ordered <- parseGenericSource
    "(a : _T; b : &_T) -> _T"
  case ordered of
    FunctionTypeExpression [binder] domain _ ->
      case prepareFunctionDomain [binder] domain of
        PreparedFunctionDomain PreparedOrderedFunctionDomain
            [ PreparedGenericFunctionDomainMember preparedBinder
            , PreparedOrdinaryFunctionDomainMember _
            , PreparedOrdinaryFunctionDomainMember _
            ] ->
          assert "ordered domains retain generic prefix position"
            (preparedBinder == binder)
        prepared -> fail ("unexpected prepared ordered domain: " <> show prepared)
    other -> fail ("unexpected ordered generic AST: " <> show other)

  forwardDomainUse <- parseGenericSource
    "(x : T; y : ^T) -> Any"
  case forwardDomainUse of
    FunctionTypeExpression [binder]
        domain@(SyntaxBoundary
          (AtlasMap
            [ IdentifierOperation (IdentifierString "x") firstUse Nothing
            , IdentifierOperation (IdentifierString "y") declaration Nothing
            ])) _ -> do
      assert "ordinary entries may use a generic before its written marker"
        ( firstUse == genericReference binder GenericUseReference
          && declaration
            == genericReference binder GenericDeclarationReference
        )
      case prepareFunctionDomain [binder] domain of
        PreparedFunctionDomain PreparedOrderedFunctionDomain
            [ PreparedGenericFunctionDomainMember _
            , PreparedOrdinaryFunctionDomainMember _
            , PreparedOrdinaryFunctionDomainMember _
            ] -> pure ()
        prepared -> fail
          ("unexpected prepared forward-use domain: " <> show prepared)
      case prepareFunctionDomainExpression [binder] domain of
        AtlasMap
            [ IdentifierOperation (IdentifierString "T") _ Nothing
            , IdentifierOperation (IdentifierString "x")
                (IdentifierReference (IdentifierString "T")) Nothing
            , IdentifierOperation (IdentifierString "y")
                (IdentifierReference (IdentifierString "T")) Nothing
            ] -> pure ()
        prepared -> fail
          ("unexpected lowered forward-use domain: " <> show prepared)
    other -> fail ("unexpected forward generic use AST: " <> show other)

  sumParsed <- parseGenericSource
    "{value? : ^T? :: Any} -> Any"
  case sumParsed of
    FunctionTypeExpression [binder] _ _ ->
      assert "sum generics use the same optional-name representation"
        ( genericBinderPolarity binder == GenericSum
          && genericBinderIdentifier binder == genericIdentifier "T" True
        )
    other -> fail ("unexpected sum generic AST: " <> show other)

  mixed <- parseGenericSource
    "{a? : ^S; b? : &T; c? : ^U} -> Any"
  case mixed of
    FunctionTypeExpression binders domain _ -> do
      assert "mixed generic prefixes retain source polarity order"
        (map genericBinderPolarity binders
          == [GenericSum, GenericProduct, GenericSum])
      case prepareFunctionDomain binders domain of
        PreparedFunctionDomain PreparedArgumentFunctionDomain members ->
          assert "mixed generic binders precede every ordinary domain member"
            ( map preparedPolarity (take 3 members)
                == map Just [GenericSum, GenericProduct, GenericSum]
              && all isOrdinary (drop 3 members)
            )
        prepared -> fail ("unexpected prepared mixed domain: " <> show prepared)
      case prepareFunctionDomainExpression binders domain of
        ArgumentativeMap
            ( IdentifierOperation (IdentifierString "S") _ Nothing
            : IdentifierOperation (IdentifierString "T") _ Nothing
            : IdentifierOperation (IdentifierString "U") _ Nothing
            : _
            ) -> pure ()
        prepared -> fail ("unexpected lowered mixed domain: " <> show prepared)
    other -> fail ("unexpected mixed generic AST: " <> show other)

  quoted <- parseGenericSource
    "{value? : &\"T-name\"?} -> Any"
  case quoted of
    FunctionTypeExpression [binder] _ _ ->
      assert "quoted simple identifiers remain valid generic names"
        (genericBinderIdentifier binder == genericIdentifier "T-name" True)
    other -> fail ("unexpected quoted generic AST: " <> show other)

  assertGenericRejected "parenthesized generic identifier is rejected"
    "{value? : &(T?)} -> T"
  assertGenericRejected "dependent generic identifier is rejected"
    "{value? : &\"Type%(it)\"?} -> Any"
  assertGenericRejected "private optional generic name is rejected"
    "{value? : &_T?} -> Any"
  duplicate <- parseGenericSource
    "{a? : &T; b? : ^T?} -> T"
  case duplicate of
    FunctionTypeExpression [first, second] _ _ ->
      assert "duplicate generic declarations remain available to compilation"
        ( genericBinderIdentifier first == genericIdentifier "T" False
          && genericBinderIdentifier second == genericIdentifier "T" True
          && genericBinderPolarity first == GenericProduct
          && genericBinderPolarity second == GenericSum
          && genericBinderId first /= genericBinderId second
        )
    other -> fail ("duplicate generic declarations were not retained: "
      <> show other)

  collision <- parseGenericSource
    "{T? : Any; marker? : &T} -> (T : Any)"
  case collision of
    FunctionTypeExpression [_]
        domain@(ArgumentativeMap
          [ OptionalType (IdentifierOperation domainName _ Nothing)
          , OptionalType (IdentifierOperation _ _ Nothing)
          ])
        codomain@(SyntaxBoundary
          (IdentifierOperation codomainName _ Nothing)) -> do
      assert "ordinary collision candidates remain declarations for semantic validation"
        ( domainName == IdentifierString "T"
          && codomainName == IdentifierString "T"
        )
      assertEqual "parsing classifies complete function-type scope identifiers"
        [ SimpleFunctionTypeIdentifier (IdentifierString "T")
        , SimpleFunctionTypeIdentifier (IdentifierString "marker")
        , SimpleFunctionTypeIdentifier (IdentifierString "T")
        ]
        (functionTypeIdentifiers domain <> functionTypeIdentifiers codomain)
    other -> fail ("generic collision candidates were not retained: "
      <> show other)

  nested <- parseGenericSource
    "{outer? : &T; inner? : ({value? : &T} -> T)} -> T"
  case nested of
    FunctionTypeExpression [outerBinder] domain _ ->
      case
          [ innerBinder
          | FunctionTypeExpression [innerBinder] _ _ <- descendants domain
          ] of
        [innerBinder] -> assert "nested function domains may shadow a generic"
          (genericBinderId outerBinder /= genericBinderId innerBinder)
        _ -> fail ("nested generic function was not preserved: " <> show domain)
    other -> fail ("unexpected nested generic AST: " <> show other)
  where
    genericReference binder role =
      GenericReferenceExpression
        (GenericReference (genericBinderId binder) role)
    descendants expressionValue =
      expressionValue : concatMap descendants (expressionChildren expressionValue)
    preparedPolarity member =
      case member of
        PreparedGenericFunctionDomainMember binder ->
          Just (genericBinderPolarity binder)
        PreparedOrdinaryFunctionDomainMember _ -> Nothing
    isOrdinary PreparedOrdinaryFunctionDomainMember {} = True
    isOrdinary _ = False

genericIdentifier :: String -> Bool -> GenericIdentifier
genericIdentifier name optionalName =
  GenericIdentifier (IdentifierString name) optionalName

parseGenericSource :: String -> IO Expression
parseGenericSource source =
  case parseDatra ("(" <> source <> "\n)") of
    Left failure -> fail
      ("unexpected generic parse failure: " <> renderParseFailure failure)
    Right expressionValue -> pure expressionValue

assertGenericRejected :: String -> String -> IO ()
assertGenericRejected label source =
  case parseDatra ("(" <> source <> "\n)") of
    Left _ -> pure ()
    Right expressionValue ->
      fail (label <> ": unexpectedly parsed as " <> show expressionValue)

testBraceSeparatorSemantics :: IO ()
testBraceSeparatorSemantics = do
  assertAstOutput "comma concatenates inside braces"
    "{1, 2}"
    (ArgumentativeMap [MapConcatenation (natural 1) (natural 2)])
  assertAstOutput "semicolon sequences argumentative-map members"
    "{1; 2}"
    (ArgumentativeMap [natural 1, natural 2])
  assertParsed "postfix comma remains inside argumentative-map syntax"
    "{Args Int,}"
    (ArgumentativeMap
      [MapConcatenation
        (FunctionApplication (ref "Args") (ref "Int")) (AtlasMap [])])
  assertParsed "postfix comma is the same operator in parentheses"
    "(Args Int,)"
    (MapConcatenation
      (FunctionApplication (ref "Args") (ref "Int")) (AtlasMap []))

testDependentDeclarationPrecedence :: IO ()
testDependentDeclarationPrecedence = do
  assertNeutral
    "template federation binds before dependent declaration assignment"
    source
    expected
  assertNeutral
    "string and greedy-template concatenation is one declaration head"
    "\"_\",%($hello; Int) := body"
    (IdentifierTemplateOperation
      [StringTemplateInterpolation
        (SyntaxBoundary
          (MapConcatenation
            (AST.asciiString "_")
            (SyntaxBoundary
              (GreedyStringTemplate
                (SyntaxBoundary
                  (AtlasMap [AST.asciiString "hello", ref "Int"]))))))]
      (ref "body")
      (Just (ref "body")))
  case (dependentDeclaration expected, declarationRuleBranches expected) of
    (Just declaration, branches) ->
      assertEqual
        "compiled syntax branches retain dependent-declaration identity and order"
        [ (declaration, 0)
        , (declaration, 1)
        ]
        [ (owner, branch) | (owner, branch, _) <- branches ]
    _ -> assertFailure "dependent declaration did not compile into syntax rules"
  where
    source = "\"verify %_Expr\" | \"verify %($hard) %_Expr\" := body"
    expected = IdentifierTemplateOperation
      [StringTemplateInterpolation
        (SyntaxBoundary
          (EitherType
            (StringTemplate
              [ StringTemplateLiteral "verify "
              , StringTemplateInterpolation (ref "_Expr")
              ])
            (StringTemplate
              [ StringTemplateLiteral "verify "
              , StringTemplateInterpolation (AST.asciiString "hard")
              , StringTemplateLiteral " "
              , StringTemplateInterpolation (ref "_Expr")
              ])))]
      (ref "body")
      (Just (ref "body"))
    assertNeutral label input wanted =
      case parseNeutralPhrase input of
        Left failure -> assertFailure (renderParseFailure failure)
        Right actual -> assertEqual label wanted actual

regressionTests :: IO ()
regressionTests = do
  assert "compact underscore identifiers are private"
    (Identifier.isPrivateIdentifier "_private")
  assert "apostrophe identifiers are ordinary public identifiers"
    (not (Identifier.isPrivateIdentifier "'fixed"))
  assert "quoted private names use the same privacy rule as compact names"
    (Identifier.isPrivateIdentifier "_ private")
  assert "quoted apostrophe names are ordinary public identifiers"
    (not (Identifier.isPrivateIdentifier "''not compact"))
  assertParsed "an explicit resource does not introduce surface this"
    "this" (ref "this")
  assertParsed "an explicit resource does not introduce surface it"
    "it" (ref "it")
  case parseSource "yield this" of
    Right actual
      | actual == Begin [] (ref "this") -> pure ()
      | otherwise -> fail
          ("implicit resource rewrote surface this: " <> show actual)
    Left failure -> fail
      ("implicit resource unexpectedly failed: " <> renderParseFailure failure)
  case parseSource "begin yield 5" of
    Right actual
      | actual == Begin [] (Begin [] (natural 5)) -> pure ()
      | otherwise -> fail
          ("top-level begin had the wrong block shape: " <> show actual)
    Left failure -> fail
      ("top-level begin unexpectedly failed: " <> renderParseFailure failure)
  assertParsed "a nested begin introduces surface this"
    "value := begin yield this"
    (AST.assignment "value"
      (Begin [] (ref "this"))
      (Begin [] (ref "this")))
  assertParsed "explicit contextual depth remains an ordinary application"
    "_this 2"
    (FunctionApplication
      (IdentifierReference (IdentifierString "_this"))
      (EllipsisNatural 2))
  assert "contextual depth renders as an ordinary application"
    ( renderSourceExpression
        (FunctionApplication
          (IdentifierReference (IdentifierString "_this"))
          (EllipsisNatural 2))
        == "_this 2"
    )
  assert "literal template text cannot manufacture interpolation holes"
    ((SyntaxTemplate.literalSyntaxTemplate "%Int++" :: SyntaxTemplate ())
      == SyntaxTemplate [SyntaxLiteral "%Int++"])
  assert "the neutral reader retains an unknown postfix symbolic literal"
    (case parseDatraRawLocatedWithSourceName "<postfix-syntax>" "(2++)" of
      Right (_, Located _ parsed) ->
        parsed == SyntaxBoundary
          (FunctionApplication (natural 2) (ref "++"))
      Left _ -> False)
  let holeKinds =
        [ ExpressionSyntaxHole (ref "_Expr")
        , BlockSyntaxHole (ref "_Block")
        , FunctionBodySyntaxHole (ref "_FunctionBody")
        , DeclarationSyntaxHole (ref "_DependentDeclaration")
        , DependentArgumentSyntaxHole (ref "_DependentArgument")
        , ValueSyntaxHole (ref "Int")
        ]
  assert "admissibility covers every typed hole kind"
    (all
      (\kind -> validateSyntaxTemplate
        (SyntaxTemplate [SyntaxHole kind]) == Right ())
      holeKinds)
  assert "expression witnesses remain recoverable after a literal prefix"
    (validateSyntaxTemplate
      (SyntaxTemplate
        [ SyntaxLiteral "call"
        , SyntaxHole (ExpressionSyntaxHole (ref "_Expr"))
        ]) == Right ())
  assert "expression witnesses remain recoverable before a literal suffix"
    (validateSyntaxTemplate
      (SyntaxTemplate
        [ SyntaxHole (ExpressionSyntaxHole (ref "_Expr"))
        , SyntaxLiteral "after"
        ]) == Right ())
  assert "multiple holes retain both adjacent literal boundaries"
    (validateSyntaxTemplate
      (SyntaxTemplate
        [ SyntaxLiteral "left"
        , SyntaxHole (ExpressionSyntaxHole (ref "_Expr"))
        , SyntaxLiteral "middle"
        , SyntaxHole (ExpressionSyntaxHole (ref "_Expr"))
        ]) == Right ())
  assert "the parser-owned expression witness inventory remains parseable"
    (all
      (\source -> case parseNeutralPhrase source of
        Right _ -> True
        Left _ -> False)
      (neutralExpressionWitnessSources "_witness" "_operand"))
  let zeroCaptureSyntax = SyntaxRule
        { syntaxName = "answer"
        , syntaxTemplate = SyntaxTemplate []
        , syntaxSemantics = SyntaxAdapter (ref "answer")
        }
  assert "zero-hole syntax supplies the empty capture tail"
    (expandSyntax zeroCaptureSyntax
      (TemplateSelection (ref "answer") [])
      == FunctionApplication
        (ref "answer")
        (AtlasMap []))
  let syntaxFunction name pieces = SyntaxRule
        { syntaxName = name
        , syntaxTemplate = SyntaxTemplate (SyntaxLiteral name : pieces)
        , syntaxSemantics = SyntaxAdapter (ref name)
        }
      intHole = SyntaxHole (ValueSyntaxHole (ref "Int"))
      intLimitHole = SyntaxHole (ValueSyntaxHole (ref "IntLimit"))
      fromPhrase = foldl FunctionApplication (ref "from")
        [natural 0, ref "to", ref "Infinity"]
      matchesNumericHole kind value = case (kind, value) of
        (ValueSyntaxHole (IdentifierReference (IdentifierString "Int")),
          EllipsisNatural _) -> True
        (ValueSyntaxHole (IdentifierReference (IdentifierString "Int")),
          Minus (EllipsisNatural _)) -> True
        (ValueSyntaxHole (IdentifierReference (IdentifierString "IntLimit")),
          EllipsisNatural _) -> True
        (ValueSyntaxHole (IdentifierReference (IdentifierString "IntLimit")),
          Minus (EllipsisNatural _)) -> True
        (ValueSyntaxHole (IdentifierReference (IdentifierString "IntLimit")),
          IdentifierReference
            (IdentifierString "Infinity")) -> True
        _ -> False
      wrongFrom = syntaxFunction "from"
        [intHole, SyntaxLiteral "to", intHole]
      correctFrom = syntaxFunction "from"
        [intHole, SyntaxLiteral "to", intLimitHole]
      unrelated = syntaxFunction "unrelated"
        [ intHole
        , SyntaxLiteral "to"
        , intLimitHole
        , SyntaxLiteral "with-more-template-text"
        ]
  assert "Int template holes reject an Infinity AST"
    (matchRules matchesNumericHole [wrongFrom] fromPhrase
      == Left NoMatchingSyntaxTemplate)
  assert "IntLimit template holes accept an Infinity AST"
    (let expected = expandSyntax correctFrom
          (TemplateSelection fromPhrase [natural 0, ref "Infinity"])
     in matchRules matchesNumericHole [correctFrom] fromPhrase
          == Right expected)
  assert "the explicit AST head selects the syntax binding"
    ( matchRules matchesNumericHole
        [unrelated, correctFrom]
        fromPhrase
        == matchRules matchesNumericHole [correctFrom] fromPhrase
    )
  assert "syntax templates rewrite an AST after it is read"
    (case parseSourceLocated False
        "<syntax-template-test>" "(from 0 to Infinity)" of
      Right (Located _ parsedPhrase) ->
        matchRules matchesNumericHole [correctFrom] parsedPhrase
          == matchRules matchesNumericHole [correctFrom] fromPhrase
      Left _ -> False)
  let nestedTailPhrase = foldl FunctionApplication (ref "from")
        [natural 0, AtlasMap [ref "to", ref "Infinity"]]
  assert "matching does not flatten through a nested AST boundary"
    (matchRules matchesNumericHole [correctFrom] nestedTailPhrase
      == Left NoMatchingSyntaxTemplate)
  let greedyRule = syntaxFunction "greedy"
        [ SyntaxHole (ValueSyntaxHole (ref "Prefix"))
        , SyntaxLiteral "marker"
        , SyntaxHole (ValueSyntaxHole (ref "Tail"))
        ]
      greedyPhrase = foldl FunctionApplication (ref "greedy")
        [ natural 1
        , ref "marker"
        , natural 2
        , ref "marker"
        , natural 3
        ]
      greedyPrefix = foldl FunctionApplication (natural 1)
        [ref "marker", natural 2]
      matchesGreedyHole kind value = case kind of
        ValueSyntaxHole (IdentifierReference (IdentifierString "Prefix")) ->
          True
        ValueSyntaxHole (IdentifierReference (IdentifierString "Tail")) ->
          value == natural 3
        _ -> False
  assert "holes match greedily inside the current AST boundary"
    (let expected = expandSyntax greedyRule
          (TemplateSelection greedyPhrase [greedyPrefix, natural 3])
     in matchRules matchesGreedyHole [greedyRule] greedyPhrase
          == Right expected)
  let contextualShort = syntaxFunction "contextual"
        [intHole]
      contextualLong = syntaxFunction "contextual"
        [intHole, SyntaxLiteral "marker", intHole]
      contextualPhrase = foldl FunctionApplication (ref "contextual")
        [natural 1, ref "marker", natural 2, ref "after"]
  assert "the first declaration wins and leaves its unmatched AST suffix"
    (let expanded = expandSyntax contextualShort
          (TemplateSelection contextualPhrase [natural 1])
     in matchRules matchesNumericHole
          [contextualShort, contextualLong]
          contextualPhrase
          == Right (foldl FunctionApplication expanded
            [ref "marker", natural 2, ref "after"]))
  let rankedShort = syntaxFunction "ranked"
        [SyntaxHole (ExpressionSyntaxHole (ref "_Expr"))]
      rankedLong = syntaxFunction "ranked"
        [ SyntaxHole (ExpressionSyntaxHole (ref "_Expr"))
        , SyntaxLiteral "marker"
        , SyntaxHole (ExpressionSyntaxHole (ref "_Expr"))
        ]
      rankedPhrase = foldl FunctionApplication (ref "ranked")
        [natural 1, ref "marker", natural 2]
  let rankedCapture = foldl FunctionApplication (natural 1)
        [ref "marker", natural 2]
  assert "the first declaration greedily takes its longest valid match"
    (let expected = expandSyntax rankedShort
          (TemplateSelection rankedPhrase [rankedCapture])
     in matchRules (const (const True))
          [rankedShort, rankedLong]
          rankedPhrase
          == Right expected)
  assertAstOutput "function arrows associate right"
    "Int -> Int -> Int" (FunctionType (ref "Int") (FunctionType (ref "Int") (ref "Int")))
  assertAstOutput "application associates left before arithmetic"
    "f 2 3 + 4" (Addition
      (FunctionApplication (FunctionApplication (IdentifierReference (IdentifierString "f")) (natural 2)) (natural 3))
      (natural 4))
  assertAstOutput "left overload"
    "a << b"
    (Overload (ref "a") (ref "b"))
  assertAstOutput "right overload reverses operands"
    "a >> b"
    (Overload (ref "b") (ref "a"))
  assertAstOutput "safe overload"
    "a <<< b"
    (SafeOverload (ref "a") (ref "b"))
  assertAstOutput "reverse safe overload reverses operands"
    "a >>> b"
    (SafeOverload (ref "b") (ref "a"))
  assertAstOutput "fun expands to an inline fixed point"
    "fun 5"
    (Fun (natural 5))
  assertParsed "removed with keyword is an ordinary identifier"
    "with T" (FunctionApplication (ref "with") (ref "T"))
  assertParsed "removed for keyword is an ordinary identifier"
    "for T" (FunctionApplication (ref "for") (ref "T"))
  assertAstOutput "not equals"
    "a =/= b"
    (Inequality (ref "a") (ref "b"))
  assertAstOutput "skip is a distinct positional symbol"
    "*"
    Skip
  assertAstOutput "a parenthesized skip remains the skip atom"
    "(*)"
    Skip
  assertAstOutput "a parenthesized skip is an explicit function argument"
    "f (*)"
    (FunctionApplication (ref "f") Skip)
  assertRejected "a bare skip is ambiguous after a function" "f *"
  assertAstOutput "parenthesized skips multiply without application ambiguity"
    "(*) * (*)"
    (Multiplication Skip Skip)
  assertRejected "bare left skip is ambiguous with multiplication" "* * 7"
  assertRejected "bare right skip is ambiguous with multiplication" "7 * *"
  assertAstOutput "coalization keeps a map operand at the current level"
    ">< (1; 2)"
    (Coalization (AtlasMap [natural 1, natural 2]))
  assertAstOutput "skip composes in an ordered map"
    "(*, 3)"
    (MapConcatenation Skip (natural 3))
  assertAstOutput "skip composes in an argumentative map"
    "{*; 3}"
    (ArgumentativeMap [Skip, natural 3])
  assertAstOutput "comma concatenates inside an argumentative map"
    "{*, 3}"
    (ArgumentativeMap [MapConcatenation Skip (natural 3)])
  assertAstOutput "rank-zero formulation remains an ordinary value"
    "((...) ^ 0, 3)"
    (MapConcatenation
      (Exponentiation EllipsisLiteral (natural 0))
      (natural 3))
  mapM_ (\value -> assertAstRoundTrip "new syntax AST roundtrip" (renderExpression value))
    [ Import ["library_one", "std"] (FunctionBody [] (natural 1))
    , InModule "std" (ref "_this")
    , ScopeAccess (ref "_this") (ref "abc")
    , FunctionBody [] (IdentifierReference (IdentifierString "x"))
    , Overload (natural 1) (natural 2)
    , Coalization (AtlasMap [natural 1, natural 2])
    , datraRef ["add"]
    , GenericIntroductionExpression (GenericIntroduction
        GenericProduct (genericIdentifier "T" True) (ref "Any") Nothing)
    , GenericIntroductionExpression (GenericIntroduction
        GenericSum (genericIdentifier "T" False) (ref "Any") Nothing)
    , Begin []
        (AST.assignment "Example"
          (Begin
            [declarationEntry (AST.assignment "x" (natural 1) (natural 1))]
            (FunctionApplication (ref "public") (ref "_this")))
          (Begin
            [declarationEntry (AST.assignment "x" (natural 1) (natural 1))]
            (FunctionApplication (ref "public") (ref "_this"))))
    ]
  assertAstOutput "eval is available as an ordinary user identifier"
    "eval : Nat" (AST.dependentArgumentType "eval" (ref "Nat"))
  assertAstOutput "eval identifier respects identifier boundaries"
    "evaluate : Nat" (AST.dependentArgumentType "evaluate" (ref "Nat"))
  assertAstOutput "argumentative map uses existing map arity"
    "{b := 8; 2}"
    (ArgumentativeMap [AST.assignment "b" (natural 8) (natural 8), natural 2])
  assertAstOutput "empty argumentative map" "{}" (ArgumentativeMap [])
  assertAstOutput "comma retains ordinary concatenation in braces"
    "{b := 8, 2}"
    (ArgumentativeMap
      [MapConcatenation
        (AST.assignment "b" (natural 8) (natural 8))
        (natural 2)])
  assertAstOutput "parenthesized concatenation remains one argument"
    "{(1, 2); 3}"
    (ArgumentativeMap [MapConcatenation (natural 1) (natural 2), natural 3])
  assertAstOutput "a trailing comma remains map concatenation"
    "{1, 2,}"
    (ArgumentativeMap
      [MapConcatenation
        (MapConcatenation (natural 1) (natural 2)) (AtlasMap [])])
  assertAstOutput "a unary trailing comma splices an argument federation"
    "{Args Int,}"
    (ArgumentativeMap
      [MapConcatenation
        (FunctionApplication (ref "Args") (ref "Int")) (AtlasMap [])])
  variadic <- parseGenericSource
    "{Args (&_T :: IntLimit),} -> _T?"
  case variadic of
    FunctionTypeExpression [binder]
        (ArgumentativeMap [MapConcatenation
          (FunctionApplication (IdentifierReference (IdentifierString "Args"))
            declaration)
          (AtlasMap [])])
        (OptionalType reference) ->
      let expectedDeclaration = GenericReferenceExpression
            (GenericReference (genericBinderId binder)
              GenericDeclarationReference)
          expectedReference = GenericReferenceExpression
            (GenericReference (genericBinderId binder) GenericUseReference)
          actualDeclaration = case declaration of
            SyntaxBoundary value -> value
            value -> value
      in assertEqual
          "generic declarations compose with trailing argument splices"
          (expectedDeclaration, expectedReference)
          (actualDeclaration, reference)
    other -> fail ("unexpected generic variadic domain: " <> show other)
  assertAstOutput "unary argumentative map" "{2}" (ArgumentativeMap [natural 2])
  assertAstOutput "argumentative map supports newline separators"
    "{1\n2}" (ArgumentativeMap [natural 1, natural 2])
  assertParsed "argumentative map AST round trip"
    "{a? : Nat; b? : Str}"
    (ArgumentativeMap
      [ OptionalType (AST.dependentArgumentType "a" (ref "Nat"))
      , OptionalType (AST.dependentArgumentType "b" (ref "Str"))
      ])
  assertRejected "private argument names cannot be optional"
    "{_x? : Nat; y : Nat}"
  let block = Begin
        [ declarationEntry (AST.dependentArgumentType "a"
            (Multiplication (natural 2) (natural 3)))
        , declarationEntry (AST.dependentArgumentType "b" (natural 5))
        ]
        (Addition (IdentifierReference (IdentifierString "a")) (IdentifierReference (IdentifierString "b")))
  assertParsed "begin newline bindings" "begin\n a : 2 * 3\n b : 5\nyield a + b" block
  let assignedBlock = Begin
        [ declarationEntry (AST.assignment "a" (natural 2) (natural 2))
        , declarationEntry (AST.assignment "b" (natural 3) (natural 3))
        ]
        (Addition (ref "a") (ref "b"))
  assertParsed "assignment infers a grouped begin block"
    "my_val := (begin\n a := 2\n b := 3\nyield a + b)"
    (AST.assignment "my_val" assignedBlock assignedBlock)
  assertParsed "assignment specifies a grouped begin block"
    "my_val : 5 := (begin\n a := 2\n b := 3\nyield a + b)"
    (AST.assignment "my_val" (natural 5) assignedBlock)
  assertParsed "optional assignment specifies a grouped begin block"
    "my_val? : 5 := (begin\n a := 2\n b := 3\nyield a + b)"
    (OptionalType
      (AST.assignment "my_val" (natural 5) assignedBlock))
  assertParsed "an unmarked multiline sequence remains ordinary syntax"
    "my_val := 5 ~>\n a := 2\nyield a"
    (AtlasMap
      [ MapSpecification
          (AST.assignment "my_val" (natural 5) (natural 5))
          (AST.assignment "a" (natural 2) (natural 2))
      , FunctionApplication (ref "yield") (ref "a")
      ])
  assertAstOutput "module remains an ordinary identifier"
    "module : Nat"
    (AST.dependentArgumentType "module" (ref "Nat"))
  assertParsed "declared import lowers paths and its function body structurally"
    "import \"library_one\" do yield 7"
    (Import ["library_one"] (FunctionBody [] (natural 7)))
  assertParsed "declared import accepts multiple paths"
    "import (\"library_one\"; \"library_two\") do yield 7"
    (Import ["library_one", "library_two"]
      (FunctionBody [] (natural 7)))
  assertAstOutput "begin AST roundtrip" "begin a : 2 * 3; b : 5 yield a + b" block
  assertParsed "let in begin"
    "begin let x := 10 yield x"
    (Begin [declarationEntry (Let
        (AST.assignment "x" (natural 10) (natural 10)))]
      (IdentifierReference (IdentifierString "x")))
  assertParsed "references are parsed independently of lexical lookup" "(begin x : 1 yield x), x"
    (MapConcatenation (Begin
        [declarationEntry (AST.dependentArgumentType "x" (natural 1))]
        (IdentifierReference (IdentifierString "x")))
      (IdentifierReference (IdentifierString "x")))
  assertParsed "let accepts an assigned declaration" "let x := 1"
    (Let (AST.assignment "x" (natural 1) (natural 1)))
  assertParsed "val marks one assigned declaration" "val x := 1"
    (Val (AST.assignment "x" (natural 1) (natural 1)))
  assertParsed "let composes outside val" "let val x := 1"
    (Let (Val (AST.assignment "x" (natural 1) (natural 1))))
  assertParsed "val preserves the rejected inner-let ordering"
    "val let x := 1"
    (Val (Let (AST.assignment "x" (natural 1) (natural 1))))
  assertParsed "an incomplete begin form remains ordinary application syntax"
    "begin x : 1"
    (FunctionApplication
      (ref "begin")
      (AST.dependentArgumentType "x" (natural 1)))
  assert "an incomplete do form is not expanded to a function body"
    (case parseSource
        "(f := ({n? : Nat} -> () do verify n of Nat)\n)" of
      Right actual -> not (containsFunctionBody actual)
      Left _ -> False)
  assert "a newline after a signature does not create a function body"
    (case parseSource "(f := ({n? : Nat} -> Nat\nyield n + 1)\n)" of
      Right actual -> not (containsFunctionBody actual)
      Left _ -> False)
  let identityBody = FunctionBody [] (ref "value")
      optionalInput =
        ArgumentativeMap
          [OptionalType (AST.dependentArgumentType "value" (ref "Any"))]
      arrowBody input output = FunctionApplication
        (FunctionType input output)
        identityBody
      appliedBody input = FunctionApplication input identityBody
  assertParsed "a function body follows an explicit function type"
    "{value? : Any} -> Any do yield value"
    (arrowBody optionalInput (ref "Any"))
  assertParsed "a function body infers Any after a non-function type"
    "{value? : Any} do yield value"
    (appliedBody optionalInput)
  assertParsed "a host function body infers Any after a non-function type"
    "Nat datra.fun_body"
    (FunctionApplication (ref "Nat") (datraRef ["fun_body"]))
  assertParsed "a leading host member remains a standalone value"
    "datra.Any"
    (datraRef ["Any"])
  assertParsed "a parenthesized type retains its signature boundary"
    "(Nat) do yield value"
    (appliedBody (ref "Nat"))
  case parseSource "((&T?) do yield value\n)" of
    Right (FunctionApplication
        (GenericIntroductionExpression introduction) body) ->
      assert "a generic introduction remains an ordinary body application"
        ( body == identityBody
          && genericIntroductionIdentifier introduction
            == genericIdentifier "T" True
        )
    result -> fail ("unexpected generic function body: " <> show result)
  assertParsed "function domains accept forward specifications"
    "(Nat ~> Any) -> Any do yield value"
    (arrowBody
      (MapSpecification (ref "Nat") (ref "Any"))
      (ref "Any"))
  assertParsed "inferred function domains accept forward specifications"
    "(Nat ~> Any) do yield value"
    (appliedBody (MapSpecification (ref "Nat") (ref "Any")))
  assertParsed "function domains accept reverse specifications"
    "(Any <~ Nat) -> Any do yield value"
    (arrowBody
      (MapSpecification (ref "Nat") (ref "Any"))
      (ref "Any"))
  assertParsed "inferred function domains accept reverse specifications"
    "(Any <~ Nat) do yield value"
    (appliedBody (MapSpecification (ref "Nat") (ref "Any")))
  assertParsed "function domains accept subfederations"
    "(Nat of Any) -> Any do yield value"
    (arrowBody
      (Subfederation (ref "Nat") (ref "Any"))
      (ref "Any"))
  assertParsed "inferred function domains accept subfederations"
    "(Nat of Any) do yield value"
    (appliedBody (Subfederation (ref "Nat") (ref "Any")))
  assertParsed "an explicit code-block codomain is preserved"
    "{value? : Any} -> Nat do yield value"
    (arrowBody optionalInput (ref "Nat"))
  assertParsed "an explicit coalized codomain owns the following body"
    "{value? : Any} -> >< (Nat; Nat) do yield value"
    (arrowBody optionalInput
      (Coalization (AtlasMap [ref "Nat", ref "Nat"])))
  assert "a category hole uses its declared type implementation" $ case
      parseSource (unlines
        [ "(_Expr := Int"
        , "\"take %_Expr\" := (Int -> Int) datra.fun_body"
        , "take 7"
        , "take Infinity)"
        ]) of
    Right (AtlasMap [_, _, Fun (EllipsisNatural 7), final]) ->
      final == FunctionApplication (ref "take") (ref "Infinity")
    _ -> False
  assert "AST capture behavior follows the interpolated value's type" $ case
      parseSource (unlines
        [ "(Capture := datra.Expr"
        , "CaptureAlias := Capture"
        , "\"take %CaptureAlias\" := (Any -> Any) datra.fun_body"
        , "take Infinity)"
        ]) of
    Right (AtlasMap values) -> case reverse values of
      Fun captured : _ -> captured == ref "Infinity"
      _ -> False
    _ -> False
  assert "a dependent argument capture is in scope for later typed captures" $ case
      parseSource (unlines
        [ "(_DependentArgument := datra.DependentArgument"
        , "_Expr := datra.Expr"
        , "\"gate %_DependentArgument bound %_Expr body %Int\" :="
            <> " ((Any; Any; Int) -> Int) datra.test.gate"
        , "gate x bound Int body x)"
        ]) of
    Right (AtlasMap [_, _, _, rewritten]) ->
      rewritten == FunctionApplication (ref "gate")
        (AtlasMap [ref "x", ref "Int", ref "x"])
    _ -> False
  let dependentArgumentTemplate = StringTemplate
        [ StringTemplateLiteral "abc"
        , StringTemplateInterpolation
            (ref "it")
        ]
  assert "a dependent argument capture does not introduce contextual it" $ case
      parseSource (unlines
        [ "(_DependentArgument := datra.DependentArgument"
        , "\"capture %_DependentArgument\" := (Any -> Any) datra.fun_body"
        , "capture \"abc%(it)\")"
        ]) of
    Right (AtlasMap [_, _, Fun captured]) ->
      captured == dependentArgumentTemplate
    _ -> False
  assert "an optional dependent argument capture does not introduce contextual it" $
    case parseSource (unlines
      [ "(_DependentArgument := datra.DependentArgument"
      , "\"capture %_DependentArgument\" := (Any -> Any) datra.fun_body"
      , "capture \"abc%(it)\"?)"
      ]) of
      Right (AtlasMap [_, _, Fun captured]) ->
        captured == OptionalType dependentArgumentTemplate
      _ -> False
  case parseSource (unlines
      [ "(_DependentArgument := datra.DependentArgument"
      , "_DependentDeclaration := datra.DependentDeclaration"
      , "\"captureId %_DependentArgument\" := (Any -> Any) datra.fun_body"
      , "\"captureDeclaration %_DependentDeclaration\" := (Any -> Any) datra.fun_body"
      , "captureId x"
      , "captureId (x : Int)"
      , "captureDeclaration x := 1"
      , "captureDeclaration x : Int"
      , "captureDeclaration x : Int := 1)"
      ]) of
      Right (AtlasMap
          [ _, _, _, _, Fun identifier, Fun dependent, Fun declaration
          , unmatched, annotated
          ])
        | identifier == ref "x"
          && dependent == AST.dependentArgumentType "x" (ref "Int")
          && declaration == AST.assignment "x" (natural 1) (natural 1)
          && unmatched == FunctionApplication
            (ref "captureDeclaration")
            (AST.dependentArgumentType "x" (ref "Int"))
          && annotated == FunctionApplication
            (ref "captureDeclaration")
            (AST.assignment "x" (ref "Int") (natural 1)) -> pure ()
      actual -> assertFailure
        ("dependent argument expressions and declarations use distinct captures: "
          <> show actual)
  assert "reserved symbols have unique identifier strings"
    Reserved.reservedSymbolIdentifiersAreUnique
  assertParsed "val requires a declaration capture"
    "val _it" (FunctionApplication (ref "val") (ref "_it"))
  assertRejected "the removed external escape is rejected" "~~\"datra.Int\""
  assertRejected "previous external symbol is rejected" "!~\"datra.Int\""
  assertRejected "legacy external symbol is rejected" "!^\"datra.Int\""
  mapM_ (\name -> assertParsed ("library name is an ordinary identifier: " <> name)
    (name <> " : Nat") (AST.dependentArgumentType name (ref "Nat")))
    ["Nat", "Int", "Str", "IdenStr", "Bool", "true", "false", "nothing"]
  assertLocatedParse
  assertResourceEnvelopes
  assertAstSyntax
  assertAstOutput
    "flat map"
    "(1; 2; 10)"
    (natural 1 <:> natural 2 <:> natural 10)
  assertAstOutput
    "nested map"
    "((1; 2);(3;4))"
    ((natural 1 <:> natural 2) <+> (natural 3 <:> natural 4))
  assertAstOutput
    "unary parentheses do not create map levels"
    "((Nat); (Nat))"
    (ref "Nat" <:> ref "Nat")
  assertAstOutput
    "left-nested map structure remains explicit"
    "((Nat; Nat); Nat)"
    ((ref "Nat" <:> ref "Nat") <+> ref "Nat")
  assertAstOutput
    "right-nested map structure remains explicit"
    "(Nat; (Nat; Nat))"
    (ref "Nat" <+> (ref "Nat" <:> ref "Nat"))
  assertAstOutput
    "comments and whitespace"
    "  (1; # retain the next value\n (2; 3)) # end\n"
    (natural 1 <+> (natural 2 <:> natural 3))
  assertAstOutput
    "empty nested maps are trimmed recursively"
    "(1; (( )  ); 2)"
    (natural 1 <:> natural 2)
  assertAstOutput
    "expansions are parenthesized at recursive depth"
    "(((1;2);(3;4));(5;6))"
    ( ((natural 1 <:> natural 2) <+> (natural 3 <:> natural 4))
        <+> (natural 5 <:> natural 6)
    )
  assertAstOutput
    "the empty map is retained at the root"
    "()"
    AST.emptyMap
  assertAstOutput
    "ellipsis literal"
    "(...)"
    (...)
  assertAstOutput
    "specification into a library range"
    "2..5 ~> range 0 up"
    ((natural 2 <..> natural 5) ~> rangeUpwards 0)
  assertAstOutput
    "bounded from call"
    "from 2 to 5"
    (fromTo 2 5)
  assertAstOutput
    "up from call"
    "from 2 up"
    (fromUpwards 2)
  assertParsed "unregistered keyword names parse as applications" "within 2 to 5"
    (foldl FunctionApplication (IdentifierReference (IdentifierString "within"))
      [natural 2, IdentifierReference (IdentifierString "to"), natural 5])
  assertParsed "the range library binding is an ordinary name" "range : Nat"
    (AST.dependentArgumentType "range" (ref "Nat"))
  assertAstOutput
    "the former valued-range prefix is available as an identifier"
    "within : Nat"
    (AST.dependentArgumentType "within" (ref "Nat"))
  assertAstOutput
    "Nat library reference"
    "Nat"
    (ref "Nat")
  assertAstOutput
    "Str library reference"
    "Str"
    (ref "Str")
  assertAstOutput
    "Int library reference"
    "Int"
    (ref "Int")
  assertAstOutput
    "descending open integer range"
    "range -1 down"
    (rangeDownwards (-1))
  assertAstOutput
    "bounded valued integer range"
    "from -3 to 4"
    (fromTo (-3) 4)
  assertAstOutput
    "unary numerical plus"
    "+6"
    (AST.plus (natural 6))
  assertAstOutput
    "unary integer negation"
    "-6"
    (AST.minus (natural 6))
  assertAstOutput
    "minus is an ordinary identifier rather than a word operator"
    "minus 6"
    (FunctionApplication (ref "minus") (natural 6))
  assertAstOutput
    "integer subtraction"
    "5 - 8"
    ((AST.-) (natural 5) (natural 8))
  assertAstOutput
    "false library reference"
    "false"
    (ref "false")
  assertAstOutput
    "nothing library reference"
    "nothing"
    (ref "nothing")
  assertAstOutput
    "Bool library reference"
    "Bool"
    (ref "Bool")
  assertAstOutput
    "Either surface operator"
    "False := 0 | True := 1"
    (AST.eitherType
      (AST.assignment "False" (natural 0) (natural 0))
      (AST.assignment "True" (natural 1) (natural 1)))
  assertAstOutput
    "Either is associative"
    "(0 | 1) | 2"
    (AST.eitherType
      (natural 0)
      (AST.eitherType (natural 1) (natural 2)))
  assertAstOutput
    "Boolean and, or, and not"
    "false and not true or true"
    (AST.or
      (AST.and (ref "false") (AST.not (ref "true")))
      (ref "true"))
  assertAstOutput
    "parenthesized blocks stay inside a nested Boolean operand"
    "(5 of (begin yield 5)) and not (6 of (begin yield 5))"
    (AST.and
      (AST.subfederation (natural 5) (Begin [] (natural 5)))
      (AST.not
        (AST.subfederation (natural 6) (Begin [] (natural 5)))))
  assertAstOutput
    "federation equality"
    "1 = 1"
    (AST.equal (natural 1) (natural 1))
  assertAstOutput
    "subfederation morphism check"
    "1 of Int"
    (AST.subfederation (natural 1) (ref "Int"))
  assertAstOutput
    "a trailing skip can be a declared syntax operand"
    "1 of *"
    (AST.subfederation (natural 1) Skip)
  assertAstOutput
    "equality binds inside a subfederation check"
    "1 of Int = true"
    (AST.subfederation
      (natural 1)
      (AST.equal (ref "Int") (ref "true")))
  assertAstOutput
    "Maybe is an ordinary type application"
    "Maybe Nat"
    (FunctionApplication (ref "Maybe") (ref "Nat"))
  assertAstOutput
    "Maybe accepts a grouped type expression"
    "Maybe (Nat | Int)"
    (FunctionApplication (ref "Maybe")
      (AST.eitherType (ref "Nat") (ref "Int")))
  assertAstOutput "postfix optional aliases Maybe"
    "Nat?" (OptionalType (ref "Nat"))
  assertAstOutput "postfix optional accepts grouped types"
    "(Nat | Int)?"
    (OptionalType (AST.eitherType (ref "Nat") (ref "Int")))
  assertAstOutput "parenthesized postfix optional nests"
    "(Nat?)?" (OptionalType (OptionalType (ref "Nat")))
  assertAstOutput "bang is no longer a postfix list operator" "values!"
    (FunctionApplication (ref "values") (ref "!"))
  assertAstOutput "Maybe sequencing includes the list split"
    "values !? maximum _it"
    (MaybeThen
      (ref "values")
      (FunctionApplication (ref "maximum") (ref "_it")))
  assertAstOutput
    "optional identifier slot"
    "a? : Nat"
    (OptionalType
      (AST.dependentArgumentType "a" (ref "Nat")))
  assertParsed "ordinary library names can name fields" "Str : Nat"
    (AST.dependentArgumentType "Str" (ref "Nat"))
  assertAstOutput
    "reserved names can be full-string identifier expressions"
    "\"Str\" : Nat"
    (AST.dependentArgumentType "Str" (ref "Nat"))
  assertAstOutput
    "contextual range words remain bare identifier expressions"
    "to : Nat"
    (AST.dependentArgumentType "to" (ref "Nat"))
  assertAstOutput
    "contextual range directions remain bare identifier expressions"
    "(up : Nat; down : Nat)"
    (AST.dependentArgumentType "up" (ref "Nat")
      <:> AST.dependentArgumentType "down" (ref "Nat"))
  assertAstOutput
    "uppercase built-in names remain bare identifier expressions"
    "False : Nat"
    (AST.dependentArgumentType "False" (ref "Nat"))
  assertAstOutput
    "full-string identifier expressions compose with optional syntax"
    "\"Abc\"? : Nat"
    (OptionalType
      (AST.dependentArgumentType "Abc" (ref "Nat")))
  assertAstOutput
    "optional assigned identifier slot"
    "a? : Nat := 5"
    (OptionalType
      (AST.assignment "a" (ref "Nat") (natural 5)))
  let optionalIntegerSlots =
        MapConcatenation
          (OptionalType
            (AST.dependentArgumentType "a" (ref "Int")))
          (OptionalType
            (AST.dependentArgumentType "b" (ref "Int")))
      integerPair = MapConcatenation (natural 12) (natural 23)
  assertAstOutput
    "optional identifier slots are concatenation operands"
    "(a? : Int, b? : Int)"
    optionalIntegerSlots
  assertAstOutput
    "parenthesized optional identifier target preserves precedence"
    "12, 23 ~> (a? : Int, b? : Int)"
    (integerPair ~> optionalIntegerSlots)
  assertAstOutput
    "unparenthesized optional identifier target preserves precedence"
    "12, 23 ~> a? : Int, b? : Int"
    (integerPair ~> optionalIntegerSlots)
  assertAstOutput
    "named source member precedes an optional identifier target"
    "12, b := 23 ~> a? : Int, b? : Int"
    ( MapConcatenation
        (natural 12)
        (AST.assignment "b" (natural 23) (natural 23))
        ~> optionalIntegerSlots
    )
  assertAstOutput
    "optional identifier range subfederation check"
    "(2, b := 5) of (a? : Int, b? : from 3 to 8)"
    (AST.subfederation
      (MapConcatenation
        (natural 2)
        (AST.assignment "b" (natural 5) (natural 5)))
      (MapConcatenation
        (OptionalType
          (AST.dependentArgumentType "a" (ref "Int")))
        (OptionalType
          (AST.dependentArgumentType "b" (fromTo 3 8)))))
  let optionalAssigned identifierString value =
        OptionalType
          (AST.assignment
            identifierString (ref "Int") (natural value))
      optionalIdentifier identifierString =
        OptionalType
          (AST.dependentArgumentType identifierString (ref "Int"))
  assertAstOutput
    "parenthesized reverse specification stays in its concatenation slot"
    "a? : Int := 12, (b? : Int) <~ (b? : Int := 23)"
    (MapConcatenation
      (optionalAssigned "a" 12)
      (optionalAssigned "b" 23 ~> optionalIdentifier "b"))
  assertAstOutput
    "optional assignment sequence equals its canonical concatenation"
    ( "(a? : Int := 12; b? : Int := 23) = "
        <> "(a? : Int := 12, b? : Int := 23)"
    )
    (AST.equal
      (optionalAssigned "a" 12 <:> optionalAssigned "b" 23)
      (MapConcatenation
        (optionalAssigned "a" 12)
        (optionalAssigned "b" 23)))
  assertAstOutput
    "ternary conditional"
    "if true then 1 else -2"
    (AST.conditional
      (ref "true")
      (natural 1)
      (AST.minus (natural 2)))
  let nextValue = FunctionApplication (ref "compute") (ref "input")
      nextDeclaration = AST.assignment "next" nextValue nextValue
  assertAstOutput
    "a referenced named condition value becomes a local declaration"
    ("if candidate >= (next : compute input) "
      <> "then candidate else next")
    (Begin
      [declarationEntry nextDeclaration]
      (AST.conditional
        (AST.greaterOrEqual (ref "candidate") (ref "next"))
        (ref "candidate")
        (ref "next")))
  assertAstOutput
    "condition-local declarations are not comparison-specific"
    "if valid (parsed : parse input) then parsed else fallback"
    (Begin
      [ declarationEntry
          (let parsed = FunctionApplication (ref "parse") (ref "input")
          in AST.assignment "parsed" parsed parsed)
      ]
      (AST.conditional
        (FunctionApplication (ref "valid") (ref "parsed"))
        (ref "parsed")
        (ref "fallback")))
  assertAstOutput
    "an unreferenced named condition value remains a value"
    "if valid (parsed : parse input) then accepted else fallback"
    (AST.conditional
      (FunctionApplication
        (ref "valid")
        (AST.dependentArgumentType "parsed"
          (FunctionApplication (ref "parse") (ref "input"))))
      (ref "accepted")
      (ref "fallback"))
  assertAstOutput
    "binary conditional defaults to unit"
    "if false then 1"
    (AST.conditionalWithoutElse (ref "false") (natural 1))
  assertAstOutput
    "conditional combines optionals, equality, logic, and identifiers"
    ( "if (Maybe Nat = (Nat | Nothing := ())) and not false "
        <> "then (a? : Nat := 5) else (Nothing := ())"
    )
    (AST.conditional
      (AST.and
        (AST.equal
          (FunctionApplication (ref "Maybe") (ref "Nat"))
          (AST.eitherType
            (ref "Nat")
            (AST.assignment "Nothing" AST.emptyMap AST.emptyMap)))
        (AST.not (ref "false")))
      (OptionalType
        (AST.assignment "a" (ref "Nat") (natural 5)))
      (AST.assignment "Nothing" AST.emptyMap AST.emptyMap))
  assertAstOutput
    "natural value specified into Nat"
    "2 ~> Nat"
    (natural 2 ~> ref "Nat")
  assertParsed "unprefixed range words have ordinary application syntax" "2 to 5"
    (FunctionApplication (FunctionApplication (natural 2) (IdentifierReference (IdentifierString "to"))) (natural 5))
  assertParsed "unprefixed direction is an ordinary reference" "2 up"
    (FunctionApplication (natural 2) (IdentifierReference (IdentifierString "up")))
  assertAstOutput
    "specification binds after access and concatenation"
    "1, 2 @ range 0 up ~> range 0 to 10"
    (((natural 1 <.> natural 2) <@> rangeUpwards 0) ~> rangeTo 0 10)
  assertAstOutput
    "access after a specification projects its fibers"
    "(2; 3) ~> (Nat; Nat) @ 0"
    ( ((natural 2 <:> natural 3)
        ~> (ref "Nat" <:> ref "Nat"))
        <@> natural 0
    )
  assertAstOutput
    "specification chains associate through the intermediate federation"
    "2..3 ~> range 2 to 5 ~> range 2 to 8"
    ((natural 2 <..> natural 3) ~> rangeTo 2 5 ~> rangeTo 2 8)
  assertAstOutput
    "reverse specification reverses its operands"
    "range 2 to 5 <~ 2..3"
    ((natural 2 <..> natural 3) ~> rangeTo 2 5)
  assertAstOutput
    "reverse specification accepts parenthesized composite operands"
    "($a; Nat) <~ ($a; 50)"
    ( (AST.asciiString "a" <:> natural 50)
        ~> (AST.asciiString "a" <:> ref "Nat")
    )
  assertAstOutput
    "reverse specification accepts concatenated composite operands"
    "$a, range 1 to 10 <~ $a, 3, 4, 5"
    ( (AST.asciiString "a" <.> natural 3 <.> natural 4 <.> natural 5)
        ~> (AST.asciiString "a" <.> rangeTo 1 10)
    )
  assertAstOutput
    "reverse specification chains associate right"
    "range 2 to 8 <~ range 2 to 5 <~ 2..3"
    ((natural 2 <..> natural 3) ~> rangeTo 2 5 ~> rangeTo 2 8)
  assertAstOutput
    "reverse specification binds after access and concatenation"
    "range 0 to 10 <~ 1, 2 @ range 0 up"
    (((natural 1 <.> natural 2) <@> rangeUpwards 0) ~> rangeTo 0 10)
  assertAstOutput
    "a postfix range can precede reverse specification"
    "2.. <~ range 2 to 5"
    (rangeTo 2 5 ~> (natural 2 ..+))
  assertAstOutput
    "simple identifier type"
    "x : Nat"
    (AST.dependentArgumentType "x" (ref "Nat"))
  assertAstOutput
    "unit identifier equals its identifier string"
    "$Value = (Value : ())"
    (AST.equal
      (AST.asciiString "Value")
      (AST.dependentArgumentType "Value" AST.emptyMap))
  assertAstOutput
    "full identifier assignment"
    "x : Nat := 5"
    (AST.assignment "x" (ref "Nat") (natural 5))
  assertAstOutput
    "assignment specified into its identifier target"
    "(a : Nat := 5) ~> (a : Nat)"
    ( AST.assignment "a" (ref "Nat") (natural 5)
        ~> AST.dependentArgumentType "a" (ref "Nat")
    )
  assertAstOutput
    "reverse specification between different identifier strings"
    "(a : Nat) <~ (b := 10)"
    ( AST.assignment "b" (natural 10) (natural 10)
        ~> AST.dependentArgumentType "a" (ref "Nat")
    )
  assertAstOutput
    "reverse assignment chain widens nested annotations"
    ( "(d : from 0 to 100) <~ "
        <> "(d : from 20 to 40 := 28) <~ "
        <> "(d : from 25 to 35 := 28) <~ (d := 28)"
    )
    ( AST.assignment "d" (natural 28) (natural 28)
        ~> AST.assignment "d" (fromTo 25 35) (natural 28)
        ~> AST.assignment "d" (fromTo 20 40) (natural 28)
        ~> AST.dependentArgumentType "d" (fromTo 0 100)
    )
  assertAstOutput
    "reverse assignment chain accepts unparenthesized multiline operands"
    ( "d : range 10 to 100 <~\n"
        <> "    d : range 12 to 85 := 23..66 <~\n"
        <> "    d := 23..66"
    )
    ( AST.assignment
        "d"
        (natural 23 <..> natural 66)
        (natural 23 <..> natural 66)
        ~> AST.assignment
          "d"
          (rangeTo 12 85)
          (natural 23 <..> natural 66)
        ~> AST.dependentArgumentType "d" (rangeTo 10 100)
    )
  assertAstOutput
    "reverse assignment chain retains an incompatible intermediate annotation"
    ( "(x : from 1 to 10) <~ "
        <> "(x : from 5 to 20) <~ (x := 8)"
    )
    ( AST.assignment "x" (natural 8) (natural 8)
        ~> AST.dependentArgumentType "x" (fromTo 5 20)
        ~> AST.dependentArgumentType "x" (fromTo 1 10)
    )
  assertAstOutput
    "binary identifier assignment"
    "x := 5"
    (AST.assignment "x" (natural 5) (natural 5))
  assertAstOutput
    "redundant assignment type canonicalizes to binary syntax"
    "x : 5 := 5"
    (AST.assignment "x" (natural 5) (natural 5))
  assertAstOutput
    "access binds inside the assignment value"
    "x : Nat := (1; 2) @ 0"
    ( AST.assignment
        "x"
        (ref "Nat")
        ((natural 1 <:> natural 2) <@> natural 0)
    )
  assertAstOutput
    "accessing an identifier operation requires grouping"
    "(x : Nat) @ 0"
    (AST.dependentArgumentType "x" (ref "Nat") <@> natural 0)
  assertAstOutput
    "bracket access uses the identifier map view"
    "(x : Nat)[0]"
    (AST.dependentArgumentType "x" (ref "Nat") <@> natural 0)
  assertAstOutput
    "bracket access uses the assignment specification view"
    "(x : Nat := 5)[1]"
    (AST.assignment "x" (ref "Nat") (natural 5) <@> natural 1)
  assertAstOutput
    "unparenthesized access belongs to the identifier type operand"
    "x : Nat @ 0"
    (AST.dependentArgumentType "x" (ref "Nat" <@> natural 0))
  assertAstOutput
    "identifier arithmetic operands compose without grouping"
    "x : 5 + y : 10 = 15"
    (AST.equal
      ((AST.+)
        (AST.dependentArgumentType "x" (natural 5))
        (AST.dependentArgumentType "y" (natural 10)))
      (natural 15))
  assertAstOutput
    "transfinite identifier arithmetic preserves precedence"
    "x : ...^2 + y : 1 = ...^2 + 1"
    (AST.equal
      ((AST.+)
        (AST.dependentArgumentType "x" ((AST.^) (...) (natural 2)))
        (AST.dependentArgumentType "y" (natural 1)))
      ((AST.+) ((AST.^) (...) (natural 2)) (natural 1)))
  assertAstOutput
    "identifier strings share canonical continuation characters"
    "A_0'z : Nat"
    (AST.dependentArgumentType "A_0'z" (ref "Nat"))
  assertRejected
    "identifier operations reject expression left sides"
    "(2 + 2) : Nat := 4"
  assertAstOutput
    "parenthesized names evaluate dependent declaration templates"
    "(abc) := 123"
    (IdentifierTemplateOperation
      [StringTemplateInterpolation (ref "abc")]
      (natural 123)
      (Just (natural 123)))
  assertAstOutput
    "parenthesized names evaluate dependent argument templates"
    "(abc) : Nat"
    (IdentifierTemplateOperation
      [StringTemplateInterpolation (ref "abc")]
      (ref "Nat")
      Nothing)
  assertAstOutput
    "bare names remain literal declarations"
    "abc := 123"
    (AST.assignment "abc" (natural 123) (natural 123))
  assertRejected
    "identifier operations reject dollar-prefixed left sides"
    "$x : Nat := 4"
  assertParsed "bare identifiers are references" "x" (IdentifierReference (IdentifierString "x"))
  assertParsed "apostrophe-prefixed identifiers are references"
    "'x" (IdentifierReference (IdentifierString "'x"))
  assertParsed "apostrophe prefixes may be followed by a digit"
    "'2x" (IdentifierReference (IdentifierString "'2x"))
  assertParsed "underscore prefixes may be followed by a digit"
    "_2x" (IdentifierReference (IdentifierString "_2x"))
  assertParsed "bare identifiers allow separated underscores"
    "my_pow" (IdentifierReference (IdentifierString "my_pow"))
  assertAstOutput "separated-underscore identifiers can be declared"
    "my_pow := 4" (AST.assignment "my_pow" (natural 4) (natural 4))
  assertParsed "bare identifiers allow consecutive underscores"
    "my__pow" (IdentifierReference (IdentifierString "my__pow"))
  assertParsed "bare identifiers allow a trailing underscore"
    "my_pow_" (IdentifierReference (IdentifierString "my_pow_"))
  assertParsed "a bare underscore is an identifier"
    "_" (ref "_")
  assertParsed "leading underscores are unrestricted"
    "__value" (ref "__value")
  assertParsed "underscore-apostrophe order is unrestricted"
    "_'value" (ref "_'value")
  assertParsed "a bare apostrophe is an identifier"
    "'" (ref "'")
  assertParsed "apostrophe-underscore order is unrestricted"
    "'_value" (ref "'_value")
  assertParsed "leading apostrophes are unrestricted"
    "''value" (ref "''value")
  assertRejected "an identifier cannot start with a digit" "345abc"
  assertParsed
    "IdentifierString produces an ASCII string literal"
    "$text"
    (AsciiStringLiteral "text")
  assertRejected
    "compact strings cannot be entirely numeric"
    "$12"
  assertRejected
    "compact strings cannot start with a digit"
    "$345abc"
  assertAstOutput
    "IdentifierString accepts all canonical continuation characters"
    "$A_0'z"
    (AST.asciiString "A_0'z")
  assertAstOutput
    "compact strings allow a leading underscore"
    "$_abc"
    (AST.asciiString "_abc")
  assertAstOutput
    "compact strings allow a single separating underscore"
    "$abc_def"
    (AST.asciiString "abc_def")
  assertAstOutput
    "compact strings allow consecutive underscores"
    "$abc__def"
    (AST.asciiString "abc__def")
  assertAstOutput
    "compact strings allow a trailing underscore"
    "$abc_"
    (AST.asciiString "abc_")
  assertAstOutput
    "compact strings allow doubled leading underscores"
    "$__abc"
    (AST.asciiString "__abc")
  assertAstOutput
    "a lone compact underscore is an identifier string"
    "$_"
    (AST.asciiString "_")
  assertAstOutput
    "standard strings may contain a trailing underscore"
    "\"abc_\""
    (AST.asciiString "abc_")
  assertAstOutput
    "StandardString canonicalizes to IdentifierString when possible"
    "\"text\""
    (AST.asciiString "text")
  assertAstOutput
    "StandardString supports the empty string"
    "\"\""
    (AST.asciiString "")
  assertAstOutput
    "StandardString escapes quote and backslash"
    "\"say \\\"hi\\\" and \\\\ path\""
    (AST.asciiString "say \"hi\" and \\ path")
  assertAstOutput
    "StandardString decodes and canonicalizes escaped newlines"
    "\"first\\nsecond\""
    (AST.asciiString "first\nsecond")
  assertAstOutput
    "StandardString accepts and canonicalizes hexadecimal byte escapes"
    "\"\\0\\8\\08\\09\\1f\\7F\\ff\""
    (AST.asciiString ['\0', '\8', '\8', '\9', '\31', '\127', '\255'])
  assertParsed
    "StandardString hexadecimal escapes select ASCII-map characters"
    "\"\\0\\8\\08\\09\\1f\\7F\\ff\""
    (AsciiStringLiteral ['\0', '\8', '\8', '\9', '\31', '\127', '\255'])
  assertAstOutput
    "StandardString canonicalizes a hexadecimal newline to its named escape"
    "\"\\0A\""
    (AST.asciiString "\n")
  assertAstOutput
    "StandardString leaves nonsyntactic keyboard-visible characters literal"
    "\" !\\%&'()*+,-./:;<=>?@^_`{|}~\""
    (AST.asciiString " !%&'()*+,-./:;<=>?@^_`{|}~")
  assertAstOutput
    "StandardString line comments retain their terminating newline"
    "\"Comment test#this is a comment!\n\""
    (AST.asciiString "Comment test\n")
  assertParsed
    "StandardString comments may terminate at the closing quote"
    "\"Hello#, world!\""
    (AsciiStringLiteral "Hello")
  assertAstOutput
    "StandardString comments ending at a quote retain canonical rendering"
    "\"Hello#, world!\""
    (AST.asciiString "Hello")
  assertAstOutput
    "StandardString escapes a literal hash"
    "\"literal \\# character\""
    (AST.asciiString "literal # character")
  assertAstOutput
    "StandardString leaves a literal dollar sign unescaped"
    "\"literal $ character\""
    (AST.asciiString "literal $ character")
  assertAstOutput
    "StandardString escapes a literal percent sign"
    "\"literal \\% character\""
    (AST.asciiString "literal % character")
  assertAstOutput
    "string template interpolates a compound expression"
    "\"example%(2 + 2)\""
    (StringTemplate
      [ StringTemplateLiteral "example"
      , StringTemplateInterpolation
          (Addition (natural 2) (natural 2))
      ])
  assertParsed
    "simple numeric interpolation has string-template syntax"
    "\"%4\""
    (StringTemplate [StringTemplateInterpolation (natural 4)])
  assertParsed
    "library names may be simple interpolations"
    "\"%Str\""
    (StringTemplate [StringTemplateInterpolation (ref "Str")])
  assertParsed
    "IdenStr is available to string templates"
    "\"%IdenStr\""
    (StringTemplate [StringTemplateInterpolation (ref "IdenStr")])
  assertAstOutput
    "digit-leading compact strings retain an apostrophe before an operator"
    "$12' of \"%(Nat)'\""
    (AST.subfederation
      (AsciiStringLiteral "12'")
      (StringTemplate
        [ StringTemplateInterpolation (ref "Nat")
        , StringTemplateLiteral "'"
        ]))
  assertRejected
    "the removed weak interpolation marker is rejected"
    "\"%!Str\""
  assertParsed
    "a question mark after simple interpolation is literal text"
    "\"%Int?\""
    (StringTemplate
      [ StringTemplateInterpolation (ref "Int")
      , StringTemplateLiteral "?"
      ])
  assertParsed
    "Maybe interpolation uses an explicit expression"
    "\"%(Maybe Int)\""
    (StringTemplate
      [StringTemplateInterpolation
        (FunctionApplication (ref "Maybe") (ref "Int"))])
  assertParsed
    "an escaped question mark remains text after a simple interpolation"
    "\"%Int\\?\""
    (StringTemplate
      [ StringTemplateInterpolation (ref "Int")
      , StringTemplateLiteral "?"
      ])
  assertParsed
    "an escaped question mark is accepted as ordinary string text"
    "\"\\?\""
    (AsciiStringLiteral "?")
  assertParsed "simple interpolation can reference the lexical scope" "\"%abc\""
    (StringTemplate [StringTemplateInterpolation (IdentifierReference (IdentifierString "abc"))])
  assertParsed
    "a compact string can itself be interpolated"
    "\"%$abc\""
    (StringTemplate
      [StringTemplateInterpolation (AsciiStringLiteral "abc")])
  assertParsed
    "signed interpolation requires the compound form"
    "\"%(-10)\""
    (StringTemplate
      [StringTemplateInterpolation (Minus (natural 10))])
  assertRejected
    "signed interpolation rejects the simple form"
    "\"%-10\""
  assertParsed
    "a nested quoted string is one simple interpolation"
    "\"hello, %\"world\"!\""
    (StringTemplate
      [ StringTemplateLiteral "hello, "
      , StringTemplateInterpolation (AsciiStringLiteral "world")
      , StringTemplateLiteral "!"
      ])
  assertParsed
    "operators outside parentheses remain template text"
    "\"%2 + 2\""
    (StringTemplate
      [ StringTemplateInterpolation (natural 2)
      , StringTemplateLiteral " + 2"
      ])
  assertParsed
    "interpolation comments terminate at the closing parenthesis"
    "\"a%(2 # ignored)b\""
    (StringTemplate
      [ StringTemplateLiteral "a"
      , StringTemplateInterpolation (natural 2)
      , StringTemplateLiteral "b"
      ])
  assertParsed
    "interpolation comments terminate at newline without emitting it"
    "\"a%(2 # ignored\n)b\""
    (StringTemplate
      [ StringTemplateLiteral "a"
      , StringTemplateInterpolation (natural 2)
      , StringTemplateLiteral "b"
      ])
  assertParsed
    "template comments ignore interpolation and retain their newline"
    "\"a# ignored %4\nb\""
    (AsciiStringLiteral "a\nb")
  assertParsed
    "escaped hashes and percents remain literal template text"
    "\"\\#\\%%4\""
    (StringTemplate
      [ StringTemplateLiteral "#%"
      , StringTemplateInterpolation (natural 4)
      ])
  assertAstOutput
    "parentheses inside nested strings do not close interpolation"
    "\"x%(\"a)b\")y\""
    (StringTemplate
      [ StringTemplateLiteral "x"
      , StringTemplateInterpolation (AsciiStringLiteral "a)b")
      , StringTemplateLiteral "y"
      ])
  assertAstOutput
    "nested grouping composes inside interpolation"
    "\"x%((2 + 3) * 4)y\""
    (StringTemplate
      [ StringTemplateLiteral "x"
      , StringTemplateInterpolation
          (Multiplication
            (Addition (natural 2) (natural 3))
            (natural 4))
      , StringTemplateLiteral "y"
      ])
  assertRejected "an empty interpolation is rejected" "\"%()\""
  assertRejected
    "an unterminated interpolation is rejected"
    "\"%(2 + 2\""
  assertRejected
    "an unescaped percent without an interpolation is rejected"
    "\"literal % character\""
  assertAstOutput
    "string literals are members of Str"
    "(\"my_string\" of Str) = true"
    (AST.equal
      (AST.subfederation (AST.asciiString "my_string") (ref "Str"))
      (ref "true"))
  assertAllHexadecimalAsciiEscapes
  assertAstOutput
    "StandardString preserves multiline leading and trailing characters"
    "(\"  first\nsecond  \")"
    (AST.asciiString "  first\nsecond  ")
  assertParsed
    "StandardString treats syntax and comments as literal contents"
    "(\"\\#;(value)\n$still_text\")"
    (AsciiStringLiteral "#;(value)\n$still_text")
  assertAstOutput
    "strings use the ordinary concatenation operator"
    "$ab, $cd"
    (AST.asciiString "ab" <.> AST.asciiString "cd")
  assertAstOutput
    "strings use the ordinary access operator"
    "$abcd @ 1..3"
    (AST.asciiString "abcd" <@> (natural 1 <..> natural 3))
  assertAstOutput
    "bounded super-ellipsis range"
    "(2..10)"
    (natural 2 <..> natural 10)
  assertAstOutput
    "open super-ellipsis ranges"
    "(2..; 10..-)"
    ((natural 2 ..+) <:> (natural 10 ..-))
  assertAstOutput
    "a prefix range starts at zero"
    "(..10)"
    (natural 0 <..> natural 10)
  assertAstOutput
    "inclusive natural range"
    "range 2 to 5"
    (rangeTo 2 5)
  assertAstOutput
    "open inclusive natural range"
    "range 2 up"
    (rangeUpwards 2)
  assertAstOutput
    "natural range access"
    "1, 2, 3 @ range 1 up"
    ((natural 1 <.> natural 2 <.> natural 3) <@> rangeUpwards 1)
  assertAstOutput
    "bracket access binds before arithmetic"
    "$a + $b[$c]"
    (AST.asciiString "a" AST.+ (AST.asciiString "b" <@> AST.asciiString "c"))
  assertAstOutput
    "grouping moves bracket access outside arithmetic"
    "($a + $b)[$c]"
    ((AST.asciiString "a" AST.+ AST.asciiString "b") <@> AST.asciiString "c")
  assertAstOutput
    "bracket access chains associate left"
    "$a[$b][$c]"
    ((AST.asciiString "a" <@> AST.asciiString "b") <@> AST.asciiString "c")
  assertAstOutput
    "module scope retains an ordinary concatenation RHS"
    "a.(b, c)"
    (ScopeAccess (ref "a")
      (MapConcatenation (ref "b") (ref "c")))
  assertAstOutput
    "module scope retains strings as ordinary RHS expressions"
    "a.(\"b\", c)"
    (ScopeAccess (ref "a")
      (MapConcatenation (AsciiStringLiteral "b") (ref "c")))
  assertAstOutput "module scope accepts an empty RHS map"
    "a.()" (ScopeAccess (ref "a") (AtlasMap []))
  assertAstOutput "module scope accepts an arithmetic RHS"
    "a.(b + c)" (ScopeAccess (ref "a") (Addition (ref "b") (ref "c")))
  assertAstOutput "short module scope uses an identifier-reference RHS"
    "a.b" (ScopeAccess (ref "a") (ref "b"))
  assertAstOutput "lookup evaluates an identifier operand"
    "~a" (Lookup (ref "a"))
  assertAstOutput "lookup accepts a concrete string operand"
    "~\"a\"" (Lookup (AsciiStringLiteral "a"))
  assertAstOutput "lookup retains a string-template operand"
    "~\"arg%Nat\""
    (Lookup (StringTemplate
      [ StringTemplateLiteral "arg"
      , StringTemplateInterpolation (ref "Nat")
      ]))
  assertAstOutput "lookup accepts a computed parenthesized operand"
    "~(a + b)" (Lookup (Addition (ref "a") (ref "b")))
  assertAstOutput "postfix selection applies to the lookup result"
    "~\"arg%Nat\"[0]"
    (MapAccess
      (Lookup (StringTemplate
        [ StringTemplateLiteral "arg"
        , StringTemplateInterpolation (ref "Nat")
        ]))
      (natural 0))
  let tupleOperand = MapConcatenation (ref "a") (ref "b")
  assertAstOutput "a parenthesized map is one lookup operand"
    "~(a, b)" (Lookup tupleOperand)
  assertRejected "lookup needs an operand" "~"
  mapM_ (\(value, expected) -> do
      assert "source rendering preserves the lookup node"
        (renderSourceExpression value == expected)
      assertAstOutput "rendered lookup reparses" expected value)
    [ (Lookup (ref "a"), "~a")
    , (Lookup (AsciiStringLiteral "a"), "~$a")
    , (Lookup tupleOperand, "~(a , b)")
    , (MapAccess (Lookup (ref "a")) (natural 0), "~a[0]")
    , (Lookup (Addition (ref "a") (ref "b")), "~(a + b)")
    , (MapAccess (ScopeAccess (ref "_this") (ref "a")) (natural 0), "_this.a[0]")
    , (MapAccess (ScopeAccess (ref "other") (ref "a")) (natural 1), "other.a[1]")
    ]
  let alternatives = EitherType (AST.asciiString "up") (AST.asciiString "down")
  assertAstOutput "assignment retains its complete alternative value"
    "x := $up | $down"
    (IdentifierOperation (IdentifierString "x") alternatives (Just alternatives))
  assert "assignment rendering does not regroup a federation"
    (renderSourceExpression
      (IdentifierOperation
        (IdentifierString "x") alternatives (Just alternatives))
      == "x := $up | $down")
  assert "quoted identifier references render as strict current-scope access"
    (renderSourceExpression (ref "___Std.Int") == "this.\"___Std.Int\"")
  assertAstOutput
    "ordinary access sees a tightly bound insertion"
    "$a @ $b[$c]"
    (AST.asciiString "a" <@> (AST.asciiString "b" <@> AST.asciiString "c"))
  assertAstOutput
    "bracket insertion accepts ordinary access"
    "$a[$b @ $c]"
    (AST.asciiString "a" <@> (AST.asciiString "b" <@> AST.asciiString "c"))
  assertAstOutput
    "bracket insertion accepts a postfix range"
    "$a[1..]"
    (AST.asciiString "a" <@> (natural 1 ..+))
  assertAstOutput
    "bracket insertion accepts a range with an identifier boundary"
    "$a[0..n]"
    (AST.asciiString "a" <@> (natural 0 <..> ref "n"))
  assertAstOutput
    "bracket insertion accepts an explicitly constructed map"
    "$a[(1; 2)]"
    (AST.asciiString "a" <@> (natural 1 <:> natural 2))
  let headTailAccess =
        AST.asciiString "a"
          <@> AtlasMap [natural 0, rangeUpwards 1]
  assertAstOutput
    "bracket insertion accepts an inline selector map"
    "$a[0; range 1 up]"
    headTailAccess
  assertAstOutput
    "infix access accepts the same selector map"
    "$a @ (0; range 1 up)"
    headTailAccess
  assertAstOutput
    "bracket access accepts an explicitly constructed map on the left"
    "(2; 3)[0]"
    ((natural 2 <:> natural 3) <@> natural 0)
  assertAstOutput
    "grouping permits bracket access on a whole specification"
    "((2; 3) ~> (Nat; Nat))[0]"
    ( ((natural 2 <:> natural 3)
        ~> (ref "Nat" <:> ref "Nat"))
        <@> natural 0
    )
  assertAstOutput
    "declared syntax does not cross newline AST boundaries"
    "range\n2\nto\n5"
    (AtlasMap [ref "range", natural 2, ref "to", natural 5])
  assertAstOutput
    "a prefix range greedily continues across a newline"
    "(..\n10)"
    (natural 0 <..> natural 10)
  assertAstOutput
    "a postfix range can end before a closing delimiter"
    "(2..\n)"
    (natural 2 ..+)
  assertAstOutput
    "a postfix range ends before lower-precedence access"
    "(...) .. @ 5"
    (((...) ..+) <@> natural 5)
  assertAstOutput
    "a postfix range ends before lower-precedence concatenation"
    "2.., 5"
    ((natural 2 ..+) <.> natural 5)
  assertAstOutput
    "Haskell arithmetic precedence"
    "(1 + 2 * 3 ^ 4)"
    (natural 1 AST.+ natural 2 AST.* natural 3 AST.^ natural 4)
  assertAstOutput
    "parentheses override arithmetic precedence"
    "((1 + 2) * 3)"
    ((natural 1 AST.+ natural 2) AST.* natural 3)
  assertAstOutput
    "right-nested addition keeps necessary parentheses"
    "(1 + (2 + 3))"
    (natural 1 AST.+ (natural 2 AST.+ natural 3))
  assertAstOutput
    "redundant parentheses are omitted"
    "(((1 + (2 * (3 ^ 4)))))"
    (natural 1 AST.+ natural 2 AST.* natural 3 AST.^ natural 4)
  assertAstOutput
    "range endpoints accept arithmetic expressions"
    "(1 + 2..3 * 4)"
    ((natural 1 AST.+ natural 2) <..> (natural 3 AST.* natural 4))
  assertAstOutput
    "range concatenation"
    "(1..3, 5..7)"
    ((natural 1 <..> natural 3) <.> (natural 5 <..> natural 7))
  assertParsed
    "a trailing comma concatenates an empty map"
    "(1,)"
    ((<.>)
      (natural 1)
      (AtlasMap []))
  assertAstOutput
    "a trailing comma retains its semantic value"
    "(1,)"
    (natural 1 <.> AST.emptyMap)
  assertAstOutput
    "a trailing comma works at the inferred map boundary"
    "1,"
    (natural 1 <.> AST.emptyMap)
  assertAstOutput
    "a trailing comma can precede a newline and closing delimiter"
    "(1, # no right operand\n)"
    (natural 1 <.> AST.emptyMap)
  assertAstOutput
    "a comma followed by an expression across a newline stays infix"
    "(1,\n2)"
    (natural 1 <.> natural 2)
  assertParsed
    "a trailing comma appends an empty map to an existing concatenation"
    "(1, 2,)"
    ((natural 1 <.> natural 2) <.> AST.emptyMap)
  assertAstOutput
    "an existing concatenation retains the postfix empty map"
    "(1, 2,)"
    ((natural 1 <.> natural 2) <.> AST.emptyMap)
  assertAstOutput
    "a trailing comma can precede a map separator"
    "(1,; 2)"
    ((natural 1 <.> AST.emptyMap) <:> natural 2)
  assertAstOutput
    "access consumes a concatenated range insertion"
    "(... @ 1..3, 5..7)"
    ((...) <@> ((natural 1 <..> natural 3) <.> (natural 5 <..> natural 7)))
  assertAstOutput
    "parentheses can concatenate an access result"
    "((... @ 1), 2)"
    (((...) <@> natural 1) <.> natural 2)
  assertAstOutput
    "map expressions are concatenation operands"
    "((1; 2), (3; 4))"
    ((natural 1 <:> natural 2) <.> (natural 3 <:> natural 4))
  assertAstOutput
    "unary grouping does not manufacture map expansion"
    "((1 + 2); (3 * 4))"
    ((natural 1 AST.+ natural 2) <:> (natural 3 AST.* natural 4))
  assertAstOutput
    "outer map parentheses are inferred"
    "2 + 3"
    (natural 2 AST.+ natural 3)
  assertAstOutput
    "completed lines become map elements"
    "2\n3"
    (natural 2 <:> natural 3)
  assertAstOutput
    "a parenthesized syntax operand ends before the next map element"
    "1 of (Nat -> Int)\n\"x\""
    ( Subfederation
        (natural 1)
        (FunctionType (ref "Nat") (ref "Int"))
        <:> AsciiStringLiteral "x"
    )
  assertAstOutput
    "a newline after an operator continues the expression"
    "2 +\n3\n4"
    ((natural 2 AST.+ natural 3) <:> natural 4)
  assertAstOutput
    "comments do not hide a required continuation"
    "2 + # continue addition\n3\n# blank comment line\n4"
    ((natural 2 AST.+ natural 3) <:> natural 4)
  assertAstOutput
    "blank lines do not create empty map elements"
    "\n# heading\n2\n\n# between values\n3\n"
    (natural 2 <:> natural 3)
  assertAstOutput
    "a semicolon separates a postfix range from the next map line"
    "2..;\n3..-"
    ((natural 2 ..+) <:> (natural 3 ..-))
  assertAstOutput
    "ellipsis is complete despite ending in dots"
    "...\n2"
    ((...) <:> natural 2)
  assertAstOutput
    "bounded range and concatenation operators continue across lines"
    "2..\n4,\n5.."
    ((natural 2 <..> natural 4) <.> (natural 5 ..+))
  assertAstOutput
    "an ambiguous postfix range greedily consumes a following operand"
    "(2..\n4)"
    (natural 2 <..> natural 4)
  assertAstOutput
    "exponentiation continues and remains right associative"
    "2 ^\n3 ^\n4"
    (natural 2 AST.^ natural 3 AST.^ natural 4)
  assertAstOutput
    "newlines separate expressions in an explicit map"
    "(2\n3)"
    (natural 2 <:> natural 3)
  assertAstOutput
    "newline inference applies independently to nested maps"
    "((1\n2)\n(3\n4))"
    ((natural 1 <:> natural 2) <+> (natural 3 <:> natural 4))
  assertAstOutput
    "separately parenthesized expressions form an implicit outer map"
    "(1)\n2"
    (natural 1 <:> natural 2)
  assertAstOutput
    "parentheses inside comments do not affect outer-map inference"
    "(1)\n2 # ) is only a comment"
    (natural 1 <:> natural 2)
  assertAstOutput
    "operator continuation also applies in explicit maps"
    "(2 +\n3\n4)"
    ((natural 2 AST.+ natural 3) <:> natural 4)
  assertAstOutput
    "newlines inside unfinished expressions are ignored"
    "(2 + \n 3)"
    (natural 2 AST.+ natural 3)
  assertAstOutput
    "multiline parenthesized expressions remain one expression"
    "(2 +\n3)\n4"
    ((natural 2 AST.+ natural 3) <:> natural 4)
  assertParsed
    "exponentiation associates right"
    "(2 ^ 3 ^ 4)"
    ((AST.^)
      (natural 2)
      ((AST.^) (natural 3) (natural 4)))
  assertParsed
    "addition associates left"
    "(1 + 2 + 3)"
    ((AST.+)
      ((AST.+) (natural 1) (natural 2))
      (natural 3))
  assertParsed
    "access associates left"
    "(... @ 1 @ 2)"
    ((<@>)
      ((<@>) (...) (natural 1))
      (natural 2))
  assertParsed
    "map is itself an expression"
    "(((1; 2), (3; 4)) @ 0)"
    ((<@>)
      ((<.>)
        (AtlasMap [natural 1, natural 2])
        (AtlasMap [natural 3, natural 4]))
      (natural 0))
  assertAstOutput
    "a single unparenthesized expression stays itself"
    "10"
    (natural 10)
  assertAstOutput
    "one trailing semicolon is ignored"
    "(1; 2; # trailing separator\n)"
    (natural 1 <:> natural 2)
  assertRejected "multiple trailing semicolons are rejected" "(1; 2;;)"
  assertRejected "IdentifierString rejects a missing body" "$"
  assertAstOutput "IdentifierString accepts a leading apostrophe"
    "$'bad" (AST.asciiString "'bad")
  assertRejected "IdentifierString rejects an apostrophe without a body" "$'"
  assertRejected "IdentifierString requires alphanumeric after apostrophe" "$'_bad"
  assertParsed "a hyphen terminates a compact string and starts subtraction" "$bad-name"
    (Subtraction (AsciiStringLiteral "bad") (IdentifierReference (IdentifierString "name")))
  assertRejected "StandardString rejects unsupported escapes" "\"bad\\t\""
  assertParsed "percent introduces a lexical interpolation" "\"bad%value\""
    (StringTemplate [StringTemplateLiteral "bad", StringTemplateInterpolation (IdentifierReference (IdentifierString "value"))])
  assertRejected "StandardString rejects the obsolete dollar escape" "\"bad\\$value\""
  assertRejected "StandardString rejects an unterminated literal" "\"bad"
  assertRejected "ASCII strings reject characters outside the ASCII map" "\"λ\""
  assertRejected "multiple trailing commas are rejected" "(1,,)"
  assertRejected "standalone brackets are not an empty map" "[]"
  assertRejected "bracket access requires an insertion" "$a[]"
  assertRejected
    "multiple trailing commas after concatenation are rejected"
    "(1, 2,,)"
  assertRejected "empty entries in the middle are rejected" "(1;;2)"
  assertRejected "bounded ranges are non-associative" "(1..2..3)"
  assertRejected "prefix and postfix ranges cannot be chained" "(..2..)"
  assertRejected "adjacent range markers cannot be chained" "(1....2)"
  assertRejected "the old explicit plus spelling is rejected" "(1..+)"
  assertParsed "AST range pattern captures an origin expression" "range (1 + 2) to 5"
    (rangeCall "range" (Addition (natural 1) (natural 2)) (UpperBound (natural 5)))
  assertParsed "AST range pattern captures a target expression" "range 1 to (2 + 3)"
    (rangeCall "range" (natural 1) (UpperBound (Addition (natural 2) (natural 3))))
  assertParsed "range-like names remain whole references" "range1to2"
    (IdentifierReference (IdentifierString "range1to2"))
  assertAstOutput
    "parentheses permit an explicitly nested range"
    "((1..2)..)"
    ((natural 1 <..> natural 2) ..+)
  assertParsed
    "a parenthesized Ellipsis can be a postfix range argument"
    "((...)..)"
    ((..+) (...))
  assertAstOutput
    "a parenthesized Ellipsis can be a prefix range argument"
    "(..(...))"
    (natural 0 <..> (...))
  assertAstOutput
    "a parenthesized Ellipsis can be a bounded range argument"
    "((...)..2; 1..(...))"
    (((...) <..> natural 2) <:> (natural 1 <..> (...)))
  assertRejected
    "a bare Ellipsis cannot be a postfix range argument"
    "(... ..)"
  assertRejected
    "a bare Ellipsis cannot be a prefix range argument"
    "(.. ...)"
  assertRejected
    "a bare Ellipsis cannot be a bounded lower argument"
    "(... .. 2)"
  assertRejected
    "a bare Ellipsis cannot be a bounded upper argument"
    "(1.. ...)"
  assertRejected "addition requires a right operand" "(1 +)"
  assertRejected "parentheses must be balanced" "((1 + 2)"
  assertAstOutput
    "a prefix operator on the next line starts a new map member"
    "2\n+ 3"
    (natural 2 <:> AST.plus (natural 3))
  assertAstOutput
    "separate parenthesized maps form an implicit outer map"
    "(1)\n(2)"
    (natural 1 <:> natural 2)

matchRules
  :: (SyntaxHoleKind Expression -> Expression -> Bool)
  -> [SyntaxRule]
  -> Expression
  -> Either SyntaxTemplateMatchFailure Expression
matchRules holeMatches rules expressionValue =
  matchSyntaxRules holeMatches rules expressionValue

assert :: String -> Bool -> IO ()
assert = assertBool

propAstRoundTrip :: H.Property
propAstRoundTrip = H.property $ do
  expressionValue <- H.forAll genExpression
  let rendered = renderExpression expressionValue
  case parseDatraAst rendered of
    Left message -> do
      H.footnote (renderParseFailure message)
      H.failure
    Right roundTripped -> renderExpression roundTripped H.=== rendered

propNaturalMapParsing :: H.Property
propNaturalMapParsing = H.property $ do
  values <- H.forAll
    (Gen.list (Range.linear 0 40) (Gen.integral (Range.linear 0 100000)))
  let source = "(" <> joinWith "; " (map show values) <> ")"
      expected = normalizeExpression (AtlasMap (map EllipsisNatural values))
  parseSource ("(" <> source <> "\n)") H.=== Right expected

genExpression :: H.Gen Expression
genExpression =
  Gen.recursive Gen.choice
    [ EllipsisNatural <$> Gen.integral (Range.linear 0 1000)
    , pure EllipsisLiteral
    , ref <$> Gen.element ["nothing", "true", "false", "Nat", "Int", "Str", "IdenStr", "Bool", "AST", "IntRange", "NatRange", "IntValRange", "NatValRange", "Template"]
    , IdentifierReference <$> genIdentifierString
    , pure (ref "_this")
    , datraRef <$> Gen.element
        [["add"], ["abs"], ["syntax", "if"]]
    , AsciiStringLiteral
        <$> Gen.list (Range.linear 0 24) (Gen.enum '\0' '\255')
    , genRangeExpression
    ]
    [ AtlasMap <$> Gen.list (Range.linear 0 6) genExpression
    , ArgumentativeMap <$> Gen.list (Range.linear 0 6) genExpression
    , pure Skip
    , MapSequence <$> Gen.list (Range.linear 0 6) genExpression
    , Gen.subterm2 genExpression genExpression FunctionType
    , Gen.subterm2 genExpression genExpression FunctionApplication
    , Gen.subterm2 genExpression genExpression ScopeAccess
    , Gen.subterm genExpression
        (Import ["std", "path/library_two"])
    , Gen.subterm genExpression (InModule "std")
    , Gen.subterm2 genExpression genExpression
        (\binding result -> FunctionBody [generatedDeclaration binding] result)
    , Gen.subterm2 genExpression genExpression
        (\binding result -> Begin [generatedDeclaration binding] result)
    , Gen.subterm genExpression Let
    , Gen.subterm genExpression (StringTemplate . (:[]) . StringTemplateInterpolation)
    , Gen.subterm2 genExpression genExpression MapExpansion
    , Gen.subterm2 genExpression genExpression SuperEllipsisRange
    , Gen.subterm genExpression SuperEllipsisRangePlus
    , Gen.subterm genExpression SuperEllipsisRangeMinus
    , Gen.subterm2 genExpression genExpression Addition
    , Gen.subterm2 genExpression genExpression Subtraction
    , Gen.subterm genExpression Plus
    , Gen.subterm genExpression Minus
    , Gen.subterm2 genExpression genExpression Multiplication
    , Gen.subterm2 genExpression genExpression Exponentiation
    , Gen.subterm2 genExpression genExpression Subfederation
    , Gen.subterm2 genExpression genExpression Equality
    , Gen.subterm2 genExpression genExpression Inequality
    , Gen.subterm2 genExpression genExpression EitherType
    , Gen.subterm2 genExpression genExpression MapConcatenation
    , Gen.subterm2 genExpression genExpression MapAccess
    , Gen.subterm2 genExpression genExpression MapSpecification
    , Gen.subterm2 genExpression genExpression Overload
    , Gen.subterm2 genExpression genExpression SafeOverload
    , IdentifierOperation
        <$> genIdentifierString
        <*> genExpression
        <*> Gen.maybe genExpression
    ]

genRangeExpression :: H.Gen Expression
genRangeExpression = rangeCall
  <$> Gen.element ["range", "from"]
  <*> endpoint
  <*> Gen.choice [UpperBound <$> endpoint, pure Upwards, pure Downwards]
  where
    endpoint = integer <$> Gen.integral (Range.linear (-1000) 1000)

genIdentifierString :: H.Gen IdentifierString
genIdentifierString = do
  prefix <- Gen.choice
    [ (: []) <$> Gen.element (['a' .. 'z'] <> ['A' .. 'Z'])
    , do
        first <- Gen.element ['_', '\'']
        second <- Gen.element
          (['a' .. 'z'] <> ['A' .. 'Z'] <> ['0' .. '9'])
        pure [first, second]
    ]
  rest <-
    Gen.list
      (Range.linear 0 12)
      (Gen.element
        (['_', '\'']
          <> ['a' .. 'z']
          <> ['A' .. 'Z']
          <> ['0' .. '9']))
  pure (IdentifierString (prefix <> rest))

joinWith :: String -> [String] -> String
joinWith _ [] = ""
joinWith _ [value] = value
joinWith separator (value : values) =
  value <> separator <> joinWith separator values

assertAllHexadecimalAsciiEscapes :: IO ()
assertAllHexadecimalAsciiEscapes = do
  mapM_ assertTwoDigitEscape [0 .. 255]
  mapM_ assertOneDigitEscape [0 .. 15]
  where
    assertTwoDigitEscape byteValue =
      assertHexadecimalEscape
        ("two-digit hexadecimal escape " <> hexadecimalByte byteValue)
        (hexadecimalByte byteValue)
        byteValue

    assertOneDigitEscape byteValue =
      assertHexadecimalEscape
        ("one-digit hexadecimal escape " <> hexadecimalDigit byteValue)
        (hexadecimalDigit byteValue)
        byteValue

    assertHexadecimalEscape label digits byteValue =
      assertParsed
        label
        ("\"\\" <> digits <> "\"")
        (AsciiStringLiteral [chr byteValue])

    hexadecimalByte byteValue =
      case hexadecimalDigit byteValue of
        [digit] -> ['0', digit]
        digits -> digits

    hexadecimalDigit byteValue =
      map toUpper (showHex byteValue "")

assertLocatedParse :: IO ()
assertLocatedParse =
  case parseSourceLocated True "<input>" "(1; 2)" of
    Left message -> fail
      ("located parse unexpectedly failed: " <> renderParseFailure message)
    Right
        (Located
          (SourceSpan source start end)
          (AtlasMap [EllipsisNatural 1, EllipsisNatural 2])) ->
      assert
        "located parsing uses an in-memory source span"
        ( source == "<input>"
          && start == SourcePosition 0 1 1
          && end == SourcePosition 6 1 7
        )
    Right actual ->
      fail ("located parse returned an unexpected value: " <> show actual)

assertResourceEnvelopes :: IO ()
assertResourceEnvelopes = do
  assertEnvelope
    "explicit outer map parentheses"
    "(1; 2)"
    ExplicitMapEnvelope
  assertEnvelope
    "implicit program"
    "1\n2"
    ImplicitBlockEnvelope
  assertEnvelope
    "parenthesized operands are not an outer envelope"
    "(1) <~ (2)"
    ImplicitBlockEnvelope
  mapM_ (\(source, expected) ->
    case parseSource source of
      Right actual -> do
        assert ("program AST: " <> source) (actual == expected)
        assertAstRoundTrip "program AST roundtrip" (renderExpression actual)
      Left message -> fail (renderParseFailure message))
    [ ("a := 6\nyield a", Begin
        [declarationEntry (AST.assignment "a" (natural 6) (natural 6))]
        (IdentifierReference (IdentifierString "a")))
    , ( "yield 5 >> {a? : Nat := 3}"
      , Begin []
          (Overload
            (ArgumentativeMap
              [OptionalType (AST.assignment "a" (ref "Nat") (natural 3))])
            (natural 5))
      )
    , ( "yield \"a\" >>> {x? : Nat := 2; Str}"
      , Begin []
          (SafeOverload
            (ArgumentativeMap
              [ OptionalType
                  (AST.assignment "x" (ref "Nat") (natural 2))
              , ref "Str"
              ])
            (AST.asciiString "a"))
      )
    , ( "yield Nat <~ (fun 5)"
      , Begin [] (MapSpecification (Fun (natural 5)) (ref "Nat"))
      )
    , ("a := 6", Begin
        [declarationEntry (AST.assignment "a" (natural 6) (natural 6))]
        (AtlasMap []))
    , ("", Begin [] (AtlasMap []))
    ]
  where
    assertEnvelope label source expected =
      case parseDatraRawLocatedWithSourceName "<input>" source of
        Left message -> fail
          (label <> ": unexpected failure: " <> renderParseFailure message)
        Right (actual, _) -> assert label (actual == expected)

assertBundledModuleBlockShape :: IO ()
assertBundledModuleBlockShape = do
  assertModule "libs/std.datra" NoStandardLibrary "Std"
  assertModule "libs/numbers.datra" QualifiedStandardLibrary "Numbers"
  where
    assertModule path visibility expectedName = do
      source <- readFile path
      case parseDatraSourceLocatedWithImportsAndStandardLibraryVisibility
          visibility [] path source of
        Left failure -> fail
          (path <> ": unexpected parse failure: " <> renderParseFailure failure)
        Right located -> case openedBody (locatedValue located) of
          Begin [] (IdentifierOperation
              (IdentifierString actualName) annotation given)
            | actualName == expectedName
            , Begin {} <- maybe annotation id given -> pure ()
          actual -> fail
            (path <> ": expected an outer block yielding a named inner block, got "
              <> show actual)
    openedBody (ScopeAccess _ body) = openedBody body
    openedBody (SyntaxBoundary body) = openedBody body
    openedBody value = value

assertStandardSyntaxDeclarationsAdmissible :: IO ()
assertStandardSyntaxDeclarationsAdmissible = do
  source <- readFile "libs/std.datra"
  case parseDatraRawLocatedWithSourceName "libs/std.datra" source of
    Left failure -> fail
      ("Std neutral parse failed: " <> renderParseFailure failure)
    Right (_, Located _ raw) -> do
      let declarations = syntaxDeclarations raw
      assert "Std contains syntax declarations" (not (null declarations))
      assert "every Std syntax declaration is admissible"
        (all (not . null . declarationRules) declarations)
  where
    syntaxDeclarations expressionValue = current
      <> concatMap syntaxDeclarations
        (expressionChildren expressionValue)
      where
        current = case expressionValue of
          declaration@IdentifierTemplateOperation { identifierTemplateParts = parts }
            | any isInterpolation parts -> [declaration]
          _ -> []
    isInterpolation StringTemplateInterpolation {} = True
    isInterpolation StringTemplateLiteral {} = False

assertAstSyntax :: IO ()
assertAstSyntax = do
  assert "ASCII-string syntax chooses its canonical spelling"
    ( renderExpression (AST.asciiString "name_1") == "$name_1"
      && renderExpression (AST.asciiString "a\"b\\c\n")
        == "\"a\\\"b\\\\c\\n\""
    )
  assert "template rendering delimits a reference before a literal optional suffix"
    ( renderExpression
        (StringTemplate
          [ StringTemplateInterpolation (ref "Int")
          , StringTemplateLiteral "?"
          ])
        == "\"%((ref $Int))?\""
    )
  assert "sequential and expansion symbols construct canonical AST nodes"
    ( renderExpression
        ((natural 1 <:> natural 2) <+> (natural 3 <:> natural 4))
        == "(<+> (<:> 1 2) (<:> 3 4))"
    )
  assert "empty and unary AST products normalize structurally"
    ( renderExpression (MapSequence [natural 1]) == "1"
      && renderExpression (MapExpansion (AtlasMap []) (natural 1)) == "1"
      && renderExpression (MapExpansion (natural 1) (AtlasMap [])) == "1"
    )
  assert "range, arithmetic, concatenation, and access symbols construct ASTs"
    ( renderExpression
        ( ((natural 1 AST.+ natural 2 AST.* natural 3) <..> (...))
            <.> ((natural 4 ..+) <@> (natural 5 ..-))
        )
        == "(<.> (<..> (+ 1 (* 2 3)) ...) (<@> (..+ 4) (..- 5)))"
    )
  assert "the specification symbol constructs its canonical AST node"
    ( renderExpression
        (((natural 2 <..> natural 5) ~> ref "Nat"))
        == "(~> (<..> 2 5) (ref $Nat))"
    )
  assertEqual
    "bounded from calls retain their scoped signature and checked captures"
    "(apply-func (in-module $Std (ref $'from)) (<:> 2 5))"
    (renderExpression (fromTo 2 5))
  assertEqual
    "directional from calls retain the private direction type"
    "(apply-func (in-module $Std (ref $'from)) (<:> 2 $up))"
    (renderExpression (fromUpwards 2))
  assert "library types render as identifier references"
    (renderExpression (ref "Nat") == "(ref $Nat)")

assertAstOutput :: String -> String -> Expression -> IO ()
assertAstOutput label source expected =
  case parseSource ("(" <> source <> "\n)") of
    Left message -> fail
      (label <> ": unexpected parse failure: " <> renderParseFailure message)
    Right actual
      | canonicalAst actual == canonicalAst expected ->
          assertAstRoundTrip label (renderExpression actual)
      | otherwise ->
          fail
            ( label
                <> ": expected "
                <> show (canonicalAst expected)
                <> ", got "
                <> show (canonicalAst actual)
            )
  where
    canonicalAst = toOperatorExpression . normalizeExpression

assertAstRoundTrip :: String -> String -> IO ()
assertAstRoundTrip label renderedAst =
  case renderExpression <$> parseDatraAst renderedAst of
    Left message ->
      fail
        (label <> ": emitted AST could not be parsed: "
          <> renderParseFailure message)
    Right roundTripped
      | roundTripped == renderedAst -> pure ()
      | otherwise ->
          fail
            ( label
                <> ": AST round trip changed "
                <> show renderedAst
                <> " to "
                <> show roundTripped
            )

assertRejected :: String -> String -> IO ()
assertRejected label source =
  case parseSource ("(" <> source <> "\n)") of
    Left _ -> pure ()
    Right actual ->
      fail (label <> ": unexpectedly parsed as " <> show actual)

assertParsed :: String -> String -> Expression -> IO ()
assertParsed label source expected =
  case parseSource ("(" <> source <> "\n)") of
    Left message -> fail
      (label <> ": unexpected parse failure: " <> renderParseFailure message)
    Right actual
      | actual == expected -> pure ()
      | otherwise ->
          fail
            ( label
                <> ": expected "
                <> show expected
                <> ", got "
                <> show actual
            )

parseSource :: String -> Either ParseFailure Expression
parseSource source =
  locatedValue <$> parseSourceLocated True "<input>" source

parseSourceLocated
  :: Bool
  -> FilePath
  -> String
  -> Either ParseFailure (Located Expression)
parseSourceLocated includeStandardLibrary =
  parseDatraSourceLocatedWithImportsAndStandardLibrary
    includeStandardLibrary []

containsFunctionBody :: Expression -> Bool
containsFunctionBody FunctionBody {} = True
containsFunctionBody value = any containsFunctionBody (expressionChildren value)

-- Source expectations describe the emitted AST directly. Keep these independent
-- of the parser's syntax expansion so they can catch changes in that expansion.
ref :: String -> Expression
ref = IdentifierReference . IdentifierString

declarationEntry :: Expression -> DependentDeclaration Expression
declarationEntry expressionValue =
  case dependentDeclaration expressionValue of
    Just declaration -> declaration
    Nothing -> error "test expression is not a dependent declaration"

generatedDeclaration :: Expression -> DependentDeclaration Expression
generatedDeclaration = DependentDeclaration
  (SimpleIdentifierDeclarationHead (IdentifierString "generated"))
  False False False

datraRef :: [String] -> Expression
datraRef = foldl ScopeAccess (ref "datra") . map ref

integer :: Integer -> Expression
integer value
  | value < 0 = Minus (natural (fromInteger (negate value)))
  | otherwise = natural (fromInteger value)

rangeTo, fromTo :: Integer -> Integer -> Expression
rangeTo start end = rangeCall "range" (integer start) (UpperBound (integer end))
fromTo start end = rangeCall "from" (integer start) (UpperBound (integer end))

rangeUpwards, rangeDownwards, fromUpwards :: Integer -> Expression
rangeUpwards start = rangeCall "range" (integer start) Upwards
rangeDownwards start = rangeCall "range" (integer start) Downwards
fromUpwards start = rangeCall "from" (integer start) Upwards

data RangeEnd = UpperBound Expression | Upwards | Downwards

rangeCall :: String -> Expression -> RangeEnd -> Expression
rangeCall name start end = FunctionApplication
  (InModule "Std" (ref ('\'' : name)))
  (AtlasMap [start, endpoint])
  where
    endpoint = case end of
      UpperBound value -> value
      Upwards -> AsciiStringLiteral "up"
      Downwards -> AsciiStringLiteral "down"
