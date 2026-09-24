-- | Romanian presentation text for typed Datra diagnostics.
module DatraLanguage.Diagnostics.Locales.Romanian
  ( localizeAccessError
  , localizeParseFailure
  , localizeModuleLoadFailure
  , localizeSyntaxExpansionFailure
  , localizeCommandLineOptionFailure
  , localizeInterpretingError
  , localizeSuperEllipsisRangeError
  , localizeSuperEllipsisRangeConcatError
  , romanianOrdinal
  ) where

import DatraLanguage.Diagnostics (LocalizedMessage (LocalizedMessage))
import DatraLanguage.Diagnostics.Application
  ( CommandLineOptionFailure (..)
  , ModuleLoadFailure (..)
  , ParseFailure (..)
  , SyntaxExpansionFailure (..)
  )
import Evaluation.Error
  ( InterpretedValueKind (..)
  , InterpretingError (..)
  , ExternalFailure (..)
  , FunctionFailure (..)
  , ModuleEvaluationFailure (..)
  , NamedAccessFailure (..)
  , OverloadFailure (..)
  , OperandSide (..)
  , AtlasMapFederationOperation (..)
  , AtlasMapFederationRefutation (..)
  , AtlasMapFederationUncertainty (..)
  )
import DatraLanguage.Diagnostics.Locales.Rendering
  ( renderOrdinal
  , renderRangeBounds
  , renderRangeDescription
  )
import DatraOrdinal (Ordinal)
import MapOperators.AccessOperator
  ( AccessError
      ( AccessInsertionRankExceedsMap
      , AccessPositionOutOfBounds
      )
  )
import SuperEllipsisRange
  ( SuperEllipsisRangeConcatError (SuperEllipsisRangesOverlap)
  , SuperEllipsisRangeError
      ( SuperEllipsisRangeInvalidDescendingBounds
      , SuperEllipsisRangeStartOutsideRank
      , SuperEllipsisRangeTargetOutsideRank
      )
  )

localizeParseFailure :: ParseFailure -> LocalizedMessage
localizeParseFailure (ParseFailure message) =
  LocalizedMessage "sursa nu a putut fi analizată" [message]

localizeModuleLoadFailure :: ModuleLoadFailure -> LocalizedMessage
localizeModuleLoadFailure failure =
  case failure of
    ImportScanFailed path parseFailure ->
      LocalizedMessage "importurile modulului nu au putut fi analizate"
        ["modul: " <> path, parseFailureMessage parseFailure]
    ImportPathResolutionFailed requested location reason ->
      LocalizedMessage "calea modulului nu a putut fi rezolvată"
        [ "modul: " <> requested
        , "locație: " <> location
        , "motiv: " <> reason
        ]
    CyclicModuleImport path ->
      LocalizedMessage "import ciclic de modul" ["modul: " <> path]
    ModuleReadFailed requested path reason ->
      LocalizedMessage "modulul nu a putut fi citit"
        [ "modul: " <> requested
        , "cale: " <> path
        , "motiv: " <> reason
        ]
    ImportedModuleParseFailed path parseFailure ->
      LocalizedMessage "modulul importat nu a putut fi analizat"
        ["modul: " <> path, parseFailureMessage parseFailure]

localizeSyntaxExpansionFailure
  :: SyntaxExpansionFailure
  -> LocalizedMessage
localizeSyntaxExpansionFailure failure =
  case failure of
    UnknownSyntaxControlAdapter name ->
      LocalizedMessage "adaptorul de control sintactic nu este înregistrat"
        ["adaptor: " <> name]
    InvalidSyntaxControlCaptures name expected given ->
      LocalizedMessage "adaptorul de control sintactic a primit capturi nevalide"
        [ "adaptor: " <> name
        , "capturi așteptate: " <> show expected
        , "capturi primite: " <> show given
        ]

localizeCommandLineOptionFailure
  :: CommandLineOptionFailure
  -> LocalizedMessage
localizeCommandLineOptionFailure failure =
  case failure of
    UnsupportedDiagnosticLocale value ->
      LocalizedMessage "limba diagnosticului nu este acceptată"
        [ "limbă furnizată: " <> value
        , "se așteaptă english, en, romana, romanian sau ro"
        ]
    UnsupportedEvaluationMode value ->
      LocalizedMessage "modul de evaluare nu este acceptat"
        [ "mod furnizat: " <> value
        , "se așteaptă dev, development, prod sau production"
        ]

localizeAccessError :: AccessError -> LocalizedMessage
localizeAccessError reason =
  case reason of
    AccessInsertionRankExceedsMap insertionRank mapOrderType ->
      LocalizedMessage
        "inserția de acces are un rang mai mare decât harta"
        [ "limita rangului inserției: " <> romanianOrdinal insertionRank
        , "tipul de ordine al ultimei pagini din hartă: "
            <> romanianOrdinal mapOrderType
        ]
    AccessPositionOutOfBounds position mapOrderType ->
      LocalizedMessage
        "inserția de acces selectează o poziție din afara hărții"
        [ "poziția selectată: " <> romanianOrdinal position
        , "tipul de ordine al ultimei pagini din hartă: "
            <> romanianOrdinal mapOrderType
        ]

localizeInterpretingError :: InterpretingError -> LocalizedMessage
localizeInterpretingError reason =
  case reason of
    NamedAccessFailed failure -> localizeNamedAccessFailure failure
    FunctionEvaluationFailed failure -> localizeFunctionFailure failure
    ExternalEvaluationFailed failure -> localizeExternalFailure failure
    ModuleEvaluationFailed failure -> localizeModuleFailure failure
    ExpectedBuiltinType name ->
      LocalizedMessage "valoarea nu aparține tipului încorporat necesar"
        ["tip așteptat: " <> name]
    NonCanonicalIdentifierTypeAnnotation ->
      LocalizedMessage "adnotarea de tip a identificatorului nu este canonică"
        ["adnotările de tip ale identificatorilor trebuie să implementeze toString canonic"]
    OverloadError failure ->
      LocalizedMessage "supraîncărcarea a eșuat" [overloadFailure failure]
    AssertionFailed -> LocalizedMessage "aserțiunea a eșuat" []
    IdentifierStringOverlap name ->
      LocalizedMessage "șirurile identificatorilor se suprapun în domeniul begin" ["identificator: " <> name]
    UnknownIdentifier name ->
      LocalizedMessage "identificatorul nu este importat în acest domeniu" ["identificator: " <> name]
    PrivateParameterCannotBeOptional name ->
      LocalizedMessage
        "parametrul privat al funcției nu poate fi opțional"
        ["identificator: " <> name]
    CyclicIdentifierReference names ->
      LocalizedMessage "dependență ciclică între identificatori" ["identificatori: " <> show names]
    LetOutsideBegin ->
      LocalizedMessage "let necesită un bloc begin" []
    ExpectedNumericalOperand side actual ->
      LocalizedMessage
        ("operandul " <> operandSide side <> " trebuie să fie numeric")
        ["tipul efectiv al valorii: " <> valueKind actual]
    ExpectedFiniteIntegerOperand side actual ->
      LocalizedMessage
        ("operandul " <> operandSide side <> " trebuie să fie un întreg finit")
        ["tipul efectiv al valorii: " <> valueKind actual]
    ExpectedBooleanOperand side actual ->
      LocalizedMessage
        ("operandul " <> operandSide side <> " trebuie să fie boolean")
        ["tipul efectiv al valorii: " <> valueKind actual]
    ExpectedBooleanCondition actual ->
      LocalizedMessage
        "condiția if trebuie să fie booleană"
        ["tipul efectiv al valorii: " <> valueKind actual]
    ExpectedNaturalExponent actual ->
      LocalizedMessage
        "exponentul trebuie să fie o valoare naturală"
        ["tipul efectiv al valorii: " <> valueKind actual]
    ExpectedInsertionOperand actual ->
      LocalizedMessage
        ( "operandul drept al accesării hărții trebuie să definească "
            <> "o inserție cu super-elipsă"
        )
        ["tipul efectiv al valorii: " <> valueKind actual]
    ExpectedTotalAtlasMap actual ->
      LocalizedMessage
        "operandul stâng al specificării trebuie să fie o hartă Atlas totală"
        ["tipul efectiv al valorii: " <> valueKind actual]
    RangeConstructionRejected rejection ->
      localizeSuperEllipsisRangeError rejection
    RangeConcatenationRejected rejection ->
      localizeSuperEllipsisRangeConcatError rejection
    AccessRejected rejection -> localizeAccessError rejection
    GivenValueOutsideTypeAnnotation expected given ->
      LocalizedMessage
        "valoarea dată este în afara adnotării de tip"
        [ "așteptat: " <> expected
        , "dat: " <> given
        ]
    IdentifierStringMismatch expected given ->
      LocalizedMessage
        "șirul identificatorului nu corespunde"
        [ "așteptat: " <> expected
        , "dat: " <> given
        ]
    IntermediateTypeAnnotationOutsideTarget expected given ->
      LocalizedMessage
        "adnotarea de tip intermediară nu se încadrează în adnotarea de tip țintă"
        [ "așteptat: " <> expected
        , "dat: " <> given
        ]
    AtlasMapFederationOperationRefuted refutation ->
      case refutation of
        AtlasMapFederationConcatenationCollision value ->
          LocalizedMessage
            "concatenarea nu produce o federație de hărți Atlas"
            [ "valoarea " <> show value
                <> " apare pe ambele părți în două configurații"
            ]
        AtlasMapFederationAccessHasEmptyCounterexample ->
          LocalizedMessage
            "accesarea eșuează pentru un membru al federației"
            ["harta vidă este contraexemplu pentru selecția nevidă"]
        AtlasMapFederationSpecificationHasNoMatchingMember ->
          LocalizedMessage
            "specificarea nu are o hartă Atlas corespunzătoare în federație"
            [ "harta Atlas totală sursă este un contraexemplu: niciun membru "
                <> "nu admite morfismul cu paginație identitate"
            ]
        AtlasMapFederationSubfederationHasMissingMember ->
          LocalizedMessage
            "federația intermediară nu este o subfederație Atlas a țintei"
            [ "o hartă Atlas din federația intermediară lipsește din "
                <> "federația finală"
            ]
    AtlasMapFederationOperationUndecidable
        (NoAtlasMapFederationDecisionProcedure operation) ->
      LocalizedMessage
        "compilatorul nu poate decide această operație pe federații"
        ["operația: " <> federationOperation operation]
    NonInjectiveStringInterpolation ->
      LocalizedMessage
        "interpolare de șir neinjectivă"
        ["valori distincte din interpolare pot avea aceeași formă de șir"]
    NoCanonicalStringConversion ->
      LocalizedMessage
        "valoarea nu are o conversie canonică în șir"
        [ "weakToString poate reda valoarea, dar specificarea necesită "
            <> "o conversie canonică injectivă"
        ]
    ExpectedStringTemplateSpecification kind ->
      LocalizedMessage
        "extract necesită o specificație concretă de șablon de șir"
        ["tipul valorii date: " <> valueKind kind]
    EitherAlternativesNotDistinct ->
      LocalizedMessage
        "alternativele Either nu sunt hărți Atlas diferențiabile"
        ["alternativele nu pot fi membri distincți ai aceleiași federații Atlas"]
    AmbiguousStringTemplate ->
      LocalizedMessage
        "șablon de șir ambiguu"
        ["șablonul nu mapează fiecare configurație sursă la un șir unic"]
    InvalidAsciiStringCharacter character ->
      LocalizedMessage
        "șirul conține un caracter din afara hărții ASCII"
        ["caracter: " <> show character]

localizeFunctionFailure :: FunctionFailure -> LocalizedMessage
localizeFunctionFailure failure =
  case failure of
    UnconstrainedInferredParameter name ->
      LocalizedMessage "nu se poate deduce un parametru de funcție fără constrângeri"
        ["parametru: " <> name, "furnizați un tip de intrare explicit"]
    IncompatibleInferredParameterConstraints name ->
      LocalizedMessage "parametrul funcției are constrângeri deduse incompatibile"
        ["parametru: " <> name]
    InferredApplicationRequiresFunction ->
      LocalizedMessage "deducerea a găsit aplicarea unei valori care nu este funcție" []
    UnsupportedInferredExpression ->
      LocalizedMessage "tipul rezultatului funcției nu poate fi dedus pentru această expresie"
        ["adăugați o specificație explicită acceptată"]
    InferredTypeOutsideRequirement actual expected ->
      LocalizedMessage "tipul dedus este în afara tipului necesar"
        ["dedus: " <> actual, "necesar: " <> expected]
    AstPatternRequiresFunctionSignature ->
      LocalizedMessage "un șablon AST necesită o semnătură de funcție" []
    AstPatternRequiresFunctionImplementation ->
      LocalizedMessage "un șablon AST necesită o implementare de funcție" []
    FunctionBodyOutsideDeclaredResult ->
      LocalizedMessage "corpul funcției nu satisface tipul de ieșire declarat" []
    ExternalAdapterRequiresAstCaptures ->
      LocalizedMessage "adaptorul extern de sintaxă necesită capturi AST neevaluate" []
    AmbiguousFunctionSumApplication ->
      LocalizedMessage "aplicarea sumei de funcții este ambiguă" []
    AmbiguousFunctionArgumentBindings ->
      LocalizedMessage "legăturile argumentelor funcției sunt ambigue"
        ["furnizați identificatori pentru a selecta pozițiile dorite"]
    NoApplicableFunctionAlternative ->
      LocalizedMessage "nicio alternativă de funcție nu acceptă argumentele"
        ["alternativele exclusiv sintactice necesită șablonul lor AST"]
    FunctionSignatureVarianceViolation ->
      LocalizedMessage "semnătura funcției încalcă varianța"
        ["intrarea trebuie să fie contravariantă, iar ieșirea covariantă"]
    FunctionSpecificationUndecidable source target ->
      LocalizedMessage "specificația funcției nu poate fi decisă"
        ["sursă: " <> source, "țintă: " <> target]
    ExpectedFunctionValue ->
      LocalizedMessage "era așteptată o valoare funcție" []
    EmptyFunctionSum ->
      LocalizedMessage "suma de funcții nu are alternative" []
    NoMatchingFunctionSpecificationAlternative ->
      LocalizedMessage "specificația funcției nu are o alternativă corespunzătoare" []
    AmbiguousFunctionSpecification ->
      LocalizedMessage "specificația funcției este ambiguă" []
    FunctionArgumentsRequireFinitePages ->
      LocalizedMessage "argumentele funcției necesită un număr finit de pagini" []
    FunctionArgumentPageUnavailable position ->
      LocalizedMessage "pagina argumentului funcției nu este disponibilă"
        ["poziție: " <> show position]
    ExpectedFunctionType ->
      LocalizedMessage "era așteptat un tip funcție" []

localizeNamedAccessFailure :: NamedAccessFailure -> LocalizedMessage
localizeNamedAccessFailure failure =
  case failure of
    NamedFieldNotFound name ->
      LocalizedMessage "câmpul denumit nu există" ["câmp: " <> name]
    NamedFieldAmbiguous name ->
      LocalizedMessage "câmpul denumit este ambiguu" ["câmp: " <> name]
    NamedFieldMapNotInspectable ->
      LocalizedMessage "harta de câmpuri nu poate fi inspectată" []
    NamedAccessRequiresFiniteMap ->
      LocalizedMessage "accesul prin nume necesită o hartă finită" []

localizeExternalFailure :: ExternalFailure -> LocalizedMessage
localizeExternalFailure failure =
  case failure of
    DuplicateExternalDescriptorField ->
      LocalizedMessage "descriptorul extern conține un câmp duplicat" []
    UnknownExternalDescriptorFields names ->
      LocalizedMessage "descriptorul extern conține câmpuri necunoscute"
        ["câmpuri: " <> show names]
    UnsupportedExternalBackend backend ->
      LocalizedMessage "backendul extern nu este acceptat"
        ["backend: " <> backend]
    MissingExternalDescriptorField name ->
      LocalizedMessage "descriptorului extern îi lipsește un câmp obligatoriu"
        ["câmp: " <> name]
    ExternalDescriptorRequiresStringMap ->
      LocalizedMessage "descriptorul extern trebuie să fie o hartă de câmpuri șir" []
    UnknownExternalSymbol symbol ->
      LocalizedMessage "simbolul extern nu este înregistrat"
        ["simbol: " <> symbol]
    MissingNativeArgument name ->
      LocalizedMessage "funcția nativă nu a primit un argument obligatoriu"
        ["argument: " <> name]

localizeModuleFailure :: ModuleEvaluationFailure -> LocalizedMessage
localizeModuleFailure failure =
  case failure of
    StandardLibraryParseFailure path message ->
      LocalizedMessage "biblioteca standard nu a putut fi analizată"
        ["cale: " <> path, message]
    StandardLibraryRequiresDeclarationBlock path ->
      LocalizedMessage "biblioteca standard trebuie să conțină un bloc de declarații"
        ["cale: " <> path]
    ImportOutsideScope ->
      LocalizedMessage "import trebuie să fie o intrare de domeniu" []
    ImportedModuleRequiresDeclarationBlock ->
      LocalizedMessage "modulul importat trebuie să conțină un bloc de declarații" []
    ImportedModuleRequiresNamedExports ->
      LocalizedMessage "modulul importat trebuie să producă un domeniu sau o hartă denumită"
        ["folosiți yield this pentru a exporta domeniul"]
    ModuleExportRequiresIdentifier ->
      LocalizedMessage "exportul modulului trebuie să aibă un identificator" []
    ModuleNotLoaded path ->
      LocalizedMessage "modulul nu a fost încărcat" ["modul: " <> path]

overloadFailure :: OverloadFailure -> String
overloadFailure failure =
  case failure of
    OverloadNoMatch ->
      "operandul drept nu corespunde operandului stâng fără valorile implicite"
    OverloadAmbiguousWithoutWrittenOrder ->
      "supraîncărcare ambiguă; nu există o potrivire care păstrează ordinea"
    OverloadAmbiguousWrittenOrder ->
      "supraîncărcare ambiguă; există mai multe potriviri care păstrează ordinea"
    OverloadMissingRequiredSlot ->
      "supraîncărcarea lasă necompletată o poziție obligatorie"
    OverloadSkippedRequiredSlot ->
      "un argument obligatoriu fără valoare implicită nu poate fi omis"
    OverloadChangedDefault ->
      "supraîncărcarea sigură nu poate schimba o valoare implicită existentă"

federationOperation :: AtlasMapFederationOperation -> String
federationOperation AtlasMapFederationConcatenation = "concatenare"
federationOperation AtlasMapFederationAccess = "accesare"
federationOperation AtlasMapFederationSpecification = "specificare"
federationOperation AtlasMapFederationSubfederation = "subfederație"

operandSide :: OperandSide -> String
operandSide LeftOperand = "stâng"
operandSide RightOperand = "drept"

valueKind :: InterpretedValueKind -> String
valueKind FunctionValueKind = "function"
valueKind NaturalValueKind = "număr natural"
valueKind IntegerValueKind = "număr întreg"
valueKind BooleanValueKind = "boolean"
valueKind EitherValueKind = "federație Either"
valueKind ExplicitOrdinalValueKind = "ordinal explicit"
valueKind FormulationValueKind = "formulare cu super-elipsă"
valueKind RangeValueKind = "interval"
valueKind RangeConcatenationValueKind = "concatenare de intervale"
valueKind AsciiStringValueKind = "șir ASCII"
valueKind DependentIdentifierTypeValueKind = "tip identificator"
valueKind MapValueKind = "hartă"
valueKind SpecificationValueKind = "morfism de specificare"

localizeSuperEllipsisRangeError
  :: SuperEllipsisRangeError
  -> LocalizedMessage
localizeSuperEllipsisRangeError reason =
  case reason of
    SuperEllipsisRangeStartOutsideRank start rankLimit ->
      LocalizedMessage
        ( "începutul intervalului " <> romanianOrdinal start
            <> " nu este sub limita de rang " <> romanianOrdinal rankLimit
        )
        []
    SuperEllipsisRangeTargetOutsideRank target rankLimit ->
      LocalizedMessage
        ( "ținta intervalului " <> romanianOrdinal target
            <> " este peste limita de rang " <> romanianOrdinal rankLimit
        )
        []
    SuperEllipsisRangeInvalidDescendingBounds start target ->
      LocalizedMessage
        ( "intervalul descrescător de la " <> romanianOrdinal start
            <> " la " <> romanianOrdinal target
            <> " traversează o limită ordinală"
        )
        []

localizeSuperEllipsisRangeConcatError
  :: SuperEllipsisRangeConcatError
  -> LocalizedMessage
localizeSuperEllipsisRangeConcatError
    (SuperEllipsisRangesOverlap first second lower upper) =
  LocalizedMessage
    "intervalele suprapuse nu pot fi folosite pentru a accesa o hartă"
    [ "primul interval: " <> renderRangeDescription first
    , "al doilea interval: " <> renderRangeDescription second
    , "suprapunere: " <> renderRangeBounds lower upper
        <> " (limita superioară este exclusă)"
    ]

romanianOrdinal :: Ordinal -> String
romanianOrdinal = renderOrdinal
