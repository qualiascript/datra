-- | Romanian presentation text for typed Datra diagnostics.
module DatraLanguage.Diagnostics.Locales.Romanian
  ( localizeAccessError
  , localizeInterpretingError
  , localizeSuperEllipsisRangeError
  , localizeSuperEllipsisRangeConcatError
  , romanianOrdinal
  ) where

import DatraLanguage.Diagnostics (LocalizedMessage (LocalizedMessage))
import Evaluation.Error
  ( InterpretedValueKind (..)
  , InterpretingError (..)
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
    NamedAccessError message -> LocalizedMessage "accesul prin nume a eșuat" [message]
    FunctionError message -> LocalizedMessage "evaluarea funcției a eșuat" [message]
    OverloadError failure ->
      LocalizedMessage "supraîncărcarea a eșuat" [overloadFailure failure]
    AssertionFailed -> LocalizedMessage "aserțiunea a eșuat" []
    IdentifierStringOverlap name ->
      LocalizedMessage "șirurile identificatorilor se suprapun în domeniul begin" ["identificator: " <> name]
    UnknownIdentifier name ->
      LocalizedMessage "identificatorul nu este importat în acest domeniu" ["identificator: " <> name]
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
