-- | Romanian presentation text for typed Datra diagnostics.
module DatraLanguage.Diagnostics.Locales.Română
  ( localizeAccessError
  , localizeInterpretingError
  , localizeSuperEllipsisRangeError
  , localizeSuperEllipsisRangeConcatError
  , romanianOrdinal
  ) where

import DatraLanguage.Diagnostics (LocalizedMessage (LocalizedMessage))
import DatraLanguage.Diagnostics.Interpreter
  ( InterpretedValueKind (..)
  , InterpretingError (..)
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
    ExpectedNumericalOperand side actual ->
      LocalizedMessage
        ("operandul " <> operandSide side <> " trebuie să fie numeric")
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
    RangeConstructionRejected rejection ->
      localizeSuperEllipsisRangeError rejection
    RangeConcatenationRejected rejection ->
      localizeSuperEllipsisRangeConcatError rejection
    AccessRejected rejection -> localizeAccessError rejection
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
    AtlasMapFederationOperationUndecidable
        (NoAtlasMapFederationDecisionProcedure operation) ->
      LocalizedMessage
        "compilatorul nu poate decide această operație pe federații"
        ["operația: " <> federationOperation operation]
    InvalidAsciiStringCharacter character ->
      LocalizedMessage
        "șirul conține un caracter din afara hărții ASCII"
        ["caracter: " <> show character]

federationOperation :: AtlasMapFederationOperation -> String
federationOperation AtlasMapFederationConcatenation = "concatenare"
federationOperation AtlasMapFederationAccess = "accesare"

operandSide :: OperandSide -> String
operandSide LeftOperand = "stâng"
operandSide RightOperand = "drept"

valueKind :: InterpretedValueKind -> String
valueKind NaturalValueKind = "număr natural"
valueKind ExplicitOrdinalValueKind = "ordinal explicit"
valueKind FormulationValueKind = "formulare cu super-elipsă"
valueKind RangeValueKind = "interval"
valueKind RangeConcatenationValueKind = "concatenare de intervale"
valueKind AsciiStringValueKind = "șir ASCII"
valueKind MapValueKind = "hartă"

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
