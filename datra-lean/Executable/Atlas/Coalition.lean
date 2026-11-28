import Executable.Atlas.Charter

namespace Datra.Executable.Atlas
open CategoryTheory

theorem covered_originImage {X : Atlas} {source : X.Element}
    {datum : X.cellData source.val.cell} (h : X.Covered source datum) :
    X.Covered (FolioData.ValidElement.originElement X.pages) (X.originImage source datum) := by
  simpa only [Atlas.Covered, Atlas.originImageRank, originImage_origin] using h

/-- The canonical datum observed by a valid coalition element. Its cached
coverage witness is erased; equality is equality of the origin datum. -/
abbrev CoalitionValue (X : Atlas) :=
  {datum : X.cellData (FolioData.ValidElement.originElement X.pages).val.cell //
    X.Covered (FolioData.ValidElement.originElement X.pages) datum}

def CoalitionValue.coveredElement {X : Atlas} (c : X.CoalitionValue) : X.CertifiedCoveredElement :=
  ⟨⟨FolioData.ValidElement.originElement X.pages, c.val,
    X.findAtlasCoverage _ c.val c.property⟩, X.findAtlasCoverage_spec _ c.val c.property⟩

/-- The executable carrier stores the canonical charted datum and the cached
origin rank. A chosen coverage witness is not part of its identity. -/
structure CoalitionElement (X : Atlas) where
  source : X.Element
  charted : Charter.CachedCellData X source.val.cell
  originRank : Nat

def CoalitionElement.datum {X : Atlas} (c : X.CoalitionElement) : X.cellData c.source.val.cell :=
  c.charted.value

-- ALIGN: COALITION-CODE.
def coalitionElementCode {X : Atlas} (c : X.CoalitionElement) : Nat := c.charted.code

abbrev CoalitionView (X : Atlas) := (source : X.Element) × X.cellData source.val.cell

def viewCoalitionElement {X : Atlas} (c : X.CoalitionElement) : X.CoalitionView :=
  ⟨c.source, c.datum⟩

-- ALIGN: COALITION-VIEW-SOURCE.
theorem viewCoalitionElement_source {X : Atlas} (c : X.CoalitionElement) :
    (viewCoalitionElement c).1 = c.source := rfl

def coalitionElement {X : Atlas} (source : X.Element)
    (charted : Charter.CachedCellData X source.val.cell) (originRank : Nat) : X.CoalitionElement :=
  ⟨source, charted, originRank⟩

def withCoalitionElement {X : Atlas} {Result : Sort*} (c : X.CoalitionElement)
    (useElement : (source : X.Element) → X.cellData source.val.cell → Result) : Result :=
  let viewed := viewCoalitionElement c
  useElement viewed.1 viewed.2

-- ALIGN: COALITION-CONSTRUCTOR-ELIM.
theorem coalitionElement_eliminate {X : Atlas} {Result : Sort*} (source : X.Element)
    (charted : Charter.CachedCellData X source.val.cell) (originRank : Nat)
    (useElement : (source : X.Element) → X.cellData source.val.cell → Result) :
    withCoalitionElement (coalitionElement source charted originRank) useElement =
      useElement source charted.value := rfl

def coalitionElementAt {X : Atlas} (c : X.CoalitionElement) (target : X.Element)
    (arrow : c.source ⟶ target) : X.cellData target.val.cell :=
  (X.data.action.normalizedMap arrow).map c.datum

def coalitionElementReaches {X : Atlas} (c : X.CoalitionElement) (target : X.Element) : Bool :=
  decide (target.val.page ≤ c.source.val.page) &&
    Trace.traceSuffix c.source.val.trace target.val.trace

-- ALIGN: COALITION-TRANSPORT-ARROW.
theorem coalitionElementReaches_iff {X : Atlas} (c : X.CoalitionElement) (target : X.Element) :
    coalitionElementReaches c target = true ↔ Nonempty (c.source ⟶ target) := by
  simp only [coalitionElementReaches, Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨precedes, transported⟩
    exact ⟨⟨precedes, transported⟩⟩
  · rintro ⟨arrow⟩
    exact ⟨arrow.precedes, arrow.transported⟩

-- ALIGN: COALITION-DATUM-NATURALITY.
theorem coalitionElementAlongArrow {X : Atlas} (c : X.CoalitionElement)
    {source target : X.Element} (first : c.source ⟶ source) (second : source ⟶ target) :
    coalitionElementReaches c target = true ∧
      coalitionElementAt c target (first ≫ second) =
        (X.data.action.normalizedMap second).map (coalitionElementAt c source first) :=
  ⟨(coalitionElementReaches_iff c target).mpr ⟨first ≫ second⟩, X.data.composition first second c.datum⟩

-- ALIGN: COALITION-DATUM-NORMALIZATION.
theorem coalitionElementAtNormalized {X : Atlas} (c : X.CoalitionElement) (target : X.Element)
    (arrow : c.source ⟶ target) :
    coalitionElementReaches c target.normalize = true ∧
      coalitionElementAt c target.normalize (arrow ≫ target.toNormalized) =
        coalitionElementAt c target arrow := by
  obtain ⟨reaches, transported⟩ := coalitionElementAlongArrow c arrow target.toNormalized
  exact ⟨reaches, transported.trans (X.data.coherence target _)⟩

-- ALIGN: COALITION-DATUM-TRANSPORT.
theorem coalitionElementAt_originImage {X : Atlas} (c : X.CoalitionElement) (target : X.Element)
    (arrow : c.source ⟶ target) :
    X.originImage target (coalitionElementAt c target arrow) = X.originImage c.source c.datum :=
  X.originImage_map arrow c.datum

def CoalitionElement.Valid {X : Atlas} (c : X.CoalitionElement) : Prop :=
  c.charted.Valid c.source ∧ c.originRank = X.originImageRank c.source c.datum ∧
    c.source = FolioData.ValidElement.originElement X.pages

/-- Equality of complete owners transports the cached coalition domain and
its canonical origin, even when endpoint carrier types were hidden. -/
-- ALIGN: COALITION-OWNER-DOMAIN-AGREEMENT.
theorem CoalitionElement.owners_agree (first second : Atlas)
    (owners : atlasOwner first = atlasOwner second) (element : first.CoalitionElement) :
    let sameOwner : first = second := congrArg AtlasOwner.value owners
    (element.Valid ↔ CoalitionElement.Valid (sameOwner ▸ element)) ∧
      HEq (FolioData.ValidElement.originElement first.pages)
        (FolioData.ValidElement.originElement second.pages) := by
  dsimp only
  generalize_proofs sameOwner
  cases sameOwner
  exact ⟨Iff.rfl, HEq.rfl⟩

abbrev CertifiedCoalitionElement (X : Atlas) :=
  {c : X.CoalitionElement // CoalitionElement.Valid c}

/-- Package an insertion into a carrier with both membership and exact-source
certificates. The same constructor serves constant and chained Dominions. -/
-- ALIGN: COALITION-UNIT-INSERTION.
def coalitionUnitInsertion {Element Value Source : Type*}
    (accepts : Element → Bool) (source : Element → Source) (origin : Source)
    (forward : Value → {element : Element // accepts element = true ∧ source element = origin})
    (backward : {element : Element // accepts element = true ∧ source element = origin} → Option Value)
    (leftInverse : ∀ value, backward (forward value) = some value) :
    DomanialInsertion Value {element : Element // accepts element = true ∧ source element = origin} :=
  ⟨forward, backward, leftInverse⟩

-- ALIGN: COALITION-COUNIT-INSERTION.
def coalitionCounitInsertion {Element Value Source : Type*}
    (accepts : Element → Bool) (source : Element → Source) (origin : Source)
    (forward : {element : Element // accepts element = true ∧ source element = origin} → Value)
    (backward : Value → Option {element : Element // accepts element = true ∧ source element = origin})
    (leftInverse : ∀ element, backward (forward element) = some element) :
    DomanialInsertion {element : Element // accepts element = true ∧ source element = origin} Value :=
  ⟨forward, backward, leftInverse⟩

/-- The public constructor uses the shared canonical cache and retains the
exact owning origin and its image rank. -/
-- ALIGN: COALITION-CHECKED-CONSTRUCTOR.
def coalitionElement_checked {X : Atlas} (source : X.Element)
    (atOrigin : source = FolioData.ValidElement.originElement X.pages)
    (datum : X.cellData source.val.cell) (witness : X.CoverageWitness)
    (covers : X.coverageWitnessCovers source datum witness = true) : X.CertifiedCoalitionElement :=
  let charted := Charter.chartCellData source datum
    ⟨witness, coverageWitnessCovers_valid covers⟩ covers
  ⟨⟨source, charted.val, witness.regionOriginRank⟩,
    charted.property, coverageWitnessRankMatches X source datum witness covers, atOrigin⟩

-- ALIGN: COALITION-PUBLIC-CONSTRUCTOR-ELIM.
theorem coalitionElement_checked_eliminate {X : Atlas} {Result : Sort*} (source : X.Element)
    (atOrigin : source = FolioData.ValidElement.originElement X.pages)
    (datum : X.cellData source.val.cell) (witness : X.CoverageWitness)
    (covers : X.coverageWitnessCovers source datum witness = true)
    (useElement : (source : X.Element) → X.cellData source.val.cell → Result) :
    withCoalitionElement (coalitionElement_checked source atOrigin datum witness covers).val useElement =
      useElement source datum := rfl

-- ALIGN: COALITION-CONSTRUCTOR-VIEW.
theorem coalitionElement_checked_view {X : Atlas} (source : X.Element)
    (atOrigin : source = FolioData.ValidElement.originElement X.pages)
    (datum : X.cellData source.val.cell) (witness : X.CoverageWitness)
    (covers : X.coverageWitnessCovers source datum witness = true) :
    viewCoalitionElement (coalitionElement_checked source atOrigin datum witness covers).val =
      ⟨source, datum⟩ := rfl

-- ALIGN: COALITION-COVERED-CARRIER.
def CertifiedCoalitionElement.coveredElement {X : Atlas}
    (c : X.CertifiedCoalitionElement) : X.CertifiedCoveredElement :=
  let accepted := Charter.CachedCellData.accepted c.property.1
  let witness := Charter.chartedCellCoverage c.val.source c.val.charted accepted
  let covers := Charter.chartedCellCoverage_spec c.val.source c.val.charted accepted
  X.atlasCoveredByWitness c.val.source c.val.datum witness covers

-- ALIGN: COALITION-COVERAGE-TRANSPORT.
theorem coalitionElementAt_coverage {X : Atlas} (c : X.CertifiedCoalitionElement)
    (target : X.Element) (arrow : c.val.source ⟶ target) :
    X.coverageWitnessCovers target (coalitionElementAt c.val target arrow)
      c.coveredElement.val.witness = true := by
  simpa only [coverageWitnessCovers, Atlas.originImageRank, coalitionElementAt_originImage]
    using c.coveredElement.property.2

def CertifiedCoalitionElement.value {X : Atlas} (c : X.CertifiedCoalitionElement) : X.CoalitionValue :=
  ⟨X.originImage c.val.source c.val.datum,
    covered_originImage (Charter.CachedCellData.covered c.property.1)⟩

def CertifiedCoalitionElement.rank {X : Atlas} (c : X.CertifiedCoalitionElement) : Nat :=
  c.val.originRank

-- ALIGN: COALITION-DATUM-RANK.
theorem coalitionElementAt_rank {X : Atlas} (c : X.CertifiedCoalitionElement)
    (target : X.Element) (arrow : c.val.source ⟶ target) :
    X.originImageRank target (coalitionElementAt c.val target arrow) = c.rank := by
  unfold originImageRank
  rw [coalitionElementAt_originImage]
  exact c.property.2.1.symm

-- ALIGN: COALITION-CACHED-RANK.
theorem CertifiedCoalitionElement.rank_spec {X : Atlas} (c : X.CertifiedCoalitionElement) :
    (X.dataAt (FolioData.ValidElement.originElement X.pages)).rank c.value.val = c.rank :=
  c.property.2.1.symm

theorem CertifiedCoalitionElement.rank_eq_iff {X : Atlas} (a b : X.CertifiedCoalitionElement) :
    a.rank = b.rank ↔ a.value = b.value := by
  rw [← a.rank_spec, ← b.rank_spec]
  constructor
  · intro h
    exact Subtype.ext ((X.dataAt (FolioData.ValidElement.originElement X.pages)).rank_injective h)
  · intro h
    exact congrArg (fun c : X.CoalitionValue =>
      (X.dataAt (FolioData.ValidElement.originElement X.pages)).rank c.val) h

def CertifiedCoalitionElement.equal {X : Atlas} (a b : X.CertifiedCoalitionElement) : Bool :=
  a.rank == b.rank

-- ALIGN: COALITION-EQUALITY.
theorem CertifiedCoalitionElement.equal_iff {X : Atlas} (a b : X.CertifiedCoalitionElement) :
    a.equal b = true ↔ a.value = b.value := by
  simpa only [equal, beq_iff_eq] using a.rank_eq_iff b

/-- Canonical cache uniqueness turns value equality into actual carrier equality. -/
theorem CertifiedCoalitionElement.ext {X : Atlas} (left right : X.CertifiedCoalitionElement)
    (same : left.value = right.value) : left = right := by
  have sameImages : X.originImage left.val.source left.val.datum =
      X.originImage right.val.source right.val.datum := congrArg Subtype.val same
  apply Subtype.ext
  clear same
  rcases left with ⟨⟨leftSource, leftData, leftRank⟩, leftValid⟩
  rcases right with ⟨⟨rightSource, rightData, rightRank⟩, rightValid⟩
  dsimp only [CoalitionElement.datum] at sameImages ⊢
  change leftData.Valid leftSource ∧ leftRank = X.originImageRank leftSource leftData.value ∧
    leftSource = FolioData.ValidElement.originElement X.pages at leftValid
  change rightData.Valid rightSource ∧ rightRank = X.originImageRank rightSource rightData.value ∧
    rightSource = FolioData.ValidElement.originElement X.pages at rightValid
  rcases leftValid with ⟨leftCode, leftRankEq, rfl⟩
  rcases rightValid with ⟨rightCode, rightRankEq, rfl⟩
  have sameDatum : leftData.value = rightData.value := by
    simpa [CoalitionElement.datum, originImage_origin] using sameImages
  have sameData := Charter.CachedCellData.ext leftCode rightCode sameDatum
  subst rightData
  have sameRank : leftRank = rightRank := leftRankEq.trans rightRankEq.symm
  cases sameRank
  rfl

-- ALIGN: COALITION-VIEW-EXTENSIONALITY.
theorem CertifiedCoalitionElement.ext_view {X : Atlas}
    (left right : X.CertifiedCoalitionElement)
    (same : viewCoalitionElement left.val = viewCoalitionElement right.val) : left = right := by
  apply CertifiedCoalitionElement.ext
  apply Subtype.ext
  exact congrArg (fun viewed : CoalitionView X => X.originImage viewed.1 viewed.2) same

-- ALIGN: COALITION-RANK-EXTENSIONALITY.
theorem CertifiedCoalitionElement.ext_rank {X : Atlas}
    (left right : X.CertifiedCoalitionElement) (same : left.rank = right.rank) : left = right :=
  CertifiedCoalitionElement.ext left right ((left.rank_eq_iff right).mp same)

-- ALIGN: COALITION-CANONICAL-RECONSTRUCTION.
theorem coalitionElement_checked_reconstruct {X : Atlas} (element : X.CertifiedCoalitionElement)
    (witness : X.CoverageWitness)
    (covers : X.coverageWitnessCovers element.val.source element.val.datum witness = true) :
    coalitionElement_checked element.val.source element.property.2.2 element.val.datum witness covers =
      element :=
  CertifiedCoalitionElement.ext _ _ rfl

-- ALIGN: COALITION-WITNESS-INDEPENDENT.
theorem coalitionElement_checked_witnessIndependent {X : Atlas} (source : X.Element)
    (atOrigin : source = FolioData.ValidElement.originElement X.pages)
    (datum : X.cellData source.val.cell) (first second : X.CoverageWitness)
    (firstCovers : X.coverageWitnessCovers source datum first = true)
    (secondCovers : X.coverageWitnessCovers source datum second = true) :
    coalitionElement_checked source atOrigin datum first firstCovers =
      coalitionElement_checked source atOrigin datum second secondCovers :=
  CertifiedCoalitionElement.ext _ _ rfl

-- ALIGN: COALITION-CERTIFIED-ELIM.
def withCoalitionElementOf (X : Atlas) {Result : Sort*} (element : X.CertifiedCoalitionElement)
    (useElement : (source : X.Element) → (datum : X.cellData source.val.cell) →
      (witness : X.CoverageWitness) → (covers : X.coverageWitnessCovers source datum witness = true) →
      (atOrigin : source = FolioData.ValidElement.originElement X.pages) →
      witness.regionOriginRank = element.rank →
      coalitionElement_checked source atOrigin datum witness covers = element → Result) : Result :=
  let covered := element.coveredElement
  useElement element.val.source element.val.datum covered.val.witness covered.property.2
    element.property.2.2
    ((coverageWitnessRankMatches X _ _ _ covered.property.2).trans element.property.2.1.symm)
    (coalitionElement_checked_reconstruct element covered.val.witness covered.property.2)

def CoalitionValue.presentation {X : Atlas} (c : X.CoalitionValue) : X.CertifiedCoalitionElement :=
  let witness := X.findAtlasCoverage _ c.val c.property
  coalitionElement_checked _ rfl c.val witness (X.findAtlasCoverage_spec _ c.val c.property).2

@[simp] theorem CoalitionValue.presentation_value {X : Atlas} (c : X.CoalitionValue) :
    c.presentation.value = c := by
  apply Subtype.ext
  exact originImage_origin X c.val

abbrev Coalition (X : Atlas) := X.CertifiedCoalitionElement

def coalitionValueEquiv (X : Atlas) : X.Coalition ≃ X.CoalitionValue where
  toFun := CertifiedCoalitionElement.value
  invFun := CoalitionValue.presentation
  left_inv c := CertifiedCoalitionElement.ext _ _ c.value.presentation_value
  right_inv := CoalitionValue.presentation_value

noncomputable def originDatumEquiv (X : Atlas) :
    X.cellData (FolioData.ValidElement.originElement X.pages).val.cell ≃
      X.toSemantics.Da.obj X.toSemantics.Fo.originElement := by
  change _ ≃ X.cellData ((FolioData.ValidElement.fromFinite X.pages).obj
    X.toSemantics.Fo.originElement).val.cell
  exact Equiv.cast (congrArg (fun c : X.Element => X.cellData c.val.cell)
    (FolioData.ValidElement.originElement_interpretation X.pages))

theorem originDatumEquiv_covered (X : Atlas)
    (datum : X.cellData (FolioData.ValidElement.originElement X.pages).val.cell) :
    X.Covered (FolioData.ValidElement.originElement X.pages) datum ↔
      Datra.Semantics.Covered X.toSemantics X.toSemantics.Fo.originElement (originDatumEquiv X datum) := by
  have transport {a b : X.Element} (h : a = b) (value : X.cellData a.val.cell) :
      X.Covered a value ↔
        X.Covered b (cast (congrArg (fun c : X.Element => X.cellData c.val.cell) h) value) := by
    cases h
    rfl
  exact (transport (FolioData.ValidElement.originElement_interpretation X.pages) datum).trans
    (X.covered_interpretation _ _)

noncomputable def CoalitionValue.semanticsEquiv (X : Atlas) :
    X.CoalitionValue ≃ Datra.Semantics.coveredDom X.toSemantics X.toSemantics.Fo.originElement :=
  (originDatumEquiv X).subtypeEquiv (originDatumEquiv_covered X)

-- ALIGN: COALITION-CARRIER-EQUIVALENCE.
noncomputable def coalitionSemanticsEquiv (X : Atlas) :
    X.Coalition ≃ Datra.Semantics.coveredDom X.toSemantics X.toSemantics.Fo.originElement :=
  (coalitionValueEquiv X).trans (CoalitionValue.semanticsEquiv X)

/-- Canonical charted data determine every field of the coalition carrier. -/
-- ALIGN: COALITION-FROM-CHARTED.
def coalitionFromCharted {X : Atlas} (source : X.Element)
    (atOrigin : source = FolioData.ValidElement.originElement X.pages)
    (datum : Charter.CertifiedCachedCellData X source) : X.CertifiedCoalitionElement :=
  ⟨⟨source, datum.val, X.originImageRank source datum.val.value⟩,
    datum.property, rfl, atOrigin⟩

/-- The finite decoder shares Charter's canonicalization and retains its origin. -/
-- ALIGN: COALITION-DECODE.
def coalitionUnrank (X : Atlas) (candidate : Nat) : Option X.CertifiedCoalitionElement :=
  (Charter.cachedUnrank X (FolioData.ValidElement.originElement X.pages) candidate).map
    (coalitionFromCharted (FolioData.ValidElement.originElement X.pages) rfl)

-- ALIGN: COALITION-ROUNDTRIP.
theorem coalition_roundtrip {X : Atlas} (c : X.CertifiedCoalitionElement) :
    coalitionUnrank X (coalitionElementCode c.val) = some c := by
  rcases c with ⟨⟨source, datum, cachedRank⟩, valid⟩
  change datum.Valid source ∧ cachedRank = X.originImageRank source datum.value ∧
    source = FolioData.ValidElement.originElement X.pages at valid
  rcases valid with ⟨validDatum, rankEq, rfl⟩
  have decoded := (Charter.cachedDominion X (FolioData.ValidElement.originElement X.pages)).coherence
    ⟨datum, validDatum⟩
  change Charter.cachedUnrank X (FolioData.ValidElement.originElement X.pages) datum.code =
    some ⟨datum, validDatum⟩ at decoded
  dsimp only [coalitionUnrank, coalitionElementCode]
  rw [decoded, Option.map_some]
  apply congrArg some
  apply Subtype.ext
  simp only [coalitionFromCharted, rankEq]

/-- Ranking reads the retained code; decoding recovers the exact canonical record. -/
-- ALIGN: COALITION-DOMINION.
def coalitionDominion (X : Atlas) : Dominion X.Coalition where
  rank c := coalitionElementCode c.val
  unrank := coalitionUnrank X
  coherence := coalition_roundtrip

/-- Canonical codes determine the complete cached coalition record. -/
-- ALIGN: COALITION-CODE-EXTENSIONALITY.
theorem coalitionCodeExtensionality {X : Atlas} (left right : X.Coalition)
    (codes : coalitionElementCode left.val = coalitionElementCode right.val) : left = right :=
  (coalitionDominion X).rank_injective codes

def coalitionMaybeCode {X : Atlas} (value : Option X.Coalition) : Option Nat :=
  value.map (fun source => coalitionElementCode source.val)

/-- Optional code observations distinguish failure and recover every successful
canonical result, including values outside an insertion's forward image. -/
theorem coalitionMaybeCode_injective (X : Atlas) :
    Function.Injective (@coalitionMaybeCode X) := by
  intro left right codes
  cases left with
  | none => cases right <;> simp_all [coalitionMaybeCode]
  | some left =>
    cases right with
    | none => simp [coalitionMaybeCode] at codes
    | some right =>
      have same : coalitionElementCode left.val = coalitionElementCode right.val :=
        Option.some.inj codes
      exact congrArg some (coalitionCodeExtensionality left right same)

-- ALIGN: COALITION-CODE-INTERPRETATION.
theorem coalitionElementCode_interpretation {X : Atlas} (c : X.CertifiedCoalitionElement) :
    coalitionElementCode c.val =
      X.findAtlasCoverageRank (FolioData.ValidElement.originElement X.pages) c.value.val c.value.property := by
  rcases c with ⟨⟨source, datum, cachedRank⟩, valid⟩
  change datum.Valid source ∧ cachedRank = X.originImageRank source datum.value ∧
    source = FolioData.ValidElement.originElement X.pages at valid
  rcases valid with ⟨validDatum, _, rfl⟩
  simpa only [coalitionElementCode, CertifiedCoalitionElement.value, CoalitionElement.datum,
    originImage_origin] using Charter.CachedCellData.rank_spec validDatum

-- ALIGN: COALITION-DECODE-VALUE.
theorem coalitionUnrank_value (X : Atlas) (candidate : Nat) :
    (coalitionUnrank X candidate).map (fun c => c.value.val) =
      X.coveredPageElementAt (FolioData.ValidElement.originElement X.pages) candidate := by
  unfold coalitionUnrank Charter.cachedUnrank
  split
  · rename_i found
    change none = X.coveredPageElementAt (FolioData.ValidElement.originElement X.pages) candidate
    exact (congrArg (Option.map Prod.fst) found).symm
  · rename_i datum witness found
    have decoded : X.coveredPageElementAt (FolioData.ValidElement.originElement X.pages) candidate =
        some datum := congrArg (Option.map Prod.fst) found
    rw [decoded]
    change some (X.originImage (FolioData.ValidElement.originElement X.pages) datum) = some datum
    rw [originImage_origin]

/-- The executable forward action: map the covered source and transport the
resulting datum to the target origin. No inverse is inferred from coverage. -/
def mapCoalitionValue {X Y : Atlas} (f : Transversal X Y) (c : X.CoalitionValue) : Y.CoalitionValue :=
  let image := f.mapCovered c.coveredElement
  ⟨Y.originImage image.val.source image.val.datum,
    covered_originImage (CoveredPageElement.covered image.property)⟩

/-- Transport covered data to the owning origin using the same valid witness,
then recover the unique canonical cache. -/
-- ALIGN: COALITION-FROM-COVERED.
def coalitionFromCovered {X : Atlas} (covered : X.CertifiedCoveredElement) : X.Coalition :=
  coalitionElement_checked (FolioData.ValidElement.originElement X.pages) rfl
    (X.originImage covered.val.source covered.val.datum) covered.val.witness (by
      simpa only [coverageWitnessCovers, originImageRank, originImage_origin]
        using covered.property.2)

theorem coalitionFromCovered_rank {X : Atlas} (covered : X.CertifiedCoveredElement) :
    (coalitionFromCovered covered).rank = covered.val.witness.regionOriginRank := rfl

-- ALIGN: COALITION-FROM-COVERED-ROUNDTRIP.
theorem coalitionFromCovered_roundtrip {X : Atlas} (c : X.Coalition) :
    coalitionFromCovered c.coveredElement = c := by
  apply CertifiedCoalitionElement.ext
  apply Subtype.ext
  exact originImage_origin X (X.originImage c.val.source c.val.datum)

/-- A canonical coalition action stores its owners in the indices and keeps
one certified function for both raw mapping and owned observation. -/
structure CoalitionAction (X Y : Atlas) where
  map : X.CertifiedCoalitionElement → Y.CertifiedCoalitionElement

def coalitionAction {X Y : Atlas} (f : Transversal X Y) : CoalitionAction X Y :=
  withAtlasTransversalCoveredAction f
    (fun forward => ⟨fun source => coalitionFromCovered (forward source.coveredElement)⟩)

/-- Erase the target-owner observation while retaining the same function. -/
-- ALIGN: COALITION-FORWARD-CARRIER.
def mapCoalitionElement {X Y : Atlas} (f : Transversal X Y)
    (c : X.CertifiedCoalitionElement) : Y.CertifiedCoalitionElement :=
  (coalitionAction f).map c

/-- The complete canonical mapping operation retains the same target owner
for all accepted source records. -/
-- ALIGN: COALITION-FORWARD-OWNED-ACTION.
def withMappedCoalitionAction {X Y : Atlas} {Result : Sort*} (f : Transversal X Y)
    (useAction : (X.CertifiedCoalitionElement → Y.CertifiedCoalitionElement) → Result) : Result :=
  useAction (coalitionAction f).map

/-- Retain the image's owner and the raw mapper's exact result. -/
-- ALIGN: COALITION-FORWARD-OWNED-ELIMINATION.
def withMappedCoalitionElement {X Y : Atlas} {Result : Sort*} (f : Transversal X Y)
    (c : X.CertifiedCoalitionElement) (useElement : Y.CertifiedCoalitionElement → Result) : Result :=
  withMappedCoalitionAction f (fun forward => useElement (forward c))

-- ALIGN: COALITION-FORWARD-ACTION-RETENTION.
theorem withMappedCoalitionAction_agrees {X Y : Atlas} {Result : Sort*} (f : Transversal X Y)
    (useAction : (X.CertifiedCoalitionElement → Y.CertifiedCoalitionElement) → Result) :
    withMappedCoalitionAction f useAction = useAction (mapCoalitionElement f) := rfl

-- ALIGN: COALITION-FORWARD-IMAGE-RETENTION.
theorem withMappedCoalitionElement_agrees {X Y : Atlas} {Result : Sort*} (f : Transversal X Y)
    (c : X.CertifiedCoalitionElement) (useElement : Y.CertifiedCoalitionElement → Result) :
    withMappedCoalitionElement f c useElement = useElement (mapCoalitionElement f c) := rfl

theorem CertifiedCoalitionElement.coveredElement_data {X : Atlas}
    (c : X.CertifiedCoalitionElement) : c.coveredElement.data = c.value.coveredElement.data := by
  rcases c with ⟨⟨source, datum, originRank⟩, valid⟩
  change datum.Valid source ∧ originRank = X.originImageRank source datum.value ∧
    source = FolioData.ValidElement.originElement X.pages at valid
  rcases valid with ⟨_, _, rfl⟩
  change (⟨_, datum.value⟩ : X.DataElement) = ⟨_, X.originImage _ datum.value⟩
  rw [originImage_origin]

theorem mapCoalitionElement_value {X Y : Atlas} (f : Transversal X Y)
    (c : X.CertifiedCoalitionElement) :
    (mapCoalitionElement f c).value = mapCoalitionValue f c.value := by
  apply Subtype.ext
  change Y.originImage (FolioData.ValidElement.originElement Y.pages)
    (Y.originImage (f.mapCovered c.coveredElement).val.source
      (f.mapCovered c.coveredElement).val.datum) = _
  rw [originImage_origin]
  exact congrArg (fun image : Y.DataElement => Y.originImage image.1 image.2)
    (f.mapCovered_data_congr c.coveredElement c.value.coveredElement c.coveredElement_data)

/-- Rebuilding the mapped value recovers every field of the executable result. -/
theorem mapCoalitionElement_presentation {X Y : Atlas} (f : Transversal X Y)
    (c : X.CertifiedCoalitionElement) :
    mapCoalitionElement f c = (mapCoalitionValue f c.value).presentation := by
  apply CertifiedCoalitionElement.ext
  rw [mapCoalitionElement_value, CoalitionValue.presentation_value]

theorem mapCoalitionElement_identity {X : Atlas} (c : X.CertifiedCoalitionElement) :
    mapCoalitionElement .identity c = c := by
  apply CertifiedCoalitionElement.ext
  rw [mapCoalitionElement_value]
  apply Subtype.ext
  exact originImage_origin X c.value.val

theorem fromSemanticOriginData (X : Atlas)
    (datum : X.cellData (FolioData.ValidElement.originElement X.pages).val.cell) :
    fromSemanticData X ⟨X.toSemantics.Fo.originElement, originDatumEquiv X datum⟩ =
      ⟨FolioData.ValidElement.originElement X.pages, datum⟩ := by
  apply Sigma.ext
  · exact (FolioData.ValidElement.originElement_interpretation X.pages).symm
  · exact cast_heq _ _

theorem originDatumEquiv_originImage (X : Atlas) (source : X.SemanticDataElement) :
    originDatumEquiv X (X.originImage (fromSemanticData X source).1 (fromSemanticData X source).2) =
      Datra.Semantics.originImage X.toSemantics source.1 source.2 := by
  apply eq_of_heq
  exact (cast_heq _ _).trans (X.originImage_interpretation source.1 source.2)

theorem mapCoalitionValue_interpretation {X Y : Atlas} (f : Transversal X Y) (c : X.CoalitionValue) :
    (CoalitionValue.semanticsEquiv Y (mapCoalitionValue f c)).val =
      Datra.Semantics.extentMap f.toSemantics.val (CoalitionValue.semanticsEquiv X c).val := by
  let source : X.SemanticDataElement :=
    ⟨X.toSemantics.Fo.originElement, originDatumEquiv X c.val⟩
  have hs : c.coveredElement.data = fromSemanticData X source := (fromSemanticOriginData X c.val).symm
  have image := f.mapCovered_interpretation c.coveredElement source hs
  change originDatumEquiv Y (Y.originImage (f.mapCovered c.coveredElement).val.source
    (f.mapCovered c.coveredElement).val.datum) = _
  change originDatumEquiv Y (Y.originImage ((f.mapCovered c.coveredElement).data).1
    ((f.mapCovered c.coveredElement).data).2) = _
  rw [image, originDatumEquiv_originImage]
  rfl

-- ALIGN: COALITION-FORWARD-INTERPRETATION.
theorem mapCoalitionElement_interpretation {X Y : Atlas} (f : Transversal X Y)
    (c : X.CertifiedCoalitionElement) :
    (coalitionSemanticsEquiv Y (mapCoalitionElement f c)).val =
      Datra.Semantics.extentMap f.toSemantics.val (coalitionSemanticsEquiv X c).val := by
  change (CoalitionValue.semanticsEquiv Y (mapCoalitionElement f c).value).val = _
  rw [mapCoalitionElement_value]
  exact mapCoalitionValue_interpretation f c.value

end Datra.Executable.Atlas
