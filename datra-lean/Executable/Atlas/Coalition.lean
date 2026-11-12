import Executable.Atlas.Transversal

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

/-- The Haskell carrier stores the same three fields as a covered page
element. Coalition values additionally belong to the canonical origin cell;
padded occurrences are permitted by the representation. -/
abbrev CoalitionElement (X : Atlas) := X.CoveredPageElement

def coalitionElement {X : Atlas} (source : X.Element) (datum : X.cellData source.val.cell)
    (witness : X.CoverageWitness) : X.CoalitionElement := ⟨source, datum, witness⟩

def withCoalitionElement {X : Atlas} {Result : Sort*} (c : X.CoalitionElement)
    (useElement : (source : X.Element) → X.cellData source.val.cell → Result) : Result :=
  useElement c.source c.datum

-- ALIGN: COALITION-CONSTRUCTOR-ELIM.
theorem coalitionElement_eliminate {X : Atlas} {Result : Sort*} (source : X.Element)
    (datum : X.cellData source.val.cell) (witness : X.CoverageWitness)
    (useElement : (source : X.Element) → X.cellData source.val.cell → Result) :
    withCoalitionElement (coalitionElement source datum witness) useElement = useElement source datum := rfl

def coalitionElementAt {X : Atlas} (c : X.CoalitionElement) (target : X.Element)
    (arrow : c.source ⟶ target) : X.cellData target.val.cell :=
  (X.data.action.normalizedMap arrow).map c.datum

-- ALIGN: COALITION-DATUM-TRANSPORT.
theorem coalitionElementAt_originImage {X : Atlas} (c : X.CoalitionElement) (target : X.Element)
    (arrow : c.source ⟶ target) :
    X.originImage target (coalitionElementAt c target arrow) = X.originImage c.source c.datum :=
  X.originImage_map arrow c.datum

-- ALIGN: COALITION-COVERAGE-TRANSPORT.
theorem coalitionElementAt_coverage {X : Atlas} (c : X.CoalitionElement) (target : X.Element)
    (arrow : c.source ⟶ target) (h : CoveredPageElement.Valid c) :
    X.coverageWitnessCovers target (coalitionElementAt c target arrow) c.witness = true := by
  change (c.witness.regionPage == X.coverageFinalPage &&
    X.originImageRank target (coalitionElementAt c target arrow) == c.witness.regionOriginRank) = true
  simpa only [Atlas.originImageRank, coalitionElementAt_originImage] using h.2

def CoalitionElement.Valid {X : Atlas} (c : X.CoalitionElement) : Prop :=
  CoveredPageElement.Valid c ∧ c.source.normalize = FolioData.ValidElement.originElement X.pages

abbrev CertifiedCoalitionElement (X : Atlas) :=
  {c : X.CoalitionElement // CoalitionElement.Valid c}

def CertifiedCoalitionElement.value {X : Atlas} (c : X.CertifiedCoalitionElement) : X.CoalitionValue :=
  ⟨X.originImage c.val.source c.val.datum,
    covered_originImage (CoveredPageElement.covered c.property.1)⟩

def CertifiedCoalitionElement.rank {X : Atlas} (c : X.CertifiedCoalitionElement) : Nat :=
  c.val.witness.regionOriginRank

-- ALIGN: COALITION-CACHED-RANK.
theorem CertifiedCoalitionElement.rank_spec {X : Atlas} (c : X.CertifiedCoalitionElement) :
    (X.dataAt (FolioData.ValidElement.originElement X.pages)).rank c.value.val = c.rank := by
  have h := c.property.1.2
  simp only [coverageWitnessCovers, Bool.and_eq_true, beq_iff_eq] at h
  exact h.2

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

def CoalitionValue.presentation {X : Atlas} (c : X.CoalitionValue) : X.CertifiedCoalitionElement :=
  ⟨c.coveredElement.val, c.coveredElement.property, by
    change (FolioData.ValidElement.originElement X.pages).normalize = _
    rw [FolioData.ValidElement.originElement_interpretation]
    exact FolioData.ValidElement.normalize_fromFinite _ _⟩

@[simp] theorem CoalitionValue.presentation_value {X : Atlas} (c : X.CoalitionValue) :
    c.presentation.value = c := by
  apply Subtype.ext
  exact originImage_origin X c.val

/-- Quotient by the public Eq observation. Different coverage witnesses do
not create different mathematical coalition values. -/
def coalitionSetoid (X : Atlas) : Setoid X.CertifiedCoalitionElement :=
  Setoid.ker CertifiedCoalitionElement.value

abbrev Coalition (X : Atlas) := Quotient (coalitionSetoid X)

def coalitionValueEquiv (X : Atlas) : X.Coalition ≃ X.CoalitionValue where
  toFun := Quotient.lift CertifiedCoalitionElement.value (fun _ _ h => h)
  invFun c := Quotient.mk _ c.presentation
  left_inv := by
    intro c
    induction c using Quotient.inductionOn with
    | _ c => exact Quotient.sound c.value.presentation_value
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

def coalitionRank {X : Atlas} (c : X.CoalitionValue) : Nat :=
  X.findAtlasCoverageRank (FolioData.ValidElement.originElement X.pages) c.val c.property

def coalitionUnrank (X : Atlas) (candidate : Nat) : Option X.CoalitionValue :=
  ((X.coveredPageElementAt (FolioData.ValidElement.originElement X.pages) candidate).attach).map
    (fun datum => ⟨datum.val, coveredPageElementAt_sound datum.property⟩)

-- ALIGN: COALITION-ROUNDTRIP.
theorem coalition_roundtrip {X : Atlas} (c : X.CoalitionValue) :
    coalitionUnrank X (coalitionRank c) = some c := by
  unfold coalitionUnrank coalitionRank
  have h := X.findAtlasCoverageRank_roundtrip (FolioData.ValidElement.originElement X.pages) c.val c.property
  rw [Option.attach_eq_some _ ⟨c.val, h⟩]
  rfl

/-- The executable ranking uses the first coverage candidate, rather than
the origin datum's rank used by the public equality observation. -/
def coalitionDominion (X : Atlas) : Dominion X.CoalitionValue where
  rank := coalitionRank
  unrank := coalitionUnrank X
  coherence := coalition_roundtrip

/-- The executable forward action: map the covered source and transport the
resulting datum to the target origin. No inverse is inferred from coverage. -/
def mapCoalitionValue {X Y : Atlas} (f : Transversal X Y) (c : X.CoalitionValue) : Y.CoalitionValue :=
  let image := f.mapCovered c.coveredElement
  ⟨Y.originImage image.val.source image.val.datum,
    covered_originImage (CoveredPageElement.covered image.property)⟩

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

-- ALIGN: COALITION-FORWARD-INTERPRETATION.
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

end Datra.Executable.Atlas
