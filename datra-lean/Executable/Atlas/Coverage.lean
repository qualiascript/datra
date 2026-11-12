import Executable.Atlas.Derived
import Executable.Atlas.Elements

namespace Datra.Executable.Atlas
open CategoryTheory

def coverageFinalPage (X : Atlas) : Nat := X.pages.depth - 1

/-- The stored representation includes the cached page and origin rank.
Neither cache is itself evidence that the retained region datum is valid. -/
structure CoverageWitness (X : Atlas) where
  region : X.Element
  datum : X.cellData region.val.cell
  regionPage : Nat
  regionOriginRank : Nat

def coverageWitnessCovers (X : Atlas) (source : X.Element)
    (datum : X.cellData source.val.cell) (witness : X.CoverageWitness) : Bool :=
  witness.regionPage == X.coverageFinalPage &&
    X.originImageRank source datum == witness.regionOriginRank

abbrev CoverageRegion (X : Atlas) :=
  (index : X.TerritoryIndex) × X.cellData (X.territory index).element.val.cell

def CoverageRegion.witness {X : Atlas} (region : X.CoverageRegion) : X.CoverageWitness :=
  ⟨(X.territory region.1).element, region.2, X.coverageFinalPage,
    X.originImageRank (X.territory region.1).element region.2⟩

/-- Cache consistency also retains a genuine final-region representative. -/
def CoverageWitness.Valid {X : Atlas} (witness : X.CoverageWitness) : Prop :=
  ∃ region : X.CoverageRegion, witness = region.witness

-- ALIGN: ATLAS-COVERAGE-WITNESS-SOUND.
theorem coverageWitnessCovers_sound {X : Atlas} {source : X.Element}
    {datum : X.cellData source.val.cell} {witness : X.CoverageWitness}
    (valid : witness.Valid) (covers : X.coverageWitnessCovers source datum witness = true) :
    X.Covered source datum := by
  obtain ⟨⟨index, regionDatum⟩, rfl⟩ := valid
  exact ⟨index, regionDatum, by simpa [coverageWitnessCovers, CoverageRegion.witness] using covers⟩

/-- The checked public constructor stores the normalized region and caches
computed from that region, exactly as atlasCoverageWitness does. -/
def atlasCoverageWitness (X : Atlas) (source region : X.Element)
    (sourceDatum : X.cellData source.val.cell) (regionDatum : X.cellData region.val.cell)
    (_conditions : region.normalize.val.page = X.coverageFinalPage ∧
      X.originImageRank source.normalize sourceDatum =
        X.originImageRank region.normalize regionDatum) : X.CoverageWitness :=
  ⟨region.normalize, regionDatum, region.normalize.val.page,
    X.originImageRank region.normalize regionDatum⟩

-- ALIGN: ATLAS-COVERAGE-CONSTRUCTOR.
theorem atlasCoverageWitness_spec (X : Atlas) (source region : X.Element)
    (sourceDatum : X.cellData source.val.cell) (regionDatum : X.cellData region.val.cell)
    (conditions : region.normalize.val.page = X.coverageFinalPage ∧
      X.originImageRank source.normalize sourceDatum =
        X.originImageRank region.normalize regionDatum) :
    (X.atlasCoverageWitness source region sourceDatum regionDatum conditions).Valid ∧
      X.coverageWitnessCovers source.normalize sourceDatum
        (X.atlasCoverageWitness source region sourceDatum regionDatum conditions) = true := by
  constructor
  · obtain ⟨index, hi⟩ := FolioData.ValidElement.lastElement_surjective
      X.pages region.normalize conditions.1
    have construct (r : X.Element) (datum : X.cellData r.val.cell)
        (h : (X.territory index).element = r) :
        (⟨r, datum, r.val.page, X.originImageRank r datum⟩ : X.CoverageWitness).Valid := by
      subst r
      exact ⟨⟨index, datum⟩, rfl⟩
    exact construct region.normalize regionDatum hi
  · simp [coverageWitnessCovers, atlasCoverageWitness, conditions.1, conditions.2]

structure CoveredPageElement (X : Atlas) where
  source : X.Element
  datum : X.cellData source.val.cell
  witness : X.CoverageWitness

def CoveredPageElement.Valid {X : Atlas} (covered : X.CoveredPageElement) : Prop :=
  covered.witness.Valid ∧ X.coverageWitnessCovers covered.source covered.datum covered.witness = true

def atlasCoveredPageElement (X : Atlas) (source region : X.Element)
    (sourceDatum : X.cellData source.val.cell) (regionDatum : X.cellData region.val.cell)
    (conditions : region.normalize.val.page = X.coverageFinalPage ∧
      X.originImageRank source.normalize sourceDatum =
        X.originImageRank region.normalize regionDatum) : X.CoveredPageElement :=
  ⟨source.normalize, sourceDatum,
    X.atlasCoverageWitness source region sourceDatum regionDatum conditions⟩

-- ALIGN: ATLAS-COVERED-CONSTRUCTOR.
theorem atlasCoveredPageElement_spec (X : Atlas) (source region : X.Element)
    (sourceDatum : X.cellData source.val.cell) (regionDatum : X.cellData region.val.cell)
    (conditions : region.normalize.val.page = X.coverageFinalPage ∧
      X.originImageRank source.normalize sourceDatum =
        X.originImageRank region.normalize regionDatum) :
    (X.atlasCoveredPageElement source region sourceDatum regionDatum conditions).Valid :=
  X.atlasCoverageWitness_spec source region sourceDatum regionDatum conditions

def withAtlasCoveredPageElement {X : Atlas} {Result : Sort*} (covered : X.CoveredPageElement)
    (useCovered : (source : X.Element) → X.cellData source.val.cell → Result) : Result :=
  useCovered covered.source covered.datum

theorem CoveredPageElement.covered {X : Atlas} {element : X.CoveredPageElement}
    (valid : element.Valid) : X.Covered element.source element.datum :=
  coverageWitnessCovers_sound valid.1 valid.2

theorem TransposalElement.coverage_interpretation {X : Atlas} (x : X.TransposalElement)
    (datum : X.cellData x.val.val.cell) :
    Datra.Semantics.Covered X.toSemantics x.toSemantics (x.dataToSemantics datum) ↔
      X.Covered x.val datum := by
  rw [← X.covered_interpretation]
  have transport {a b : X.Element} (h : a = b) (value : X.cellData b.val.cell) :
      X.Covered a (cast (congrArg (fun y : X.Element => X.cellData y.val.cell) h.symm) value) ↔
        X.Covered b value := by
    cases h
    rfl
  exact transport x.fromFinite_toSemantics datum

-- ALIGN: ATLAS-COVERED-SEMANTICS.
noncomputable def CoveredPageElement.toSemantics {X : Atlas}
    (element : X.CoveredPageElement) (valid : element.Valid) :
    Datra.Semantics.CoveredPageElement X.toSemantics where
  pageElement := (X.transposalElement element.source).toSemantics
  datum := (X.transposalElement element.source).dataToSemantics element.datum
  covered := ((X.transposalElement element.source).coverage_interpretation element.datum).mpr
    ((X.covered_normalize_iff element.source element.datum).mpr (CoveredPageElement.covered valid))

/-- The same paired enumeration and checked chain lookup as atlasCoverageAt
and coverageCandidate. No assumption is made about unranking unused ranks. -/
def decodeCoverageRegion (X : Atlas) (candidate : Nat) : Option X.CoverageRegion := do
  let (positionCode, datumRank) := Ordinal.unpairNatural candidate
  let index ← X.pagination.final.chain.chainIndex
    (Ordinal.ordinal (CoverageEnumeration.decodeNaturalList positionCode))
  let datum ← (X.territory index).dominion.unrank datumRank
  return ⟨index, datum⟩

def CoverageRegion.code {X : Atlas} (region : X.CoverageRegion) : Nat :=
  Ordinal.pairNatural
    (CoverageEnumeration.encodeNaturalList region.1.position.coefficients)
    ((X.territory region.1).dominion.rank region.2)

theorem decodeCoverageRegion_code (X : Atlas) (region : X.CoverageRegion) :
    X.decodeCoverageRegion region.code = some region := by
  obtain ⟨index, datum⟩ := region
  have hi : X.pagination.final.chain.chainIndex index.position = some index := by
    rw [← index.position_eq, Chain.chainIndex_position]
    exact congrArg some (X.pagination.final.chain.indexEquiv.left_inv index)
  simp [decodeCoverageRegion, CoverageRegion.code, Ordinal.unpairNatural_pair,
    CoverageEnumeration.ordinal_decode_encode, hi, Dominion.coherence]

def coverageCandidate (X : Atlas) (source : X.Element)
    (datum : X.cellData source.val.cell) (candidate : Nat) : Option X.CoverageWitness :=
  match X.decodeCoverageRegion candidate with
  | none => none
  | some region =>
    if X.originImageRank source datum =
        X.originImageRank (X.territory region.1).element region.2 then
      some region.witness
    else none

-- ALIGN: ATLAS-COVERAGE-CANDIDATE-SOUND.
theorem coverageCandidate_sound {X : Atlas} {source : X.Element}
    {datum : X.cellData source.val.cell} {candidate : Nat} {witness : X.CoverageWitness}
    (h : X.coverageCandidate source datum candidate = some witness) :
    witness.Valid ∧ X.coverageWitnessCovers source datum witness = true := by
  unfold coverageCandidate at h
  cases hd : X.decodeCoverageRegion candidate with
  | none => simp [hd] at h
  | some region =>
      simp only [hd] at h
      split at h
      · rename_i he
        cases Option.some.inj h
        exact ⟨⟨region, rfl⟩, by simp [coverageWitnessCovers, CoverageRegion.witness, he]⟩
      · simp at h

-- ALIGN: ATLAS-COVERAGE-CANDIDATE-COMPLETE.
theorem coverageCandidate_complete {X : Atlas} {source : X.Element}
    {datum : X.cellData source.val.cell} (covered : X.Covered source datum) :
    ∃ candidate witness, X.coverageCandidate source datum candidate = some witness := by
  obtain ⟨index, value, he⟩ := covered
  let region : X.CoverageRegion := ⟨index, value⟩
  exact ⟨region.code, region.witness, by
    simp [coverageCandidate, decodeCoverageRegion_code, region, he]⟩

/-- A left inverse can return arbitrary values outside its image. The final
rank comparison checks that a proposed pullback really has the required image. -/
def coverageAt (X : Atlas) (source : X.Element) (candidate : Nat) :
    Option (X.cellData source.val.cell × X.CoverageWitness) :=
  match X.decodeCoverageRegion candidate with
  | none => none
  | some region =>
    match (X.data.action.normalizedMap source.toOrigin).preimage
        (X.originImage (X.territory region.1).element region.2) with
    | none => none
    | some datum =>
      if X.originImageRank source datum =
          X.originImageRank (X.territory region.1).element region.2 then
        some (datum, region.witness)
      else none

-- ALIGN: ATLAS-COVERAGE-DECODE-SOUND.
theorem coverageAt_sound {X : Atlas} {source : X.Element} {candidate : Nat}
    {datum : X.cellData source.val.cell} {witness : X.CoverageWitness}
    (h : X.coverageAt source candidate = some (datum, witness)) :
    witness.Valid ∧ X.coverageWitnessCovers source datum witness = true := by
  unfold coverageAt at h
  cases hd : X.decodeCoverageRegion candidate with
  | none => simp [hd] at h
  | some region =>
      simp only [hd] at h
      cases hp : (X.data.action.normalizedMap source.toOrigin).preimage
          (X.originImage (X.territory region.1).element region.2) with
      | none => simp [hp] at h
      | some value =>
          simp only [hp] at h
          split at h
          · rename_i he
            have hh := Prod.mk.inj (Option.some.inj h)
            obtain ⟨rfl, rfl⟩ := hh
            exact ⟨⟨region, rfl⟩, by simp [coverageWitnessCovers, CoverageRegion.witness, he]⟩
          · simp at h

-- ALIGN: ATLAS-COVERAGE-DECODE-COMPLETE.
theorem coverageAt_complete {X : Atlas} {source : X.Element}
    {datum : X.cellData source.val.cell} (covered : X.Covered source datum) :
    ∃ candidate witness, X.coverageAt source candidate = some (datum, witness) := by
  obtain ⟨index, value, he⟩ := covered
  let region : X.CoverageRegion := ⟨index, value⟩
  have image_eq := (X.originImageRank_eq_iff source (X.territory index).element datum value).mp he
  refine ⟨region.code, region.witness, ?_⟩
  simp only [coverageAt, decodeCoverageRegion_code]
  change (match (X.data.action.normalizedMap source.toOrigin).preimage
      (X.originImage (X.territory index).element value) with
    | none => none
    | some result =>
      if X.originImageRank source result = X.originImageRank (X.territory index).element value
        then some (result, region.witness) else none) = _
  rw [← image_eq]
  simp [originImage, DomanialInsertion.leftInverse, he]

/-- Candidate success is exactly the existential mathematical coverage
predicate; malformed caches cannot provide an alternative route to success. -/
theorem coverageCandidate_exists_iff (X : Atlas) (source : X.Element)
    (datum : X.cellData source.val.cell) :
    (∃ candidate, (X.coverageCandidate source datum candidate).isSome = true) ↔
      X.Covered source datum := by
  constructor
  · rintro ⟨candidate, h⟩
    obtain ⟨witness, hw⟩ := Option.isSome_iff_exists.mp h
    obtain ⟨valid, covers⟩ := coverageCandidate_sound hw
    exact coverageWitnessCovers_sound valid covers
  · intro covered
    obtain ⟨candidate, witness, hw⟩ := coverageCandidate_complete covered
    exact ⟨candidate, Option.isSome_iff_exists.mpr ⟨witness, hw⟩⟩

/-- Nat.find executes the ascending search from zero, and the coverage proof
establishes its termination without supplying an executable bound. -/
def findAtlasCoverage (X : Atlas) (source : X.Element)
    (datum : X.cellData source.val.cell) (covered : X.Covered source datum) : X.CoverageWitness :=
  let existsCandidate := (X.coverageCandidate_exists_iff source datum).mpr covered
  (X.coverageCandidate source datum (Nat.find existsCandidate)).get (Nat.find_spec existsCandidate)

-- ALIGN: ATLAS-COVERAGE-SEARCH-SPEC.
theorem findAtlasCoverage_spec (X : Atlas) (source : X.Element)
    (datum : X.cellData source.val.cell) (covered : X.Covered source datum) :
    (X.findAtlasCoverage source datum covered).Valid ∧
      X.coverageWitnessCovers source datum (X.findAtlasCoverage source datum covered) = true :=
  coverageCandidate_sound (Option.some_get _).symm

def coveredPageElementAt (X : Atlas) (source : X.Element) (candidate : Nat) :
    Option (X.cellData source.val.cell) := (X.coverageAt source candidate).map Prod.fst

theorem coveredPageElementAt_sound {X : Atlas} {source : X.Element} {candidate : Nat}
    {datum : X.cellData source.val.cell} (h : X.coveredPageElementAt source candidate = some datum) :
    X.Covered source datum := by
  unfold coveredPageElementAt at h
  cases hc : X.coverageAt source candidate with
  | none => simp [hc] at h
  | some result =>
      obtain ⟨value, witness⟩ := result
      simp only [hc, Option.map_some, Option.some.injEq] at h
      subst value
      obtain ⟨valid, covers⟩ := coverageAt_sound hc
      exact coverageWitnessCovers_sound valid covers

/-- Equality is tested using the source Dominion's rank, as in the runtime
Charter enumeration; no decidable equality on dependent cell data is needed. -/
def coverageRankCandidate (X : Atlas) (source : X.Element)
    (datum : X.cellData source.val.cell) (candidate : Nat) : Bool :=
  match X.coveredPageElementAt source candidate with
  | none => false
  | some value => (X.dataAt source).rank value == (X.dataAt source).rank datum

theorem coverageRankCandidate_iff (X : Atlas) (source : X.Element)
    (datum : X.cellData source.val.cell) (candidate : Nat) :
    X.coverageRankCandidate source datum candidate = true ↔
      X.coveredPageElementAt source candidate = some datum := by
  unfold coverageRankCandidate
  cases hc : X.coveredPageElementAt source candidate with
  | none => simp
  | some value => simp [Dominion.rank_injective (X.dataAt source) |>.eq_iff]

theorem coverageRankCandidate_exists_iff (X : Atlas) (source : X.Element)
    (datum : X.cellData source.val.cell) :
    (∃ candidate, X.coverageRankCandidate source datum candidate = true) ↔
      X.Covered source datum := by
  constructor
  · rintro ⟨candidate, h⟩
    exact coveredPageElementAt_sound ((X.coverageRankCandidate_iff source datum candidate).mp h)
  · intro covered
    obtain ⟨candidate, witness, h⟩ := coverageAt_complete covered
    exact ⟨candidate, (X.coverageRankCandidate_iff source datum candidate).mpr (by
      simp [coveredPageElementAt, h])⟩

def findAtlasCoverageRank (X : Atlas) (source : X.Element)
    (datum : X.cellData source.val.cell) (covered : X.Covered source datum) : Nat :=
  Nat.find ((X.coverageRankCandidate_exists_iff source datum).mpr covered)

-- ALIGN: ATLAS-COVERAGE-RANK-ROUNDTRIP.
theorem findAtlasCoverageRank_roundtrip (X : Atlas) (source : X.Element)
    (datum : X.cellData source.val.cell) (covered : X.Covered source datum) :
    X.coveredPageElementAt source (X.findAtlasCoverageRank source datum covered) = some datum :=
  (X.coverageRankCandidate_iff source datum _).mp
    (Nat.find_spec ((X.coverageRankCandidate_exists_iff source datum).mpr covered))

-- ALIGN: ATLAS-COVERAGE-RANK-MINIMAL.
theorem findAtlasCoverageRank_minimal (X : Atlas) (source : X.Element)
    (datum : X.cellData source.val.cell) (covered : X.Covered source datum) {candidate : Nat}
    (h : X.coveredPageElementAt source candidate = some datum) :
    X.findAtlasCoverageRank source datum covered ≤ candidate :=
  Nat.find_min' _ ((X.coverageRankCandidate_iff source datum candidate).mpr h)

end Datra.Executable.Atlas
