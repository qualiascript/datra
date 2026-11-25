import Executable.Atlas.Derived
import Executable.Atlas.Elements
import Executable.NaturalSearch

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

-- ALIGN: ATLAS-COVERAGE-VALIDATION.
def coverageWitnessValid (X : Atlas) (witness : X.CoverageWitness) : Bool :=
  witness.region.val.page == X.coverageFinalPage &&
    (witness.regionPage == witness.region.val.page &&
      witness.regionOriginRank == X.originImageRank witness.region witness.datum)

-- ALIGN: ATLAS-COVERAGE-ELIM.
def withAtlasCoverageWitness (X : Atlas) {result : Sort*}
    (witness : X.CoverageWitness) (valid : X.coverageWitnessValid witness = true)
    (useRegion : (region : X.Element) → region.val.page = X.coverageFinalPage →
      (datum : X.cellData region.val.cell) →
      X.originImageRank region datum = witness.regionOriginRank → result) : result := by
  simp only [coverageWitnessValid, Bool.and_eq_true, beq_iff_eq] at valid
  exact useRegion witness.region valid.1 witness.datum valid.2.2.symm

-- ALIGN: ATLAS-COVERAGE-RANK-OBSERVE.

def coverageWitnessOriginRank {X : Atlas} (witness : X.CoverageWitness) : Nat :=
  witness.regionOriginRank


def coverageWitnessCovers (X : Atlas) (source : X.Element)
    (datum : X.cellData source.val.cell) (witness : X.CoverageWitness) : Bool :=
  X.coverageWitnessValid witness &&
    (witness.regionPage == X.coverageFinalPage &&
      X.originImageRank source datum == witness.regionOriginRank)

-- ALIGN: ATLAS-COVERAGE-TRANSPORT.
-- Transport preserves the origin image, so the cached witness covers both data.
theorem coverageWitnessAlongArrow {X : Atlas} {source target : X.Element}
    (arrow : source ⟶ target) (datum : X.cellData source.val.cell)
    (witness : X.CoverageWitness)
    (covers : X.coverageWitnessCovers target
      ((X.data.action.normalizedMap arrow).map datum) witness = true) :
    X.coverageWitnessCovers source datum witness = true := by
  simpa only [coverageWitnessCovers, originImageRank, originImage_map] using covers

abbrev CoverageRegion (X : Atlas) :=
  (index : X.TerritoryIndex) × X.cellData (X.territory index).element.val.cell

def CoverageRegion.witness {X : Atlas} (region : X.CoverageRegion) : X.CoverageWitness :=
  ⟨(X.territory region.1).element, region.2, X.coverageFinalPage,
    X.originImageRank (X.territory region.1).element region.2⟩

/-- Cache consistency also retains a genuine final-region representative. -/
def CoverageWitness.Valid {X : Atlas} (witness : X.CoverageWitness) : Prop :=
  ∃ region : X.CoverageRegion, witness = region.witness

@[simp] theorem CoverageRegion.witness_valid {X : Atlas} (region : X.CoverageRegion) :
    X.coverageWitnessValid region.witness = true := by
  have page : (X.territory region.1).element.val.page = X.coverageFinalPage := rfl
  simp [coverageWitnessValid, CoverageRegion.witness, page]

@[simp] theorem CoverageRegion.witness_covers {X : Atlas} (source : X.Element)
    (datum : X.cellData source.val.cell) (region : X.CoverageRegion) :
    X.coverageWitnessCovers source datum region.witness =
      (X.originImageRank source datum ==
        X.originImageRank (X.territory region.1).element region.2) := by
  rw [coverageWitnessCovers, region.witness_valid]
  simp [CoverageRegion.witness]

theorem CoverageWitness.Valid.checked {X : Atlas} {witness : X.CoverageWitness}
    (valid : witness.Valid) : X.coverageWitnessValid witness = true := by
  obtain ⟨region, rfl⟩ := valid
  exact region.witness_valid

-- The executable validator recovers the existential territory representative.
theorem coverageWitnessValid_iff (X : Atlas) (witness : X.CoverageWitness) :
    X.coverageWitnessValid witness = true ↔ witness.Valid := by
  constructor
  · rcases witness with ⟨region, datum, cachedPage, cachedRank⟩
    intro checked
    simp only [coverageWitnessValid, Bool.and_eq_true, beq_iff_eq] at checked
    obtain ⟨atFinal, page, valueRank⟩ := checked
    obtain ⟨index, hi⟩ := FolioData.ValidElement.lastElement_surjective X.pages region atFinal
    subst cachedPage
    subst cachedRank
    have construct (r : X.Element) (value : X.cellData r.val.cell)
        (h : (X.territory index).element = r) :
        (⟨r, value, r.val.page, X.originImageRank r value⟩ : X.CoverageWitness).Valid := by
      subst r
      exact ⟨⟨index, value⟩, rfl⟩
    exact construct region datum hi
  · exact CoverageWitness.Valid.checked

theorem coverageWitnessCovers_valid {X : Atlas} {source : X.Element}
    {datum : X.cellData source.val.cell} {witness : X.CoverageWitness}
    (covers : X.coverageWitnessCovers source datum witness = true) : witness.Valid := by
  simp only [coverageWitnessCovers, Bool.and_eq_true] at covers
  exact (coverageWitnessValid_iff X witness).mp covers.1

-- ALIGN: ATLAS-COVERAGE-CACHED-RANK-MATCHES.
theorem coverageWitnessRankMatches (X : Atlas) (source : X.Element)
    (datum : X.cellData source.val.cell) (witness : X.CoverageWitness)
    (covers : X.coverageWitnessCovers source datum witness = true) :
    witness.regionOriginRank = X.originImageRank source datum := by
  simp only [coverageWitnessCovers, Bool.and_eq_true, beq_iff_eq] at covers
  exact covers.2.2.symm

theorem CoverageWitness.Valid.covered {X : Atlas} {witness : X.CoverageWitness}
    (valid : witness.Valid) : X.Covered witness.region witness.datum := by
  obtain ⟨⟨index, datum⟩, rfl⟩ := valid
  exact ⟨index, datum, rfl⟩

theorem CoverageWitness.Valid.finalPage {X : Atlas} {witness : X.CoverageWitness}
    (valid : witness.Valid) : witness.region.normalize.val.page = X.coverageFinalPage := by
  obtain ⟨⟨index, datum⟩, rfl⟩ := valid
  change (FolioData.ValidElement.lastElement X.pages index).normalize.val.page = _
  rw [FolioData.ValidElement.lastElement_interpretation,
    FolioData.ValidElement.normalize_fromFinite]
  rfl

theorem CoverageWitness.Valid.originImage_eq {X : Atlas} {source : X.Element}
    {datum : X.cellData source.val.cell} {witness : X.CoverageWitness}
    (valid : witness.Valid) (covers : X.coverageWitnessCovers source datum witness = true) :
    X.originImage source datum = X.originImage witness.region witness.datum := by
  obtain ⟨⟨index, regionDatum⟩, rfl⟩ := valid
  apply (X.originImageRank_eq_iff _ _ _ _).mp
  simpa only [CoverageRegion.witness_covers, beq_iff_eq] using covers

-- ALIGN: ATLAS-COVERAGE-WITNESS-SOUND.
theorem coverageWitnessCovers_sound {X : Atlas} {source : X.Element}
    {datum : X.cellData source.val.cell} {witness : X.CoverageWitness}
    (valid : witness.Valid) (covers : X.coverageWitnessCovers source datum witness = true) :
    X.Covered source datum := by
  obtain ⟨⟨index, regionDatum⟩, rfl⟩ := valid
  exact ⟨index, regionDatum, by simpa only [CoverageRegion.witness_covers, beq_iff_eq] using covers⟩

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
  · simp [coverageWitnessCovers, coverageWitnessValid, atlasCoverageWitness, conditions.1, conditions.2]

structure CoveredPageElement (X : Atlas) where
  source : X.Element
  datum : X.cellData source.val.cell
  witness : X.CoverageWitness

-- ALIGN: ATLAS-COVERED-WITNESS.
def atlasCoveredPageElementWitness {X : Atlas} (covered : X.CoveredPageElement) : X.CoverageWitness :=
  covered.witness

def CoveredPageElement.Valid {X : Atlas} (covered : X.CoveredPageElement) : Prop :=
  covered.witness.Valid ∧ X.coverageWitnessCovers covered.source covered.datum covered.witness = true

-- ALIGN: ATLAS-COVERED-PAYLOAD-VALIDITY.
def coveredPageElementValid (X : Atlas) (covered : X.CoveredPageElement) : Bool :=
  X.coverageWitnessCovers covered.source covered.datum covered.witness

-- ALIGN: ATLAS-COVERED-SOURCE.
def coveredPageElementSource {X : Atlas} (covered : X.CoveredPageElement) : X.Element :=
  covered.source

theorem coveredPageElementValid_iff (X : Atlas) (covered : X.CoveredPageElement) :
    X.coveredPageElementValid covered = true ↔ covered.Valid :=
  ⟨fun valid => ⟨coverageWitnessCovers_valid valid, valid⟩, fun valid => valid.2⟩

-- ALIGN: ATLAS-COVERED-BY-WITNESS.
def atlasCoveredByWitness (X : Atlas) (source : X.Element)
    (datum : X.cellData source.val.cell) (witness : X.CoverageWitness)
    (covers : X.coverageWitnessCovers source datum witness = true) :
    {covered : X.CoveredPageElement // covered.Valid} :=
  ⟨⟨source, datum, witness⟩, coverageWitnessCovers_valid covers, covers⟩

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

-- ALIGN: ATLAS-COVERED-CERTIFIED-ELIM.
def withAtlasCoveredPageElementOf (X : Atlas) {Result : Sort*} (covered : X.CoveredPageElement)
    (valid : X.coveredPageElementValid covered = true)
    (useCovered : (source : X.Element) → (datum : X.cellData source.val.cell) →
      (witness : X.CoverageWitness) → X.coverageWitnessCovers source datum witness = true →
      source = covered.source → witness = covered.witness → Result) : Result :=
  useCovered covered.source covered.datum covered.witness valid rfl rfl

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
and coverageAt. No assumption is made about unranking unused ranks. -/
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

-- ALIGN: ATLAS-COVERAGE-WITNESS-CODE.
def coverageWitnessCode (X : Atlas) (witness : X.CoverageWitness)
    (valid : X.coverageWitnessValid witness = true) : Nat :=
  have atFinal : witness.region.val.page = X.pages.depth - 1 := by
    simp only [coverageWitnessValid, Bool.and_eq_true, beq_iff_eq] at valid
    exact valid.1
  (X.withTerritoryOf witness.region atFinal (fun _ target _ _ _ arrow =>
    Ordinal.pairNatural
      (CoverageEnumeration.encodeNaturalList target.val.position.coefficients)
      ((X.dataAt target).rank ((X.data.action.normalizedMap arrow).map witness.datum)))).getD 0

theorem coverageWitnessCode_direct (X : Atlas) (witness : X.CoverageWitness)
    (valid : X.coverageWitnessValid witness = true) :
    X.coverageWitnessCode witness valid =
      Ordinal.pairNatural
        (CoverageEnumeration.encodeNaturalList witness.region.val.position.coefficients)
        ((X.dataAt witness.region).rank witness.datum) := by
  simp only [coverageWitnessCode, Atlas.withTerritoryOf_eq_self, X.data.identity, Option.getD_some]

@[simp] theorem CoverageRegion.witness_code {X : Atlas} (region : X.CoverageRegion)
    (valid : X.coverageWitnessValid region.witness = true) :
    X.coverageWitnessCode region.witness valid = region.code := by
  simp only [coverageWitnessCode_direct, CoverageRegion.witness, Atlas.territory_position, CoverageRegion.code]
  rfl

theorem decodeCoverageRegion_code (X : Atlas) (region : X.CoverageRegion) :
    X.decodeCoverageRegion region.code = some region := by
  obtain ⟨index, datum⟩ := region
  have hi : X.pagination.final.chain.chainIndex index.position = some index := by
    rw [← index.position_eq, Chain.chainIndex_position]
    exact congrArg some (X.pagination.final.chain.indexEquiv.left_inv index)
  simp [decodeCoverageRegion, CoverageRegion.code, Ordinal.unpairNatural_pair,
    CoverageEnumeration.ordinal_decode_encode, hi, Dominion.coherence]

def coverageRegionWitness (X : Atlas) (region : X.Element)
    (datum : X.cellData region.val.cell) : X.CoverageWitness :=
  ⟨region, datum, region.val.page, X.originImageRank region datum⟩

/-- A decoded region datum is pulled back through the source's checked insertion. -/
def coveragePullback (X : Atlas) (source region : X.Element)
    (regionDatum : X.cellData region.val.cell) :
    Option (X.cellData source.val.cell × X.CoverageWitness) :=
  match (X.cellOriginRankInsertion source).preimage (X.originImageRank region regionDatum) with
  | none => none
  | some datum =>
    if X.originImageRank source datum = X.originImageRank region regionDatum then
      some (datum, X.coverageRegionWitness region regionDatum)
    else none

def coverageDecodedDatum {Datum Witness : Type*} : Option (Datum × Witness) → Option Datum
  | none => none
  | some (datum, _) => some datum

-- ALIGN: ATLAS-COVERAGE-PULLBACK-INVERSE.
theorem coveragePullbackInverse (X : Atlas) (source region : X.Element)
    (datum : X.cellData source.val.cell) (regionDatum : X.cellData region.val.cell)
    (_atFinal : region.val.page = X.coverageFinalPage)
    (same : X.originImageRank region regionDatum = X.originImageRank source datum) :
    coverageDecodedDatum (X.coveragePullback source region regionDatum) = some datum := by
  have inverse : (X.cellOriginRankInsertion source).preimage
      (X.originImageRank region regionDatum) = some datum := by
    rw [same, ← X.cellOriginRankInsertion_map source datum]
    exact (X.cellOriginRankInsertion source).leftInverse datum
  simp only [coveragePullback, inverse]
  simp [same, coverageDecodedDatum]

def coverageAtRegion (X : Atlas) (source region : X.Element) (datumRank : Nat) :
    Option (X.cellData source.val.cell × X.CoverageWitness) :=
  match (X.dataAt region).unrank datumRank with
  | none => none
  | some datum => X.coveragePullback source region datum

-- ALIGN: ATLAS-COVERAGE-REGION-INVERSE.
theorem coverageAtRegionInverse (X : Atlas) (source region : X.Element)
    (datum : X.cellData source.val.cell) (regionDatum : X.cellData region.val.cell)
    (atFinal : region.val.page = X.coverageFinalPage)
    (same : X.originImageRank region regionDatum = X.originImageRank source datum) :
    coverageDecodedDatum (X.coverageAtRegion source region ((X.dataAt region).rank regionDatum)) = some datum := by
  simp only [coverageAtRegion, Dominion.coherence]
  exact X.coveragePullbackInverse source region datum regionDatum atFinal same

def coverageAtIndex (X : Atlas) (source : X.Element) (datumRank : Nat)
    (index : X.TerritoryIndex) : Option (X.cellData source.val.cell × X.CoverageWitness) :=
  X.withTerritory index (fun region _ => X.coverageAtRegion source region datumRank)

-- ALIGN: ATLAS-COVERAGE-SELECTED-REGION.
theorem coverageAtIndexSelected (X : Atlas) (source : X.Element) (index : X.TerritoryIndex)
    (datumRank : Nat) (region : X.Element) (selected : region = X.territoryElement index) :
    X.coverageAtIndex source datumRank index = X.coverageAtRegion source region datumRank := by
  subst region
  rfl

/-- Decode the position, then unrank and pull back the selected region datum. -/
def coverageAt (X : Atlas) (source : X.Element) (candidate : Nat) :
    Option (X.cellData source.val.cell × X.CoverageWitness) :=
  let (positionCode, datumRank) := Ordinal.unpairNatural candidate
  match X.pagination.final.chain.chainIndex
      (Ordinal.ordinal (CoverageEnumeration.decodeNaturalList positionCode)) with
  | none => none
  | some index => X.coverageAtIndex source datumRank index

-- ALIGN: ATLAS-COVERAGE-INDEX-DECODE.
theorem coverageIndexEncode (X : Atlas) (source : X.Element)
    (index : X.TerritoryIndex) (datumRank : Nat) :
    X.coverageAt source (Ordinal.pairNatural
      (CoverageEnumeration.encodeNaturalList index.position.coefficients) datumRank) =
        X.coverageAtIndex source datumRank index := by
  have indexed : X.pagination.final.chain.chainIndex index.position = some index := by
    rw [← index.position_eq, Chain.chainIndex_position]
    exact congrArg some (X.pagination.final.chain.indexEquiv.left_inv index)
  simp [coverageAt, Ordinal.unpairNatural_pair, CoverageEnumeration.ordinal_decode_encode, indexed]

theorem coverageAt_eq_decode (X : Atlas) (source : X.Element) (candidate : Nat) :
    X.coverageAt source candidate =
      match X.decodeCoverageRegion candidate with
      | none => none
      | some region => X.coveragePullback source (X.territory region.1).element region.2 := by
  rcases paired : Ordinal.unpairNatural candidate with ⟨positionCode, datumRank⟩
  simp only [coverageAt, coverageAtIndex, Atlas.withTerritory, Atlas.territoryElement, decodeCoverageRegion, paired]
  cases indexed : X.pagination.final.chain.chainIndex
      (Ordinal.ordinal (CoverageEnumeration.decodeNaturalList positionCode)) with
  | none => simp
  | some index =>
      cases decoded : (X.territory index).dominion.unrank datumRank <;>
        simp only [Atlas.territory] at decoded <;>
        simp [coverageAtRegion, Atlas.territory, decoded]

/-- The checked rank inverse is exactly the origin pullback followed by
its image test, including outside the source insertion's image. -/
-- ALIGN: ATLAS-COVERAGE-RANK-DECODER.
theorem coverageAt_eq_pullback (X : Atlas) (source : X.Element) (candidate : Nat) :
    X.coverageAt source candidate =
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
          else none := by
  rw [coverageAt_eq_decode]
  unfold coveragePullback coverageRegionWitness
  cases X.decodeCoverageRegion candidate with
  | none => rfl
  | some region =>
    simp only [Atlas.cellOriginRankInsertion, DomanialInsertion.rankImageInsertion,
      DomanialInsertion.rankImagePreimage, Atlas.originImageRank, Dominion.coherence,
      bind, Option.bind, DomanialInsertion.rankImage]
    cases (X.data.action.normalizedMap source.toOrigin).preimage
        (X.originImage (X.territory region.1).element region.2) with
    | none => rfl
    | some datum =>
      change (match (if X.originImageRank source datum =
          X.originImageRank (X.territory region.1).element region.2 then some datum else none) with
        | none => none
        | some value => if X.originImageRank source value =
            X.originImageRank (X.territory region.1).element region.2 then some (value, region.witness) else none) = _
      split <;> simp_all [Atlas.originImageRank]

-- ALIGN: ATLAS-COVERAGE-DECODE-SOUND.
theorem coverageAt_sound {X : Atlas} {source : X.Element} {candidate : Nat}
    {datum : X.cellData source.val.cell} {witness : X.CoverageWitness}
    (h : X.coverageAt source candidate = some (datum, witness)) :
    witness.Valid ∧ X.coverageWitnessCovers source datum witness = true := by
  rw [coverageAt_eq_pullback] at h
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
            exact ⟨⟨region, rfl⟩, by simp [he]⟩
          · simp at h

-- ALIGN: ATLAS-COVERED-DECODE.
def atlasCoveredAt (X : Atlas) (source : X.Element) (candidate : Nat) :
    Option {covered : X.CoveredPageElement // covered.Valid} :=
  match h : X.coverageAt source candidate with
  | none => none
  | some (datum, witness) =>
    some (X.atlasCoveredByWitness source datum witness
      (coverageAt_sound h).2)

-- ALIGN: ATLAS-COVERAGE-DECODE-COMPLETE.
theorem coverageAt_complete {X : Atlas} {source : X.Element}
    {datum : X.cellData source.val.cell} (covered : X.Covered source datum) :
    ∃ candidate witness, X.coverageAt source candidate = some (datum, witness) := by
  obtain ⟨index, value, he⟩ := covered
  let region : X.CoverageRegion := ⟨index, value⟩
  have image_eq := (X.originImageRank_eq_iff source (X.territory index).element datum value).mp he
  refine ⟨region.code, region.witness, ?_⟩
  simp only [coverageAt_eq_pullback, decodeCoverageRegion_code]
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
def coverageValueMatches {Value : Type} (values : Dominion Value) (datum : Value) : Option Value → Bool
  | none => false
  | some value => values.rank value == values.rank datum

def coverageRankCandidate (X : Atlas) (source : X.Element)
    (datum : X.cellData source.val.cell) (candidate : Nat) : Bool :=
  coverageValueMatches (X.dataAt source) datum (X.coveredPageElementAt source candidate)

-- ALIGN: ATLAS-COVERAGE-CANDIDATE-EXACT.
theorem coverageRankCandidate_iff (X : Atlas) (source : X.Element)
    (datum : X.cellData source.val.cell) (candidate : Nat) :
    X.coverageRankCandidate source datum candidate = true ↔
      X.coveredPageElementAt source candidate = some datum := by
  unfold coverageRankCandidate
  cases hc : X.coveredPageElementAt source candidate with
  | none => simp [coverageValueMatches]
  | some value => simp [coverageValueMatches, Dominion.rank_injective (X.dataAt source) |>.eq_iff]

theorem coverageDecodedDatum_eq_map {Value Witness : Type*} (result : Option (Value × Witness)) :
    coverageDecodedDatum result = result.map Prod.fst := by
  cases result <;> rfl

theorem coveragePullbackMatches (X : Atlas) (source region : X.Element)
    (datum : X.cellData source.val.cell) (regionDatum : X.cellData region.val.cell)
    (atFinal : region.val.page = X.coverageFinalPage) :
    coverageValueMatches (X.dataAt source) datum
      ((X.coveragePullback source region regionDatum).map Prod.fst) =
      (X.originImageRank source datum == X.originImageRank region regionDatum) := by
  by_cases same : X.originImageRank source datum = X.originImageRank region regionDatum
  · have inverse := X.coveragePullbackInverse source region datum regionDatum atFinal same.symm
    rw [coverageDecodedDatum_eq_map] at inverse
    simp [inverse, coverageValueMatches, same]
  · unfold coveragePullback
    cases decoded : (X.cellOriginRankInsertion source).preimage (X.originImageRank region regionDatum) with
    | none => simp [coverageValueMatches, same]
    | some value =>
        by_cases matched : X.originImageRank source value = X.originImageRank region regionDatum
        · have different : value ≠ datum := by
            intro equal
            subst value
            exact same matched
          have ranks : (X.dataAt source).rank value ≠ (X.dataAt source).rank datum := by
            intro equal
            exact different ((X.dataAt source).rank_injective equal)
          simp [matched, coverageValueMatches, ranks, same]
        · simp [matched, coverageValueMatches, same]

-- ALIGN: ATLAS-COVERAGE-CANDIDATE-SAME-ORIGIN.
theorem coverageRankCandidateSameOrigin (X : Atlas) (source target : X.Element)
    (datum : X.cellData source.val.cell) (targetDatum : X.cellData target.val.cell)
    (same : X.originImageRank source datum = X.originImageRank target targetDatum) (candidate : Nat) :
    X.coverageRankCandidate source datum candidate = X.coverageRankCandidate target targetDatum candidate := by
  simp only [coverageRankCandidate, coveredPageElementAt, coverageAt_eq_decode]
  cases decoded : X.decodeCoverageRegion candidate with
  | none => rfl
  | some region =>
      rw [coveragePullbackMatches X source _ datum region.2 rfl,
        coveragePullbackMatches X target _ targetDatum region.2 rfl, same]

/-- Recover the coverage evidence at an already certified enumeration index. -/
def coverageRankWitness (X : Atlas) (source : X.Element)
    (_datum : X.cellData source.val.cell) (candidate : Nat) : Option X.CoverageWitness :=
  (X.coverageAt source candidate).map Prod.snd

-- ALIGN: ATLAS-COVERAGE-RANK-WITNESS.
theorem coverageRankWitness_spec (X : Atlas) (source : X.Element)
    (datum : X.cellData source.val.cell) (candidate : Nat)
    (accepted : X.coverageRankCandidate source datum candidate = true) :
    (X.coverageRankWitness source datum candidate).isSome = true ∧
      ∀ witness, X.coverageRankWitness source datum candidate = some witness →
        X.coverageWitnessCovers source datum witness = true := by
  have exactDatum := (X.coverageRankCandidate_iff source datum candidate).mp accepted
  unfold coveredPageElementAt at exactDatum
  cases decoded : X.coverageAt source candidate with
  | none => simp [decoded] at exactDatum
  | some result =>
      rcases result with ⟨value, witness⟩
      have same : value = datum := by simpa [decoded] using exactDatum
      subst value
      have sound := coverageAt_sound decoded
      simp [coverageRankWitness, decoded, sound.2]

theorem coverageWitnessCode_matches {X : Atlas} {source : X.Element}
    {datum : X.cellData source.val.cell} (witness : X.CoverageWitness)
    (valid : X.coverageWitnessValid witness = true)
    (covers : X.coverageWitnessCovers source datum witness = true) :
    X.coverageRankCandidate source datum (X.coverageWitnessCode witness valid) = true := by
  obtain ⟨region, rfl⟩ := (coverageWitnessValid_iff X witness).mp valid
  rw [CoverageRegion.witness_code]
  apply (coverageRankCandidate_iff X source datum region.code).2
  have same : X.originImageRank source datum =
      X.originImageRank (X.territory region.1).element region.2 := by
    simpa only [CoverageRegion.witness_covers, beq_iff_eq] using covers
  have inverse : (X.cellOriginRankInsertion source).preimage
      (X.originImageRank (X.territory region.1).element region.2) = some datum := by
    rw [← same, ← X.cellOriginRankInsertion_map source datum]
    exact (X.cellOriginRankInsertion source).leftInverse datum
  simp [coveredPageElementAt, coverageAt_eq_decode, coveragePullback, coverageRegionWitness, decodeCoverageRegion_code, inverse, same]

-- ALIGN: ATLAS-COVERAGE-SELECTED-INDEX-INVERSE.
theorem coverageSelectedIndexInverse (X : Atlas) (source : X.Element)
    (datum : X.cellData source.val.cell) (index : X.TerritoryIndex)
    (region : X.Element) (selected : region = X.territoryElement index)
    (regionDatum : X.cellData region.val.cell)
    (atFinal : region.val.page = X.coverageFinalPage)
    (same : X.originImageRank region regionDatum = X.originImageRank source datum) :
    X.coverageRankCandidate source datum (Ordinal.pairNatural
      (CoverageEnumeration.encodeNaturalList index.position.coefficients)
      ((X.dataAt region).rank regionDatum)) = true := by
  apply (X.coverageRankCandidate_iff source datum _).2
  unfold coveredPageElementAt
  rw [X.coverageIndexEncode, X.coverageAtIndexSelected source index _ region selected]
  have inverse := X.coverageAtRegionInverse source region datum regionDatum atFinal same
  cases decoded : X.coverageAtRegion source region ((X.dataAt region).rank regionDatum) with
  | none => simp [decoded, coverageDecodedDatum] at inverse
  | some result => simpa [decoded, coverageDecodedDatum] using inverse

-- ALIGN: ATLAS-COVERAGE-WITNESS-BOUND.
def coverageWitnessBound (X : Atlas) (source : X.Element)
    (datum : X.cellData source.val.cell) (witness : X.CoverageWitness)
    (valid : X.coverageWitnessValid witness = true)
    (_covers : X.coverageWitnessCovers source datum witness = true) : Nat :=
  X.coverageWitnessCode witness valid

theorem coverageWitnessBound_spec (X : Atlas) (source : X.Element)
    (datum : X.cellData source.val.cell) (witness : X.CoverageWitness)
    (valid : X.coverageWitnessValid witness = true)
    (covers : X.coverageWitnessCovers source datum witness = true) :
    X.coverageRankCandidate source datum
      (X.coverageWitnessBound source datum witness valid covers) = true :=
  coverageWitnessCode_matches witness valid covers

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

/-- Ascending coverage search delegates to the shared finite search. -/
def searchCoverageRank (X : Atlas) (source : X.Element)
    (datum : X.cellData source.val.cell) (candidate remaining : Nat) : Option Nat :=
  NaturalSearch.search (X.coverageRankCandidate source datum) candidate remaining

theorem searchCoverageRank_sound {X : Atlas} {source : X.Element}
    {datum : X.cellData source.val.cell} {candidate remaining found : Nat}
    (h : X.searchCoverageRank source datum candidate remaining = some found) :
    candidate ≤ found ∧ found ≤ candidate + remaining ∧
      X.coverageRankCandidate source datum found = true := NaturalSearch.sound h

theorem searchCoverageRank_least {X : Atlas} {source : X.Element}
    {datum : X.cellData source.val.cell} {candidate remaining found earlier : Nat}
    (h : X.searchCoverageRank source datum candidate remaining = some found)
    (lower : candidate ≤ earlier) (before : earlier < found) :
    X.coverageRankCandidate source datum earlier = false := NaturalSearch.least h lower before

theorem searchCoverageRank_complete {X : Atlas} {source : X.Element}
    {datum : X.cellData source.val.cell} {candidate remaining successful : Nat}
    (lower : candidate ≤ successful) (upper : successful ≤ candidate + remaining)
    (accepted : X.coverageRankCandidate source datum successful = true) :
    ∃ found, X.searchCoverageRank source datum candidate remaining = some found :=
  NaturalSearch.complete lower upper accepted

def atlasCoverageRankWithin (X : Atlas) (source : X.Element)
    (datum : X.cellData source.val.cell) (bound : Nat) : Option Nat :=
  X.searchCoverageRank source datum 0 bound

-- ALIGN: ATLAS-COVERAGE-BOUNDED-RANK.
theorem atlasCoverageRankWithin_sound {X : Atlas} {source : X.Element}
    {datum : X.cellData source.val.cell} {bound found : Nat}
    (h : X.atlasCoverageRankWithin source datum bound = some found) :
    found ≤ bound ∧ X.coverageRankCandidate source datum found = true := by
  have hs := searchCoverageRank_sound h
  simpa using hs.2

-- ALIGN: ATLAS-COVERAGE-BOUNDED-MINIMAL.
theorem atlasCoverageRankLeast {X : Atlas} {source : X.Element}
    {datum : X.cellData source.val.cell} {bound found earlier : Nat}
    (h : X.atlasCoverageRankWithin source datum bound = some found) (before : earlier < found) :
    X.coverageRankCandidate source datum earlier = false :=
  searchCoverageRank_least h (Nat.zero_le earlier) before

theorem atlasCoverageRankWithin_witness {X : Atlas} {source : X.Element}
    {datum : X.cellData source.val.cell} (witness : X.CoverageWitness)
    (valid : X.coverageWitnessValid witness = true)
    (covers : X.coverageWitnessCovers source datum witness = true) :
    ∃ found, X.atlasCoverageRankWithin source datum (X.coverageWitnessCode witness valid) = some found :=
  searchCoverageRank_complete (Nat.zero_le _) (by omega)
    (coverageWitnessCode_matches witness valid covers)

def findAtlasCoverageRank (X : Atlas) (source : X.Element)
    (datum : X.cellData source.val.cell) (covered : X.Covered source datum) : Nat :=
  Nat.find ((X.coverageRankCandidate_exists_iff source datum).mpr covered)

theorem atlasCoverageRankWithin_eq_find {X : Atlas} {source : X.Element}
    {datum : X.cellData source.val.cell} (covered : X.Covered source datum) {limit found : Nat}
    (h : X.atlasCoverageRankWithin source datum limit = some found) :
    found = X.findAtlasCoverageRank source datum covered := by
  have hs := atlasCoverageRankWithin_sound h
  have least := Nat.find_min' ((X.coverageRankCandidate_exists_iff source datum).mpr covered) hs.2
  apply Nat.le_antisymm _ least
  by_contra hn
  have before : X.findAtlasCoverageRank source datum covered < found := Nat.lt_of_not_ge hn
  have rejected := atlasCoverageRankLeast h before
  have accepted := Nat.find_spec ((X.coverageRankCandidate_exists_iff source datum).mpr covered)
  change X.coverageRankCandidate source datum
    (X.findAtlasCoverageRank source datum covered) = true at accepted
  rw [accepted] at rejected
  contradiction

/-- A successful search remains successful when trimmed to its selected rank. -/
theorem atlasCoverageRankWithin_trim {X : Atlas} {source : X.Element}
    {datum : X.cellData source.val.cell} {limit found : Nat}
    (selected : X.atlasCoverageRankWithin source datum limit = some found) :
    X.atlasCoverageRankWithin source datum found = some found := by
  simpa only [atlasCoverageRankWithin, searchCoverageRank, Nat.sub_zero] using NaturalSearch.trim selected

def coverageRankCanonical (X : Atlas) (source : X.Element)
    (datum : X.cellData source.val.cell) (candidate : Nat) : Bool :=
  X.atlasCoverageRankWithin source datum candidate == some candidate

-- ALIGN: ATLAS-COVERAGE-CANONICAL-SAME-ORIGIN.
theorem coverageRankCanonicalSameOrigin (X : Atlas) (source target : X.Element)
    (datum : X.cellData source.val.cell) (targetDatum : X.cellData target.val.cell)
    (same : X.originImageRank source datum = X.originImageRank target targetDatum) (candidate : Nat) :
    X.coverageRankCanonical source datum candidate = X.coverageRankCanonical target targetDatum candidate := by
  unfold coverageRankCanonical atlasCoverageRankWithin searchCoverageRank
  rw [NaturalSearch.congruent _ _ (X.coverageRankCandidateSameOrigin source target datum targetDatum same)]

-- ALIGN: ATLAS-COVERAGE-RANK-TRANSPORT.
theorem coverageRankAlongArrow (X : Atlas) {source target : X.Element}
    (arrow : source ⟶ target) (datum : X.cellData source.val.cell) (candidate : Nat) :
    X.coverageRankCandidate source datum candidate =
      X.coverageRankCandidate target ((X.data.action.normalizedMap arrow).map datum) candidate ∧
    X.coverageRankCanonical source datum candidate =
      X.coverageRankCanonical target ((X.data.action.normalizedMap arrow).map datum) candidate := by
  have same : X.originImageRank source datum =
      X.originImageRank target ((X.data.action.normalizedMap arrow).map datum) := by
    simp only [Atlas.originImageRank, X.originImage_map]
  exact ⟨X.coverageRankCandidateSameOrigin source target datum _ same candidate,
    X.coverageRankCanonicalSameOrigin source target datum _ same candidate⟩

-- ALIGN: ATLAS-COVERAGE-RANK-NORMALIZATION.
theorem coverageRankNormalized (X : Atlas) (source : X.Element)
    (datum : X.cellData source.val.cell) (candidate : Nat) :
    X.coverageRankCandidate source datum candidate =
      X.coverageRankCandidate source.normalize datum candidate ∧
    X.coverageRankCanonical source datum candidate =
      X.coverageRankCanonical source.normalize datum candidate :=
  ⟨X.coverageRankCandidateSameOrigin source source.normalize datum datum
      (X.originImageRank_normalize source datum).symm candidate,
   X.coverageRankCanonicalSameOrigin source source.normalize datum datum
      (X.originImageRank_normalize source datum).symm candidate⟩


-- ALIGN: ATLAS-COVERAGE-CANONICAL-UNIQUE.
theorem coverageRankCanonicalUnique (X : Atlas) (source : X.Element)
    (datum : X.cellData source.val.cell) (left right : Nat)
    (leftCanonical : X.coverageRankCanonical source datum left = true)
    (rightCanonical : X.coverageRankCanonical source datum right = true) : left = right := by
  simp only [coverageRankCanonical, beq_iff_eq] at leftCanonical rightCanonical
  have accepted := (atlasCoverageRankWithin_sound leftCanonical).2
  have covered := coveredPageElementAt_sound ((X.coverageRankCandidate_iff source datum left).mp accepted)
  exact (atlasCoverageRankWithin_eq_find covered leftCanonical).trans
    (atlasCoverageRankWithin_eq_find covered rightCanonical).symm

-- ALIGN: ATLAS-COVERAGE-WITNESS-RANK.
def atlasCoverageRank (X : Atlas) (source : X.Element)
    (datum : X.cellData source.val.cell) (witness : X.CoverageWitness)
    (valid : X.coverageWitnessValid witness = true)
    (covers : X.coverageWitnessCovers source datum witness = true) : Nat :=
  (X.atlasCoverageRankWithin source datum
    (X.coverageWitnessBound source datum witness valid covers)).getD 0

theorem atlasCoverageRank_eq_find (X : Atlas) (source : X.Element)
    (datum : X.cellData source.val.cell) (witness : X.CoverageWitness)
    (valid : X.coverageWitnessValid witness = true)
    (covers : X.coverageWitnessCovers source datum witness = true) :
    X.atlasCoverageRank source datum witness valid covers =
      X.findAtlasCoverageRank source datum
        (coverageWitnessCovers_sound ((coverageWitnessValid_iff X witness).mp valid) covers) := by
  obtain ⟨found, selected⟩ := atlasCoverageRankWithin_witness witness valid covers
  simp only [atlasCoverageRank, coverageWitnessBound, selected, Option.getD_some]
  exact atlasCoverageRankWithin_eq_find _ selected

theorem atlasCoverageRank_spec (X : Atlas) (source : X.Element)
    (datum : X.cellData source.val.cell) (witness : X.CoverageWitness)
    (valid : X.coverageWitnessValid witness = true)
    (covers : X.coverageWitnessCovers source datum witness = true) :
    X.coverageRankCandidate source datum
      (X.atlasCoverageRank source datum witness valid covers) = true := by
  obtain ⟨found, selected⟩ := atlasCoverageRankWithin_witness witness valid covers
  simp only [atlasCoverageRank, coverageWitnessBound, selected, Option.getD_some]
  exact (atlasCoverageRankWithin_sound selected).2

theorem atlasCoverageRank_canonical (X : Atlas) (source : X.Element)
    (datum : X.cellData source.val.cell) (witness : X.CoverageWitness)
    (valid : X.coverageWitnessValid witness = true)
    (covers : X.coverageWitnessCovers source datum witness = true) :
    X.coverageRankCanonical source datum
      (X.atlasCoverageRank source datum witness valid covers) = true := by
  obtain ⟨found, selected⟩ := atlasCoverageRankWithin_witness witness valid covers
  simp only [atlasCoverageRank, coverageWitnessBound, selected, Option.getD_some,
    coverageRankCanonical, beq_iff_eq]
  exact atlasCoverageRankWithin_trim selected

theorem findAtlasCoverageRank_roundtrip (X : Atlas) (source : X.Element)
    (datum : X.cellData source.val.cell) (covered : X.Covered source datum) :
    X.coveredPageElementAt source (X.findAtlasCoverageRank source datum covered) = some datum :=
  (X.coverageRankCandidate_iff source datum _).mp
    (Nat.find_spec ((X.coverageRankCandidate_exists_iff source datum).mpr covered))

theorem findAtlasCoverageRank_minimal (X : Atlas) (source : X.Element)
    (datum : X.cellData source.val.cell) (covered : X.Covered source datum) {candidate : Nat}
    (h : X.coveredPageElementAt source candidate = some datum) :
    X.findAtlasCoverageRank source datum covered ≤ candidate :=
  Nat.find_min' _ ((X.coverageRankCandidate_iff source datum candidate).mpr h)

/-- The covered semantic carrier selects its least code and uses the same
finite witness decoder as the cached runtime carrier. -/
def findAtlasCoverage (X : Atlas) (source : X.Element)
    (datum : X.cellData source.val.cell) (covered : X.Covered source datum) : X.CoverageWitness :=
  let candidate := X.findAtlasCoverageRank source datum covered
  let accepted := (X.coverageRankCandidate_iff source datum candidate).mpr
    (X.findAtlasCoverageRank_roundtrip source datum covered)
  (X.coverageRankWitness source datum candidate).get
    (X.coverageRankWitness_spec source datum candidate accepted).1

theorem findAtlasCoverage_spec (X : Atlas) (source : X.Element)
    (datum : X.cellData source.val.cell) (covered : X.Covered source datum) :
    (X.findAtlasCoverage source datum covered).Valid ∧
      X.coverageWitnessCovers source datum (X.findAtlasCoverage source datum covered) = true := by
  have accepted := (X.coverageRankCandidate_iff source datum _).mpr
    (X.findAtlasCoverageRank_roundtrip source datum covered)
  have covers : X.coverageWitnessCovers source datum (X.findAtlasCoverage source datum covered) = true :=
    (X.coverageRankWitness_spec source datum _ accepted).2 _ (Option.some_get _).symm
  exact ⟨coverageWitnessCovers_valid covers, covers⟩

end Datra.Executable.Atlas
