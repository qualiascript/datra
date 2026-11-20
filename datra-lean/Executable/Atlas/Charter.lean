import Executable.Atlas.Map

namespace Datra.Executable.Charter
open CategoryTheory

/-- The mathematical datum obtained by forgetting the canonical cache. -/
structure CellData (X : Atlas) (cell : PageElementCell) where
  value : X.cellData cell

@[ext] theorem CellData.ext {X : Atlas} {cell : PageElementCell} {a b : CellData X cell}
    (same : a.value = b.value) : a = b := by
  cases a
  cases b
  cases same
  rfl

def CellData.Valid {X : Atlas} (source : X.Element) (datum : CellData X source.val.cell) : Prop :=
  X.Covered source datum.value

abbrev CertifiedCellData (X : Atlas) (source : X.Element) :=
  {datum : CellData X source.val.cell // datum.Valid source}

/-- The invariant can be indexed by the same genuine cell as the runtime
family. Its existential occurrence only supplies a presentation of that cell. -/
def CellData.Covered {X : Atlas} {cell : PageElementCell} (datum : CellData X cell) : Prop :=
  ∃ (source : X.Element) (sameCell : cell = source.val.cell),
    X.Covered source (cast (congrArg X.cellData sameCell) datum.value)

theorem CellData.covered_iff_valid {X : Atlas} (source : X.Element)
    (datum : CellData X source.val.cell) : datum.Covered ↔ datum.Valid source := by
  constructor
  · rintro ⟨target, sameCell, covered⟩
    exact (X.covered_cast_iff sameCell datum.value).mp covered
  · intro covered
    exact ⟨source, rfl, covered⟩

abbrev IndexedCellData (X : Atlas) (cell : PageElementCell) :=
  {datum : CellData X cell // datum.Covered}

def indexedCellEquiv (X : Atlas) (source : X.Element) :
    IndexedCellData X source.val.cell ≃ CertifiedCellData X source where
  toFun datum := ⟨datum.val, (CellData.covered_iff_valid source datum.val).mp datum.property⟩
  invFun datum := ⟨datum.val, (CellData.covered_iff_valid source datum.val).mpr datum.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

def chartedUnrank (X : Atlas) (source : X.Element) (candidate : Nat) :
    Option (CertifiedCellData X source) :=
  (X.coveredPageElementAt source candidate).attach.map
    (fun datum => ⟨⟨datum.val⟩, Atlas.coveredPageElementAt_sound datum.property⟩)

/-- Charter uses the first coverage-enumeration rank, matching its executable
Dominion, rather than reusing the rank of the unrestricted source datum. -/
def chartedDominion (X : Atlas) (source : X.Element) : Dominion (CertifiedCellData X source) where
  rank datum := X.findAtlasCoverageRank source datum.val.value datum.property
  unrank := chartedUnrank X source
  coherence datum := by
    unfold chartedUnrank
    have h := X.findAtlasCoverageRank_roundtrip source datum.val.value datum.property
    rw [Option.attach_eq_some _ ⟨datum.val.value, h⟩]
    rfl

/-- The original insertion is only required to be a left inverse. A candidate
outside its image must pass the target rank check before it can be charted. -/
def chartedPreimage {X : Atlas} {source target : X.Element} (arrow : source ⟶ target)
    (datum : CertifiedCellData X target) : Option (CertifiedCellData X source) :=
  let original := X.data.action.normalizedMap arrow
  match original.preimage datum.val.value with
  | none => none
  | some candidate =>
      if same : (X.dataAt target).rank (original.map candidate) =
          (X.dataAt target).rank datum.val.value then
        some ⟨⟨candidate⟩, (X.covered_map_iff arrow candidate).mp
          (by rw [(X.dataAt target).rank_injective same]; exact datum.property)⟩
      else none

def chartedInsertion {X : Atlas} {source target : X.Element} (arrow : source ⟶ target) :
    DomanialInsertion (CertifiedCellData X source) (CertifiedCellData X target) where
  map datum := ⟨⟨(X.data.action.normalizedMap arrow).map datum.val.value⟩,
    (X.covered_map_iff arrow datum.val.value).mpr datum.property⟩
  preimage := chartedPreimage arrow
  leftInverse datum := by
    simp only [chartedPreimage, DomanialInsertion.leftInverse, dite_true]

theorem chartedPreimage_sound {X : Atlas} {source target : X.Element} (arrow : source ⟶ target)
    (datum : CertifiedCellData X target) (candidate : CertifiedCellData X source)
    (found : chartedPreimage arrow datum = some candidate) :
    (chartedInsertion arrow).map candidate = datum := by
  simp only [chartedPreimage] at found
  split at found
  · contradiction
  · split at found
    · rename_i value same
      have equal := Option.some.inj found
      subst candidate
      apply Subtype.ext
      apply CellData.ext
      exact (X.dataAt target).rank_injective same
    · contradiction

def indexedDominion (X : Atlas) (source : X.Element) : Dominion (IndexedCellData X source.val.cell) where
  rank datum := (chartedDominion X source).rank (indexedCellEquiv X source datum)
  unrank candidate := ((chartedDominion X source).unrank candidate).map (indexedCellEquiv X source).symm
  coherence datum := by simp only [Dominion.coherence, Option.map_some, Equiv.symm_apply_apply]

def indexedInsertion {X : Atlas} {source target : X.Element} (arrow : source ⟶ target) :
    DomanialInsertion (IndexedCellData X source.val.cell) (IndexedCellData X target.val.cell) where
  map datum := (indexedCellEquiv X target).symm
    ((chartedInsertion arrow).map (indexedCellEquiv X source datum))
  preimage datum := ((chartedInsertion arrow).preimage (indexedCellEquiv X target datum)).map
    (indexedCellEquiv X source).symm
  leftInverse datum := by
    simp only [Equiv.apply_symm_apply, DomanialInsertion.leftInverse, Option.map_some,
      Equiv.symm_apply_apply]

/-- Restrict the data family to covered values at each genuine cell; retain
the original pagination and its normalized data action. -/
def chartAtlas (X : Atlas) : Atlas where
  pagination := X.pagination
  cellData := IndexedCellData X
  data :=
    { action := { dataAt := indexedDominion X, mapData := indexedInsertion }
      identity := fun source datum => by
        apply Subtype.ext
        apply CellData.ext
        exact X.data.identity source.normalize datum.val.value
      composition := fun first second datum => by
        apply Subtype.ext
        apply CellData.ext
        exact X.data.composition (FolioData.ValidElement.normalizeArrow first)
          (FolioData.ValidElement.normalizeArrow second) datum.val.value
      coherence := fun source datum => by
        apply Subtype.ext
        apply CellData.ext
        change (X.data.action.normalizedMap
          (FolioData.ValidElement.normalizeArrow source.toNormalized)).map datum.val.value = _
        rw [AtlasAction.normalizedMap_normalizeArrow]
        exact X.data.coherence source datum.val.value
      disjoint := fun hp hv hb ho leftArrow rightArrow left right same => by
        have values := congrArg (fun datum => datum.val.value) same
        change (X.data.action.normalizedMap
          (FolioData.ValidElement.normalizeArrow leftArrow)).map left.val.value =
          (X.data.action.normalizedMap
            (FolioData.ValidElement.normalizeArrow rightArrow)).map right.val.value at values
        simp only [AtlasAction.normalizedMap_normalizeArrow] at values
        exact X.data.disjoint hp hv hb ho leftArrow rightArrow left.val.value right.val.value values }

theorem chartAtlas_originImage_value (X : Atlas) (source : X.Element)
    (datum : IndexedCellData X source.val.cell) :
    ((chartAtlas X).originImage source datum).val.value = X.originImage source datum.val.value := by
  change (X.data.action.normalizedMap
    (FolioData.ValidElement.normalizeArrow source.toOrigin)).map datum.val.value = _
  rw [AtlasAction.normalizedMap_normalizeArrow]
  rfl

-- ALIGN: CHARTER-ATLAS-COVERED.
theorem chartAtlas_covered (X : Atlas) (source : X.Element)
    (datum : IndexedCellData X source.val.cell) : (chartAtlas X).Covered source datum := by
  obtain ⟨index, regionDatum, sameRank⟩ :=
    (CellData.covered_iff_valid source datum.val).mp datum.property
  have regionCovered : X.Covered (X.territory index).element regionDatum :=
    ⟨index, regionDatum, rfl⟩
  let chartedRegion : IndexedCellData X (X.territory index).element.val.cell :=
    ⟨⟨regionDatum⟩, (CellData.covered_iff_valid _ _).mpr regionCovered⟩
  refine ⟨index, chartedRegion, ?_⟩
  apply ((chartAtlas X).originImageRank_eq_iff _ _ _ _).mpr
  apply Subtype.ext
  apply CellData.ext
  rw [chartAtlas_originImage_value, chartAtlas_originImage_value]
  exact (X.originImageRank_eq_iff _ _ _ _).mp sameRank

/-- Reuse the original Atlas search and wrap its retained region datum.
The charted Atlas has its own ranking, so the public constructor recomputes
its witness caches from that same region. -/
-- ALIGN: CHARTER-COVERAGE-WITNESS.
def chartCoverageWitness (X : Atlas) (source : X.Element)
    (datum : IndexedCellData X source.val.cell) :
    {w : (chartAtlas X).CoverageWitness // w.Valid ∧
      (chartAtlas X).coverageWitnessCovers source datum w = true} := by
  let covered := (CellData.covered_iff_valid source datum.val).mp datum.property
  let original := X.findAtlasCoverage source datum.val.value covered
  have originalSpec := X.findAtlasCoverage_spec source datum.val.value covered
  let chartedRegion : IndexedCellData X original.region.val.cell :=
    ⟨⟨original.datum⟩, (CellData.covered_iff_valid _ _).mpr originalSpec.1.covered⟩
  have conditions : original.region.normalize.val.page = (chartAtlas X).coverageFinalPage ∧
      (chartAtlas X).originImageRank source.normalize datum =
        (chartAtlas X).originImageRank original.region.normalize chartedRegion := by
    refine ⟨originalSpec.1.finalPage, ?_⟩
    apply ((chartAtlas X).originImageRank_eq_iff _ _ _ _).mpr
    apply Subtype.ext
    apply CellData.ext
    rw [chartAtlas_originImage_value, chartAtlas_originImage_value,
      X.originImage_normalize, X.originImage_normalize]
    exact originalSpec.1.originImage_eq originalSpec.2
  refine ⟨(chartAtlas X).atlasCoverageWitness source original.region datum chartedRegion conditions, ?_⟩
  have checked := (chartAtlas X).atlasCoverageWitness_spec source original.region
    datum chartedRegion conditions
  refine ⟨checked.1, ?_⟩
  simpa only [Atlas.coverageWitnessCovers, Atlas.originImageRank_normalize] using checked.2

def chartAtlasMap (X : Atlas) : AtlasMap (chartAtlas X) :=
  AtlasMap.atlasMap (chartAtlas X)
    (chartCoverageWitness X (FolioData.ValidElement.originElement X.pages))

/-- The runtime carrier retains a datum and its canonical coverage code. -/
structure CachedCellData (X : Atlas) (cell : PageElementCell) where
  value : X.cellData cell
  code : Nat

def CachedCellData.Valid {X : Atlas} (source : X.Element)
    (datum : CachedCellData X source.val.cell) : Prop :=
  X.coverageRankCanonical source datum.value datum.code = true

abbrev CertifiedCachedCellData (X : Atlas) (source : X.Element) :=
  {datum : CachedCellData X source.val.cell // datum.Valid source}

-- ALIGN: CHARTER-CELL-CONSTRUCTOR.
def chartCellData {X : Atlas} (source : X.Element) (datum : X.cellData source.val.cell)
    (witness : {w : X.CoverageWitness // w.Valid})
    (covers : X.coverageWitnessCovers source datum witness.val = true) : CertifiedCachedCellData X source :=
  let valid := (X.coverageWitnessValid_iff witness.val).mpr witness.property
  ⟨⟨datum, X.atlasCoverageRank source datum witness.val valid covers⟩,
    X.atlasCoverageRank_canonical source datum witness.val valid covers⟩

-- ALIGN: CHARTER-CELL-CACHE-EXTENSIONALITY.
theorem CachedCellData.ext {X : Atlas} {source : X.Element}
    {left right : CachedCellData X source.val.cell}
    (leftValid : left.Valid source) (rightValid : right.Valid source)
    (same : left.value = right.value) : left = right := by
  rcases left with ⟨left, leftCode⟩
  rcases right with ⟨right, rightCode⟩
  simp only at same
  subst right
  have codes := X.coverageRankCanonicalUnique source left leftCode rightCode leftValid rightValid
  subst rightCode
  rfl

def CachedCellData.accepted {X : Atlas} {source : X.Element} {datum : CachedCellData X source.val.cell}
    (valid : datum.Valid source) : X.coverageRankCandidate source datum.value datum.code = true := by
  have selected : X.atlasCoverageRankWithin source datum.value datum.code = some datum.code := by
    simpa only [CachedCellData.Valid, Atlas.coverageRankCanonical, beq_iff_eq] using valid
  exact (Atlas.atlasCoverageRankWithin_sound selected).2

-- ALIGN: CHARTER-CELL-MEMBERSHIP.
def chartedDatumValid (X : Atlas) (source : X.Element)
    (datum : CachedCellData X source.val.cell) : Bool :=
  X.coverageRankCandidate source datum.value datum.code &&
    X.coverageRankCanonical source datum.value datum.code

theorem chartedDatumValid_iff (X : Atlas) (source : X.Element)
    (datum : CachedCellData X source.val.cell) : chartedDatumValid X source datum = true ↔ datum.Valid source := by
  simp only [chartedDatumValid, Bool.and_eq_true]
  constructor
  · exact fun valid => valid.2
  · exact fun valid => ⟨CachedCellData.accepted valid, valid⟩

def chartedCellCoverage {X : Atlas} (source : X.Element) (datum : CachedCellData X source.val.cell)
    (accepted : X.coverageRankCandidate source datum.value datum.code = true) : X.CoverageWitness :=
  (X.coverageRankWitness source datum.value datum.code).get
    (X.coverageRankWitness_spec source datum.value datum.code accepted).1

-- ALIGN: CHARTER-CELL-COVERAGE-CACHE.
theorem chartedCellCoverage_spec {X : Atlas} (source : X.Element) (datum : CachedCellData X source.val.cell)
    (accepted : X.coverageRankCandidate source datum.value datum.code = true) :
    X.coverageWitnessCovers source datum.value (chartedCellCoverage source datum accepted) = true :=
  (X.coverageRankWitness_spec source datum.value datum.code accepted).2 _ (Option.some_get _).symm

def CachedCellData.covered {X : Atlas} {source : X.Element} {datum : CachedCellData X source.val.cell}
    (valid : datum.Valid source) : X.Covered source datum.value :=
  Atlas.coveredPageElementAt_sound ((X.coverageRankCandidate_iff source datum.value datum.code).mp (CachedCellData.accepted valid))

/-- The cache has no effect on the covered carrier's mathematical equality. -/
def cachedCellEquiv (X : Atlas) (source : X.Element) :
    CertifiedCachedCellData X source ≃ CertifiedCellData X source where
  toFun datum := ⟨⟨datum.val.value⟩, CachedCellData.covered datum.property⟩
  invFun datum :=
    let witness := X.findAtlasCoverage source datum.val.value datum.property
    let checked := X.findAtlasCoverage_spec source datum.val.value datum.property
    chartCellData source datum.val.value ⟨witness, checked.1⟩ checked.2
  left_inv datum := by
    apply Subtype.ext
    apply CachedCellData.ext
    · exact (chartCellData source datum.val.value _ _).property
    · exact datum.property
    · rfl
  right_inv datum := by
    apply Subtype.ext
    apply CellData.ext
    rfl

theorem CachedCellData.rank_spec {X : Atlas} {source : X.Element}
    {datum : CachedCellData X source.val.cell} (valid : datum.Valid source) :
    datum.code = X.findAtlasCoverageRank source datum.value (CachedCellData.covered valid) := by
  apply Atlas.atlasCoverageRankWithin_eq_find
  simpa only [CachedCellData.Valid, Atlas.coverageRankCanonical, beq_iff_eq] using valid

/-- Finite decoding canonicalizes the successful input code before storing it. -/
def cachedUnrank (X : Atlas) (source : X.Element) (candidate : Nat) :
    Option (CertifiedCachedCellData X source) :=
  match found : X.coverageAt source candidate with
  | none => none
  | some (datum, witness) =>
    some (chartCellData source datum ⟨witness, (Atlas.coverageAt_sound found).1⟩
      (Atlas.coverageAt_sound found).2)

theorem cachedUnrank_eq (X : Atlas) (source : X.Element) (candidate : Nat) :
    cachedUnrank X source candidate =
      (chartedUnrank X source candidate).map (cachedCellEquiv X source).symm := by
  unfold cachedUnrank
  split
  · rename_i found
    have decoded : X.coveredPageElementAt source candidate = none :=
      congrArg (Option.map Prod.fst) found
    unfold chartedUnrank
    rw [Option.attach_eq_none_iff.mpr decoded]
    rfl
  · rename_i datum witness found
    have decoded : X.coveredPageElementAt source candidate = some datum := by
      simp [Atlas.coveredPageElementAt, found]
    unfold chartedUnrank
    rw [Option.attach_eq_some _ ⟨datum, decoded⟩]
    simp only [Option.map_some]
    congr 1
    apply Subtype.ext
    apply CachedCellData.ext
    · exact (chartCellData source datum _ _).property
    · exact ((cachedCellEquiv X source).symm _).property
    · rfl

/-- The executable rank reads the retained code; unranking uses finite decoding. -/
def cachedDominion (X : Atlas) (source : X.Element) : Dominion (CertifiedCachedCellData X source) where
  rank datum := datum.val.code
  unrank := cachedUnrank X source
  coherence datum := by
    rw [cachedUnrank_eq, CachedCellData.rank_spec datum.property]
    change ((chartedDominion X source).unrank
      ((chartedDominion X source).rank (cachedCellEquiv X source datum))).map _ = _
    rw [Dominion.coherence, Option.map_some, Equiv.symm_apply_apply]

-- ALIGN: CHARTER-DOMINION-ROUNDTRIP.
theorem cachedDominion_roundtrip (X : Atlas) (source : X.Element)
    (datum : CertifiedCachedCellData X source) :
    (cachedDominion X source).unrank ((cachedDominion X source).rank datum) = some datum :=
  (cachedDominion X source).coherence datum

theorem cachedDominion_rank (X : Atlas) (source : X.Element)
    (datum : CertifiedCachedCellData X source) :
    (cachedDominion X source).rank datum =
      (chartedDominion X source).rank (cachedCellEquiv X source datum) :=
  CachedCellData.rank_spec datum.property

/-- An Atlas data arrow preserves the canonical code together with the datum. -/
-- ALIGN: CHARTER-CELL-CACHE-TRANSPORT.
def cachedDataMap {X : Atlas} {source target : X.Element} (arrow : source ⟶ target)
    (datum : CertifiedCachedCellData X source) : CertifiedCachedCellData X target :=
  ⟨⟨(X.data.action.normalizedMap arrow).map datum.val.value, datum.val.code⟩, by
    change X.coverageRankCanonical target _ _ = true
    rw [← (X.coverageRankAlongArrow arrow datum.val.value datum.val.code).2]
    exact datum.property⟩

def cachedDataPreimage {X : Atlas} {source target : X.Element} (arrow : source ⟶ target)
    (datum : CertifiedCachedCellData X target) : Option (CertifiedCachedCellData X source) :=
  let original := X.data.action.normalizedMap arrow
  match original.preimage datum.val.value with
  | none => none
  | some candidate =>
    if same : (X.dataAt target).rank (original.map candidate) =
        (X.dataAt target).rank datum.val.value then
      some ⟨⟨candidate, datum.val.code⟩, by
        change X.coverageRankCanonical source candidate datum.val.code = true
        rw [(X.coverageRankAlongArrow arrow candidate datum.val.code).2,
          (X.dataAt target).rank_injective same]
        exact datum.property⟩
    else none

-- ALIGN: CHARTER-DATA-INSERTION.
def cachedDataInsertion {X : Atlas} {source target : X.Element} (arrow : source ⟶ target) :
    DomanialInsertion (CertifiedCachedCellData X source) (CertifiedCachedCellData X target) where
  map := cachedDataMap arrow
  preimage := cachedDataPreimage arrow
  leftInverse datum := by
    simp only [cachedDataPreimage, cachedDataMap, DomanialInsertion.leftInverse, dite_true]

/-- Forgetting the cache commutes with both directions of the data insertion. -/
theorem cachedDataMap_interpretation {X : Atlas} {source target : X.Element} (arrow : source ⟶ target)
    (datum : CertifiedCachedCellData X source) :
    cachedCellEquiv X target (cachedDataMap arrow datum) =
      (chartedInsertion arrow).map (cachedCellEquiv X source datum) := rfl

theorem cachedDataPreimage_interpretation {X : Atlas} {source target : X.Element}
    (arrow : source ⟶ target) (datum : CertifiedCachedCellData X target) :
    (cachedDataPreimage arrow datum).map (cachedCellEquiv X source) =
      chartedPreimage arrow (cachedCellEquiv X target datum) := by
  simp only [cachedDataPreimage, chartedPreimage, cachedCellEquiv, Equiv.coe_fn_mk]
  split
  · rfl
  · split <;> rfl

-- ALIGN: CHARTER-DATA-INVERSE-SOUND.
theorem cachedDataPreimage_sound {X : Atlas} {source target : X.Element} (arrow : source ⟶ target)
    (datum : CertifiedCachedCellData X target) (candidate : CertifiedCachedCellData X source)
    (found : cachedDataPreimage arrow datum = some candidate) :
    (cachedDataInsertion arrow).map candidate = datum := by
  have interpreted : chartedPreimage arrow (cachedCellEquiv X target datum) =
      some (cachedCellEquiv X source candidate) := by
    rw [← cachedDataPreimage_interpretation, found]
    rfl
  apply (cachedCellEquiv X target).injective
  change cachedCellEquiv X target (cachedDataMap arrow candidate) = _
  rw [cachedDataMap_interpretation]
  exact chartedPreimage_sound arrow _ _ interpreted

/-- A total partial inverse is supplied explicitly; uncovered data need not
be searched for a final-region witness. -/
def counitInsertion {X : Atlas} {source : X.Element}
    (backward : X.cellData source.val.cell → Option (CertifiedCellData X source))
    (leftInverse : ∀ datum, backward datum.val.value = some datum) :
    DomanialInsertion (CertifiedCellData X source) (X.cellData source.val.cell) where
  map datum := datum.val.value
  preimage := backward
  leftInverse := leftInverse

/-- Restrict a complete transversal component. Unlike an Atlas data arrow,
it need not reflect coverage, so its candidate passes through the explicit
inverse of the source's covered-subtype inclusion. -/
def chartMapInsertion {X Y : Atlas} {source : X.Element} {target : Y.Element}
    (original : DomanialInsertion (X.cellData source.val.cell) (Y.cellData target.val.cell))
    (preserves : ∀ datum, X.Covered source datum → Y.Covered target (original.map datum))
    (backward : X.cellData source.val.cell → Option (CertifiedCellData X source))
    (leftInverse : ∀ datum, backward datum.val.value = some datum) :
    DomanialInsertion (CertifiedCellData X source) (CertifiedCellData Y target) where
  map datum := ⟨⟨original.map datum.val.value⟩, preserves datum.val.value datum.property⟩
  preimage datum := (original.preimage datum.val.value).bind backward
  leftInverse datum := by simp only [original.leftInverse, Option.bind_some, leftInverse]

/-- Inverse contracts quantify over canonical cached data, not arbitrary
pairs whose projection could never be injective. -/
-- ALIGN: CHARTER-COUNIT-INSERTION.
def cachedCounitInsertion {X : Atlas} {source : X.Element}
    (backward : X.cellData source.val.cell → Option (CertifiedCachedCellData X source))
    (leftInverse : ∀ datum, backward datum.val.value = some datum) :
    DomanialInsertion (CertifiedCachedCellData X source) (X.cellData source.val.cell) where
  map datum := datum.val.value
  preimage := backward
  leftInverse := leftInverse

-- ALIGN: CHARTER-MAP-INSERTION.
def cachedMapInsertion {X Y : Atlas} {source : X.Element} {target : Y.Element}
    (original : DomanialInsertion (X.cellData source.val.cell) (Y.cellData target.val.cell))
    (forward : CertifiedCachedCellData X source → CertifiedCachedCellData Y target)
    (forwardValue : ∀ datum, (forward datum).val.value = original.map datum.val.value)
    (backward : X.cellData source.val.cell → Option (CertifiedCachedCellData X source))
    (leftInverse : ∀ datum, backward datum.val.value = some datum) :
    DomanialInsertion (CertifiedCachedCellData X source) (CertifiedCachedCellData Y target) where
  map := forward
  preimage datum := (original.preimage datum.val.value).bind backward
  leftInverse datum := by rw [forwardValue, original.leftInverse, Option.bind_some, leftInverse]

-- ALIGN: CHARTER-MAP-INVERSE.
theorem cachedMapInsertion_preimage {X Y : Atlas} {source : X.Element} {target : Y.Element}
    (original : DomanialInsertion (X.cellData source.val.cell) (Y.cellData target.val.cell))
    (forward : CertifiedCachedCellData X source → CertifiedCachedCellData Y target)
    (forwardValue : ∀ datum, (forward datum).val.value = original.map datum.val.value)
    (backward : X.cellData source.val.cell → Option (CertifiedCachedCellData X source))
    (leftInverse : ∀ datum, backward datum.val.value = some datum)
    (datum : CertifiedCachedCellData Y target) :
    (cachedMapInsertion original forward forwardValue backward leftInverse).preimage datum =
      (original.preimage datum.val.value).bind backward := rfl

def forgetCachedInverse {X : Atlas} {source : X.Element}
    (backward : X.cellData source.val.cell → Option (CertifiedCachedCellData X source))
    (datum : X.cellData source.val.cell) : Option (CertifiedCellData X source) :=
  (backward datum).map (cachedCellEquiv X source)

theorem forgetCachedInverse_leftInverse {X : Atlas} {source : X.Element}
    (backward : X.cellData source.val.cell → Option (CertifiedCachedCellData X source))
    (leftInverse : ∀ datum, backward datum.val.value = some datum)
    (datum : CertifiedCellData X source) : forgetCachedInverse backward datum.val.value = some datum := by
  have law := congrArg (Option.map (cachedCellEquiv X source))
    (leftInverse ((cachedCellEquiv X source).symm datum))
  simpa only [Option.map_some, Equiv.apply_symm_apply] using law

theorem cachedCounitInsertion_reindex {X : Atlas} {source : X.Element}
    (backward : X.cellData source.val.cell → Option (CertifiedCachedCellData X source))
    (leftInverse : ∀ datum, backward datum.val.value = some datum) :
    (cachedCounitInsertion backward leftInverse).reindex (cachedCellEquiv X source) (Equiv.refl _) =
      counitInsertion (forgetCachedInverse backward) (forgetCachedInverse_leftInverse backward leftInverse) := by
  apply DomanialInsertion.ext <;> rfl

theorem cachedMapInsertion_map_interpretation {X Y : Atlas} {source : X.Element} {target : Y.Element}
    (original : DomanialInsertion (X.cellData source.val.cell) (Y.cellData target.val.cell))
    (forward : CertifiedCachedCellData X source → CertifiedCachedCellData Y target)
    (forwardValue : ∀ datum, (forward datum).val.value = original.map datum.val.value)
    (preserves : ∀ datum, X.Covered source datum → Y.Covered target (original.map datum))
    (backward : X.cellData source.val.cell → Option (CertifiedCachedCellData X source))
    (leftInverse : ∀ datum, backward datum.val.value = some datum)
    (datum : CertifiedCachedCellData X source) :
    cachedCellEquiv Y target ((cachedMapInsertion original forward forwardValue backward leftInverse).map datum) =
      (chartMapInsertion original preserves (forgetCachedInverse backward)
        (forgetCachedInverse_leftInverse backward leftInverse)).map (cachedCellEquiv X source datum) := by
  apply Subtype.ext
  apply CellData.ext
  exact forwardValue datum

theorem cachedMapInsertion_preimage_interpretation {X Y : Atlas} {source : X.Element} {target : Y.Element}
    (original : DomanialInsertion (X.cellData source.val.cell) (Y.cellData target.val.cell))
    (forward : CertifiedCachedCellData X source → CertifiedCachedCellData Y target)
    (forwardValue : ∀ datum, (forward datum).val.value = original.map datum.val.value)
    (preserves : ∀ datum, X.Covered source datum → Y.Covered target (original.map datum))
    (backward : X.cellData source.val.cell → Option (CertifiedCachedCellData X source))
    (leftInverse : ∀ datum, backward datum.val.value = some datum)
    (datum : CertifiedCachedCellData Y target) :
    ((cachedMapInsertion original forward forwardValue backward leftInverse).preimage datum).map
        (cachedCellEquiv X source) =
      (chartMapInsertion original preserves (forgetCachedInverse backward)
        (forgetCachedInverse_leftInverse backward leftInverse)).preimage (cachedCellEquiv Y target datum) := by
  simp only [cachedMapInsertion, chartMapInsertion, Option.map_bind]
  rfl

def completeAction {X Y : Atlas} (f : Atlas.Transversal X Y) : PrimitiveAtlasMorphism X Y :=
  f.underlying.underlying.hom.materialize.action.normalized

theorem completeAction_preserves {X Y : Atlas} (f : Atlas.Transversal X Y) (source : X.Element)
    (datum : X.cellData source.val.cell) (covered : X.Covered source datum) :
    Y.Covered ((completeAction f).object source) ((completeAction f).component source |>.map datum) := by
  have result := f.preservesData ⟨source, datum⟩ covered
  have image := congrArg (fun image : Atlas.Morphism.Image X Y source =>
    (⟨image.1, image.2.map datum⟩ : Y.DataElement))
      (f.underlying.underlying.hom.materialize.action_image source)
  change (Atlas.Hom.mapData f.underlying.underlying.hom ⟨source, datum⟩).Covered at result
  change (⟨(completeAction f).object source, ((completeAction f).component source).map datum⟩ : Y.DataElement) =
    f.underlying.underlying.hom.mapData ⟨source, datum⟩ at image
  rw [← image] at result
  exact result

def indexedMapInsertion {X Y : Atlas} {source : X.Element} {target : Y.Element}
    (original : DomanialInsertion (X.cellData source.val.cell) (Y.cellData target.val.cell))
    (preserves : ∀ datum, X.Covered source datum → Y.Covered target (original.map datum))
    (backward : X.cellData source.val.cell → Option (IndexedCellData X source.val.cell))
    (leftInverse : ∀ datum, backward datum.val.value = some datum) :
    DomanialInsertion (IndexedCellData X source.val.cell) (IndexedCellData Y target.val.cell) :=
  let certified := chartMapInsertion original preserves
    (fun datum => (backward datum).map (indexedCellEquiv X source))
    (by
      intro datum
      change (backward ((indexedCellEquiv X source).symm datum).val.value).map
        (indexedCellEquiv X source) = some datum
      rw [leftInverse ((indexedCellEquiv X source).symm datum)]
      rfl)
  { map datum := (indexedCellEquiv Y target).symm (certified.map (indexedCellEquiv X source datum))
    preimage datum := (certified.preimage (indexedCellEquiv Y target datum)).map (indexedCellEquiv X source).symm
    leftInverse datum := by
      simp only [Equiv.apply_symm_apply, DomanialInsertion.leftInverse, Option.map_some,
        Equiv.symm_apply_apply] }

def chartMorphism {X Y : Atlas} (f : Atlas.Transversal X Y)
    (backward : (source : X.Element) → X.cellData source.val.cell → Option (IndexedCellData X source.val.cell))
    (leftInverse : ∀ source datum, backward source datum.val.value = some datum) :
    PrimitiveAtlasMorphism (chartAtlas X) (chartAtlas Y) where
  object := (completeAction f).object
  component source := indexedMapInsertion ((completeAction f).component source)
    (completeAction_preserves f source) (backward source) (leftInverse source)
  arrow := (completeAction f).arrow
  naturality := by
    intro source target arrow datum
    apply Subtype.ext
    apply CellData.ext
    change ((completeAction f).component target.normalize).map
        ((X.data.action.normalizedMap (FolioData.ValidElement.normalizeArrow arrow)).map datum.val.value) =
      (Y.data.action.normalizedMap (FolioData.ValidElement.normalizeArrow ((completeAction f).arrow arrow))).map
        (((completeAction f).component source.normalize).map datum.val.value)
    rw [AtlasAction.normalizedMap_normalizeArrow, AtlasAction.normalizedMap_normalizeArrow]
    exact (completeAction f).naturality arrow datum.val.value

def chartHom {X Y : Atlas} (f : Atlas.Transversal X Y)
    (backward : (source : X.Element) → X.cellData source.val.cell → Option (IndexedCellData X source.val.cell))
    (leftInverse : ∀ source datum, backward source datum.val.value = some datum) :
    Atlas.Hom (chartAtlas X) (chartAtlas Y) := .primitive (.primitive (chartMorphism f backward leftInverse))

theorem chartHom_object {X Y : Atlas} (f : Atlas.Transversal X Y)
    (backward : (source : X.Element) → X.cellData source.val.cell → Option (IndexedCellData X source.val.cell))
    (leftInverse : ∀ source datum, backward source datum.val.value = some datum) (source : X.Element) :
    (chartHom f backward leftInverse).mapObject source = f.underlying.underlying.hom.mapObject source :=
  congrArg Sigma.fst ((Atlas.Morphism.normalized_action_image
    f.underlying.underlying.hom.materialize.action source).trans
      (f.underlying.underlying.hom.materialize.action_image source))

def chartTransposal {X Y : Atlas} (f : Atlas.Transversal X Y)
    (backward : (source : X.Element) → X.cellData source.val.cell → Option (IndexedCellData X source.val.cell))
    (leftInverse : ∀ source datum, backward source datum.val.value = some datum) :
    Atlas.Transposal (chartAtlas X) (chartAtlas Y) where
  hom := chartHom f backward leftInverse
  objectInsertion := f.underlying.underlying.objectInsertion
  object_eq source := by
    rw [f.underlying.underlying.object_eq]
    apply Subtype.ext
    exact (chartHom_object f backward leftInverse source.val).symm

def chartOrdered {X Y : Atlas} (f : Atlas.Transversal X Y)
    (backward : (source : X.Element) → X.cellData source.val.cell → Option (IndexedCellData X source.val.cell))
    (leftInverse : ∀ source datum, backward source datum.val.value = some datum) :
    Atlas.OrderedTransposal (chartAtlas X) (chartAtlas Y) :=
  .primitive (chartTransposal f backward leftInverse) (fun source target h =>
    f.underlying.preservesOrder source target h)

def chartTransversal {X Y : Atlas} (f : Atlas.Transversal X Y)
    (backward : (source : X.Element) → X.cellData source.val.cell → Option (IndexedCellData X source.val.cell))
    (leftInverse : ∀ source datum, backward source datum.val.value = some datum) :
    Atlas.Transversal (chartAtlas X) (chartAtlas Y) :=
  Atlas.atlasTransversal (chartOrdered f backward leftInverse) (fun covered =>
    let image := (chartHom f backward leftInverse).mapData covered.data
    chartCoverageWitness Y image.1 image.2)

/-- The public arrow keeps the full-subcategory wrapper used by Haskell. -/
def chartMap {X Y : Atlas} (f : Atlas.Transversal X Y)
    (backward : (source : X.Element) → X.cellData source.val.cell → Option (IndexedCellData X source.val.cell))
    (leftInverse : ∀ source datum, backward source datum.val.value = some datum) :
    AtlasTransversalMap (chartAtlas X) (chartAtlas Y) :=
  ⟨chartTransversal f backward leftInverse⟩

def forgetData {X : Atlas} (datum : (chartAtlas X).DataElement) : X.DataElement :=
  ⟨datum.1, datum.2.val.value⟩

theorem forgetData_injective (X : Atlas) : Function.Injective (@forgetData X) := by
  rintro ⟨source, datum⟩ ⟨target, other⟩ same
  have cells := congrArg Sigma.fst same
  change source = target at cells
  subst target
  have values := eq_of_heq (Sigma.mk.inj same).2
  have dataEqual : datum = other := Subtype.ext (CellData.ext values)
  subst other
  rfl

theorem chartHom_mapData {X Y : Atlas} (f : Atlas.Transversal X Y)
    (backward : (source : X.Element) → X.cellData source.val.cell → Option (IndexedCellData X source.val.cell))
    (leftInverse : ∀ source datum, backward source datum.val.value = some datum)
    (source : (chartAtlas X).DataElement) :
    forgetData ((chartHom f backward leftInverse).mapData source) =
      f.underlying.underlying.hom.mapData (forgetData source) :=
  congrArg (fun image : Atlas.Morphism.Image X Y source.1 =>
    (⟨image.1, image.2.map source.2.val.value⟩ : Y.DataElement))
      ((Atlas.Morphism.normalized_action_image f.underlying.underlying.hom.materialize.action source.1).trans
        (f.underlying.underlying.hom.materialize.action_image source.1))

theorem chartHom_page {X Y : Atlas} (f : Atlas.Transversal X Y)
    (backward : (source : X.Element) → X.cellData source.val.cell → Option (IndexedCellData X source.val.cell))
    (leftInverse : ∀ source datum, backward source datum.val.value = some datum)
    (source : X.toSemantics.El) :
    (chartHom f backward leftInverse).finiteSemantics.Pa.obj source =
      f.underlying.underlying.hom.finiteSemantics.Pa.obj source := by
  have charted := (chartTransposal f backward leftInverse).mapObject_interpretation
    (Atlas.TransposalElement.fromSemantics (chartAtlas X) source)
  have original := f.underlying.underlying.mapObject_interpretation
    (Atlas.TransposalElement.fromSemantics X source)
  simp only [Atlas.TransposalElement.toSemantics_fromSemantics] at charted original
  exact charted.symm.trans original

def counitMorphism (X : Atlas)
    (backward : (source : X.Element) → X.cellData source.val.cell → Option (IndexedCellData X source.val.cell))
    (leftInverse : ∀ source datum, backward source datum.val.value = some datum) :
    PrimitiveAtlasMorphism (chartAtlas X) X where
  object := id
  component source := ⟨fun datum => datum.val.value, backward source, leftInverse source⟩
  arrow := fun arrow => FolioData.ValidElement.normalizeArrow (FolioData.ValidElement.normalizeArrow arrow)
  naturality := by
    intro source target arrow datum
    change (X.data.action.normalizedMap (FolioData.ValidElement.normalizeArrow arrow)).map datum.val.value =
      (X.data.action.normalizedMap (FolioData.ValidElement.normalizeArrow
        (FolioData.ValidElement.normalizeArrow arrow))).map datum.val.value
    simp only [AtlasAction.normalizedMap_normalizeArrow]

def counitHom (X : Atlas)
    (backward : (source : X.Element) → X.cellData source.val.cell → Option (IndexedCellData X source.val.cell))
    (leftInverse : ∀ source datum, backward source datum.val.value = some datum) :
    Atlas.Hom (chartAtlas X) X := .primitive (.primitive (counitMorphism X backward leftInverse))

def counitTransposal (X : Atlas)
    (backward : (source : X.Element) → X.cellData source.val.cell → Option (IndexedCellData X source.val.cell))
    (leftInverse : ∀ source datum, backward source datum.val.value = some datum) :
    Atlas.Transposal (chartAtlas X) X where
  hom := counitHom X backward leftInverse
  objectInsertion := DomanialInsertion.identity _
  object_eq source := Subtype.ext ((source.val.normalize_idempotent.trans source.property).symm)

def counitOrdered (X : Atlas)
    (backward : (source : X.Element) → X.cellData source.val.cell → Option (IndexedCellData X source.val.cell))
    (leftInverse : ∀ source datum, backward source datum.val.value = some datum) :
    Atlas.OrderedTransposal (chartAtlas X) X :=
  .primitive (counitTransposal X backward leftInverse) (fun _ _ h => h)

def chartCounit (X : Atlas)
    (backward : (source : X.Element) → X.cellData source.val.cell → Option (IndexedCellData X source.val.cell))
    (leftInverse : ∀ source datum, backward source datum.val.value = some datum) :
    Atlas.Transversal (chartAtlas X) X :=
  Atlas.atlasTransversal (counitOrdered X backward leftInverse) (fun covered =>
    let image := (counitHom X backward leftInverse).mapData covered.data
    let valid : X.Covered image.1 image.2 := by
      change X.Covered covered.val.source.normalize.normalize covered.val.datum.val.value
      rw [X.covered_normalize_iff, X.covered_normalize_iff]
      exact (CellData.covered_iff_valid (X := X) covered.val.source covered.val.datum.val).mp covered.val.datum.property
    ⟨X.findAtlasCoverage image.1 image.2 valid, X.findAtlasCoverage_spec image.1 image.2 valid⟩)

theorem counitHom_page (X : Atlas)
    (backward : (source : X.Element) → X.cellData source.val.cell → Option (IndexedCellData X source.val.cell))
    (leftInverse : ∀ source datum, backward source datum.val.value = some datum)
    (source : X.toSemantics.El) : (counitHom X backward leftInverse).finiteSemantics.Pa.obj source = source := by
  have page := (counitTransposal X backward leftInverse).mapObject_interpretation
    (Atlas.TransposalElement.fromSemantics (chartAtlas X) source)
  change (Atlas.TransposalElement.fromSemantics X source).toSemantics =
    (counitHom X backward leftInverse).finiteSemantics.Pa.obj
      (Atlas.TransposalElement.fromSemantics (chartAtlas X) source).toSemantics at page
  simpa only [Atlas.TransposalElement.toSemantics_fromSemantics] using page.symm

def unitMorphism {X : Atlas} (value : AtlasMap X) : PrimitiveAtlasMorphism X (chartAtlas X) where
  object := id
  component source :=
    { map datum := ⟨⟨datum⟩, (CellData.covered_iff_valid source _).mpr (value.allCovered source datum)⟩
      preimage datum := some datum.val.value
      leftInverse _ := rfl }
  arrow := fun arrow => FolioData.ValidElement.normalizeArrow (FolioData.ValidElement.normalizeArrow arrow)
  naturality := by
    intro source target arrow datum
    apply Subtype.ext
    apply CellData.ext
    change (X.data.action.normalizedMap arrow).map datum =
      (X.data.action.normalizedMap (FolioData.ValidElement.normalizeArrow
        (FolioData.ValidElement.normalizeArrow (FolioData.ValidElement.normalizeArrow arrow)))).map datum
    simp only [AtlasAction.normalizedMap_normalizeArrow]

def unitHom {X : Atlas} (value : AtlasMap X) : Atlas.Hom X (chartAtlas X) :=
  .primitive (.primitive (unitMorphism value))

def unitTransposal {X : Atlas} (value : AtlasMap X) : Atlas.Transposal X (chartAtlas X) where
  hom := unitHom value
  objectInsertion := DomanialInsertion.identity _
  object_eq source := Subtype.ext ((source.val.normalize_idempotent.trans source.property).symm)

def unitOrdered {X : Atlas} (value : AtlasMap X) : Atlas.OrderedTransposal X (chartAtlas X) :=
  .primitive (unitTransposal value) (fun _ _ h => h)

def chartUnit {X : Atlas} (value : AtlasMap X) : Atlas.Transversal X (chartAtlas X) :=
  Atlas.atlasTransversal (unitOrdered value) (fun covered =>
    let image := (unitHom value).mapData covered.data
    chartCoverageWitness X image.1 image.2)

def liftTransversal {X Y : Atlas} (value : AtlasMap X) (f : Atlas.Transversal X Y) :
    Atlas.Transversal X (chartAtlas Y) :=
  Atlas.Transversal.comp
    (chartTransversal f (fun source datum => some ((unitMorphism value).component source |>.map datum))
      (fun _ _ => rfl))
    (chartUnit value)

def lowerTransversal {X Y : Atlas}
    (backward : (source : Y.Element) → Y.cellData source.val.cell → Option (IndexedCellData Y source.val.cell))
    (leftInverse : ∀ source datum, backward source datum.val.value = some datum)
    (f : Atlas.Transversal X (chartAtlas Y)) : Atlas.Transversal X Y :=
  Atlas.Transversal.comp (chartCounit Y backward leftInverse) f

def chartLift {X Y : Atlas} (value : AtlasMap X) (f : Atlas.Transversal X Y) :
    AtlasTransversalMap X (chartAtlas Y) :=
  ⟨liftTransversal value f⟩

def chartLower {X Y : Atlas}
    (backward : (source : Y.Element) → Y.cellData source.val.cell → Option (IndexedCellData Y source.val.cell))
    (leftInverse : ∀ source datum, backward source datum.val.value = some datum)
    (f : AtlasTransversalMap X (chartAtlas Y)) : Atlas.Transversal X Y :=
  lowerTransversal backward leftInverse f.transversal

theorem unitHom_page {X : Atlas} (value : AtlasMap X) (source : X.toSemantics.El) :
    (unitHom value).finiteSemantics.Pa.obj source = source := by
  have page := (unitTransposal value).mapObject_interpretation
    (Atlas.TransposalElement.fromSemantics X source)
  change (Atlas.TransposalElement.fromSemantics (chartAtlas X) source).toSemantics =
    (unitHom value).finiteSemantics.Pa.obj (Atlas.TransposalElement.fromSemantics X source).toSemantics at page
  simpa only [Atlas.TransposalElement.toSemantics_fromSemantics] using page.symm

theorem counitInsertion_value {X : Atlas} {source : X.Element}
    (backward : X.cellData source.val.cell → Option (CertifiedCellData X source))
    (leftInverse : ∀ datum, backward datum.val.value = some datum)
    (datum : CertifiedCellData X source) :
    (counitInsertion backward leftInverse).map datum = datum.val.value := rfl

theorem counitInsertion_preimage {X : Atlas} {source : X.Element}
    (backward : X.cellData source.val.cell → Option (CertifiedCellData X source))
    (leftInverse : ∀ datum, backward datum.val.value = some datum)
    (datum : X.cellData source.val.cell) :
    (counitInsertion backward leftInverse).preimage datum = backward datum := rfl

def mapCellData {X Y : Atlas} {source target : PageElementCell}
    (f : X.cellData source → Y.cellData target) (code : Y.cellData target → Nat)
    (datum : CachedCellData X source) : CachedCellData Y target :=
  ⟨f datum.value, code (f datum.value)⟩

-- ALIGN: CHARTER-FUNCTOR-IDENTITY.
theorem mapCellData_identity {X : Atlas} {cell : PageElementCell}
    (code : X.cellData cell → Nat) (datum : CachedCellData X cell) (canonical : code datum.value = datum.code) :
    mapCellData id code datum = datum := by
  cases datum
  simp_all [mapCellData]

-- ALIGN: CHARTER-FUNCTOR-COMPOSITION.
theorem mapCellData_composition {X Y Z : Atlas} {source middle target : PageElementCell}
    (first : X.cellData source → Y.cellData middle) (second : Y.cellData middle → Z.cellData target)
    (middleCode : Y.cellData middle → Nat) (targetCode : Z.cellData target → Nat)
    (datum : CachedCellData X source) :
    mapCellData second targetCode (mapCellData first middleCode datum) =
      mapCellData (second ∘ first) targetCode datum := rfl

def homToValue {A : Type} {X : Atlas} {cell : PageElementCell}
    (f : A → X.cellData cell) (code : X.cellData cell → Nat) (value : A) : CachedCellData X cell :=
  ⟨f value, code (f value)⟩

def homFromValue {A : Type} {X : Atlas} {cell : PageElementCell}
    (f : A → CachedCellData X cell) (value : A) : X.cellData cell := (f value).value

-- ALIGN: CHARTER-HOM-LEFT-INVERSE.
theorem homLeftInverse {A : Type} {X : Atlas} {cell : PageElementCell}
    (f : A → X.cellData cell) (code : X.cellData cell → Nat) (value : A) :
    homFromValue (homToValue f code) value = f value := rfl

-- ALIGN: CHARTER-HOM-RIGHT-INVERSE.
theorem homRightInverse {A : Type} {X : Atlas} {cell : PageElementCell}
    (f : A → CachedCellData X cell) (code : X.cellData cell → Nat)
    (canonical : ∀ value, code (f value).value = (f value).code) (value : A) :
    homToValue (homFromValue f) code value = f value := by
  simp only [homToValue, homFromValue, canonical]

-- ALIGN: CHARTER-HOM-NATURALITY-LEFT.
theorem homNaturalityLeft {A B : Type} {X : Atlas} {cell : PageElementCell}
    (before : A → B) (f : B → X.cellData cell) (code : X.cellData cell → Nat) (value : A) :
    homToValue (f ∘ before) code value = homToValue f code (before value) := rfl

-- ALIGN: CHARTER-HOM-NATURALITY-RIGHT.
theorem homNaturalityRight {A : Type} {X Y : Atlas} {source target : PageElementCell}
    (f : A → X.cellData source) (after : X.cellData source → Y.cellData target)
    (middleCode : X.cellData source → Nat) (targetCode : Y.cellData target → Nat) (value : A) :
    homToValue (after ∘ f) targetCode value = mapCellData after targetCode (homToValue f middleCode value) := rfl

/-- At a genuine cell the runtime wrapper and its invariant are exactly the
covered subtype used by the written Charter definition. -/
noncomputable def cellSemanticsEquiv (X : Atlas) (source : X.toSemantics.El) :
    CertifiedCellData X ((FolioData.ValidElement.fromFinite X.pages).obj source) ≃
      Datra.Semantics.coveredDom X.toSemantics source where
  toFun datum := ⟨datum.val.value, (X.covered_interpretation source datum.val.value).mp datum.property⟩
  invFun datum := ⟨⟨datum.val⟩, (X.covered_interpretation source datum.val).mpr datum.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

noncomputable def chartCellSemanticsEquiv (X : Atlas) (source : X.toSemantics.El) :
    (chartAtlas X).toSemantics.Da.obj source ≃ Datra.Semantics.coveredDom X.toSemantics source :=
  (indexedCellEquiv X ((FolioData.ValidElement.fromFinite X.pages).obj source)).trans
    (cellSemanticsEquiv X source)

noncomputable def interpretationHom (X : Atlas) :
    (chartAtlas X).toSemantics ⟶ Datra.Semantics.chartAtlas X.toSemantics where
  Pa := 𝟭 _
  Da :=
    { app := fun source => (chartCellSemanticsEquiv X source).toEmbedding
      naturality := by
        intro source target arrow
        apply Function.Embedding.ext
        intro datum
        apply Subtype.ext
        change (X.data.action.normalizedMap (FolioData.ValidElement.normalizeArrow
          ((FolioData.ValidElement.fromFinite X.pages).map arrow))).map datum.val.value =
          (X.data.action.normalizedMap ((FolioData.ValidElement.fromFinite X.pages).map arrow)).map
            datum.val.value
        rw [AtlasAction.normalizedMap_normalizeArrow] }

noncomputable def interpretationInv (X : Atlas) :
    Datra.Semantics.chartAtlas X.toSemantics ⟶ (chartAtlas X).toSemantics where
  Pa := 𝟭 _
  Da :=
    { app := fun source => (chartCellSemanticsEquiv X source).symm.toEmbedding
      naturality := by
        intro source target arrow
        apply Function.Embedding.ext
        intro datum
        apply Subtype.ext
        apply CellData.ext
        change (X.data.action.normalizedMap ((FolioData.ValidElement.fromFinite X.pages).map arrow)).map
            datum.val =
          (X.data.action.normalizedMap (FolioData.ValidElement.normalizeArrow
            ((FolioData.ValidElement.fromFinite X.pages).map arrow))).map datum.val
        rw [AtlasAction.normalizedMap_normalizeArrow] }

-- ALIGN: CHARTER-ATLAS-INTERPRETATION.
noncomputable def interpretationIso (X : Atlas) :
    (chartAtlas X).toSemantics ≅ Datra.Semantics.chartAtlas X.toSemantics where
  hom := interpretationHom X
  inv := interpretationInv X
  hom_inv_id := by
    apply Datra.Semantics.AtlHom.ext _ _ rfl
    rfl
  inv_hom_id := by
    apply Datra.Semantics.AtlHom.ext _ _ rfl
    rfl

noncomputable def interpretationTransversalIso (X : Atlas) :
    (WideSubcategory.mk (chartAtlas X).toSemantics : Datra.Semantics.AtlTrav) ≅
      WideSubcategory.mk (Datra.Semantics.chartAtlas X.toSemantics) where
  hom := ⟨interpretationHom X, ⟨⟨Function.injective_id, fun _ _ h => h⟩,
    fun _ => Datra.Semantics.chart_all_covered X.toSemantics _ _⟩⟩
  inv := ⟨interpretationInv X, ⟨⟨Function.injective_id, fun _ _ h => h⟩,
    fun _ => Datra.Semantics.atlasMap_all_covered (chartAtlasMap X).isAtlasMap _ _⟩⟩
  hom_inv_id := Subtype.ext (interpretationIso X).hom_inv_id
  inv_hom_id := Subtype.ext (interpretationIso X).inv_hom_id

-- ALIGN: CHARTER-MAP-INTERPRETATION.
theorem chartMap_interpretation {X Y : Atlas} (f : Atlas.Transversal X Y)
    (backward : (source : X.Element) → X.cellData source.val.cell → Option (IndexedCellData X source.val.cell))
    (leftInverse : ∀ source datum, backward source datum.val.value = some datum) :
    (chartTransversal f backward leftInverse).toSemantics.val =
      interpretationHom X ≫ Datra.Semantics.chartMap f.toSemantics ≫ interpretationInv Y := by
  apply Atlas.semanticHom_ext
  · exact CategoryTheory.Functor.ext (chartHom_page f backward leftInverse)
  · intro source
    apply Atlas.fromSemanticData_injective (chartAtlas Y)
    apply forgetData_injective Y
    change forgetData (Atlas.fromSemanticData (chartAtlas Y)
      (Atlas.mapSemanticData (chartHom f backward leftInverse).finiteSemantics source)) = _
    rw [Atlas.Hom.mapData_interpretation, chartHom_mapData]
    change f.underlying.underlying.hom.mapData
        (Atlas.fromSemanticData X ⟨source.1, source.2.val.value⟩) =
      Atlas.fromSemanticData Y
        (Atlas.mapSemanticData f.underlying.underlying.hom.finiteSemantics ⟨source.1, source.2.val.value⟩)
    exact (f.underlying.underlying.hom.mapData_interpretation _).symm

-- ALIGN: CHARTER-COUNIT-ARROW.
theorem chartCounit_interpretation (X : Atlas)
    (backward : (source : X.Element) → X.cellData source.val.cell → Option (IndexedCellData X source.val.cell))
    (leftInverse : ∀ source datum, backward source datum.val.value = some datum) :
    (chartCounit X backward leftInverse).toSemantics.val =
      interpretationHom X ≫ Datra.Semantics.chartCounit X.toSemantics := by
  apply Atlas.semanticHom_ext
  · exact CategoryTheory.Functor.ext (counitHom_page X backward leftInverse)
  · intro source
    apply Atlas.fromSemanticData_injective X
    change Atlas.fromSemanticData X
      (Atlas.mapSemanticData (counitHom X backward leftInverse).finiteSemantics source) = _
    rw [Atlas.Hom.mapData_interpretation]
    change (⟨((FolioData.ValidElement.fromFinite X.pages).obj source.1).normalize.normalize,
      source.2.val.value⟩ : X.DataElement) =
      ⟨(FolioData.ValidElement.fromFinite X.pages).obj source.1, source.2.val.value⟩
    apply Sigma.ext
    · exact ((FolioData.ValidElement.fromFinite X.pages).obj source.1).normalize_idempotent.trans
        (FolioData.ValidElement.normalize_fromFinite X.pages source.1)
    · rfl

-- ALIGN: CHARTER-UNIT-INTERPRETATION.
theorem chartUnit_interpretation {X : Atlas} (value : AtlasMap X) :
    (chartUnit value).toSemantics.val =
      (Datra.Semantics.chartLift (A := value.toTransversalSemantics) (𝟙 _)).val ≫ interpretationInv X := by
  apply Atlas.semanticHom_ext
  · exact CategoryTheory.Functor.ext (unitHom_page value)
  · intro source
    apply Atlas.fromSemanticData_injective (chartAtlas X)
    apply forgetData_injective X
    change forgetData (Atlas.fromSemanticData (chartAtlas X)
      (Atlas.mapSemanticData (unitHom value).finiteSemantics source)) = _
    rw [Atlas.Hom.mapData_interpretation]
    change (⟨((FolioData.ValidElement.fromFinite X.pages).obj source.1).normalize.normalize,
      source.2⟩ : X.DataElement) = ⟨(FolioData.ValidElement.fromFinite X.pages).obj source.1, source.2⟩
    apply Sigma.ext
    · exact ((FolioData.ValidElement.fromFinite X.pages).obj source.1).normalize_idempotent.trans
        (FolioData.ValidElement.normalize_fromFinite X.pages source.1)
    · rfl

theorem semanticLift_factor {X Y : Atlas} (value : AtlasMap X) (f : Atlas.Transversal X Y) :
    (Datra.Semantics.chartLift (A := value.toTransversalSemantics) (𝟙 _)).val ≫
        Datra.Semantics.chartMap f.toSemantics =
      (Datra.Semantics.chartLift (A := value.toTransversalSemantics) f.toSemantics).val := by
  apply Datra.Semantics.AtlHom.ext _ _ rfl
  rfl

-- ALIGN: CHARTER-LIFT-INTERPRETATION.
theorem chartLift_interpretation {X Y : Atlas} (value : AtlasMap X) (f : Atlas.Transversal X Y) :
    (liftTransversal value f).toSemantics.val =
      (Datra.Semantics.chartLift (A := value.toTransversalSemantics) f.toSemantics).val ≫ interpretationInv Y := by
  rw [liftTransversal, Atlas.Transversal.toSemantics_comp]
  change (chartUnit value).toSemantics.val ≫ (chartTransversal f _ _).toSemantics.val = _
  rw [chartUnit_interpretation, chartMap_interpretation]
  have cancel : interpretationInv X ≫ interpretationHom X = 𝟙 _ := (interpretationIso X).inv_hom_id
  simp only [Category.assoc]
  rw [← Category.assoc (interpretationInv X) (interpretationHom X), cancel, Category.id_comp]
  rw [← Category.assoc, semanticLift_factor]

-- ALIGN: CHARTER-LOWER-INTERPRETATION.
theorem chartLower_interpretation {X Y : Atlas}
    (backward : (source : Y.Element) → Y.cellData source.val.cell → Option (IndexedCellData Y source.val.cell))
    (leftInverse : ∀ source datum, backward source datum.val.value = some datum)
    (f : Atlas.Transversal X (chartAtlas Y)) :
    (lowerTransversal backward leftInverse f).toSemantics.val =
      f.toSemantics.val ≫ interpretationHom Y ≫ Datra.Semantics.chartCounit Y.toSemantics := by
  rw [lowerTransversal, Atlas.Transversal.toSemantics_comp]
  change f.toSemantics.val ≫ (chartCounit Y backward leftInverse).toSemantics.val = _
  rw [chartCounit_interpretation]

theorem chartLift_semantics {X Y : Atlas} (value : AtlasMap X) (f : Atlas.Transversal X Y) :
    (liftTransversal value f).toSemantics =
      Datra.Semantics.AtlTravMapInc.map
        (Datra.Semantics.chartHomEquiv value.toTransversalSemantics (WideSubcategory.mk Y.toSemantics)
          f.toSemantics) ≫ (interpretationTransversalIso Y).inv :=
  Subtype.ext (chartLift_interpretation value f)

theorem chartMap_semantics {X Y : Atlas} (f : Atlas.Transversal X Y)
    (backward : (source : X.Element) → X.cellData source.val.cell → Option (IndexedCellData X source.val.cell))
    (leftInverse : ∀ source datum, backward source datum.val.value = some datum) :
    (chartTransversal f backward leftInverse).toSemantics =
      (interpretationTransversalIso X).hom ≫ Datra.Semantics.AtlTravMapInc.map
        (Datra.Semantics.Chr.map f.toSemantics) ≫ (interpretationTransversalIso Y).inv :=
  Subtype.ext (chartMap_interpretation f backward leftInverse)

-- ALIGN: CHARTER-ARROW-IDENTITY.
theorem chartMap_identity (X : Atlas)
    (backward : (source : X.Element) → X.cellData source.val.cell → Option (IndexedCellData X source.val.cell))
    (leftInverse : ∀ source datum, backward source datum.val.value = some datum) :
    (chartTransversal (.identity : Atlas.Transversal X X) backward leftInverse).toSemantics =
      𝟙 (WideSubcategory.mk (chartAtlas X).toSemantics : Datra.Semantics.AtlTrav) := by
  rw [chartMap_semantics, Atlas.Transversal.toSemantics_identity,
    CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id]
  change (interpretationTransversalIso X).hom ≫ 𝟙 _ ≫ (interpretationTransversalIso X).inv = _
  simp only [Category.id_comp]
  exact (interpretationTransversalIso X).hom_inv_id

-- ALIGN: CHARTER-ARROW-COMPOSITION.
theorem chartMap_composition {X Y Z : Atlas} (first : Atlas.Transversal X Y) (second : Atlas.Transversal Y Z)
    (backwardX : (source : X.Element) → X.cellData source.val.cell → Option (IndexedCellData X source.val.cell))
    (leftInverseX : ∀ source datum, backwardX source datum.val.value = some datum)
    (backwardY : (source : Y.Element) → Y.cellData source.val.cell → Option (IndexedCellData Y source.val.cell))
    (leftInverseY : ∀ source datum, backwardY source datum.val.value = some datum) :
    (chartTransversal (Atlas.Transversal.comp second first) backwardX leftInverseX).toSemantics =
      (chartTransversal first backwardX leftInverseX).toSemantics ≫
        (chartTransversal second backwardY leftInverseY).toSemantics := by
  rw [chartMap_semantics, Atlas.Transversal.toSemantics_comp, Functor.map_comp, Functor.map_comp,
    chartMap_semantics, chartMap_semantics]
  simp only [Category.assoc]
  rw [← Category.assoc (interpretationTransversalIso Y).inv (interpretationTransversalIso Y).hom,
    (interpretationTransversalIso Y).inv_hom_id, Category.id_comp]

theorem chartLower_semantics {X Y : Atlas}
    (backward : (source : Y.Element) → Y.cellData source.val.cell → Option (IndexedCellData Y source.val.cell))
    (leftInverse : ∀ source datum, backward source datum.val.value = some datum)
    (f : Atlas.Transversal X (chartAtlas Y)) :
    (lowerTransversal backward leftInverse f).toSemantics =
      f.toSemantics ≫ (interpretationTransversalIso Y).hom ≫
        Datra.Semantics.chartCounitTrav (WideSubcategory.mk Y.toSemantics) :=
  Subtype.ext (chartLower_interpretation backward leftInverse f)

/-- The hom correspondence is an equivalence after interpretation. Its laws
do not identify arbitrary off-image behavior of executable partial inverses. -/
-- ALIGN: CHARTER-HOM-LEFT-INVERSE-FULL.
theorem chartLower_chartLift {X Y : Atlas} (value : AtlasMap X) (f : Atlas.Transversal X Y)
    (backward : (source : Y.Element) → Y.cellData source.val.cell → Option (IndexedCellData Y source.val.cell))
    (leftInverse : ∀ source datum, backward source datum.val.value = some datum) :
    (lowerTransversal backward leftInverse (liftTransversal value f)).toSemantics = f.toSemantics := by
  rw [chartLower_semantics, chartLift_semantics]
  simp only [Category.assoc]
  rw [← Category.assoc (interpretationTransversalIso Y).inv (interpretationTransversalIso Y).hom,
    (interpretationTransversalIso Y).inv_hom_id, Category.id_comp]
  exact (Datra.Semantics.chartHomEquiv value.toTransversalSemantics
    (WideSubcategory.mk Y.toSemantics)).left_inv f.toSemantics

-- ALIGN: CHARTER-HOM-RIGHT-INVERSE-FULL.
theorem chartLift_chartLower {X Y : Atlas} (value : AtlasMap X)
    (backward : (source : Y.Element) → Y.cellData source.val.cell → Option (IndexedCellData Y source.val.cell))
    (leftInverse : ∀ source datum, backward source datum.val.value = some datum)
    (f : Atlas.Transversal X (chartAtlas Y)) :
    (liftTransversal value (lowerTransversal backward leftInverse f)).toSemantics = f.toSemantics := by
  rw [chartLift_semantics, chartLower_semantics]
  let g : value.toTransversalSemantics ⟶ Datra.Semantics.Chr.obj (WideSubcategory.mk Y.toSemantics) :=
    (f.toSemantics ≫ (interpretationTransversalIso Y).hom :
      (WideSubcategory.mk X.toSemantics : Datra.Semantics.AtlTrav) ⟶
        WideSubcategory.mk (Datra.Semantics.chartAtlas Y.toSemantics))
  have inverse := (Datra.Semantics.chartHomEquiv value.toTransversalSemantics
    (WideSubcategory.mk Y.toSemantics)).right_inv g
  change Datra.Semantics.chartHomEquiv value.toTransversalSemantics (WideSubcategory.mk Y.toSemantics)
    (g ≫ Datra.Semantics.chartCounitTrav _) = g at inverse
  rw [← Category.assoc f.toSemantics (interpretationTransversalIso Y).hom, inverse]
  change (f.toSemantics ≫ (interpretationTransversalIso Y).hom) ≫ (interpretationTransversalIso Y).inv = _
  rw [Category.assoc, (interpretationTransversalIso Y).hom_inv_id, Category.comp_id]

-- ALIGN: CHARTER-HOM-NATURALITY-LEFT-FULL.
theorem chartLift_naturality_left {A X Y : Atlas} (sourceMap : AtlasMap A) (middleMap : AtlasMap X)
    (before : Atlas.Transversal A X) (f : Atlas.Transversal X Y) :
    (liftTransversal sourceMap (Atlas.Transversal.comp f before)).toSemantics =
      before.toSemantics ≫ (liftTransversal middleMap f).toSemantics := by
  rw [chartLift_semantics, Atlas.Transversal.toSemantics_comp, chartLift_semantics]
  let beforeMap : sourceMap.toTransversalSemantics ⟶ middleMap.toTransversalSemantics := before.toSemantics
  have natural := congrArg (fun arrow => Datra.Semantics.AtlTravMapInc.map arrow)
    (Datra.Semantics.chartHomEquiv_naturality_left beforeMap f.toSemantics)
  change Datra.Semantics.AtlTravMapInc.map
      (Datra.Semantics.chartHomEquiv sourceMap.toTransversalSemantics (WideSubcategory.mk Y.toSemantics)
        (before.toSemantics ≫ f.toSemantics)) =
    before.toSemantics ≫ Datra.Semantics.AtlTravMapInc.map
      (Datra.Semantics.chartHomEquiv middleMap.toTransversalSemantics (WideSubcategory.mk Y.toSemantics)
        f.toSemantics) at natural
  rw [natural, Category.assoc]

-- ALIGN: CHARTER-HOM-NATURALITY-RIGHT-FULL.
theorem chartLift_naturality_right {X Y Z : Atlas} (sourceMap : AtlasMap X)
    (first : Atlas.Transversal X Y) (second : Atlas.Transversal Y Z)
    (backward : (source : Y.Element) → Y.cellData source.val.cell → Option (IndexedCellData Y source.val.cell))
    (leftInverse : ∀ source datum, backward source datum.val.value = some datum) :
    (liftTransversal sourceMap (Atlas.Transversal.comp second first)).toSemantics =
      (liftTransversal sourceMap first).toSemantics ≫ (chartTransversal second backward leftInverse).toSemantics := by
  rw [chartLift_semantics, Atlas.Transversal.toSemantics_comp, chartLift_semantics, chartMap_semantics,
    Datra.Semantics.chartHomEquiv_naturality_right, Functor.map_comp]
  simp only [Category.assoc]
  rw [← Category.assoc (interpretationTransversalIso Y).inv (interpretationTransversalIso Y).hom,
    (interpretationTransversalIso Y).inv_hom_id, Category.id_comp]

/-- The written hom equivalence, transported to the executable Charter object.
The following equations identify its two operations with executable lift and
lower whenever the required inverse evidence is supplied. -/
noncomputable def cartographyHomEquiv {X : Atlas} (value : AtlasMap X) (Y : Atlas) :
    ((WideSubcategory.mk X.toSemantics : Datra.Semantics.AtlTrav) ⟶ WideSubcategory.mk Y.toSemantics) ≃
      ((WideSubcategory.mk X.toSemantics : Datra.Semantics.AtlTrav) ⟶ WideSubcategory.mk (chartAtlas Y).toSemantics) :=
  let original :
      ((WideSubcategory.mk X.toSemantics : Datra.Semantics.AtlTrav) ⟶ WideSubcategory.mk Y.toSemantics) ≃
        ((WideSubcategory.mk X.toSemantics : Datra.Semantics.AtlTrav) ⟶
          WideSubcategory.mk (Datra.Semantics.chartAtlas Y.toSemantics)) :=
    Datra.Semantics.chartHomEquiv value.toTransversalSemantics (WideSubcategory.mk Y.toSemantics)
  original.trans ((Iso.refl _).homCongr (interpretationTransversalIso Y).symm)

-- ALIGN: CHARTER-HOM-EQUIV-TO.
theorem cartographyHomEquiv_to {X Y : Atlas} (value : AtlasMap X) (f : Atlas.Transversal X Y) :
    cartographyHomEquiv value Y f.toSemantics = (liftTransversal value f).toSemantics := by
  rw [chartLift_semantics]
  change 𝟙 _ ≫ Datra.Semantics.AtlTravMapInc.map
      (Datra.Semantics.chartHomEquiv value.toTransversalSemantics (WideSubcategory.mk Y.toSemantics)
        f.toSemantics) ≫ (interpretationTransversalIso Y).inv = _
  rw [Category.id_comp]

-- ALIGN: CHARTER-HOM-EQUIV-FROM.
theorem cartographyHomEquiv_from {X Y : Atlas} (value : AtlasMap X)
    (backward : (source : Y.Element) → Y.cellData source.val.cell → Option (IndexedCellData Y source.val.cell))
    (leftInverse : ∀ source datum, backward source datum.val.value = some datum)
    (f : Atlas.Transversal X (chartAtlas Y)) :
    (cartographyHomEquiv value Y).symm f.toSemantics = (lowerTransversal backward leftInverse f).toSemantics := by
  rw [chartLower_semantics]
  change (𝟙 _ ≫ f.toSemantics ≫ (interpretationTransversalIso Y).hom) ≫
    Datra.Semantics.chartCounitTrav _ = _
  rw [Category.id_comp, Category.assoc]
  rfl

/-- Forgetting only the full-subcategory wrapper recovers the proved arrow
interpretation; the wrapper does not discard the stored executable inverse. -/
-- ALIGN: CHARTER-MAP-FULL-SUBCATEGORY.
theorem chartMap_subcategory {X Y : Atlas} (f : Atlas.Transversal X Y)
    (backward : (source : X.Element) → X.cellData source.val.cell → Option (IndexedCellData X source.val.cell))
    (leftInverse : ∀ source datum, backward source datum.val.value = some datum) :
    Datra.Semantics.AtlTravMapInc.map
        ((chartMap f backward leftInverse).toSemantics (chartAtlasMap X) (chartAtlasMap Y)) =
      (interpretationTransversalIso X).hom ≫
        Datra.Semantics.AtlTravMapInc.map (Datra.Semantics.Chr.map f.toSemantics) ≫
          (interpretationTransversalIso Y).inv :=
  chartMap_semantics f backward leftInverse

-- ALIGN: CHARTER-LIFT-FULL-SUBCATEGORY.
theorem chartLift_subcategory {X Y : Atlas} (value : AtlasMap X) (f : Atlas.Transversal X Y) :
    Datra.Semantics.AtlTravMapInc.map ((chartLift value f).toSemantics value (chartAtlasMap Y)) =
      cartographyHomEquiv value Y f.toSemantics :=
  (cartographyHomEquiv_to value f).symm

-- ALIGN: CHARTER-LOWER-FULL-SUBCATEGORY.
theorem chartLower_subcategory {X Y : Atlas} (value : AtlasMap X)
    (backward : (source : Y.Element) → Y.cellData source.val.cell → Option (IndexedCellData Y source.val.cell))
    (leftInverse : ∀ source datum, backward source datum.val.value = some datum)
    (f : AtlasTransversalMap X (chartAtlas Y)) :
    (chartLower backward leftInverse f).toSemantics =
      (cartographyHomEquiv value Y).symm
        (Datra.Semantics.AtlTravMapInc.map (f.toSemantics value (chartAtlasMap Y))) :=
  (cartographyHomEquiv_from value backward leftInverse f.transversal).symm

-- ALIGN: CHARTER-COUNIT-INTERPRETATION.
theorem cachedCounitInsertion_interpretation (X : Atlas) (source : X.toSemantics.El)
    (backward : X.toSemantics.Da.obj source →
      Option (CertifiedCachedCellData X ((FolioData.ValidElement.fromFinite X.pages).obj source)))
    (leftInverse : ∀ datum, backward datum.val.value = some datum) :
    (cachedCounitInsertion backward leftInverse).toSemantics =
      (cachedCellEquiv X ((FolioData.ValidElement.fromFinite X.pages).obj source)).toEmbedding.trans
        ((cellSemanticsEquiv X source).toEmbedding.trans
          ((Datra.Semantics.chartCounit X.toSemantics).Da.app source)) := by
  apply Function.Embedding.ext
  intro datum
  rfl

end Datra.Executable.Charter
