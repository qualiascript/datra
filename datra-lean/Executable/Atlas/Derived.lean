import Executable.Atlas.Data
import Executable.CoverageEnumeration

namespace Datra.Executable
open CategoryTheory

def Atlas.extent (X : Atlas) : X.CellDominion :=
  ⟨FolioData.ValidElement.originElement X.pages,
    X.dataAt (FolioData.ValidElement.originElement X.pages)⟩

-- ALIGN: ATLAS-EXTENT-INTERPRETATION.
theorem Atlas.extent_interpretation (X : Atlas) :
    X.extent.toSemantics = Datra.Semantics.extent X.toSemantics := by
  unfold Atlas.extent Atlas.CellDominion.toSemantics Atlas.dataAt
  rw [FolioData.ValidElement.originElement_interpretation]
  rfl

abbrev Atlas.TerritoryIndex (X : Atlas) := ChainIndex X.pagination.final.chain

def Atlas.territoryIndexToSemantics (X : Atlas) (index : X.TerritoryIndex) :
    Datra.Semantics.TerritoryIndex X.toSemantics :=
  FolioData.ValidElement.finalFiniteValue X.pages index.object

def Atlas.territoryIndexEquiv (X : Atlas) : X.TerritoryIndex ≃ Datra.Semantics.TerritoryIndex X.toSemantics :=
  X.pagination.final.chain.indexEquiv.trans
    (Equiv.cast (congrArg Page.Carrier (FolioData.ValidElement.finalIndex_page X.pages).symm))

def Atlas.territory (X : Atlas) (index : X.TerritoryIndex) : X.CellDominion :=
  ⟨FolioData.ValidElement.lastElement X.pages index,
    X.dataAt (FolioData.ValidElement.lastElement X.pages index)⟩

-- ALIGN: ATLAS-TERRITORY-INTERPRETATION.
theorem Atlas.territory_interpretation (X : Atlas) (index : X.TerritoryIndex) :
    (X.territory index).toSemantics =
      Datra.Semantics.territory X.toSemantics (X.territoryIndexToSemantics index) := by
  unfold Atlas.territory Atlas.CellDominion.toSemantics Atlas.dataAt
  rw [FolioData.ValidElement.lastElement_interpretation]
  rfl

def Atlas.region (X : Atlas) (index : X.TerritoryIndex) : X.CellDominion := X.territory index

def Atlas.originImage (X : Atlas) (x : X.Element) (datum : X.cellData x.val.cell) :
    X.cellData (FolioData.ValidElement.originElement X.pages).val.cell :=
  (X.data.action.normalizedMap x.toOrigin).map datum

theorem Atlas.originImage_origin (X : Atlas)
    (datum : X.cellData (FolioData.ValidElement.originElement X.pages).val.cell) :
    X.originImage (FolioData.ValidElement.originElement X.pages) datum = datum := by
  unfold Atlas.originImage
  rw [show (FolioData.ValidElement.originElement X.pages).toOrigin =
    𝟙 (FolioData.ValidElement.originElement X.pages) from Subsingleton.elim _ _]
  exact X.data.identity _ datum

def Atlas.originImageRank (X : Atlas) (x : X.Element) (datum : X.cellData x.val.cell) : Nat :=
  (X.dataAt (FolioData.ValidElement.originElement X.pages)).rank (X.originImage x datum)

theorem Atlas.originImage_normalize (X : Atlas) (x : X.Element)
    (datum : X.cellData x.val.cell) : X.originImage x.normalize datum = X.originImage x datum := by
  have he : x.toNormalized ≫ x.normalize.toOrigin = x.toOrigin := Subsingleton.elim _ _
  have hc := X.data.composition x.toNormalized x.normalize.toOrigin datum
  rw [he, X.data.coherence] at hc
  exact hc.symm

-- ALIGN: ATLAS-ORIGIN-RANK-NORMALIZATION.
theorem Atlas.originImageRank_normalize (X : Atlas) (x : X.Element)
    (datum : X.cellData x.val.cell) :
    X.originImageRank x.normalize datum = X.originImageRank x datum := by
  unfold Atlas.originImageRank
  rw [X.originImage_normalize]

-- ALIGN: ATLAS-COVERAGE-RANK-EQUALITY.
theorem Atlas.originImageRank_eq_iff (X : Atlas) (x y : X.Element)
    (a : X.cellData x.val.cell) (b : X.cellData y.val.cell) :
    X.originImageRank x a = X.originImageRank y b ↔ X.originImage x a = X.originImage y b :=
  (X.dataAt (FolioData.ValidElement.originElement X.pages)).rank_injective.eq_iff

-- ALIGN: ATLAS-ORIGIN-IMAGE-INTERPRETATION.
theorem Atlas.originImage_interpretation (X : Atlas) (x : X.toSemantics.El)
    (datum : X.toSemantics.Da.obj x) :
    HEq (X.originImage ((FolioData.ValidElement.fromFinite X.pages).obj x) datum)
      (Datra.Semantics.originImage X.toSemantics x datum) := by
  let source := (FolioData.ValidElement.fromFinite X.pages).obj x
  have map_heq {y z : X.Element} (h : y = z) (f : source ⟶ y) (g : source ⟶ z) :
      HEq ((X.data.action.normalizedMap f).map datum)
        ((X.data.action.normalizedMap g).map datum) := by
    subst z
    have hg : f = g := Subsingleton.elim _ _
    subst g
    rfl
  exact map_heq (FolioData.ValidElement.originElement_interpretation X.pages)
    source.toOrigin ((FolioData.ValidElement.fromFinite X.pages).map
      (X.toSemantics.Fo.toOrigin x))

-- ALIGN: ATLAS-ORIGIN-RANK-INTERPRETATION.
theorem Atlas.originImageRank_interpretation (X : Atlas) (x : X.toSemantics.El)
    (datum : X.toSemantics.Da.obj x) :
    X.originImageRank ((FolioData.ValidElement.fromFinite X.pages).obj x) datum =
      (Datra.Semantics.extent X.toSemantics).toDom.rank (Datra.Semantics.originImage X.toSemantics x datum) := by
  let source := (FolioData.ValidElement.fromFinite X.pages).obj x
  have map_eq {y z : X.Element} (h : y = z) (f : source ⟶ y) (g : source ⟶ z) :
      (X.dataAt y).rank ((X.data.action.normalizedMap f).map datum) =
        (X.dataAt z).rank ((X.data.action.normalizedMap g).map datum) := by
    subst z
    have hg : f = g := Subsingleton.elim _ _
    subst g
    rfl
  exact map_eq (FolioData.ValidElement.originElement_interpretation X.pages)
    source.toOrigin ((FolioData.ValidElement.fromFinite X.pages).map
      (X.toSemantics.Fo.toOrigin x))

/-- Coverage is witnessed by a final-region datum with the same origin rank.
The executable witness search decides this equation for each candidate. -/
def Atlas.Covered (X : Atlas) (x : X.Element) (datum : X.cellData x.val.cell) : Prop :=
  ∃ (index : X.TerritoryIndex)
    (regionDatum : X.cellData (X.territory index).element.val.cell),
    X.originImageRank x datum = X.originImageRank (X.territory index).element regionDatum

theorem Atlas.covered_normalize_iff (X : Atlas) (x : X.Element)
    (datum : X.cellData x.val.cell) : X.Covered x.normalize datum ↔ X.Covered x datum := by
  simp only [Atlas.Covered, X.originImageRank_normalize]

/-- Coverage depends on the genuine cell index, independently of which padded
occurrence presents it. This permits a covered subtype as an Atlas data family. -/
theorem Atlas.covered_cast_iff (X : Atlas) {source target : X.Element}
    (sameCell : source.val.cell = target.val.cell) (datum : X.cellData source.val.cell) :
    X.Covered target (cast (congrArg X.cellData sameCell) datum) ↔ X.Covered source datum := by
  have transfer (a b : X.Element) (h : a = b) (value : X.cellData a.val.cell) :
      X.Covered b (cast (congrArg (fun x : X.Element => X.cellData x.val.cell) h) value) ↔
        X.Covered a value := by
    cases h
    rfl
  rw [← X.covered_normalize_iff target, ← X.covered_normalize_iff source]
  exact transfer source.normalize target.normalize
    ((FolioData.ValidElement.cell_eq_iff_normalize_eq source target).mp sameCell) datum

theorem Atlas.originImage_map (X : Atlas) {source target : X.Element} (arrow : source ⟶ target)
    (datum : X.cellData source.val.cell) :
    X.originImage target ((X.data.action.normalizedMap arrow).map datum) =
      X.originImage source datum := by
  have composition := X.data.composition arrow target.toOrigin datum
  have same : arrow ≫ target.toOrigin = source.toOrigin := Subsingleton.elim _ _
  rw [same] at composition
  exact composition.symm

/-- Atlas data arrows preserve and reflect coverage, since they preserve the
origin image. Arbitrary transversal components need only preserve coverage. -/
theorem Atlas.covered_map_iff (X : Atlas) {source target : X.Element} (arrow : source ⟶ target)
    (datum : X.cellData source.val.cell) :
    X.Covered target ((X.data.action.normalizedMap arrow).map datum) ↔ X.Covered source datum := by
  simp only [Atlas.Covered, Atlas.originImageRank, X.originImage_map]

-- ALIGN: ATLAS-COVERAGE-INTERPRETATION.
theorem Atlas.covered_interpretation (X : Atlas) (x : X.toSemantics.El)
    (datum : X.toSemantics.Da.obj x) :
    X.Covered ((FolioData.ValidElement.fromFinite X.pages).obj x) datum ↔
      Datra.Semantics.Covered X.toSemantics x datum := by
  have hw : X.Covered ((FolioData.ValidElement.fromFinite X.pages).obj x) datum ↔
      ∃ (index : X.TerritoryIndex)
        (value : Datra.Semantics.territory X.toSemantics (X.territoryIndexToSemantics index)),
        X.originImageRank ((FolioData.ValidElement.fromFinite X.pages).obj x) datum =
          X.originImageRank ((FolioData.ValidElement.fromFinite X.pages).obj
            (X.toSemantics.Pa.cell X.toSemantics.Fo.lastBase
              (X.territoryIndexToSemantics index))) value := by
    apply exists_congr
    intro index
    exact iff_of_eq (congrArg (fun region : X.Element =>
      ∃ value : X.cellData region.val.cell,
        X.originImageRank ((FolioData.ValidElement.fromFinite X.pages).obj x) datum =
          X.originImageRank region value)
      (FolioData.ValidElement.lastElement_interpretation X.pages index))
  rw [hw]
  simp only [Atlas.originImageRank_interpretation]
  have hr (a b : Datra.Semantics.extent X.toSemantics) :
      (Datra.Semantics.extent X.toSemantics).toDom.rank a =
        (Datra.Semantics.extent X.toSemantics).toDom.rank b ↔ a = b :=
    (Datra.Semantics.extent X.toSemantics).toDom.rank.injective.eq_iff
  simp only [hr]
  constructor
  · rintro ⟨index, value, h⟩
    exact ⟨X.territoryIndexToSemantics index, value, h⟩
  · rintro ⟨index, value, h⟩
    obtain ⟨i, hi⟩ := X.territoryIndexEquiv.surjective index
    have he : X.territoryIndexToSemantics i = index := hi
    subst index
    exact ⟨i, value, h⟩

/-- The exact raw-arrow conditions needed to act on a cell at the Atlas origin. -/
-- ALIGN: ATLAS-CELL-HAS-ORIGIN.
def Atlas.cellHasOrigin (X : Atlas) (source : PageElement X.pages) : Prop :=
  PageElement.precedes source (FolioData.ValidElement.originElement X.pages).val ∧
    PageElement.transported source (FolioData.ValidElement.originElement X.pages).val

theorem Atlas.validCell_hasOrigin (X : Atlas) (source : X.Element) : X.cellHasOrigin source.val :=
  ⟨source.toOrigin.precedes, source.toOrigin.transported⟩

/-- The common origin-rank insertion used by merge and sequence membership
and by their dependent data components. -/
-- ALIGN: ATLAS-CELL-ORIGIN-RANK-INSERTION.
def Atlas.cellOriginRankInsertion (X : Atlas) (source : X.Element) :
    DomanialInsertion (X.cellData source.val.cell) Nat :=
  DomanialInsertion.rankImageInsertion (X.dataAt (FolioData.ValidElement.originElement X.pages))
    (X.data.action.normalizedMap source.toOrigin)

theorem Atlas.cellOriginRankInsertion_map (X : Atlas) (source : X.Element)
    (datum : X.cellData source.val.cell) :
    (X.cellOriginRankInsertion source).map datum = X.originImageRank source datum := rfl

def Atlas.cellContainsRank (X : Atlas) (source : X.Element) (valueRank : Nat) : Bool :=
  ((X.cellOriginRankInsertion source).preimage valueRank).isSome

-- ALIGN: ATLAS-CELL-CONTAINS-RANK.
theorem Atlas.cellContainsRank_iff (X : Atlas) (source : X.Element) (valueRank : Nat) :
    X.cellContainsRank source valueRank = true ↔ ∃ datum, X.originImageRank source datum = valueRank :=
  DomanialInsertion.rankImagePreimage_exists_iff _ _ _

-- ALIGN: ATLAS-CELL-CONTAINS-IMAGE.
theorem Atlas.cellContainsRank_image (X : Atlas) (source : X.Element)
    (datum : X.cellData source.val.cell) :
    X.cellContainsRank source ((X.cellOriginRankInsertion source).map datum) = true :=
  (X.cellContainsRank_iff source _).mpr ⟨datum, rfl⟩

-- ALIGN: ATLAS-CELL-RANK-PREIMAGE-SOUND.
theorem Atlas.cellOriginRankPreimage_sound (X : Atlas) (source : X.Element)
    (valueRank : Nat) (datum : X.cellData source.val.cell)
    (found : (X.cellOriginRankInsertion source).preimage valueRank = some datum) :
    (X.cellOriginRankInsertion source).map datum = valueRank :=
  DomanialInsertion.rankImagePreimage_sound _ _ _ _ found

theorem Atlas.cellContainsRank_normalize (X : Atlas) (source : X.Element) (valueRank : Nat) :
    X.cellContainsRank source.normalize valueRank = X.cellContainsRank source valueRank := by
  apply Bool.eq_iff_iff.mpr
  simp only [X.cellContainsRank_iff, X.originImageRank_normalize]
  rfl

/-- A shared origin rank identifies at most one cell on any full-spine page,
including a repeated padding page. -/
theorem Atlas.cellContainsRank_samePage (X : Atlas) (left right : X.Element)
    (samePage : left.val.page = right.val.page) (valueRank : Nat)
    (inLeft : X.cellContainsRank left valueRank = true)
    (inRight : X.cellContainsRank right valueRank = true) : left = right := by
  obtain ⟨a, ha⟩ := (X.cellContainsRank_iff left valueRank).mp inLeft
  obtain ⟨b, hb⟩ := (X.cellContainsRank_iff right valueRank).mp inRight
  apply FolioData.ValidElement.eq_of_page_position samePage
  by_contra different
  have distinct := X.data.disjoint
    (left := left.normalize) (right := right.normalize)
    (congrArg (fun n => min n (X.pages.depth - 1)) samePage) different
    (min_le_right _ _) rfl left.normalize.toOrigin right.normalize.toOrigin a b
  apply distinct
  change X.originImage left.normalize a = X.originImage right.normalize b
  rw [X.originImage_normalize, X.originImage_normalize]
  exact (X.originImageRank_eq_iff left right a b).mp (ha.trans hb.symm)

def Atlas.extentContainsRank (X : Atlas) (valueRank : Nat) : Bool :=
  X.cellContainsRank (FolioData.ValidElement.originElement X.pages) valueRank

-- ALIGN: ATLAS-EXTENT-CONTAINS-RANK.
theorem Atlas.extentContainsRank_iff (X : Atlas) (valueRank : Nat) :
    X.extentContainsRank valueRank = true ↔
      ∃ datum, (X.dataAt (FolioData.ValidElement.originElement X.pages)).rank datum = valueRank := by
  rw [Atlas.extentContainsRank, X.cellContainsRank_iff]
  simp only [Atlas.originImageRank, X.originImage_origin]

end Datra.Executable
