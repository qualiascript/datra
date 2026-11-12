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

end Datra.Executable
