import Executable.Pagination
import Executable.DomanialInsertion

namespace Datra.Executable
open CategoryTheory

/-- The two dependent operations carried by AtlasAction. The family is indexed
by the genuine cell identity and payload, so normalization has exactly the
same data type. -/
structure AtlasAction {origin final : Page} (pages : FolioData origin final)
    (cellData : PageElementCell → Type) where
  dataAt : (x : pages.ValidElement) → Dominion (cellData x.val.cell)
  mapData : ∀ {x y : pages.ValidElement}, (x ⟶ y) →
    DomanialInsertion (cellData x.val.cell) (cellData y.val.cell)

namespace AtlasAction
variable {origin final : Page} {pages : FolioData origin final}
  {cellData : PageElementCell → Type}

def normalizedMap (action : AtlasAction pages cellData) {x y : pages.ValidElement}
    (f : x ⟶ y) : DomanialInsertion (cellData x.val.cell) (cellData y.val.cell) :=
  action.mapData (x := x.normalize) (y := y.normalize) (FolioData.ValidElement.normalizeArrow f)

end AtlasAction

/-- The four pointwise smart-constructor obligations. Every action is evaluated
on normalized arrows, as in Atlas.LiquidInternal.atlasData. -/
structure AtlasData {origin final : Page} (pages : FolioData origin final)
    (cellData : PageElementCell → Type) where
  action : AtlasAction pages cellData
  identity : ∀ (x : pages.ValidElement) (datum : cellData x.val.cell),
    (action.normalizedMap (𝟙 x)).map datum = datum
  composition : ∀ {x y z : pages.ValidElement} (first : x ⟶ y) (second : y ⟶ z)
    (datum : cellData x.val.cell),
    (action.normalizedMap (first ≫ second)).map datum =
      (action.normalizedMap second).map ((action.normalizedMap first).map datum)
  coherence : ∀ (x : pages.ValidElement) (datum : cellData x.val.cell),
    (action.normalizedMap x.toNormalized).map datum = datum
  disjoint : ∀ {left right origin : pages.ValidElement},
    left.val.page = right.val.page → left.val.position ≠ right.val.position →
    left.val.page ≤ pages.depth - 1 → origin.val.page = 0 →
    (leftToOrigin : left ⟶ origin) → (rightToOrigin : right ⟶ origin) →
    (leftDatum : cellData left.val.cell) → (rightDatum : cellData right.val.cell) →
    (action.normalizedMap leftToOrigin).map leftDatum ≠
      (action.normalizedMap rightToOrigin).map rightDatum

namespace AtlasData
variable {origin final : Page} {pages : FolioData origin final}
  {cellData : PageElementCell → Type}

-- ALIGN: ATLAS-DATA-FUNCTOR.
def toFunctor (data : AtlasData pages cellData) : pages.ValidElement ⥤ Datra.Semantics.DomIns where
  obj x := ⟨(data.action.dataAt x.normalize).toSemantics⟩
  map f := (data.action.normalizedMap f).toSemantics
  map_id x := by apply Function.Embedding.ext; intro datum; exact data.identity x datum
  map_comp first second := by
    apply Function.Embedding.ext
    intro datum
    exact data.composition first second datum

noncomputable def tallFunctor (data : AtlasData pages cellData) :
    pages.toSemantics.TallEl ⥤ Datra.Semantics.DomIns :=
  (FolioData.ValidElement.elementsEquivalence pages).inverse ⋙ data.toFunctor

noncomputable def finiteFunctor (data : AtlasData pages cellData) :
    pages.toSemantics.El ⥤ Datra.Semantics.DomIns :=
  pages.toSemantics.includeElements ⋙ data.tallFunctor

end AtlasData
end Datra.Executable

namespace Datra.Executable.AtlasData
open CategoryTheory Opposite
variable {origin final : Page} {pages : FolioData origin final}
  {cellData : PageElementCell → Type}

-- ALIGN: ATLAS-DATA-DISJOINT.
theorem finite_disjoint (data : AtlasData pages cellData) :
    Datra.Semantics.IsPagewiseDisjoint ⟨pages.toSemantics⟩ data.finiteFunctor := by
  intro m i j hij x y
  let P : Datra.Semantics.Pag := ⟨pages.toSemantics⟩
  let F := FolioData.ValidElement.fromFinite pages
  have hp : (F.obj (P.cell m i)).val.page = (F.obj (P.cell m j)).val.page := rfl
  have hv : (F.obj (P.cell m i)).val.position ≠ (F.obj (P.cell m j)).val.position := by
    intro he
    have ho := FolioData.ValidElement.eq_of_page_position hp he
    have hc := FolioData.ValidElement.fromFinite_injective pages ho
    exact hij (by cases hc; rfl)
  have hb : (F.obj (P.cell m i)).val.page ≤ pages.depth - 1 := by
    change m.unop.val ≤ pages.depth - 1
    have := m.unop.isLt
    change m.unop.val < pages.depth at this
    omega
  exact data.disjoint hp hv hb rfl (F.map (P.cellToOrigin m i))
    (F.map (P.cellToOrigin m j)) x y

noncomputable def toSemantics (data : AtlasData pages cellData) : Datra.Semantics.Atl where
  Pa := ⟨pages.toSemantics⟩
  Da := data.finiteFunctor
  disjoint := data.finite_disjoint

end Datra.Executable.AtlasData

namespace Datra.Executable
open CategoryTheory

/-- An Atlas owns a finite folio and its dependent data assignment. Its value
is the object index used by symbolic arrows. -/
structure Atlas where
  pagination : Pagination
  cellData : PageElementCell → Type
  data : AtlasData pagination.pages cellData

abbrev Atlas.pages (X : Atlas) := X.pagination.pages
abbrev Atlas.Element (X : Atlas) := X.pagination.Element

noncomputable def Atlas.toSemantics (X : Atlas) : Datra.Semantics.Atl := X.data.toSemantics

/-- Public Atlas data lookup evaluates the action at the normalized cell. -/
def Atlas.dataAt (X : Atlas) (x : X.Element) : Dominion (X.cellData x.val.cell) :=
  X.data.action.dataAt x.normalize

/-- A dependent dominion retains its selected cell, as AtlasCellDominion does. -/
structure Atlas.CellDominion (X : Atlas) where
  element : X.Element
  dominion : Dominion (X.cellData element.val.cell)

def Atlas.CellDominion.toSemantics {X : Atlas} (value : X.CellDominion) : Datra.Semantics.DomIns :=
  ⟨value.dominion.toSemantics⟩

end Datra.Executable

namespace Datra.Executable.AtlasAction
open CategoryTheory
variable {origin final : Page} {pages : FolioData origin final}
  {cellData : PageElementCell → Type}

theorem normalizedMap_normalizeArrow (action : AtlasAction pages cellData)
    {x y : pages.ValidElement} (f : x ⟶ y) :
    action.normalizedMap (FolioData.ValidElement.normalizeArrow f) = action.normalizedMap f := by
  unfold normalizedMap
  congr 1 <;> try simp only [FolioData.ValidElement.normalize_idempotent]
  have hom_heq : ∀ {a b c d : pages.ValidElement}, a = c → b = d →
      (f : a ⟶ b) → (g : c ⟶ d) → HEq f g := by
    intro a b c d ha hb f g
    subst c
    subst d
    exact heq_of_eq (Subsingleton.elim _ _)
  exact hom_heq (FolioData.ValidElement.normalize_idempotent x)
    (FolioData.ValidElement.normalize_idempotent y) _ _

end Datra.Executable.AtlasAction
