import Executable.Atlas.OrderedTransposal
import Executable.Atlas.Coverage

namespace Datra.Executable.Atlas
open CategoryTheory

/-- Public covered elements retain the invariant of their hidden constructor. -/
abbrev CertifiedCoveredElement (X : Atlas) := {c : X.CoveredPageElement // c.Valid}

def CertifiedCoveredElement.data {X : Atlas} (c : X.CertifiedCoveredElement) : X.DataElement :=
  ⟨c.val.source, c.val.datum⟩

def DataElement.Covered {X : Atlas} (c : X.DataElement) : Prop := X.Covered c.1 c.2

theorem fromSemanticData_covered (X : Atlas) (c : X.SemanticDataElement) :
    (fromSemanticData X c).Covered ↔ Datra.Semantics.Covered X.toSemantics c.1 c.2 :=
  X.covered_interpretation c.1 c.2

noncomputable def CertifiedCoveredElement.fromSemantics {X : Atlas}
    (c : Datra.Semantics.CoveredPageElement X.toSemantics) : X.CertifiedCoveredElement :=
  let source : X.DataElement := fromSemanticData X ⟨c.pageElement, c.datum⟩
  let covered : X.Covered source.1 source.2 :=
    (X.covered_interpretation c.pageElement c.datum).mpr c.covered
  ⟨⟨source.1, source.2, X.findAtlasCoverage source.1 source.2 covered⟩,
    X.findAtlasCoverage_spec source.1 source.2 covered⟩

theorem CertifiedCoveredElement.fromSemantics_data {X : Atlas}
    (c : Datra.Semantics.CoveredPageElement X.toSemantics) :
    (CertifiedCoveredElement.fromSemantics c).data = fromSemanticData X ⟨c.pageElement, c.datum⟩ := rfl

theorem CertifiedCoveredElement.covered {X : Atlas} (c : X.CertifiedCoveredElement) :
    c.data.Covered := CoveredPageElement.covered c.property

/-- The primitive callback retains the full LiquidHaskell contract: every
supplied target occurrence and datum must receive a valid coverage witness. -/
inductive Transversal : Atlas → Atlas → Type 2
  | primitive {X Y} (ordered : OrderedTransposal X Y)
      (preserves : X.CertifiedCoveredElement → (target : Y.Element) →
        (datum : Y.cellData target.val.cell) →
        {w : Y.CoverageWitness // w.Valid ∧ Y.coverageWitnessCovers target datum w = true}) :
      Transversal X Y
  | identity {X} : Transversal X X
  | composite {X Y Z} : Transversal Y Z → Transversal X Y → Transversal X Z

namespace Transversal

def underlying {X Y : Atlas} : Transversal X Y → OrderedTransposal X Y
  | .primitive ordered _ => ordered
  | .identity => .identity
  | .composite second first => OrderedTransposal.comp second.underlying first.underlying

def mapCovered {X Y : Atlas} : Transversal X Y → X.CertifiedCoveredElement → Y.CertifiedCoveredElement
  | .identity, c => c
  | .composite second first, c => second.mapCovered (first.mapCovered c)
  | .primitive ordered preserves, c =>
      let image := ordered.underlying.hom.mapData c.data
      let witness := preserves c image.1 image.2
      ⟨⟨image.1, image.2, witness.val⟩, witness.property⟩

theorem underlying_composite {X Y Z : Atlas} (second : Transversal Y Z) (first : Transversal X Y) :
    (composite second first).underlying.underlying.hom.finiteSemantics =
      first.underlying.underlying.hom.finiteSemantics ≫ second.underlying.underlying.hom.finiteSemantics :=
  congrArg Subtype.val (OrderedTransposal.toSemantics_comp second.underlying first.underlying)

/-- The operational mapper produces precisely the semantic image, including
the dependent datum rather than only its page element. -/
-- ALIGN: ATLAS-TRANSVERSAL-COVERED-IMAGE.
theorem mapCovered_interpretation {X Y : Atlas} (f : Transversal X Y)
    (c : X.CertifiedCoveredElement) (source : X.SemanticDataElement)
    (h : c.data = fromSemanticData X source) :
    (f.mapCovered c).data = fromSemanticData Y
      (mapSemanticData f.underlying.underlying.hom.finiteSemantics source) := by
  induction f with
  | primitive ordered preserves =>
      change ordered.underlying.hom.mapData c.data = _
      rw [h]
      exact (ordered.underlying.hom.mapData_interpretation source).symm
  | identity =>
      change c.data = fromSemanticData _ (mapSemanticData (Hom.finiteSemantics .identity) source)
      rw [Hom.finiteSemantics_identity]
      exact h
  | composite second first ih₂ ih₁ =>
      rw [underlying_composite]
      exact ih₂ (first.mapCovered c)
        (mapSemanticData first.underlying.underlying.hom.finiteSemantics source) (ih₁ c source h)

theorem mapCovered_covers_semantic {X Y : Atlas} (f : Transversal X Y)
    (c : X.CertifiedCoveredElement) (source : X.SemanticDataElement)
    (h : c.data = fromSemanticData X source) :
    Datra.Semantics.Covered Y.toSemantics
      (mapSemanticData f.underlying.underlying.hom.finiteSemantics source).1
      (mapSemanticData f.underlying.underlying.hom.finiteSemantics source).2 := by
  have imageCovered := (f.mapCovered c).covered
  rw [f.mapCovered_interpretation c source h] at imageCovered
  exact (fromSemanticData_covered Y
    (mapSemanticData f.underlying.underlying.hom.finiteSemantics source)).mp imageCovered

-- ALIGN: ATLAS-TRANSVERSAL-COVERAGE.
theorem semantic_preservesCoverage {X Y : Atlas} (f : Transversal X Y) :
    Datra.Semantics.PreservesCoveredPageElements f.underlying.underlying.hom.finiteSemantics := by
  intro c
  exact f.mapCovered_covers_semantic (CertifiedCoveredElement.fromSemantics c)
    ⟨c.pageElement, c.datum⟩ (CertifiedCoveredElement.fromSemantics_data c)

-- ALIGN: ATLAS-TRANSVERSAL-INTERPRETATION.
theorem semantic_transversal {X Y : Atlas} (f : Transversal X Y) :
    Datra.Semantics.IsTransversal f.underlying.underlying.hom.finiteSemantics :=
  ⟨f.underlying.semantic_order, f.semantic_preservesCoverage⟩

noncomputable def toSemantics {X Y : Atlas} (f : Transversal X Y) :
    (WideSubcategory.mk X.toSemantics : Datra.Semantics.AtlTrav) ⟶
      (WideSubcategory.mk Y.toSemantics : Datra.Semantics.AtlTrav) :=
  ⟨f.underlying.underlying.hom.finiteSemantics, f.semantic_transversal⟩

def comp {X Y Z : Atlas} : Transversal Y Z → Transversal X Y → Transversal X Z
  | .identity, first => first
  | second, .identity => second
  | second, .composite middle first => .composite (comp second middle) first
  | second, first => .composite second first

-- ALIGN: ATLAS-TRANSVERSAL-IDENTITY.
@[simp] theorem toSemantics_identity (X : Atlas) :
    (identity : Transversal X X).toSemantics =
      𝟙 (WideSubcategory.mk X.toSemantics : Datra.Semantics.AtlTrav) := by
  apply Subtype.ext
  exact Hom.finiteSemantics_identity X

@[simp] theorem toSemantics_composite {X Y Z : Atlas} (second : Transversal Y Z) (first : Transversal X Y) :
    (composite second first).toSemantics = first.toSemantics ≫ second.toSemantics := by
  apply Subtype.ext
  exact underlying_composite second first

-- ALIGN: ATLAS-TRANSVERSAL-COMPOSITION.
theorem toSemantics_comp {X Y Z : Atlas} (second : Transversal Y Z) (first : Transversal X Y) :
    (comp second first).toSemantics = first.toSemantics ≫ second.toSemantics := by
  induction first with
  | identity => cases second <;> simp [comp]
  | primitive _ _ => cases second <;> simp [comp]
  | composite middle first ih _ => cases second <;> simp_all [comp, Category.assoc]

end Transversal
end Datra.Executable.Atlas
