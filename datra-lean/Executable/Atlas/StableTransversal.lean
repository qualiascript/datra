import Executable.Atlas.Transversal

namespace Datra.Executable.Atlas
open CategoryTheory

def stableOrigin (X : Atlas) : X.TransposalElement :=
  X.transposalElement (FolioData.ValidElement.originElement X.pages)

theorem stableOrigin_interpretation (X : Atlas) :
    (stableOrigin X).toSemantics = X.toSemantics.Fo.originElement := by
  have h : stableOrigin X = TransposalElement.fromSemantics X X.toSemantics.Fo.originElement := by
    apply Subtype.ext
    change (FolioData.ValidElement.originElement X.pages).normalize = _
    rw [FolioData.ValidElement.originElement_interpretation]
    exact FolioData.ValidElement.normalize_fromFinite _ _
  rw [h, TransposalElement.toSemantics_fromSemantics]

/-- The runtime predicate compares the normalized image's page and ordinal
with the canonical origin's page and ordinal. -/
def stableOriginPreserved {X Y : Atlas} (f : Transversal X Y) : Bool :=
  TransposalElement.equal (f.underlying.mapObject (stableOrigin X)) (stableOrigin Y)

theorem stableOriginPreserved_interpretation {X Y : Atlas} (f : Transversal X Y) :
    stableOriginPreserved f = true ↔ Datra.Semantics.IsStableTransversal f.toSemantics := by
  rw [stableOriginPreserved, TransposalElement.equal_iff,
    ← (TransposalElement.semanticsEquiv Y).injective.eq_iff]
  change (f.underlying.mapObject (stableOrigin X)).toSemantics = (stableOrigin Y).toSemantics ↔ _
  rw [OrderedTransposal.mapObject, Transposal.mapObject_interpretation,
    stableOrigin_interpretation, stableOrigin_interpretation]
  rfl

/-- The primitive certificate is precisely the checked Haskell boundary.
Identity and composition derive stability by their constructor cases. -/
inductive StableTransversal : Atlas → Atlas → Type 2
  | primitive {X Y} (transversal : Transversal X Y)
      (preserves : stableOriginPreserved transversal = true) : StableTransversal X Y
  | identity {X} : StableTransversal X X
  | composite {X Y Z} : StableTransversal Y Z → StableTransversal X Y → StableTransversal X Z

namespace StableTransversal

def underlying {X Y : Atlas} : StableTransversal X Y → Transversal X Y
  | .primitive transversal _ => transversal
  | .identity => .identity
  | .composite second first => Transversal.comp second.underlying first.underlying

theorem semantic_stable {X Y : Atlas} (f : StableTransversal X Y) :
    Datra.Semantics.IsStableTransversal f.underlying.toSemantics := by
  induction f with
  | primitive transversal preserves => exact (stableOriginPreserved_interpretation transversal).mp preserves
  | identity =>
      change Datra.Semantics.IsStableTransversal (Transversal.identity.toSemantics)
      rw [Transversal.toSemantics_identity]
      exact Datra.Semantics.IsStableTransversal.id_mem _
  | composite second first ih₂ ih₁ =>
      change Datra.Semantics.IsStableTransversal ((Transversal.comp second.underlying first.underlying).toSemantics)
      rw [Transversal.toSemantics_comp]
      exact Datra.Semantics.IsStableTransversal.comp_mem _ _ ih₁ ih₂

theorem preservesExtent {X Y : Atlas} (f : StableTransversal X Y) :
    stableOriginPreserved f.underlying = true :=
  (stableOriginPreserved_interpretation f.underlying).mpr f.semantic_stable

noncomputable def toSemantics {X Y : Atlas} (f : StableTransversal X Y) :
    (WideSubcategory.mk (WideSubcategory.mk X.toSemantics) : Datra.Semantics.StaAtlTrav) ⟶
      (WideSubcategory.mk (WideSubcategory.mk Y.toSemantics) : Datra.Semantics.StaAtlTrav) :=
  ⟨f.underlying.toSemantics, f.semantic_stable⟩

def comp {X Y Z : Atlas} : StableTransversal Y Z → StableTransversal X Y → StableTransversal X Z
  | .identity, first => first
  | second, .identity => second
  | second, .composite middle first => .composite (comp second middle) first
  | second, first => .composite second first

@[simp] theorem toSemantics_identity (X : Atlas) :
    (identity : StableTransversal X X).toSemantics =
      𝟙 (WideSubcategory.mk (WideSubcategory.mk X.toSemantics) : Datra.Semantics.StaAtlTrav) := by
  apply Subtype.ext
  exact Transversal.toSemantics_identity X

@[simp] theorem toSemantics_composite {X Y Z : Atlas}
    (second : StableTransversal Y Z) (first : StableTransversal X Y) :
    (composite second first).toSemantics = first.toSemantics ≫ second.toSemantics := by
  apply Subtype.ext
  exact Transversal.toSemantics_comp second.underlying first.underlying

theorem toSemantics_comp {X Y Z : Atlas} (second : StableTransversal Y Z) (first : StableTransversal X Y) :
    (comp second first).toSemantics = first.toSemantics ≫ second.toSemantics := by
  induction first with
  | identity => cases second <;> simp [comp]
  | primitive _ _ => cases second <;> simp [comp]
  | composite middle first ih _ => cases second <;> simp_all [comp, Category.assoc]

def mapCovered {X Y : Atlas} (f : StableTransversal X Y) : X.CertifiedCoveredElement → Y.CertifiedCoveredElement :=
  f.underlying.mapCovered

theorem mapCovered_interpretation {X Y : Atlas} (f : StableTransversal X Y)
    (c : X.CertifiedCoveredElement) (source : X.SemanticDataElement)
    (h : c.data = fromSemanticData X source) :
    (f.mapCovered c).data = fromSemanticData Y (mapSemanticData f.toSemantics.val.val source) :=
  f.underlying.mapCovered_interpretation c source h

end StableTransversal
end Datra.Executable.Atlas
