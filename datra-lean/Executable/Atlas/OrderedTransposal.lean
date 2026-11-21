import Executable.Atlas.Transposal

namespace Datra.Executable.Atlas
open CategoryTheory

/-- The three runtime constructors retain the primitive order witness and
derive the witnesses of identities and composites structurally. -/
inductive OrderedTransposal : Atlas → Atlas → Type 2
  | primitive {X Y} (transposal : Transposal X Y)
      (preserves : ∀ x y, TransposalElement.lt x y = true →
        TransposalElement.lt (transposal.mapObject x) (transposal.mapObject y) = true) :
      OrderedTransposal X Y
  | identity {X} : OrderedTransposal X X
  | composite {X Y Z} : OrderedTransposal Y Z → OrderedTransposal X Y → OrderedTransposal X Z

namespace OrderedTransposal

def underlying {X Y : Atlas} : OrderedTransposal X Y → Transposal X Y
  | .primitive transposal _ => transposal
  | .identity => Transposal.identity _
  | .composite second first => Transposal.comp second.underlying first.underlying

def mapObject {X Y : Atlas} (f : OrderedTransposal X Y) : X.TransposalElement → Y.TransposalElement :=
  f.underlying.mapObject

-- ALIGN: ATLAS-ORDERED-PRESERVATION.
theorem preservesOrder {X Y : Atlas} (f : OrderedTransposal X Y) (x y : X.TransposalElement)
    (h : TransposalElement.lt x y = true) : TransposalElement.lt (f.mapObject x) (f.mapObject y) = true := by
  induction f with
  | primitive f preserves => exact preserves x y h
  | identity => exact h
  | composite second first ih₂ ih₁ => exact ih₂ _ _ (ih₁ x y h)

def comp {X Y Z : Atlas} : OrderedTransposal Y Z → OrderedTransposal X Y → OrderedTransposal X Z
  | .identity, first => first
  | second, .identity => second
  | second, .composite middle first => .composite (comp second middle) first
  | second, first => .composite second first

-- ALIGN: ATLAS-ORDERED-INTERPRETATION.
theorem semantic_order {X Y : Atlas} (f : OrderedTransposal X Y) :
    Datra.Semantics.IsOrderedTransposal f.underlying.hom.finiteSemantics := by
  refine ⟨f.underlying.semantic_injective, ?_⟩
  intro x y h
  have hh := (TransposalElement.lt_fromSemantics X x y).mpr h
  have hm := f.preservesOrder _ _ hh
  have hs := (TransposalElement.lt_interpretation _ _).mp hm
  simpa only [mapObject, Transposal.mapObject_interpretation,
    TransposalElement.toSemantics_fromSemantics] using hs

noncomputable def toSemantics {X Y : Atlas} (f : OrderedTransposal X Y) :
    (WideSubcategory.mk X.toSemantics : Datra.Semantics.OrdAtlTrap) ⟶
      (WideSubcategory.mk Y.toSemantics : Datra.Semantics.OrdAtlTrap) :=
  ⟨f.underlying.hom.finiteSemantics, f.semantic_order⟩

-- ALIGN: ATLAS-ORDERED-IDENTITY.
@[simp] theorem toSemantics_identity (X : Atlas) :
    (identity : OrderedTransposal X X).toSemantics =
      𝟙 (WideSubcategory.mk X.toSemantics : Datra.Semantics.OrdAtlTrap) := by
  apply Subtype.ext
  exact Hom.finiteSemantics_identity X

@[simp] theorem toSemantics_composite {X Y Z : Atlas}
    (second : OrderedTransposal Y Z) (first : OrderedTransposal X Y) :
    (composite second first).toSemantics = first.toSemantics ≫ second.toSemantics := by
  apply Subtype.ext
  exact Hom.finiteSemantics_compose second.underlying.hom first.underlying.hom

-- ALIGN: ATLAS-ORDERED-COMPOSITION.
theorem toSemantics_comp {X Y Z : Atlas} (second : OrderedTransposal Y Z) (first : OrderedTransposal X Y) :
    (comp second first).toSemantics = first.toSemantics ≫ second.toSemantics := by
  induction first with
  | identity => cases second <;> simp [comp]
  | primitive _ _ => cases second <;> simp [comp]
  | composite middle first ih _ => cases second <;> simp_all [comp, Category.assoc]

end OrderedTransposal
end Datra.Executable.Atlas
