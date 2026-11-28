import Executable.Atlas.Transposal

namespace Datra.Executable.TransposalPath

/-- Raw ordering certificates compose on the domain accepted by every stage. -/
-- ALIGN: ATLAS-ORDERED-PATH-PRESERVATION.
theorem preservesRelation {Object : Type*} {Primitive : Object → Object → Type*}
    {Raw : Object → Type*}
    (domain : ∀ {X Y}, Primitive X Y → Raw X → Prop)
    (forward : ∀ {X Y}, Primitive X Y → Raw X → Raw Y)
    (relation : ∀ {X}, Raw X → Raw X → Prop)
    (primitiveLaw : ∀ {X Y} (operation : Primitive X Y) (left right : Raw X),
      domain operation left → domain operation right → relation left right →
      relation (forward operation left) (forward operation right))
    {X Y} (arrow : AtlasHom Primitive X Y) (left right : Raw X)
    (leftValid : pathValid @domain @forward arrow left)
    (rightValid : pathValid @domain @forward arrow right)
    (related : relation left right) :
    relation (mapObject @forward arrow left) (mapObject @forward arrow right) := by
  induction arrow with
  | primitive operation => exact primitiveLaw operation left right leftValid rightValid related
  | identity => exact related
  | composite second first ih₂ ih₁ =>
      exact ih₂ _ _ leftValid.2 rightValid.2 (ih₁ left right leftValid.1 rightValid.1 related)

/-- The checked owning-domain implication supplies both path premises of an
order certificate for the same underlying native arrow. -/
-- ALIGN: ATLAS-ORDERED-OWNED-PRESERVATION.
theorem relation_of_owned_domain {Object : Type*} {Primitive : Object → Object → Type*}
    {Raw : Object → Type*}
    (domain : ∀ {X Y}, Primitive X Y → Raw X → Prop)
    (forward : ∀ {X Y}, Primitive X Y → Raw X → Raw Y)
    (relation : ∀ {X}, Raw X → Raw X → Prop)
    {X Y} (arrow : AtlasHom Primitive X Y) (owned : Raw X → Prop)
    (ownerPath : ∀ source, owned source → pathValid @domain @forward arrow source)
    (orderLaw : ∀ left right, pathValid @domain @forward arrow left →
      pathValid @domain @forward arrow right → relation left right →
      relation (mapObject @forward arrow left) (mapObject @forward arrow right))
    (left right : Raw X) (leftValid : owned left) (rightValid : owned right)
    (related : relation left right) :
    relation (mapObject @forward arrow left) (mapObject @forward arrow right) :=
  orderLaw left right (ownerPath left leftValid) (ownerPath right rightValid) related

/-- Normalizing the outer composition preserves the owner certificate of
its expanded native syntax, even when a primitive expands to an identity tree. -/
-- ALIGN: ATLAS-ORDERED-NORMALIZED-OWNERS.
theorem normalized_expansion_owners {Object : Type*}
    {Outer Native : Object → Object → Type*} {Owner : Type*}
    (operation : ∀ {X Y}, Outer X Y → AtlasHom Native X Y)
    (sourceOf targetOf : ∀ {X Y}, Native X Y → Owner)
    {X M Y} (first : AtlasHom Outer X M) : ∀ second : AtlasHom Outer M Y,
    SameOwners @sourceOf @targetOf
      ((AtlasHom.composeAtlasHoms second first).expandPrimitives @operation)
      (.composite (second.expandPrimitives @operation) (first.expandPrimitives @operation)) := by
  have ownerEta (owner : Option Owner) :
      (match owner with | none => none | some value => some value) = owner := by
    cases owner <;> rfl
  induction first with
  | identity =>
      intro second
      cases second <;> simp [AtlasHom.composeAtlasHoms, AtlasHom.expandPrimitives,
        SameOwners, sourceOwner, targetOwner, OwnersCompatible]
      all_goals exact (ownerEta _).symm
  | primitive value =>
      intro second
      cases second <;> simp [AtlasHom.composeAtlasHoms, AtlasHom.expandPrimitives,
        SameOwners, sourceOwner, targetOwner, OwnersCompatible]
      all_goals exact (ownerEta _).symm
  | composite middle first ihMiddle _ =>
      intro second
      cases second with
      | identity =>
          simp [AtlasHom.composeAtlasHoms, AtlasHom.expandPrimitives,
            SameOwners, sourceOwner, targetOwner, OwnersCompatible]
          exact (ownerEta _).symm
      | primitive value =>
          have congruent := sameOwners_comp_left @sourceOf @targetOf (first.expandPrimitives @operation)
            _ _ (ihMiddle (.primitive value))
          have assoc := owners_associativity @sourceOf @targetOf (operation value)
            (middle.expandPrimitives @operation) (first.expandPrimitives @operation)
          exact congruent.trans ⟨assoc.1.symm, assoc.2.1.symm, assoc.2.2.symm⟩
      | composite second last =>
          have congruent := sameOwners_comp_left @sourceOf @targetOf (first.expandPrimitives @operation)
            _ _ (ihMiddle (.composite second last))
          have assoc := owners_associativity @sourceOf @targetOf
            ((AtlasHom.composite second last).expandPrimitives @operation)
            (middle.expandPrimitives @operation) (first.expandPrimitives @operation)
          exact congruent.trans ⟨assoc.1.symm, assoc.2.1.symm, assoc.2.2.symm⟩

end Datra.Executable.TransposalPath

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
