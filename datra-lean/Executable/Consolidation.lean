import Executable.Chain

namespace Datra.Executable

/-- Consolidations retain the chosen executable right inverse. Equality of this
record therefore compares both stored maps, unlike semantic ConHom equality. -/
structure Consolidation {A B : Type} (source : Chain A) (target : Chain B) where
  map : A → B
  preimage : B → A
  monotone : ∀ x y, (source.position x).toSemantics ≤ (source.position y).toSemantics →
    (target.position (map x)).toSemantics ≤ (target.position (map y)).toSemantics
  rightInverse : ∀ y, map (preimage y) = y

namespace Consolidation
variable {A B C D : Type} {X : Chain A} {Y : Chain B} {Z : Chain C} {W : Chain D}

def identity (X : Chain A) : Consolidation X X where
  map := id
  preimage := id
  monotone := fun _ _ h => h
  rightInverse := fun _ => rfl

def comp (first : Consolidation X Y) (second : Consolidation Y Z) : Consolidation X Z where
  map := second.map ∘ first.map
  preimage := first.preimage ∘ second.preimage
  monotone := fun _ _ h => second.monotone _ _ (first.monotone _ _ h)
  rightInverse := fun y => by simp [first.rightInverse, second.rightInverse]

@[ext] theorem ext (f g : Consolidation X Y) (hm : f.map = g.map)
    (hp : f.preimage = g.preimage) : f = g := by cases f; cases g; cases hm; cases hp; rfl

-- ALIGN: CONSOLIDATION-LEFT-IDENTITY.
@[simp] theorem identity_comp (f : Consolidation X Y) : comp (identity X) f = f := by
  apply ext <;> rfl

-- ALIGN: CONSOLIDATION-RIGHT-IDENTITY.
@[simp] theorem comp_identity (f : Consolidation X Y) : comp f (identity Y) = f := by
  apply ext <;> rfl

-- ALIGN: CONSOLIDATION-ASSOC.
theorem comp_assoc (f : Consolidation X Y) (g : Consolidation Y Z) (h : Consolidation Z W) :
    comp (comp f g) h = comp f (comp g h) := by
  apply ext <;> rfl

noncomputable def toSemantics (f : Consolidation X Y) : Datra.Semantics.ConHom X.toSemantics Y.toSemantics where
  toFun := f.map
  monotone := f.monotone
  point_surjective := fun y => ⟨f.preimage y, f.rightInverse y⟩

/-- Componentwise transport on an ordinal sum retains the chosen preimages
from both consolidations, as used by merged pages. -/
-- ALIGN: CONSOLIDATION-SUM.
def sum {A' B' : Type} {X' : Chain A'} {Y' : Chain B'}
    (left : Consolidation X Y) (right : Consolidation X' Y') :
    Consolidation (Chain.sumChains X X') (Chain.sumChains Y Y') where
  map := Sum.map left.map right.map
  preimage := Sum.map left.preimage right.preimage
  monotone a b h :=
    (Chain.sumOrderIso Y Y').symm.monotone
      ((Datra.Semantics.ConHom.sum left.toSemantics right.toSemantics).monotone
        ((Chain.sumOrderIso X X').monotone h))
  rightInverse value := by
    cases value <;> simp [Sum.map, left.rightInverse, right.rightInverse]

-- ALIGN: CONSOLIDATION-SUM-INTERPRETATION.
theorem sum_interpretation {A' B' : Type} {X' : Chain A'} {Y' : Chain B'}
    (left : Consolidation X Y) (right : Consolidation X' Y')
    (value : Sum A A') :
    Chain.sumOrderIso Y Y' ((sum left right).map value) =
      (Datra.Semantics.ConHom.sum left.toSemantics right.toSemantics)
        (Chain.sumOrderIso X X' value) := by cases value <;> rfl

end Consolidation
end Datra.Executable
