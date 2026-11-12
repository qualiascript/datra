import Executable.Dominion

namespace Datra.Executable

universe u v w z

/-- An executable insertion includes its partial inverse, rather than only an
injectivity proposition. Behavior outside the image remains observable. -/
structure DomanialInsertion (A : Type u) (B : Type v) where
  map : A → B
  preimage : B → Option A
  leftInverse : ∀ x, preimage (map x) = some x

namespace DomanialInsertion
variable {A : Type u} {B : Type v} {C : Type w} {D : Type z}

-- ALIGN: INSERTION-INJECTIVE.
theorem injective (f : DomanialInsertion A B) : Function.Injective f.map := by
  intro x y h
  have := congrArg f.preimage h
  simpa [f.leftInverse] using this

def identity (A : Type u) : DomanialInsertion A A := ⟨id, some, fun _ => rfl⟩

def comp (first : DomanialInsertion A B) (second : DomanialInsertion B C) : DomanialInsertion A C where
  map := second.map ∘ first.map
  preimage := fun x => (second.preimage x).bind first.preimage
  leftInverse := fun x => by simp [second.leftInverse, first.leftInverse]

@[ext] theorem ext (f g : DomanialInsertion A B) (hm : f.map = g.map)
    (hp : f.preimage = g.preimage) : f = g := by cases f; cases g; cases hm; cases hp; rfl

@[simp] theorem identity_comp (f : DomanialInsertion A B) : comp (identity A) f = f := by
  apply ext
  · rfl
  · funext x; simp [comp, identity]

@[simp] theorem comp_identity (f : DomanialInsertion A B) : comp f (identity B) = f := by
  apply ext <;> rfl

theorem comp_assoc (f : DomanialInsertion A B) (g : DomanialInsertion B C)
    (h : DomanialInsertion C D) : comp (comp f g) h = comp f (comp g h) := by
  apply ext
  · rfl
  · funext x; simp [comp, Option.bind_assoc]

def toSemantics (f : DomanialInsertion A B) : A ↪ B := ⟨f.map, f.injective⟩

end DomanialInsertion
end Datra.Executable
