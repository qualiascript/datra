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

-- ALIGN: INSERTION-IDENTITY.
def identity (A : Type u) : DomanialInsertion A A := ⟨id, some, fun _ => rfl⟩

-- ALIGN: INSERTION-COMPOSITION.
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

-- ALIGN: INSERTION-IDENTITY-ROUNDTRIP.
theorem identity_roundtrip (value : A) :
    (identity A).preimage ((identity A).map value) = some value := rfl

@[simp] theorem identity_toSemantics (A : Type u) :
    (identity A).toSemantics = Function.Embedding.refl A := rfl

-- ALIGN: INSERTION-COMPOSITION-INTERPRETATION.
@[simp] theorem comp_toSemantics (first : DomanialInsertion A B) (second : DomanialInsertion B C) :
    (comp first second).toSemantics = first.toSemantics.trans second.toSemantics := rfl

-- ALIGN: INSERTION-COMPOSITION-ROUNDTRIP.
theorem comp_roundtrip (first : DomanialInsertion A B) (second : DomanialInsertion B C) (value : A) :
    (comp first second).preimage ((comp first second).map value) = some value :=
  (comp first second).leftInverse value

/-- Encode the image of an insertion using the target Dominion's ranks. -/
-- ALIGN: INSERTION-RANK-IMAGE.
def rankImage {A B : Type} (target : Dominion B) (insertion : DomanialInsertion A B) (value : A) : Nat :=
  target.rank (insertion.map value)

/-- The induced ranking retains unfiltered off-image inverse behavior, as in
the public Haskell pullback operation. -/
-- ALIGN: INSERTION-PULLBACK-UNRANK.
def pullbackUnrank {A B : Type} (target : Dominion B) (insertion : DomanialInsertion A B)
    (valueRank : Nat) : Option A :=
  (target.unrank valueRank).bind insertion.preimage

-- ALIGN: INSERTION-PULLBACK-ROUNDTRIP.
theorem pullbackRoundTrip {A B : Type} (target : Dominion B) (insertion : DomanialInsertion A B)
    (value : A) : pullbackUnrank target insertion (rankImage target insertion value) = some value := by
  simp [pullbackUnrank, rankImage, target.coherence, insertion.leftInverse]

-- ALIGN: INSERTION-PULLBACK-DOMINION.
def pullbackDominion {A B : Type} (target : Dominion B) (insertion : DomanialInsertion A B) : Dominion A where
  rank := rankImage target insertion
  unrank := pullbackUnrank target insertion
  coherence := pullbackRoundTrip target insertion

-- ALIGN: INSERTION-PULLBACK-INTERPRETATION.
theorem pullbackDominion_interpretation {A B : Type} (target : Dominion B)
    (insertion : DomanialInsertion A B) :
    (pullbackDominion target insertion).toSemantics =
      ⟨A, insertion.toSemantics.trans target.toSemantics.rank⟩ := rfl

-- ALIGN: INSERTION-RANK-PREIMAGE.
def rankImagePreimage {A B : Type} (target : Dominion B) (insertion : DomanialInsertion A B)
    (valueRank : Nat) : Option A := do
  let rootDatum ← target.unrank valueRank
  let candidate ← insertion.preimage rootDatum
  if rankImage target insertion candidate = valueRank then some candidate else none

-- ALIGN: INSERTION-RANK-ROUNDTRIP.
theorem rankImagePreimage_roundtrip {A B : Type} (target : Dominion B) (insertion : DomanialInsertion A B)
    (value : A) : rankImagePreimage target insertion (rankImage target insertion value) = some value := by
  simp [rankImagePreimage, rankImage, target.coherence, insertion.leftInverse]

-- ALIGN: INSERTION-RANK-PACKAGE.
def rankImageInsertion {A B : Type} (target : Dominion B) (insertion : DomanialInsertion A B) :
    DomanialInsertion A Nat where
  map := rankImage target insertion
  preimage := rankImagePreimage target insertion
  leftInverse := rankImagePreimage_roundtrip target insertion

-- ALIGN: INSERTION-RANK-SOUND.
theorem rankImagePreimage_sound {A B : Type} (target : Dominion B) (insertion : DomanialInsertion A B)
    (valueRank : Nat) (value : A) (found : rankImagePreimage target insertion valueRank = some value) :
    rankImage target insertion value = valueRank := by
  unfold rankImagePreimage at found
  cases decoded : target.unrank valueRank with
  | none => simp [decoded] at found
  | some rootDatum =>
    cases pulled : insertion.preimage rootDatum with
    | none => simp [decoded, pulled] at found
    | some candidate =>
      simp [decoded, pulled] at found
      obtain ⟨correct, rfl⟩ := found
      exact correct

theorem rankImagePreimage_exists_iff {A B : Type} (target : Dominion B) (insertion : DomanialInsertion A B)
    (valueRank : Nat) :
    (rankImagePreimage target insertion valueRank).isSome = true ↔
      ∃ value, rankImage target insertion value = valueRank := by
  constructor
  · intro found
    obtain ⟨value, equality⟩ := Option.isSome_iff_exists.mp found
    exact ⟨value, rankImagePreimage_sound target insertion valueRank value equality⟩
  · rintro ⟨value, rfl⟩
    rw [rankImagePreimage_roundtrip]
    rfl

/-- The retained natural ranks denote exactly the mathematical image
Dominion. Its equivalence decodes ranks using the checked executable inverse. -/
-- ALIGN: INSERTION-RANK-IMAGE-EQUIV.
def rankImageSemanticsEquiv {A B : Type} (source : Dominion A) (target : Dominion B)
    (insertion : DomanialInsertion A B) :
    {n : Nat // (rankImagePreimage target insertion n).isSome = true} ≃
      Datra.Semantics.imageDom (A := ⟨source.toSemantics⟩) (R := ⟨target.toSemantics⟩) insertion.toSemantics where
  toFun n :=
    let datum := (rankImagePreimage target insertion n.val).get n.property
    ⟨insertion.map datum, ⟨datum, rfl⟩⟩
  invFun datum := ⟨target.rank datum.val, (rankImagePreimage_exists_iff _ _ _).mpr (by
    obtain ⟨value, equality⟩ := datum.property
    exact ⟨value, congrArg target.rank equality⟩)⟩
  left_inv n := by
    apply Subtype.ext
    exact rankImagePreimage_sound _ _ _ _ (Option.some_get n.property).symm
  right_inv datum := by
    apply Subtype.ext
    apply target.rank_injective
    exact rankImagePreimage_sound _ _ _ _ (Option.some_get _).symm

-- ALIGN: INSERTION-RANK-IMAGE-EQUIV-RANK.
theorem rankImageSemanticsEquiv_rank {A B : Type} (source : Dominion A) (target : Dominion B)
    (insertion : DomanialInsertion A B)
    (n : {n : Nat // (rankImagePreimage target insertion n).isSome = true}) :
    (Datra.Semantics.imageDom (A := ⟨source.toSemantics⟩) (R := ⟨target.toSemantics⟩)
      insertion.toSemantics).toDom.rank (rankImageSemanticsEquiv source target insertion n) = n.val :=
  rankImagePreimage_sound _ _ _ _ (Option.some_get n.property).symm

end DomanialInsertion

/-- The executable opposite retains both operations of its underlying insertion. -/
structure CodomanialInsertion (A : Type u) (B : Type v) where
  unop : DomanialInsertion B A

namespace CodomanialInsertion
open CategoryTheory Opposite
variable {A : Type u} {B : Type v} {C : Type w}

def op (insertion : DomanialInsertion A B) : CodomanialInsertion B A := ⟨insertion⟩

-- ALIGN: CODOMANIAL-OP.
@[simp] theorem unop_op (insertion : DomanialInsertion A B) : (op insertion).unop = insertion := rfl

-- ALIGN: CODOMANIAL-UNOP.
@[simp] theorem op_unop (insertion : CodomanialInsertion A B) : op insertion.unop = insertion := rfl

def identity (A : Type u) : CodomanialInsertion A A := ⟨DomanialInsertion.identity A⟩

def comp (first : CodomanialInsertion A B) (second : CodomanialInsertion B C) : CodomanialInsertion A C :=
  ⟨DomanialInsertion.comp second.unop first.unop⟩

def toSemantics {A B : Type} (source : Dominion A) (target : Dominion B)
    (insertion : CodomanialInsertion A B) :
    (Opposite.op (⟨source.toSemantics⟩ : Datra.Semantics.DomIns)) ⟶
      Opposite.op (⟨target.toSemantics⟩ : Datra.Semantics.DomIns) :=
  Quiver.Hom.op (V := Datra.Semantics.DomIns)
    (X := ⟨target.toSemantics⟩) (Y := ⟨source.toSemantics⟩) insertion.unop.toSemantics

theorem identity_interpretation {A : Type} (source : Dominion A) :
    toSemantics source source (identity A) = 𝟙 _ := rfl

theorem comp_interpretation {A B C : Type} (source : Dominion A) (middle : Dominion B) (target : Dominion C)
    (first : CodomanialInsertion A B) (second : CodomanialInsertion B C) :
    toSemantics source target (comp first second) =
      toSemantics source middle first ≫ toSemantics middle target second := rfl

end CodomanialInsertion
end Datra.Executable
