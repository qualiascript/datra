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

/-- Both maps and their laws are checked on the accepted carriers. -/
-- ALIGN: CONSOLIDATION-RESTRICTED.
def restricted {A B : Type} (sourceContains : A → Prop) (targetContains : B → Prop)
    (source : Chain {value // sourceContains value}) (target : Chain {value // targetContains value})
    (forward : {value // sourceContains value} → {value // targetContains value})
    (backward : {value // targetContains value} → {value // sourceContains value})
    (monotone : ∀ left right, (source.position left).toSemantics ≤ (source.position right).toSemantics →
      (target.position (forward left)).toSemantics ≤ (target.position (forward right)).toSemantics)
    (surjective : ∀ value, forward (backward value) = value) : Consolidation source target :=
  ⟨forward, backward, monotone, surjective⟩

/-- The carrier map retains both chain orders when used as opposite transport. -/
-- ALIGN: COCONSOLIDATION-MONOTONE.
theorem map_order (f : Consolidation X Y) (left right : A)
    (ordered : (X.position left).toSemantics ≤ (X.position right).toSemantics) :
    (Y.position (f.map left)).toSemantics ≤ (Y.position (f.map right)).toSemantics :=
  f.monotone left right ordered

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

theorem sum_interpretation {A' B' : Type} {X' : Chain A'} {Y' : Chain B'}
    (left : Consolidation X Y) (right : Consolidation X' Y')
    (value : Sum A A') :
    Chain.sumOrderIso Y Y' ((sum left right).map value) =
      (Datra.Semantics.ConHom.sum left.toSemantics right.toSemantics)
        (Chain.sumOrderIso X X' value) := by cases value <;> rfl

end Consolidation

/-- The concrete-chain wrapper retains the source and target before a caller
hides their carriers. Its map includes the order and chosen-preimage laws. -/
structure OrderedConsolidation (A B : Type) where
  source : Chain A
  target : Chain B
  map : Consolidation source target

namespace OrderedConsolidation

def apply {A B : Type} (value : OrderedConsolidation A B) : A → B := value.map.map

def preimage {A B : Type} (value : OrderedConsolidation A B) : B → A := value.map.preimage

-- ALIGN: CONSOLIDATION-ORDERED-PREIMAGE.
theorem preimage_apply {A B : Type} (mapping : OrderedConsolidation A B) (value : B) :
    mapping.apply (mapping.preimage value) = value := mapping.map.rightInverse value

-- ALIGN: CONSOLIDATION-ORDERED.
def orderedConsolidation {A B : Type} (source : Chain A) (target : Chain B)
    (mapping : Consolidation source target) : OrderedConsolidation A B :=
  ⟨source, target, mapping⟩

-- ALIGN: CONSOLIDATION-ORDERED-MONOTONE.
theorem orderedMonotone {A B : Type} (value : OrderedConsolidation A B)
    (left right : A) (ordered : value.source.precedes left right = true) :
    value.target.precedes (value.map.map left) (value.map.map right) = true :=
  (value.target.precedes_correct _ _).2
    (value.map.monotone left right ((value.source.precedes_correct _ _).1 ordered))

-- ALIGN: CONSOLIDATION-ORDERED-IDENTITY.
def identity {A : Type} (page : Chain A) : OrderedConsolidation A A :=
  orderedConsolidation page page (Consolidation.identity page)

-- ALIGN: CONSOLIDATION-ORDERED-COMPOSITION.
def comp {A B C : Type} (second : OrderedConsolidation B C)
    (first : OrderedConsolidation A B) (matching : first.target = second.source) :
    OrderedConsolidation A C :=
  orderedConsolidation first.source second.target
    (Consolidation.comp (matching ▸ first.map) second.map)

def sumBetween {A B C D : Type} (left : OrderedConsolidation A B) (right : OrderedConsolidation C D)
    (source : Chain (Sum A C)) (target : Chain (Sum B D))
    (sourcePosition : source.position = Chain.sumChainPosition left.source right.source)
    (targetPosition : target.position = Chain.sumChainPosition left.target right.target) :
    OrderedConsolidation (Sum A C) (Sum B D) :=
  let mapping := Consolidation.sum left.map right.map
  ⟨source, target, {
    map := mapping.map
    preimage := mapping.preimage
    monotone := by
      intro first second ordered
      rw [sourcePosition] at ordered
      rw [targetPosition]
      exact mapping.monotone first second ordered
    rightInverse := mapping.rightInverse }⟩

-- ALIGN: CONSOLIDATION-SUM.
def sum {A B C D : Type} (left : OrderedConsolidation A B) (right : OrderedConsolidation C D) :
    OrderedConsolidation (Sum A C) (Sum B D) :=
  sumBetween left right (Chain.sumChains left.source right.source)
    (Chain.sumChains left.target right.target) rfl rfl

-- ALIGN: CONSOLIDATION-SUM-INTERPRETATION.
theorem sum_interpretation {A B C D : Type} (left : OrderedConsolidation A B)
    (right : OrderedConsolidation C D) (value : Sum A C) :
    Chain.sumOrderIso left.target right.target ((sum left right).map.map value) =
      (Datra.Semantics.ConHom.sum left.map.toSemantics right.map.toSemantics)
        (Chain.sumOrderIso left.source right.source value) :=
  Consolidation.sum_interpretation left.map right.map value

/-- Transport both maps through carrier equivalences, keeping the native orders. -/
-- ALIGN: CONSOLIDATION-REINDEX.
def reindex {A B C D : Type} (mapping : OrderedConsolidation A B)
    (sourceEquiv : A ≃ C) (targetEquiv : B ≃ D) : OrderedConsolidation C D :=
  ⟨mapping.source.reindex sourceEquiv, mapping.target.reindex targetEquiv, {
    map := fun value => targetEquiv (mapping.map.map (sourceEquiv.symm value))
    preimage := fun value => sourceEquiv (mapping.map.preimage (targetEquiv.symm value))
    monotone := by
      intro first second ordered
      simpa only [Chain.reindex, Equiv.symm_apply_apply] using
        mapping.map.monotone (sourceEquiv.symm first) (sourceEquiv.symm second) ordered
    rightInverse := by
      intro value
      simp only [Equiv.symm_apply_apply, mapping.map.rightInverse, Equiv.apply_symm_apply] }⟩

-- ALIGN: CONSOLIDATION-ENDPOINTS.
def withEndpoints {A B : Type} (mapping : OrderedConsolidation A B)
    (source : Chain A) (target : Chain B)
    (sourcePositions : ∀ value, source.position value = mapping.source.position value)
    (targetPositions : ∀ value, target.position value = mapping.target.position value) :
    OrderedConsolidation A B :=
  ⟨source, target, {
    map := mapping.map.map
    preimage := mapping.map.preimage
    monotone := by
      intro first second ordered
      rw [sourcePositions, sourcePositions] at ordered
      rw [targetPositions, targetPositions]
      exact mapping.map.monotone first second ordered
    rightInverse := mapping.map.rightInverse }⟩

/-- Retain the exact chains while exposing pointwise-equal transport functions. -/
-- ALIGN: CONSOLIDATION-FUNCTIONS.
def withFunctions {A B : Type} (mapping : OrderedConsolidation A B)
    (forward : A → B) (backward : B → A)
    (forwardSame : ∀ value, forward value = mapping.map.map value)
    (backwardSame : ∀ value, backward value = mapping.map.preimage value) :
    OrderedConsolidation A B :=
  ⟨mapping.source, mapping.target, {
    map := forward
    preimage := backward
    monotone := by
      intro first second ordered
      rw [forwardSame, forwardSame]
      exact mapping.map.monotone first second ordered
    rightInverse := by
      intro value
      rw [forwardSame, backwardSame]
      exact mapping.map.rightInverse value }⟩

theorem withFunctions_eq {A B : Type} (mapping : OrderedConsolidation A B)
    (forward : A → B) (backward : B → A)
    (forwardSame : ∀ value, forward value = mapping.map.map value)
    (backwardSame : ∀ value, backward value = mapping.map.preimage value) :
    mapping.withFunctions forward backward forwardSame backwardSame = mapping := by
  have hf := funext forwardSame
  have hb := funext backwardSame
  cases mapping
  cases hf
  cases hb
  rfl

end OrderedConsolidation
end Datra.Executable
