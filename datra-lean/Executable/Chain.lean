import Executable.Ordinal
import Semantics

namespace Datra.Executable

/-- Chain.Internal.Chain. Surjectivity is a checked lookup, not a choice of
preimages from a semantic order. Out-of-bounds lookup is intentionally unconstrained. -/
structure Chain (Carrier : Type) where
  orderType : Ordinal
  position : Carrier → Ordinal
  lookup : Ordinal → Option Carrier
  positionBelow : ∀ x, Ordinal.ordinalLT (position x) orderType = true
  positionInjective : Function.Injective position
  positionSurjective : ∀ p, Ordinal.ordinalLT p orderType = true →
    ∃ x, lookup p = some x ∧ position x = p

/-- The executable non-strict order compares positions in the owning chain. -/
-- ALIGN: CHAIN-ORDER-PREDICATE.
def Chain.precedes {A : Type} (C : Chain A) (earlier later : A) : Bool :=
  !(Ordinal.ordinalLT (C.position later) (C.position earlier))

theorem Chain.precedes_correct {A : Type} (C : Chain A) (earlier later : A) :
    C.precedes earlier later = true ↔
      (C.position earlier).toSemantics ≤ (C.position later).toSemantics := by
  have comparison := Ordinal.ordinalLT_correct (C.position later) (C.position earlier)
  cases result : Ordinal.ordinalLT (C.position later) (C.position earlier) <;>
    simp_all [precedes, not_lt]

-- ALIGN: CHAIN-LOOKUP-POSITION.
theorem Chain.lookup_position {A : Type} (C : Chain A) (x : A) :
    C.lookup (C.position x) = some x := by
  obtain ⟨y, hy, hp⟩ := C.positionSurjective _ (C.positionBelow x)
  have he := C.positionInjective hp
  simpa [he] using hy

/-- Equal positions determine the same decoder when both reject out-of-range inputs. -/
theorem Chain.ext_of_boundedLookup {A : Type} (source target : Chain A)
    (order : source.orderType = target.orderType) (position : source.position = target.position)
    (sourceOutside : ∀ p, Ordinal.ordinalLT p source.orderType = false → source.lookup p = none)
    (targetOutside : ∀ p, Ordinal.ordinalLT p target.orderType = false → target.lookup p = none) :
    source = target := by
  have lookup : source.lookup = target.lookup := by
    funext p
    cases bound : Ordinal.ordinalLT p source.orderType with
    | false => rw [sourceOutside p bound, targetOutside p (by rwa [← order])]
    | true =>
        obtain ⟨first, firstFound, firstPosition⟩ := source.positionSurjective p bound
        obtain ⟨second, secondFound, secondPosition⟩ := target.positionSurjective p (by rwa [← order])
        have same : first = second := source.positionInjective
          (firstPosition.trans (by rw [position]; exact secondPosition.symm))
        rw [firstFound, secondFound, same]
  cases source
  cases target
  cases order
  cases position
  cases lookup
  rfl

/-- Reindex the executable decoder through a checked carrier equivalence. -/
-- ALIGN: CHAIN-REINDEX.
def Chain.reindex {A B : Type} (source : Chain A) (equiv : A ≃ B) : Chain B where
  orderType := source.orderType
  position value := source.position (equiv.symm value)
  lookup position := (source.lookup position).map equiv
  positionBelow value := source.positionBelow (equiv.symm value)
  positionInjective := source.positionInjective.comp equiv.symm.injective
  positionSurjective position below := by
    obtain ⟨value, found, same⟩ := source.positionSurjective position below
    exact ⟨equiv value, by simp [found], by simpa using same⟩

/-- Certified chain indices retain their object, just as ChainIndex does. -/
structure ChainIndex {A : Type} (C : Chain A) where
  position : Ordinal
  object : A
  below : Ordinal.ordinalLT position C.orderType = true
  position_eq : C.position object = position

def Chain.chainIndexOf {A : Type} (C : Chain A) (x : A) : ChainIndex C :=
  ⟨C.position x, x, C.positionBelow x, rfl⟩

/-- The public lookup checks the bound before consulting the stored decoder.
The decoder's behavior outside the chain is deliberately not constrained. -/
def Chain.chainIndex {A : Type} (C : Chain A) (p : Ordinal) : Option (ChainIndex C) :=
  if h : Ordinal.ordinalLT p C.orderType = true then
    match he : C.lookup p with
    | none => none
    | some x => some ⟨p, x, h, by
        obtain ⟨y, hy, hp⟩ := C.positionSurjective p h
        have : x = y := Option.some.inj (he.symm.trans hy)
        exact this ▸ hp⟩
  else none

-- ALIGN: CHAIN-INDEX-LOOKUP.
theorem Chain.chainIndex_object {A : Type} (C : Chain A) (p : Ordinal) :
    (C.chainIndex p).map ChainIndex.object =
      if Ordinal.ordinalLT p C.orderType then C.lookup p else none := by
  unfold chainIndex
  split
  · split <;> simp_all
  · rfl

-- ALIGN: CHAIN-INDEX-ROUNDTRIP.
theorem Chain.chainIndex_position {A : Type} (C : Chain A) (x : A) :
    C.chainIndex (C.position x) = some (C.chainIndexOf x) := by
  unfold chainIndex
  rw [dif_pos (C.positionBelow x)]
  split
  · rename_i he
    have := C.lookup_position x
    simp [he] at this
  · rename_i y he
    have hy : y = x := Option.some.inj (he.symm.trans (C.lookup_position x))
    subst y
    rfl

theorem Chain.chainIndex_requested {A : Type} (C : Chain A) (position : Ordinal)
    (index : ChainIndex C) (found : C.chainIndex position = some index) :
    index.position = position := by
  unfold chainIndex at found
  split at found
  · split at found
    · contradiction
    · cases Option.some.inj found
      rfl
  · contradiction

-- ALIGN: CHAIN-INDEX-BOUNDS.
theorem Chain.chainIndex_isSome {A : Type} (C : Chain A) (p : Ordinal) :
    (C.chainIndex p).isSome = Ordinal.ordinalLT p C.orderType := by
  unfold chainIndex
  split
  · rename_i h
    obtain ⟨x, hx, _⟩ := C.positionSurjective p h
    split
    · rename_i he
      simp [he] at hx
    · simp [h]
  · rename_i h
    simp_all

/-- Certified positions and objects carry the same information. -/
def Chain.indexEquiv {A : Type} (C : Chain A) : ChainIndex C ≃ A where
  toFun := ChainIndex.object
  invFun := C.chainIndexOf
  left_inv index := by
    cases index with
    | mk p x hp hx => cases hx; rfl
  right_inv _ := rfl

noncomputable def Chain.linearOrder {A : Type} (C : Chain A) : LinearOrder A :=
  LinearOrder.lift' (fun x => (C.position x).toSemantics)
    (Ordinal.toSemantics_injective.comp C.positionInjective)

end Datra.Executable

namespace Datra.Executable

/-- The semantic order uses exactly the executable positions. -/
noncomputable def Chain.toSemantics {A : Type} (C : Chain A) : Datra.Semantics.Chain := by
  letI := C.linearOrder
  let positionInto : A → Set.Iio C.orderType.toSemantics := fun x =>
    ⟨(C.position x).toSemantics, (Ordinal.ordinalLT_correct _ _).1 (C.positionBelow x)⟩
  let embedding : A ↪o C.orderType.toSemantics.toType :=
    ({ toFun := positionInto
       inj' := fun _ _ h => C.positionInjective
         (Ordinal.toSemantics_injective (congrArg Subtype.val h))
       map_rel_iff' := Iff.rfl } : A ↪o Set.Iio C.orderType.toSemantics).trans
      (_root_.Ordinal.enumIsoToType C.orderType.toSemantics).toOrderEmbedding
  letI : WellFoundedLT A := ⟨embedding.ltEmbedding.wellFounded wellFounded_lt⟩
  refine ⟨A, C.linearOrder, inferInstance, ?_⟩
  have h := embedding.ltEmbedding.ordinal_type_le
  rw [_root_.Ordinal.type_toType] at h
  exact h.trans_lt C.orderType.toSemantics_lt

end Datra.Executable

namespace Datra.Executable.Chain

-- ALIGN: CHAIN-SPINE.
def spine : Chain Nat where
  orderType := Ordinal.omega
  position := Ordinal.finiteOrdinal
  lookup := Ordinal.naturalAtOrdinal
  positionBelow n := by
    apply (Ordinal.ordinalLT_correct _ _).2
    simp only [Ordinal.finiteOrdinal_denote, Ordinal.omega_denote]
    exact _root_.Ordinal.nat_lt_omega0 n
  positionInjective := Ordinal.finiteOrdinal_injective
  positionSurjective p hp := Ordinal.naturalAtOrdinal_complete p hp

end Datra.Executable.Chain

namespace Datra.Executable.Chain
variable {A B : Type}

def sumChainPosition (left : Chain A) (right : Chain B) : Sum A B → Ordinal
  | .inl x => left.position x
  | .inr y => Ordinal.addOrdinals left.orderType (right.position y)

def sumChainLookup (left : Chain A) (right : Chain B) (position : Ordinal) : Option (Sum A B) :=
  if Ordinal.ordinalLT position left.orderType then (left.lookup position).map Sum.inl
  else if Ordinal.ordinalLT position (Ordinal.addOrdinals left.orderType right.orderType) then
    (right.lookup (Ordinal.ordinalSubtractBetween left.orderType right.orderType position)).map Sum.inr
  else none

-- ALIGN: CHAIN-SUM.
def sumChains (left : Chain A) (right : Chain B) : Chain (Sum A B) where
  orderType := Ordinal.addOrdinals left.orderType right.orderType
  position := sumChainPosition left right
  lookup := sumChainLookup left right
  positionBelow := by
    intro x
    cases x with
    | inl x => exact Ordinal.ordinalAddLeftBelow _ _ _ (left.positionBelow x)
    | inr y => exact Ordinal.ordinalAddRightBelow _ _ _ (right.positionBelow y)
  positionInjective := by
    intro x y h
    cases x with
    | inl x =>
        cases y with
        | inl y => exact congrArg Sum.inl (left.positionInjective h)
        | inr y => exact (Ordinal.ordinalAddSeparatesLeft _ _ _ (left.positionBelow x) h).elim
    | inr x =>
        cases y with
        | inl y => exact (Ordinal.ordinalAddSeparatesLeft _ _ _ (left.positionBelow y) h.symm).elim
        | inr y => exact congrArg Sum.inr (right.positionInjective
            (Ordinal.ordinalAddRightInjective _ _ _ h))
  positionSurjective := by
    intro p hp
    by_cases hl : Ordinal.ordinalLT p left.orderType = true
    · obtain ⟨x, hx, he⟩ := left.positionSurjective p hl
      refine ⟨Sum.inl x, ?_, he⟩
      simp [sumChainLookup, hl, hx]
    · have hf : Ordinal.ordinalLT p left.orderType = false := by
        cases h : Ordinal.ordinalLT p left.orderType <;> simp_all
      obtain ⟨hd, he⟩ := Ordinal.ordinalSubtractBetween_correct left.orderType right.orderType p hf hp
      obtain ⟨y, hy, heq⟩ := right.positionSurjective _ hd
      refine ⟨Sum.inr y, ?_, ?_⟩
      · simp [sumChainLookup, hf, hp, hy]
      · simp only [sumChainPosition, heq, he]

theorem sumChains_lookup_outside (left : Chain A) (right : Chain B) (position : Ordinal)
    (outside : Ordinal.ordinalLT position (sumChains left right).orderType = false) :
    (sumChains left right).lookup position = none := by
  by_cases inLeft : Ordinal.ordinalLT position left.orderType = true
  · have inside := Ordinal.ordinalAddLeftBelow left.orderType right.orderType position inLeft
    change Ordinal.ordinalLT position (sumChains left right).orderType = true at inside
    rw [outside] at inside
    contradiction
  · simp only [sumChains] at outside ⊢
    simp [sumChainLookup, inLeft, outside]

-- ALIGN: CHAIN-SUM-SEMANTICS.
noncomputable def sumOrderIso (left : Chain A) (right : Chain B) :
    (sumChains left right).toSemantics.Obj ≃o
      (Datra.Semantics.Chain.sum left.toSemantics right.toSemantics).Obj where
  toFun := toLex
  invFun := ofLex
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl
  map_rel_iff' := by
    intro x y
    change Sum.Lex
      (fun a b => (left.position a).toSemantics ≤ (left.position b).toSemantics)
      (fun a b => (right.position a).toSemantics ≤ (right.position b).toSemantics)
      x y ↔ (sumChainPosition left right x).toSemantics ≤
        (sumChainPosition left right y).toSemantics
    cases x with
    | inl x =>
        cases y with
        | inl y => exact Sum.lex_inl_inl
        | inr y =>
            constructor
            · intro _
              change (left.position x).toSemantics ≤
                (Ordinal.addOrdinals left.orderType (right.position y)).toSemantics
              rw [Ordinal.addOrdinals_denote]
              exact ((Ordinal.ordinalLT_correct _ _).1 (left.positionBelow x)).le.trans
                (_root_.Ordinal.le_add_right _ _)
            · intro _
              exact Sum.Lex.sep _ _
    | inr x =>
        cases y with
        | inl y =>
            constructor
            · intro h
              exact (Sum.lex_inr_inl h).elim
            · intro h
              change (Ordinal.addOrdinals left.orderType (right.position x)).toSemantics ≤
                (left.position y).toSemantics at h
              rw [Ordinal.addOrdinals_denote] at h
              have hy := (Ordinal.ordinalLT_correct _ _).1 (left.positionBelow y)
              exact (not_lt_of_ge ((_root_.Ordinal.le_add_right _ _).trans h) hy).elim
        | inr y =>
            rw [Sum.lex_inr_inr]
            change (right.position x).toSemantics ≤ (right.position y).toSemantics ↔
              (Ordinal.addOrdinals left.orderType (right.position x)).toSemantics ≤
                (Ordinal.addOrdinals left.orderType (right.position y)).toSemantics
            rw [Ordinal.addOrdinals_denote, Ordinal.addOrdinals_denote]
            exact (add_le_add_iff_left _).symm

end Datra.Executable.Chain
