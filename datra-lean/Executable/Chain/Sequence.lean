import Executable.Chain
import Executable.Ordinal.Subtraction

namespace Datra.Executable.Chain

/-- Transport both position and checked lookup through a computable carrier
equivalence. No choice is needed to recover the original payload. -/
def reindex {A B : Type} (source : Chain A) (equiv : B ≃ A) : Chain B where
  orderType := source.orderType
  position value := source.position (equiv value)
  lookup position := (source.lookup position).map equiv.symm
  positionBelow value := source.positionBelow (equiv value)
  positionInjective := source.positionInjective.comp equiv.injective
  positionSurjective position below := by
    obtain ⟨value, found, same⟩ := source.positionSurjective position below
    refine ⟨equiv.symm value, by simp [found], ?_⟩
    simpa using same

end Datra.Executable.Chain

namespace Datra.Executable.ChainSequence
open Ordinal

theorem add_assoc (a b c : Ordinal) :
    addOrdinals (addOrdinals a b) c = addOrdinals a (addOrdinals b c) := by
  apply toSemantics_injective
  simp only [addOrdinals_denote, _root_.add_assoc]

@[simp] theorem zero_add (a : Ordinal) : addOrdinals (finiteOrdinal 0) a = a := by
  apply toSemantics_injective
  simp

@[simp] theorem add_zero (a : Ordinal) : addOrdinals a (finiteOrdinal 0) = a := by
  apply toSemantics_injective
  simp

theorem not_below_add (a b : Ordinal) : ordinalLT (addOrdinals a b) a = false := by
  apply Bool.eq_false_iff.mpr
  intro below
  have h := (ordinalLT_correct _ _).mp below
  rw [addOrdinals_denote] at h
  exact (not_lt_of_ge (_root_.Ordinal.le_add_right _ _)) h

def orderSum : List Ordinal → Ordinal
  | [] => finiteOrdinal 0
  | first :: rest => addOrdinals first (orderSum rest)

theorem foldl_eq (orders : List Ordinal) (initial : Ordinal) :
    orders.foldl addOrdinals initial = addOrdinals initial (orderSum orders) := by
  induction orders generalizing initial with
  | nil => simp [orderSum]
  | cons first rest ih => simp only [List.foldl_cons, ih, orderSum, add_assoc]

/-- Haskell's left-folded total and this recursive sum agree exactly. -/
-- ALIGN: SEQUENCE-PAGE-TOTAL-ORDER.
theorem orderSum_foldl (orders : List Ordinal) :
    orderSum orders = orders.foldl addOrdinals (finiteOrdinal 0) := by
  rw [foldl_eq, zero_add]

/-- The runtime prefix accumulator stops at the requested member or the
end of the member list, whichever comes first. -/
def prefixFrom : List Ordinal → Nat → Ordinal → Ordinal
  | _, 0, accumulated => accumulated
  | [], _, accumulated => accumulated
  | first :: rest, remaining + 1, accumulated =>
      prefixFrom rest remaining (addOrdinals accumulated first)

theorem prefixFrom_foldl (orders : List Ordinal) (index : Nat) (initial : Ordinal) :
    prefixFrom orders index initial = (orders.take index).foldl addOrdinals initial := by
  induction orders generalizing index initial with
  | nil => cases index <;> rfl
  | cons first rest ih =>
    cases index with
    | zero => rfl
    | succ index => simpa only [prefixFrom, List.take_succ_cons, List.foldl_cons] using ih index _

-- ALIGN: SEQUENCE-PAGE-PREFIX-ORDER.
def prefixOrder (orders : List Ordinal) (index : Nat) : Ordinal :=
  prefixFrom orders index (finiteOrdinal 0)

@[simp] theorem prefixOrder_zero (orders : List Ordinal) :
    prefixOrder orders 0 = finiteOrdinal 0 := by cases orders <;> rfl

@[simp] theorem prefixOrder_cons_succ (first : Ordinal) (rest : List Ordinal) (index : Nat) :
    prefixOrder (first :: rest) (index + 1) = addOrdinals first (prefixOrder rest index) := by
  simp [prefixOrder, prefixFrom_foldl, foldl_eq]

def validPosition (orders : List Ordinal) (position : Nat × Ordinal) : Bool :=
  match orders[position.1]? with
  | none => false
  | some order => ordinalLT position.2 order

def position (orders : List Ordinal) (value : Nat × Ordinal) : Ordinal :=
  addOrdinals (prefixOrder orders value.1) value.2

/-- The runtime member scan with its callback replaced by the selected
member number and local ordinal position. -/
-- ALIGN: SEQUENCE-MEMBER-POSITION-RESOLVER.
def locate : List Ordinal → Ordinal → Option (Nat × Ordinal)
  | [], _ => none
  | first :: rest, value =>
    if ordinalLT value first then some (0, value)
    else (subtractOrdinal first value).bind (fun remaining =>
      (locate rest remaining).map (fun found => (found.1 + 1, found.2)))

theorem position_below (orders : List Ordinal) (value : Nat × Ordinal)
    (valid : validPosition orders value = true) :
    ordinalLT (position orders value) (orderSum orders) = true := by
  induction orders generalizing value with
  | nil => simp [validPosition] at valid
  | cons first rest ih =>
    rcases value with ⟨index, localPosition⟩
    cases index with
    | zero =>
      have valid : ordinalLT localPosition first = true := valid
      simpa [position, orderSum] using ordinalAddLeftBelow first (orderSum rest) localPosition valid
    | succ index =>
      have valid : validPosition rest (index, localPosition) = true := valid
      simpa [position, orderSum, add_assoc] using
        ordinalAddRightBelow first (position rest (index, localPosition)) (orderSum rest) (ih _ valid)

-- ALIGN: SEQUENCE-MEMBER-POSITION-ROUNDTRIP.
theorem locate_position (orders : List Ordinal) (value : Nat × Ordinal)
    (valid : validPosition orders value = true) : locate orders (position orders value) = some value := by
  induction orders generalizing value with
  | nil => simp [validPosition] at valid
  | cons first rest ih =>
    rcases value with ⟨index, localPosition⟩
    cases index with
    | zero =>
      have valid : ordinalLT localPosition first = true := valid
      simp [position, locate, valid]
    | succ index =>
      have valid : validPosition rest (index, localPosition) = true := valid
      simpa [position, locate, add_assoc, not_below_add, subtractOrdinal_add] using ih _ valid

-- ALIGN: SEQUENCE-MEMBER-POSITION-SOUND.
theorem locate_sound (orders : List Ordinal) (value : Ordinal) (found : Nat × Ordinal)
    (decoded : locate orders value = some found) :
    validPosition orders found = true ∧ position orders found = value := by
  induction orders generalizing value found with
  | nil => simp [locate] at decoded
  | cons first rest ih =>
    simp only [locate] at decoded
    split at decoded
    · rename_i below
      cases Option.some.inj decoded
      exact ⟨below, by simp [position]⟩
    · cases subtraction : subtractOrdinal first value with
      | none => simp [subtraction] at decoded
      | some remaining =>
        cases scan : locate rest remaining with
        | none => simp [subtraction, scan] at decoded
        | some tail =>
          simp only [subtraction, Option.bind_some, scan, Option.map_some] at decoded
          cases Option.some.inj decoded
          obtain ⟨valid, same⟩ := ih remaining tail scan
          refine ⟨valid, ?_⟩
          change addOrdinals (prefixOrder (first :: rest) (tail.1 + 1)) tail.2 = value
          rw [prefixOrder_cons_succ, add_assoc]
          exact (congrArg (addOrdinals first) same).trans (subtractOrdinal_sound _ _ _ subtraction)

theorem locate_complete (orders : List Ordinal) (value : Ordinal)
    (below : ordinalLT value (orderSum orders) = true) : ∃ found, locate orders value = some found := by
  induction orders generalizing value with
  | nil =>
    have h := (ordinalLT_correct _ _).mp below
    simp [orderSum] at h
  | cons first rest ih =>
    by_cases inFirst : ordinalLT value first = true
    · exact ⟨(0, value), by simp [locate, inFirst]⟩
    · have notFirst : ordinalLT value first = false := Bool.eq_false_iff.mpr inFirst
      let remaining := ordinalSubtractBetween first (finiteOrdinal 0) value
      have sub : subtractOrdinal first value = some remaining := by
        simp [subtractOrdinal_eq, notFirst, remaining]
      have remainingBelow : ordinalLT remaining (orderSum rest) = true := by
        apply (ordinalLT_correct _ _).mpr
        have h := (ordinalLT_correct _ _).mp below
        have same := subtractOrdinal_sound _ _ _ sub
        rw [← same, orderSum, addOrdinals_denote, addOrdinals_denote] at h
        exact (add_lt_add_iff_left _).mp h
      obtain ⟨found, decoded⟩ := ih remaining remainingBelow
      exact ⟨(found.1 + 1, found.2), by simp [locate, notFirst, sub, decoded]⟩

theorem locate_isSome (orders : List Ordinal) (value : Ordinal) :
    (locate orders value).isSome = ordinalLT value (orderSum orders) := by
  apply Bool.eq_iff_iff.mpr
  constructor
  · intro found
    obtain ⟨datum, decoded⟩ := Option.isSome_iff_exists.mp found
    obtain ⟨valid, same⟩ := locate_sound orders value datum decoded
    rw [← same]
    exact position_below orders datum valid
  · intro below
    obtain ⟨found, decoded⟩ := locate_complete orders value below
    simp [decoded]

abbrev Position (orders : List Ordinal) := {value : Nat × Ordinal // validPosition orders value = true}

theorem validPosition_index_lt {orders : List Ordinal} {value : Nat × Ordinal}
    (valid : validPosition orders value = true) : value.1 < orders.length := by
  unfold validPosition at valid
  cases entry : orders[value.1]? with
  | none => simp [entry] at valid
  | some order => exact (List.getElem?_eq_some_iff.mp entry).1

-- ALIGN: SEQUENCE-MEMBER-INDEX-BOUND.
theorem locate_index_lt (orders : List Ordinal) (value : Ordinal) (found : Nat × Ordinal)
    (decoded : locate orders value = some found) : found.1 < orders.length :=
  validPosition_index_lt (locate_sound orders value found decoded).1

theorem position_le_iff (orders : List Ordinal) (a b : Nat × Ordinal)
    (ha : validPosition orders a = true) (hb : validPosition orders b = true) :
    (position orders a).toSemantics ≤ (position orders b).toSemantics ↔
      a.1 < b.1 ∨ (a.1 = b.1 ∧ a.2.toSemantics ≤ b.2.toSemantics) := by
  induction orders generalizing a b with
  | nil => simp [validPosition] at ha
  | cons first rest ih =>
    rcases a with ⟨i, x⟩
    rcases b with ⟨j, y⟩
    cases i with
    | zero =>
      cases j with
      | zero => simp [position]
      | succ j =>
        have bound := (ordinalLT_correct _ _).mp ha
        change x.toSemantics < first.toSemantics at bound
        have less : x.toSemantics ≤ (addOrdinals first (position rest (j, y))).toSemantics := by
          rw [addOrdinals_denote]
          exact bound.le.trans (_root_.Ordinal.le_add_right _ _)
        simpa [position, add_assoc] using less
    | succ i =>
      cases j with
      | zero =>
        have bound := (ordinalLT_correct _ _).mp hb
        change y.toSemantics < first.toSemantics at bound
        have notLe : ¬ (addOrdinals first (position rest (i, x))).toSemantics ≤ y.toSemantics := by
          rw [addOrdinals_denote]
          intro h
          exact (not_lt_of_ge ((_root_.Ordinal.le_add_right _ _).trans h)) bound
        simpa [position, add_assoc] using notLe
      | succ j =>
        have ha : validPosition rest (i, x) = true := ha
        have hb : validPosition rest (j, y) = true := hb
        simpa [position, add_assoc, addOrdinals_denote, add_le_add_iff_left] using ih (i, x) (j, y) ha hb

/-- A finite ordinal sum with checked local-position tags. The carrier is
independent of the component payload types. -/
def chain (orders : List Ordinal) : Chain (Position orders) where
  orderType := orderSum orders
  position value := position orders value.val
  lookup value := (locate orders value).attach.map (fun found =>
    ⟨found.val, (locate_sound orders value found.val found.property).1⟩)
  positionBelow value := position_below orders value.val value.property
  positionInjective := by
    intro a b same
    apply Subtype.ext
    have := congrArg (locate orders) same
    simpa [locate_position orders a.val a.property, locate_position orders b.val b.property] using this
  positionSurjective value below := by
    obtain ⟨found, decoded⟩ := locate_complete orders value below
    let datum : Position orders := ⟨found, (locate_sound orders value found decoded).1⟩
    refine ⟨datum, ?_, (locate_sound orders value found decoded).2⟩
    rw [Option.attach_eq_some _ ⟨found, decoded⟩]
    rfl

end Datra.Executable.ChainSequence
