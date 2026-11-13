import Executable.Ordinal

namespace Datra.Executable
namespace Trace
variable {α : Type} [DecidableEq α]

/-- The first position in a nonempty transport trace. -/
def traceStartsWith (position : α) : List α → Bool
  | [] => false
  | first :: _ => decide (position = first)

-- ALIGN: PE-TRACE-START.
theorem traceStartsWith_iff_head (position : α) (values : List α) :
    traceStartsWith position values = true ↔ values.head? = some position := by
  cases values <;> simp [traceStartsWith, eq_comm]

/-- Natural-number indexing used by both executable Atlas order operations. -/
def tracePosition (offset : Nat) : List α → Option α
  | [] => none
  | position :: rest => if offset = 0 then some position else tracePosition (offset - 1) rest

-- ALIGN: PE-TRACE-POSITION.
omit [DecidableEq α] in
theorem tracePosition_eq_drop (offset : Nat) (values : List α) :
    tracePosition offset values = (values.drop offset).head? := by
  induction values generalizing offset with
  | nil => simp [tracePosition]
  | cons position rest ih =>
      cases offset <;> simp [tracePosition, ih]

/-- PageElements.LiquidInternal.traceSuffix, with the same recursion direction. -/
def traceSuffix : List α → List α → Bool
  | [], target => decide ([] = target)
  | source@(_ :: rest), target => if source = target then true else traceSuffix rest target

-- ALIGN: PE-TRACE-SUFFIX.
theorem traceSuffix_iff (source target : List α) :
    traceSuffix source target = true ↔ target <:+ source := by
  induction source with
  | nil => simp [traceSuffix, eq_comm]
  | cons head rest ih =>
      simp only [traceSuffix, List.suffix_cons_iff]
      by_cases h : head :: rest = target
      · simp [h]
      · simp [h, ih, Ne.symm h]

/-- Negative limits, allowed by Haskell's Int interface, also trim to empty. -/
def trimTrace (limit : Int) : List α → List α
  | [] => []
  | values@(_ :: rest) => if (values.length : Int) ≤ limit then values else trimTrace limit rest

-- ALIGN: PE-TRIM-IDEMPOTENT.
omit [DecidableEq α] in
theorem trimTraceIdempotent (limit : Int) (values : List α) :
    trimTrace limit (trimTrace limit values) = trimTrace limit values := by
  induction values with
  | nil => rfl
  | cons head rest ih =>
      by_cases h : ((head :: rest).length : Int) ≤ limit
      · simp only [trimTrace, if_pos h]
      · simpa only [trimTrace, if_neg h] using ih

-- ALIGN: PE-TRIM-SUFFIX.
theorem trimTraceIsSuffix (limit : Int) (values : List α) :
    traceSuffix values (trimTrace limit values) = true := by
  rw [traceSuffix_iff]
  induction values with
  | nil => simp [trimTrace]
  | cons head rest ih =>
      by_cases h : ((head :: rest).length : Int) ≤ limit
      · simp only [trimTrace, if_pos h, List.suffix_rfl]
      · exact (by simpa only [trimTrace, if_neg h] using ih.trans (List.suffix_cons head rest))

omit [DecidableEq α] in
theorem trimTrace_eq_drop (limit : Int) (values : List α) :
    trimTrace limit values = values.drop (values.length - limit.toNat) := by
  induction values with
  | nil => simp [trimTrace]
  | cons head rest ih =>
      by_cases h : ((head :: rest).length : Int) ≤ limit
      · have hn : (head :: rest).length - limit.toNat = 0 := by
          simp only [List.length_cons] at *
          omega
        simp only [trimTrace, if_pos h, hn, List.drop_zero]
      · have hn : (head :: rest).length - limit.toNat = (rest.length - limit.toNat) + 1 := by
          simp only [List.length_cons] at *
          omega
        simp only [trimTrace, if_neg h, hn, List.drop_succ_cons, ih]

-- ALIGN: PE-TRIM-EXACT-SUFFIX.
theorem trimTraceToSuffix (source target : List α)
    (suffix : traceSuffix source target = true) (limit : Int)
    (length : limit = target.length) : trimTrace limit source = target := by
  rw [length, trimTrace_eq_drop, Int.toNat_natCast]
  exact ((List.suffix_iff_eq_drop).mp ((traceSuffix_iff _ _).mp suffix)).symm

-- ALIGN: PE-TRIM-PRESERVES-SUFFIX.
theorem trimTracePreservesSuffix (limit : Int) (source target : List α)
    (h : traceSuffix source target = true) :
    traceSuffix (trimTrace limit source) (trimTrace limit target) = true := by
  rw [traceSuffix_iff] at h ⊢
  obtain ⟨padding, rfl⟩ := h
  simp only [trimTrace_eq_drop, List.length_append]
  by_cases h : limit.toNat ≤ target.length
  · have hn : padding.length + target.length - limit.toNat =
        padding.length + (target.length - limit.toNat) := by omega
    rw [hn, ← List.drop_drop, List.drop_left]
  · have ht : target.length - limit.toNat = 0 := by omega
    rw [ht, List.drop_zero]
    have hn : padding.length + target.length - limit.toNat ≤ padding.length := by omega
    rw [List.drop_append_of_le_length hn]
    exact List.suffix_append _ _

end Trace
end Datra.Executable
