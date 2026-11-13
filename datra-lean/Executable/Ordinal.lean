import Mathlib

namespace Datra.Executable

/-- Descending finite Cantor coefficients, exactly as in DatraOrdinal.Internal. -/
def canonicalCoefficients : List Nat → Prop
  | [] => True
  | leading :: _ => 0 < leading

structure Ordinal where
  coefficients : List Nat
  canonical : canonicalCoefficients coefficients
  deriving DecidableEq

namespace Ordinal

def dropLeadingZeros : List Nat → List Nat
  | [] => []
  | leading :: rest => if 0 < leading then leading :: rest else dropLeadingZeros rest

theorem dropLeadingZeros_canonical (values : List Nat) :
    canonicalCoefficients (dropLeadingZeros values) := by
  induction values with
  | nil => trivial
  | cons head rest ih =>
      by_cases h : 0 < head
      · simpa only [dropLeadingZeros, if_pos h, canonicalCoefficients] using h
      · simpa only [dropLeadingZeros, if_neg h] using ih

def ordinal (values : List Nat) : Ordinal :=
  ⟨dropLeadingZeros values, dropLeadingZeros_canonical values⟩

def finiteOrdinal (n : Nat) : Ordinal := ordinal [n]
def omega : Ordinal := ordinal [1, 0]
def omegaPower (n : Nat) : Ordinal := ordinal (1 :: List.replicate n 0)

def lexicographicLT : List Nat → List Nat → Bool
  | [], _ => false
  | _, [] => false
  | left :: lefts, right :: rights =>
      if left < right then true else if right < left then false else lexicographicLT lefts rights

def coefficientsLT (left right : List Nat) : Bool :=
  decide (left.length < right.length) ||
    (decide (left.length = right.length) && lexicographicLT left right)

def ordinalLT (left right : Ordinal) : Bool := coefficientsLT left.coefficients right.coefficients

/-- The recursive equations of Haskell ordinal addition; the right summand
replaces all lower powers of omega in the left summand. -/
def addCoefficients : List Nat → List Nat → List Nat
  | left, [] => left
  | [], right => right
  | left@(a :: rest), right@(b :: tail) =>
      if left.length < right.length then right
      else if left.length = right.length then (a + b) :: tail
      else a :: addCoefficients rest right

theorem addCoefficients_canonical (left right : List Nat)
    (hl : canonicalCoefficients left) (hr : canonicalCoefficients right) :
    canonicalCoefficients (addCoefficients left right) := by
  cases left with
  | nil => cases right <;> simpa [addCoefficients] using hr
  | cons a rest =>
    cases right with
    | nil => exact hl
    | cons b tail =>
      simp only [addCoefficients]
      split
      · exact hr
      · split
        · change 0 < a + b
          change 0 < a at hl
          omega
        · exact hl

def addOrdinals (left right : Ordinal) : Ordinal :=
  ⟨addCoefficients left.coefficients right.coefficients,
    addCoefficients_canonical _ _ left.canonical right.canonical⟩

/-- Denotation does not invoke choice or a reverse enumeration. -/
noncomputable def denoteCoefficients : List Nat → _root_.Ordinal.{0}
  | [] => 0
  | leading :: rest =>
      _root_.Ordinal.omega0 ^ (rest.length : _root_.Ordinal) * leading + denoteCoefficients rest

noncomputable def toSemantics (value : Ordinal) : _root_.Ordinal.{0} :=
  denoteCoefficients value.coefficients

theorem denoteCoefficients_lt (values : List Nat) :
    denoteCoefficients values < _root_.Ordinal.omega0 ^ (values.length : _root_.Ordinal) := by
  induction values with
  | nil => simp [denoteCoefficients]
  | cons head rest ih =>
      apply _root_.Ordinal.opow_mul_add_lt_opow (_root_.Ordinal.nat_lt_omega0 head) ih
      simp

-- ALIGN: ORDINAL-BOUND.
theorem toSemantics_lt (value : Ordinal) :
    value.toSemantics < _root_.Ordinal.omega0 ^ _root_.Ordinal.omega0 := by
  exact (denoteCoefficients_lt value.coefficients).trans
    ((_root_.Ordinal.opow_lt_opow_iff_right _root_.Ordinal.one_lt_omega0).2
      (_root_.Ordinal.nat_lt_omega0 _))

-- ALIGN: ORDINAL-NORMALIZE-DENOTATION.
theorem dropLeadingZeros_denote (values : List Nat) :
    denoteCoefficients (dropLeadingZeros values) = denoteCoefficients values := by
  induction values with
  | nil => rfl
  | cons head rest ih =>
      by_cases h : 0 < head
      · rw [dropLeadingZeros, if_pos h]
      · have hz : head = 0 := by omega
        rw [dropLeadingZeros, if_neg h, ih]
        simp [hz, denoteCoefficients]

@[simp] theorem finiteOrdinal_denote (n : Nat) : (finiteOrdinal n).toSemantics = n := by
  simp [finiteOrdinal, ordinal, toSemantics, dropLeadingZeros_denote, denoteCoefficients]

example : (ordinal [0, 2, 0]).coefficients = [2, 0] := rfl
example : (addOrdinals (ordinal [1, 5]) (ordinal [1, 2])).coefficients = [2, 2] := rfl
example : ordinalLT (ordinal [9]) omega = true := rfl

end Ordinal
end Datra.Executable

namespace Datra.Executable.Ordinal
open _root_.Ordinal

private theorem head_lt {a b : Nat} {left right : List Nat}
    (lengths : left.length = right.length) (h : a < b) :
    denoteCoefficients (a :: left) < denoteCoefficients (b :: right) := by
  dsimp only [denoteCoefficients]
  rw [← lengths]
  exact (opow_mul_add_lt_opow_mul (denoteCoefficients_lt left)
    (by exact_mod_cast h)).trans_le (le_add_right _ _)

-- ALIGN: ORDINAL-LEX-COMPARE.
theorem lexicographicLT_correct (left right : List Nat) (lengths : left.length = right.length) :
    lexicographicLT left right = true ↔ denoteCoefficients left < denoteCoefficients right := by
  induction left generalizing right with
  | nil =>
      have : right = [] := List.length_eq_zero_iff.mp lengths.symm
      subst right
      simp [lexicographicLT, denoteCoefficients]
  | cons a left ih =>
      cases right with
      | nil => simp at lengths
      | cons b right =>
          have ht : left.length = right.length := by simpa using lengths
          by_cases hab : a < b
          · simp only [lexicographicLT, if_pos hab, true_iff]
            exact head_lt ht hab
          · by_cases hba : b < a
            · simp only [lexicographicLT, if_neg hab, if_pos hba, Bool.false_eq_true, false_iff]
              exact not_lt_of_gt (head_lt ht.symm hba)
            · have he : a = b := by omega
              subst b
              simp only [lexicographicLT, if_neg hab, denoteCoefficients,
                ht, add_lt_add_iff_left]
              exact ih right ht

private theorem leading_lower (a : Nat) (rest : List Nat) (h : 0 < a) :
    omega0 ^ (rest.length : _root_.Ordinal) ≤ denoteCoefficients (a :: rest) := by
  have hn : (1 : _root_.Ordinal) ≤ (a : _root_.Ordinal) := by exact_mod_cast h
  have hm := mul_le_mul_left' hn (omega0 ^ (rest.length : _root_.Ordinal))
  simpa only [mul_one] using hm.trans (le_add_right _ (denoteCoefficients rest))

private theorem shorter_lt (left right : List Nat) (hr : canonicalCoefficients right)
    (h : left.length < right.length) : denoteCoefficients left < denoteCoefficients right := by
  cases right with
  | nil => simp at h
  | cons a rest =>
      have hn : (left.length : _root_.Ordinal) ≤ (rest.length : _root_.Ordinal) := by
        exact_mod_cast (show left.length ≤ rest.length by simp only [List.length_cons] at h; omega)
      exact (denoteCoefficients_lt left).trans_le
        ((opow_le_opow_right omega0_pos hn).trans (leading_lower a rest hr))

-- ALIGN: ORDINAL-COMPARE.
theorem ordinalLT_correct (left right : Ordinal) :
    ordinalLT left right = true ↔ left.toSemantics < right.toSemantics := by
  rcases lt_trichotomy left.coefficients.length right.coefficients.length with h | h | h
  · simp only [ordinalLT, coefficientsLT, h, decide_true, Bool.true_or, true_iff]
    exact shorter_lt _ _ right.canonical h
  · simp only [ordinalLT, coefficientsLT, h, lt_self_iff_false, decide_false, decide_true,
      Bool.true_and, Bool.false_or]
    exact lexicographicLT_correct _ _ h
  · have hn := not_lt_of_gt h
    have he := ne_of_gt h
    simp only [ordinalLT, coefficientsLT, hn, he, decide_false, Bool.false_and,
      Bool.false_or, Bool.false_eq_true, false_iff]
    exact not_lt_of_gt (shorter_lt _ _ left.canonical h)

end Datra.Executable.Ordinal

namespace Datra.Executable.Ordinal
open _root_.Ordinal

private theorem denoteCoefficients_injective_length (left right : List Nat)
    (lengths : left.length = right.length)
    (h : denoteCoefficients left = denoteCoefficients right) : left = right := by
  induction left generalizing right with
  | nil => simpa using lengths.symm
  | cons a left ih =>
      cases right with
      | nil => simp at lengths
      | cons b right =>
          have ht : left.length = right.length := by simpa using lengths
          have hab : a = b := by
            rcases lt_trichotomy a b with hab | hab | hab
            · exact False.elim ((ne_of_lt (head_lt ht hab)) h)
            · exact hab
            · exact False.elim ((ne_of_gt (head_lt ht.symm hab)) h)
          subst b
          simp only [denoteCoefficients, ht] at h
          exact congrArg (List.cons a) (ih right ht (add_left_cancel h))

theorem toSemantics_injective : Function.Injective toSemantics := by
  intro left right h
  have he : left.coefficients.length = right.coefficients.length := by
    rcases lt_trichotomy left.coefficients.length right.coefficients.length with hl | he | hr
    · exact False.elim ((ne_of_lt (shorter_lt _ _ right.canonical hl)) h)
    · exact he
    · exact False.elim ((ne_of_gt (shorter_lt _ _ left.canonical hr)) h)
  have hc := denoteCoefficients_injective_length _ _ he h
  cases left
  cases right
  cases hc
  rfl

end Datra.Executable.Ordinal

namespace Datra.Executable.Ordinal
open _root_.Ordinal

theorem addCoefficients_length (left right : List Nat) :
    (addCoefficients left right).length = max left.length right.length := by
  induction left generalizing right with
  | nil => cases right <;> simp [addCoefficients]
  | cons a rest ih =>
      cases right with
      | nil => simp [addCoefficients]
      | cons b tail =>
          simp only [addCoefficients]
          split
          · simp only [List.length_cons] at *
            omega
          · split
            · simp only [List.length_cons] at *
              omega
            · simp only [List.length_cons, ih] at *
              omega

private theorem absorb_multiple {x : _root_.Ordinal} (n : Nat) (b : Nat)
    (hb : 0 < b) (hx : x < omega0 ^ (n : _root_.Ordinal)) :
    x + omega0 ^ (n : _root_.Ordinal) * b = omega0 ^ (n : _root_.Ordinal) * b := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hb)
  have hk : ((k + 1 : Nat) : _root_.Ordinal) = 1 + (k : _root_.Ordinal) := by
    norm_cast
    omega
  rw [show Nat.succ k = k + 1 from rfl, hk, mul_add, mul_one, ← add_assoc,
    add_omega0_opow hx]

-- ALIGN: ORDINAL-ADD.
theorem addCoefficients_denote (left right : List Nat) (hr : canonicalCoefficients right) :
    denoteCoefficients (addCoefficients left right) =
      denoteCoefficients left + denoteCoefficients right := by
  induction left generalizing right with
  | nil => cases right <;> simp [addCoefficients, denoteCoefficients]
  | cons a rest ih =>
      cases right with
      | nil => simp [addCoefficients, denoteCoefficients]
      | cons b tail =>
          by_cases shorter : (a :: rest).length < (b :: tail).length
          · rw [addCoefficients, if_pos shorter]
            have hn : ((a :: rest).length : _root_.Ordinal) ≤ (tail.length : _root_.Ordinal) := by
              exact_mod_cast (show (a :: rest).length ≤ tail.length by
                simp only [List.length_cons] at shorter ⊢; omega)
            have hx := (denoteCoefficients_lt (a :: rest)).trans_le
              (opow_le_opow_right omega0_pos hn)
            rw [denoteCoefficients, ← add_assoc, absorb_multiple tail.length b hr hx]
          · by_cases equal : (a :: rest).length = (b :: tail).length
            · rw [addCoefficients, if_neg shorter, if_pos equal]
              have ht : rest.length = tail.length := by simpa using equal
              have habs : denoteCoefficients rest +
                  (omega0 ^ (tail.length : _root_.Ordinal) * b + denoteCoefficients tail) =
                  omega0 ^ (tail.length : _root_.Ordinal) * b + denoteCoefficients tail := by
                rw [← add_assoc,
                  absorb_multiple tail.length b hr (ht ▸ denoteCoefficients_lt rest)]
              simp only [denoteCoefficients, ht, Nat.cast_add, mul_add, add_assoc, habs]
            · rw [addCoefficients, if_neg shorter, if_neg equal]
              have hm : max rest.length (b :: tail).length = rest.length := by
                simp only [List.length_cons] at shorter equal ⊢
                omega
              simp only [denoteCoefficients, addCoefficients_length, hm, ih _ hr, add_assoc]

@[simp] theorem addOrdinals_denote (left right : Ordinal) :
    (addOrdinals left right).toSemantics = left.toSemantics + right.toSemantics :=
  addCoefficients_denote _ _ right.canonical

end Datra.Executable.Ordinal

namespace Datra.Executable.Ordinal

/-- The checked subtraction used by sum-chain lookup. -/
def subtractEqualCoefficients : List Nat → List Nat → List Nat
  | [], _ => []
  | _, [] => []
  | initial :: prefixes, value :: values =>
      if value < initial then []
      else if value = initial then subtractEqualCoefficients prefixes values
      else (value - initial) :: values

-- ALIGN: ORDINAL-SUBTRACT-EQUAL.
theorem subtractEqualCoefficients_correct (initial value : List Nat)
    (hl : value.length = initial.length) (ho : lexicographicLT value initial = false) :
    canonicalCoefficients (subtractEqualCoefficients initial value) ∧
      addCoefficients initial (subtractEqualCoefficients initial value) = value := by
  induction initial generalizing value with
  | nil =>
      have : value = [] := List.length_eq_zero_iff.mp hl
      subst value
      exact ⟨True.intro, rfl⟩
  | cons a tail ih =>
      cases value with
      | nil => simp at hl
      | cons b rest =>
          have hlen : rest.length = tail.length := by simpa using hl
          have hba : ¬ b < a := by
            intro h
            simp [lexicographicLT, h] at ho
          by_cases he : b = a
          · subst b
            have hr : lexicographicLT rest tail = false := by
              simpa [lexicographicLT] using ho
            obtain ⟨hc, hadd⟩ := ih rest hlen hr
            simp only [subtractEqualCoefficients, lt_self_iff_false, ↓reduceIte]
            refine ⟨hc, ?_⟩
            have hd : (subtractEqualCoefficients tail rest).length ≤ tail.length := by
              have hh := congrArg List.length hadd
              rw [addCoefficients_length, hlen] at hh
              omega
            cases hdiff : subtractEqualCoefficients tail rest with
            | nil => simpa [hdiff, addCoefficients] using congrArg (List.cons a) hadd
            | cons d ds =>
                have hn : ¬ (a :: tail).length < (d :: ds).length := by
                  rw [hdiff] at hd
                  simp only [List.length_cons] at *
                  omega
                have hne : (a :: tail).length ≠ (d :: ds).length := by
                  rw [hdiff] at hd
                  simp only [List.length_cons] at *
                  omega
                simp only [addCoefficients, if_neg hn, if_neg hne]
                simpa only [hdiff] using congrArg (List.cons a) hadd
          · have hab : a < b := by omega
            have hc : 0 < b - a := by omega
            simp only [subtractEqualCoefficients, if_neg hba, if_neg he]
            refine ⟨hc, ?_⟩
            have hsum : a + (b - a) = b := by omega
            simp [addCoefficients, hlen, hsum]

end Datra.Executable.Ordinal

namespace Datra.Executable.Ordinal

@[ext] theorem ext (x y : Ordinal) (h : x.coefficients = y.coefficients) : x = y := by
  cases x
  cases y
  cases h
  rfl

theorem subtractEqualCoefficients_canonical (initial value : List Nat) :
    canonicalCoefficients (subtractEqualCoefficients initial value) := by
  induction initial generalizing value with
  | nil => cases value <;> exact True.intro
  | cons a tail ih =>
      cases value with
      | nil => exact True.intro
      | cons b rest =>
          simp only [subtractEqualCoefficients]
          split
          · exact True.intro
          · split
            · exact ih rest
            · change 0 < b - a
              omega

/-- The suffix is used only by Haskell's proof witnesses; the executable
subtraction branches depend on the initial segment and requested position. -/
def ordinalSubtractBetween (initial _suffix value : Ordinal) : Ordinal :=
  if initial.coefficients.length < value.coefficients.length then value
  else if value.coefficients.length < initial.coefficients.length then finiteOrdinal 0
  else ⟨subtractEqualCoefficients initial.coefficients value.coefficients,
    subtractEqualCoefficients_canonical _ _⟩

theorem ordinalSubtractBetween_add (initial suffix value : Ordinal)
    (h : ordinalLT value initial = false) :
    addOrdinals initial (ordinalSubtractBetween initial suffix value) = value := by
  unfold ordinalSubtractBetween
  split
  · rename_i hlen
    apply ext
    change addCoefficients initial.coefficients value.coefficients = value.coefficients
    cases hi : initial.coefficients with
    | nil => cases value.coefficients <;> rfl
    | cons a tail =>
        cases hv : value.coefficients with
        | nil => simp [hi, hv] at hlen
        | cons b rest =>
            have hh : (a :: tail).length < (b :: rest).length := by simpa [hi, hv] using hlen
            simp only [addCoefficients, if_pos hh]
  · rename_i hlen
    split
    · rename_i hshort
      have : ordinalLT value initial = true := by
        simp [ordinalLT, coefficientsLT, hshort]
      simp [this] at h
    · rename_i hshort
      have he : value.coefficients.length = initial.coefficients.length := by omega
      have ho : lexicographicLT value.coefficients initial.coefficients = false := by
        simpa [ordinalLT, coefficientsLT, he] using h
      apply ext
      exact (subtractEqualCoefficients_correct _ _ he ho).2

-- ALIGN: ORDINAL-SUBTRACT-BETWEEN.
theorem ordinalSubtractBetween_correct (initial suffix value : Ordinal)
    (lower : ordinalLT value initial = false)
    (upper : ordinalLT value (addOrdinals initial suffix) = true) :
    ordinalLT (ordinalSubtractBetween initial suffix value) suffix = true ∧
      addOrdinals initial (ordinalSubtractBetween initial suffix value) = value := by
  have he := ordinalSubtractBetween_add initial suffix value lower
  refine ⟨(ordinalLT_correct _ _).2 ?_, he⟩
  have hu := (ordinalLT_correct _ _).1 upper
  rw [← he, addOrdinals_denote, addOrdinals_denote] at hu
  exact (add_lt_add_iff_left _).1 hu

-- ALIGN: ORDINAL-ADD-LEFT-BELOW.
theorem ordinalAddLeftBelow (initial suffix value : Ordinal)
    (h : ordinalLT value initial = true) : ordinalLT value (addOrdinals initial suffix) = true := by
  apply (ordinalLT_correct _ _).2
  rw [addOrdinals_denote]
  exact ((ordinalLT_correct _ _).1 h).trans_le (_root_.Ordinal.le_add_right _ _)

-- ALIGN: ORDINAL-ADD-RIGHT-BELOW.
theorem ordinalAddRightBelow (initial left right : Ordinal)
    (h : ordinalLT left right = true) :
    ordinalLT (addOrdinals initial left) (addOrdinals initial right) = true := by
  apply (ordinalLT_correct _ _).2
  rw [addOrdinals_denote, addOrdinals_denote]
  exact add_lt_add_left ((ordinalLT_correct _ _).1 h) _

-- ALIGN: ORDINAL-ADD-RIGHT-INJECTIVE.
theorem ordinalAddRightInjective (initial left right : Ordinal)
    (h : addOrdinals initial left = addOrdinals initial right) : left = right := by
  apply toSemantics_injective
  have he := congrArg toSemantics h
  simp only [addOrdinals_denote] at he
  exact add_left_cancel he

-- ALIGN: ORDINAL-ADD-SEPARATES-LEFT.
theorem ordinalAddSeparatesLeft (initial left right : Ordinal)
    (h : ordinalLT left initial = true) : left ≠ addOrdinals initial right := by
  intro he
  have hl := (ordinalLT_correct _ _).1 h
  rw [he, addOrdinals_denote] at hl
  exact (not_lt_of_ge (_root_.Ordinal.le_add_right _ _)) hl

end Datra.Executable.Ordinal

namespace Datra.Executable.Ordinal

def naturalAtOrdinal (value : Ordinal) : Option Nat :=
  match value.coefficients with
  | [] => some 0
  | [n] => some n
  | _ => none

@[simp] theorem naturalAtOrdinal_finite (n : Nat) : naturalAtOrdinal (finiteOrdinal n) = some n := by
  cases n <;> simp [naturalAtOrdinal, finiteOrdinal, ordinal, dropLeadingZeros]

@[simp] theorem omega_denote : omega.toSemantics = _root_.Ordinal.omega0 := by
  simp [omega, ordinal, dropLeadingZeros, toSemantics, denoteCoefficients]

theorem finiteOrdinal_injective : Function.Injective finiteOrdinal := by
  intro a b h
  have := congrArg naturalAtOrdinal h
  simpa using this

-- ALIGN: ORDINAL-NATURAL-LOOKUP.
theorem naturalAtOrdinal_complete (value : Ordinal) (h : ordinalLT value omega = true) :
    ∃ n, naturalAtOrdinal value = some n ∧ finiteOrdinal n = value := by
  rcases value with ⟨coefficients, canonical⟩
  cases coefficients with
  | nil => exact ⟨0, rfl, rfl⟩
  | cons a tail =>
      have ha : 0 < a := canonical
      cases tail with
      | nil =>
          refine ⟨a, rfl, ?_⟩
          apply ext
          simp [finiteOrdinal, ordinal, dropLeadingZeros, ha]
      | cons b rest =>
          exfalso
          have hn : ¬ a < 1 := by omega
          cases rest with
          | nil =>
              simp [ordinalLT, omega, ordinal, dropLeadingZeros, coefficientsLT,
                lexicographicLT, hn] at h
          | cons c rest =>
              simp [ordinalLT, omega, ordinal, dropLeadingZeros, coefficientsLT] at h
              omega

end Datra.Executable.Ordinal

namespace Datra.Executable.Ordinal

private def triangular (n : Nat) : Nat := n * (n + 1) / 2

private theorem triangular_succ (n : Nat) : triangular (n + 1) = triangular n + n + 1 := by
  have h := Nat.triangle_succ (n + 1)
  simpa [triangular, Nat.mul_comm, Nat.add_assoc] using h

private theorem triangular_strictMono : StrictMono triangular :=
  strictMono_nat_of_lt_succ (fun n => by rw [triangular_succ]; omega)

/-- Cantor's triangular pairing, with the first coordinate added on the diagonal.
This is the enumeration used by DatraOrdinal.Internal, not Mathlib's square pairing. -/
def pairNatural (first second : Nat) : Nat := triangular (first + second) + first

def unpairNaturalGo (diagonal remaining : Nat) : Nat × Nat :=
  if remaining ≤ diagonal then (remaining, diagonal - remaining)
  else unpairNaturalGo (diagonal + 1) (remaining - diagonal - 1)
termination_by remaining

def unpairNatural (code : Nat) : Nat × Nat := unpairNaturalGo 0 code

private theorem pair_unpairNaturalGo (diagonal remaining : Nat) :
    pairNatural (unpairNaturalGo diagonal remaining).1 (unpairNaturalGo diagonal remaining).2 =
      triangular diagonal + remaining := by
  induction remaining using Nat.strong_induction_on generalizing diagonal with
  | h remaining ih =>
      rw [unpairNaturalGo]
      split
      · rename_i hle
        have hsum : remaining + (diagonal - remaining) = diagonal := by omega
        simp [pairNatural, hsum]
      · rename_i hgt
        rw [ih (remaining - diagonal - 1) (by omega) (diagonal + 1), triangular_succ]
        omega

-- ALIGN: ORDINAL-PAIR-UNPAIR.
theorem pair_unpairNatural (code : Nat) :
    pairNatural (unpairNatural code).1 (unpairNatural code).2 = code := by
  simpa [unpairNatural, triangular] using pair_unpairNaturalGo 0 code

theorem pairNatural_injective : Function.Injective (fun p : Nat × Nat => pairNatural p.1 p.2) := by
  rintro ⟨a, b⟩ ⟨c, d⟩ h
  have he : a + b = c + d := by
    by_contra hn
    rcases lt_or_gt_of_ne hn with hlt | hgt
    · have ht := triangular_strictMono.monotone (show a + b + 1 ≤ c + d by omega)
      rw [triangular_succ] at ht
      simp only [pairNatural] at h
      omega
    · have ht := triangular_strictMono.monotone (show c + d + 1 ≤ a + b by omega)
      rw [triangular_succ] at ht
      simp only [pairNatural] at h
      omega
  have ha : a = c := by
    simp only [pairNatural, he] at h
    omega
  have hb : b = d := by omega
  simp [ha, hb]

theorem unpairNatural_pair (first second : Nat) : unpairNatural (pairNatural first second) = (first, second) :=
  pairNatural_injective (pair_unpairNatural _)

theorem pairNatural_right_le (first second : Nat) : second ≤ pairNatural first second := by
  have ht : ∀ n, n ≤ triangular n := by
    intro n
    induction n with
    | zero => simp [triangular]
    | succ n ih => rw [triangular_succ]; omega
  have := ht (first + second)
  unfold pairNatural
  omega

theorem unpairNatural_second_le (code : Nat) : (unpairNatural code).2 ≤ code := by
  simpa [pair_unpairNatural] using
    pairNatural_right_le (unpairNatural code).1 (unpairNatural code).2

end Datra.Executable.Ordinal

namespace Datra.Executable.Ordinal

def coefficientTuple : Nat → Nat → Option (List Nat)
  | 0, code => if code = 0 then some [] else none
  | 1, code => some [code]
  | width + 2, code =>
      (coefficientTuple (width + 1) (unpairNatural code).2).map ((unpairNatural code).1 :: ·)

def encodeTuple : List Nat → Option Nat
  | [] => some 0
  | [value] => some value
  | value :: values => (encodeTuple values).map (pairNatural value)

theorem coefficientTuple_encode (values : List Nat) :
    (encodeTuple values).bind (coefficientTuple values.length) = some values := by
  induction values with
  | nil => rfl
  | cons a values ih =>
      cases values with
      | nil => rfl
      | cons b rest =>
          cases he : encodeTuple (b :: rest) with
          | none => simp [he] at ih
          | some code =>
              simp only [he, Option.bind_some] at ih
              rw [encodeTuple, he]
              all_goals simp_all only [Option.map_some, Option.bind_some, List.length_cons,
                coefficientTuple, unpairNatural_pair, List.cons_ne_nil]
              all_goals simp

theorem encode_coefficientTuple (width code : Nat) (values : List Nat)
    (h : coefficientTuple width code = some values) :
    values.length = width ∧ encodeTuple values = some code := by
  induction width using Nat.strong_induction_on generalizing code values with
  | h width ih =>
      cases width with
      | zero =>
          simp only [coefficientTuple] at h
          split at h
          · rename_i hc
            subst code
            cases h
            exact ⟨rfl, rfl⟩
          · contradiction
      | succ width =>
          cases width with
          | zero => cases h; exact ⟨rfl, rfl⟩
          | succ width =>
              simp only [coefficientTuple] at h
              cases hd : coefficientTuple (width + 1) (unpairNatural code).2 with
              | none => simp [hd] at h
              | some tail =>
                  simp only [hd, Option.map_some, Option.some.injEq] at h
                  subst values
                  obtain ⟨hlen, hencode⟩ := ih (width + 1) (by omega) _ tail hd
                  refine ⟨by simp [hlen], ?_⟩
                  cases tail with
                  | nil => simp at hlen
                  | cons b rest =>
                      rw [encodeTuple, hencode]
                      all_goals simp only [Option.map_some, pair_unpairNatural, List.cons_ne_nil]
                      all_goals simp

end Datra.Executable.Ordinal

namespace Datra.Executable.Ordinal

theorem dropLeadingZeros_length (values : List Nat) :
    (dropLeadingZeros values).length ≤ values.length := by
  induction values with
  | nil => rfl
  | cons a rest ih =>
      simp only [dropLeadingZeros]
      split
      · rfl
      · simp only [List.length_cons]
        omega

theorem dropLeadingZeros_of_canonical (values : List Nat) (h : canonicalCoefficients values) :
    dropLeadingZeros values = values := by
  cases values with
  | nil => rfl
  | cons a rest =>
      change 0 < a at h
      simp only [dropLeadingZeros, if_pos h]

theorem dropLeadingZeros_decomposition (values : List Nat) :
    List.replicate (values.length - (dropLeadingZeros values).length) 0 ++ dropLeadingZeros values =
      values := by
  induction values with
  | nil => rfl
  | cons a rest ih =>
      by_cases ha : 0 < a
      · simp [dropLeadingZeros, ha]
      · have haz : a = 0 := by omega
        subst a
        have hl := dropLeadingZeros_length rest
        have hn : rest.length + 1 - (dropLeadingZeros rest).length =
            (rest.length - (dropLeadingZeros rest).length) + 1 := by omega
        simpa only [dropLeadingZeros, lt_self_iff_false, ↓reduceIte, List.length_cons,
          hn, List.replicate_succ, List.cons_append] using congrArg (List.cons 0) ih

theorem lexicographicLT_zeros (values : List Nat) (width : Nat) :
    lexicographicLT values (List.replicate width 0) = false := by
  induction values generalizing width with
  | nil => cases width <;> rfl
  | cons a rest ih =>
      cases width with
      | zero => rfl
      | succ width => simp [List.replicate_succ, lexicographicLT, ih]

theorem ordinalLT_omegaPower_iff (value : Ordinal) (width : Nat) :
    ordinalLT value (omegaPower width) = true ↔ value.coefficients.length ≤ width := by
  have hc : (omegaPower width).coefficients = 1 :: List.replicate width 0 := rfl
  have hl : lexicographicLT value.coefficients (1 :: List.replicate width 0) = false := by
    cases he : value.coefficients with
    | nil => rfl
    | cons a rest =>
        have ha : 0 < a := by simpa [he, canonicalCoefficients] using value.canonical
        have hn : ¬ a < 1 := by omega
        simp [lexicographicLT, hn, lexicographicLT_zeros]
  simp [ordinalLT, coefficientsLT, hc, hl, Nat.lt_succ_iff]

def padCoefficients (width : Nat) (values : List Nat) : List Nat :=
  List.replicate (width - values.length) 0 ++ values

theorem padCoefficients_length (width : Nat) (values : List Nat) (h : values.length ≤ width) :
    (padCoefficients width values).length = width := by
  simp only [padCoefficients, List.length_append, List.length_replicate]
  omega

theorem padCoefficients_normalized (values : List Nat) :
    padCoefficients values.length (dropLeadingZeros values) = values :=
  dropLeadingZeros_decomposition values

theorem dropLeadingZeros_pad (width : Nat) (values : List Nat) :
    dropLeadingZeros (padCoefficients width values) = dropLeadingZeros values := by
  unfold padCoefficients
  generalize width - values.length = n
  induction n with
  | zero => rfl
  | succ n ih => simpa [List.replicate_succ, dropLeadingZeros] using ih

def ordinalAtNaturalRank (width code : Nat) : Option Ordinal :=
  (coefficientTuple width code).map ordinal

def naturalRankOfOrdinal (width : Nat) (value : Ordinal) : Option Nat :=
  if ordinalLT value (omegaPower width) then encodeTuple (padCoefficients width value.coefficients)
  else none

theorem ordinalAtNaturalRank_bound (width code : Nat) (value : Ordinal)
    (h : ordinalAtNaturalRank width code = some value) : ordinalLT value (omegaPower width) = true := by
  unfold ordinalAtNaturalRank at h
  cases ht : coefficientTuple width code with
  | none => simp [ht] at h
  | some values =>
      simp only [ht, Option.map_some, Option.some.injEq] at h
      subst value
      have hl := (encode_coefficientTuple width code values ht).1
      apply (ordinalLT_omegaPower_iff _ _).2
      change (dropLeadingZeros values).length ≤ width
      exact hl ▸ dropLeadingZeros_length values

end Datra.Executable.Ordinal

namespace Datra.Executable.Ordinal

-- ALIGN: ORDINAL-ENUMERATION-ENCODE.
theorem naturalRankOfOrdinal_decode (width code : Nat) (value : Ordinal)
    (h : ordinalAtNaturalRank width code = some value) :
    naturalRankOfOrdinal width value = some code := by
  have hb := ordinalAtNaturalRank_bound width code value h
  unfold ordinalAtNaturalRank at h
  cases ht : coefficientTuple width code with
  | none => simp [ht] at h
  | some values =>
      simp only [ht, Option.map_some, Option.some.injEq] at h
      subst value
      obtain ⟨hlen, hencode⟩ := encode_coefficientTuple width code values ht
      unfold naturalRankOfOrdinal
      rw [if_pos hb]
      change encodeTuple (padCoefficients width (dropLeadingZeros values)) = some code
      rw [← hlen, padCoefficients_normalized]
      exact hencode

-- ALIGN: ORDINAL-ENUMERATION-DECODE.
theorem ordinalAtNaturalRank_encode (width code : Nat) (value : Ordinal)
    (h : naturalRankOfOrdinal width value = some code) :
    ordinalAtNaturalRank width code = some value := by
  unfold naturalRankOfOrdinal at h
  split at h
  · rename_i hb
    have hl := (ordinalLT_omegaPower_iff value width).1 hb
    have hp := padCoefficients_length width value.coefficients hl
    have hd := coefficientTuple_encode (padCoefficients width value.coefficients)
    rw [h, Option.bind_some, hp] at hd
    unfold ordinalAtNaturalRank
    rw [hd, Option.map_some]
    congr 1
    apply ext
    change dropLeadingZeros (padCoefficients width value.coefficients) = value.coefficients
    rw [dropLeadingZeros_pad, dropLeadingZeros_of_canonical _ value.canonical]
  · contradiction

end Datra.Executable.Ordinal
