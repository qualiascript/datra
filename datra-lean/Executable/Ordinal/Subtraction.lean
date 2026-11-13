import Executable.Ordinal

namespace Datra.Executable.Ordinal

/-- The optional coefficient subtraction used by the public prefix decoder. -/
def subtractCoefficients : List Nat → List Nat → Option (List Nat)
  | [], [] => some []
  | left :: lefts, value :: values =>
      if value < left then none
      else if value = left then subtractCoefficients lefts values
      else some ((value - left) :: values)
  | _, _ => none

def subtractOrdinal (initial value : Ordinal) : Option Ordinal :=
  if value.coefficients.length < initial.coefficients.length then none
  else if initial.coefficients.length < value.coefficients.length then some (ordinal value.coefficients)
  else (subtractCoefficients initial.coefficients value.coefficients).map ordinal

-- ALIGN: ORDINAL-PREFIX-COEFFICIENTS.
theorem subtractCoefficients_equal_length (initial value : List Nat)
    (lengths : initial.length = value.length) :
    subtractCoefficients initial value =
      if lexicographicLT value initial then none else some (subtractEqualCoefficients initial value) := by
  induction initial generalizing value with
  | nil =>
    have empty : value = [] := List.length_eq_zero_iff.mp lengths.symm
    subst value
    rfl
  | cons a initial ih =>
    cases value with
    | nil => simp at lengths
    | cons b value =>
      have tailLengths : initial.length = value.length := by simpa using lengths
      by_cases below : b < a
      · simp [subtractCoefficients, lexicographicLT, below]
      · by_cases equal : b = a
        · subst b
          simpa [subtractCoefficients, subtractEqualCoefficients, lexicographicLT] using ih value tailLengths
        · have above : a < b := by omega
          simp [subtractCoefficients, subtractEqualCoefficients, lexicographicLT, below, equal, above]

/-- Prefix subtraction rejects exactly values below the prefix; successful
decoding agrees with the checked sum-interval subtraction. -/
-- ALIGN: ORDINAL-PREFIX-SUBTRACTION.
theorem subtractOrdinal_eq (initial value : Ordinal) :
    subtractOrdinal initial value =
      if ordinalLT value initial then none else some (ordinalSubtractBetween initial (finiteOrdinal 0) value) := by
  by_cases shorter : value.coefficients.length < initial.coefficients.length
  · simp [subtractOrdinal, ordinalLT, coefficientsLT, shorter]
  · by_cases longer : initial.coefficients.length < value.coefficients.length
    · have unequal : value.coefficients.length ≠ initial.coefficients.length := by omega
      simp [subtractOrdinal, ordinalLT, coefficientsLT, shorter, longer, unequal,
        ordinalSubtractBetween, ordinal, dropLeadingZeros_of_canonical _ value.canonical]
    · have lengths : initial.coefficients.length = value.coefficients.length := by omega
      rw [subtractOrdinal, if_neg shorter, if_neg longer, subtractCoefficients_equal_length _ _ lengths]
      by_cases lex : lexicographicLT value.coefficients initial.coefficients = true
      · simp [ordinalLT, coefficientsLT, lengths, lex]
      · simp [ordinalLT, coefficientsLT, lengths, ordinalSubtractBetween, lex, ordinal,
          dropLeadingZeros_of_canonical _ (subtractEqualCoefficients_canonical _ _)]

-- ALIGN: ORDINAL-PREFIX-ROUNDTRIP.
theorem subtractOrdinal_add (initial suffix : Ordinal) :
    subtractOrdinal initial (addOrdinals initial suffix) = some suffix := by
  have lower : ordinalLT (addOrdinals initial suffix) initial = false := by
    apply Bool.eq_false_iff.mpr
    intro below
    have h := (ordinalLT_correct _ _).mp below
    rw [addOrdinals_denote] at h
    exact (not_lt_of_ge (_root_.Ordinal.le_add_right _ _)) h
  rw [subtractOrdinal_eq, lower]
  simp only [Bool.false_eq_true, if_false]
  congr 1
  apply ordinalAddRightInjective initial
  exact ordinalSubtractBetween_add initial (finiteOrdinal 0) _ lower

-- ALIGN: ORDINAL-PREFIX-INVERSE-SOUND.
theorem subtractOrdinal_sound (initial value difference : Ordinal)
    (found : subtractOrdinal initial value = some difference) : addOrdinals initial difference = value := by
  rw [subtractOrdinal_eq] at found
  split at found
  · contradiction
  · rename_i lower
    have same := Option.some.inj found
    rw [← same]
    exact ordinalSubtractBetween_add _ _ _ (Bool.eq_false_iff.mpr lower)

end Datra.Executable.Ordinal
