import Executable.Ordinal

namespace Datra.Executable.CoverageEnumeration
open Ordinal

/-- The coverage search enumerates all finite coefficient lists, including
noncanonical ones; canonicalization is a separate ordinal operation. -/
def decodeNaturalList (code : Nat) : List Nat :=
  if code = 0 then [] else
    (unpairNatural (code - 1)).1 :: decodeNaturalList (unpairNatural (code - 1)).2
termination_by code
decreasing_by
  have := unpairNatural_second_le (code - 1)
  omega

def encodeNaturalList : List Nat → Nat
  | [] => 0
  | value :: values => pairNatural value (encodeNaturalList values) + 1

-- ALIGN: COVERAGE-LIST-DECODE-ENCODE.
theorem decode_encode (values : List Nat) :
    decodeNaturalList (encodeNaturalList values) = values := by
  induction values with
  | nil => simp [encodeNaturalList, decodeNaturalList]
  | cons value values ih =>
      rw [encodeNaturalList, decodeNaturalList]
      simp [unpairNatural_pair, ih]

-- ALIGN: COVERAGE-LIST-ENCODE-DECODE.
theorem encode_decode (code : Nat) :
    encodeNaturalList (decodeNaturalList code) = code := by
  induction code using Nat.strong_induction_on with
  | h code ih =>
      rw [decodeNaturalList]
      split
      · rename_i hz
        simp [hz, encodeNaturalList]
      · rename_i hn
        rw [encodeNaturalList, ih (unpairNatural (code - 1)).2 (by
          have := unpairNatural_second_le (code - 1)
          omega), pair_unpairNatural]
        omega

-- ALIGN: COVERAGE-ORDINAL-ENUMERATION.
theorem ordinal_decode_encode (value : Ordinal) :
    ordinal (decodeNaturalList (encodeNaturalList value.coefficients)) = value := by
  rw [decode_encode]
  apply Ordinal.ext
  exact dropLeadingZeros_of_canonical _ value.canonical

end Datra.Executable.CoverageEnumeration
