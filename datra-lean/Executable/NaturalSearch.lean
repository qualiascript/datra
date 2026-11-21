import Mathlib.Tactic

namespace Datra.Executable.NaturalSearch

/-- Ascending search of an inclusive finite interval. -/
def search (accepts : Nat → Bool) (candidate : Nat) : Nat → Option Nat
  | 0 => if accepts candidate then some candidate else none
  | remaining + 1 =>
    if accepts candidate then some candidate
    else search accepts (candidate + 1) remaining

theorem sound {accepts : Nat → Bool} {candidate remaining found : Nat}
    (h : search accepts candidate remaining = some found) :
    candidate ≤ found ∧ found ≤ candidate + remaining ∧
      accepts found = true := by
  induction remaining generalizing candidate with
  | zero =>
    cases ht : accepts candidate with
    | false => simp [search, ht] at h
    | true =>
      have hf : candidate = found := by simpa [search, ht] using h
      subst found
      exact ⟨le_rfl, by omega, ht⟩
  | succ remaining ih =>
    cases ht : accepts candidate with
    | false =>
      have hr := ih (candidate := candidate + 1) (by simpa [search, ht] using h)
      exact ⟨by omega, by omega, hr.2.2⟩
    | true =>
      have hf : candidate = found := by simpa [search, ht] using h
      subst found
      exact ⟨le_rfl, by omega, ht⟩

theorem least {accepts : Nat → Bool} {candidate remaining found earlier : Nat}
    (h : search accepts candidate remaining = some found)
    (lower : candidate ≤ earlier) (before : earlier < found) :
    accepts earlier = false := by
  induction remaining generalizing candidate with
  | zero =>
    cases ht : accepts candidate with
    | false => simp [search, ht] at h
    | true =>
      have hf : candidate = found := by simpa [search, ht] using h
      omega
  | succ remaining ih =>
    cases ht : accepts candidate with
    | false =>
      by_cases he : earlier = candidate
      · simpa [he] using ht
      · exact ih (candidate := candidate + 1)
          (by simpa [search, ht] using h) (by omega)
    | true =>
      have hf : candidate = found := by simpa [search, ht] using h
      omega

theorem complete {accepts : Nat → Bool} {candidate remaining successful : Nat}
    (lower : candidate ≤ successful) (upper : successful ≤ candidate + remaining)
    (accepted : accepts successful = true) :
    ∃ found, search accepts candidate remaining = some found := by
  induction remaining generalizing candidate with
  | zero =>
    have he : successful = candidate := by omega
    subst successful
    exact ⟨candidate, by simp [search, accepted]⟩
  | succ remaining ih =>
    cases ht : accepts candidate with
    | false =>
      have ne : successful ≠ candidate := by
        intro he
        subst successful
        simp [ht] at accepted
      obtain ⟨found, hf⟩ := ih (candidate := candidate + 1) (by omega) (by omega)
      exact ⟨found, by simpa [search, ht] using hf⟩
    | true => exact ⟨candidate, by simp [search, ht]⟩

theorem unique {accepts : Nat → Bool} {candidate leftLimit rightLimit left right : Nat}
    (hl : search accepts candidate leftLimit = some left)
    (hr : search accepts candidate rightLimit = some right) : left = right := by
  have leftSound := sound hl
  have rightSound := sound hr
  rcases lt_trichotomy left right with before | same | before
  · have rejected := least hr leftSound.1 before
    rw [leftSound.2.2] at rejected
    contradiction
  · exact same
  · have rejected := least hl rightSound.1 before
    rw [rightSound.2.2] at rejected
    contradiction

theorem trim {accepts : Nat → Bool} {candidate remaining found : Nat}
    (h : search accepts candidate remaining = some found) :
    search accepts candidate (found - candidate) = some found := by
  have accepted := sound h
  obtain ⟨value, trimmed⟩ := complete (candidate := candidate) (remaining := found - candidate)
    accepted.1 (by omega) accepted.2.2
  have same := unique trimmed h
  simpa only [same] using trimmed

theorem congruent (left right : Nat → Bool) (same : ∀ value, left value = right value)
    (candidate remaining : Nat) : search left candidate remaining = search right candidate remaining := by
  rw [funext same]

end Datra.Executable.NaturalSearch
