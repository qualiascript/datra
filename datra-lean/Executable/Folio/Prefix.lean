import Executable.PageElements

namespace Datra.Executable

theorem Page.cast_position {source target : Page} (same : source = target) (value : source.Carrier) :
    target.chain.position (cast (congrArg Page.Carrier same) value) = source.chain.position value := by
  cases same
  rfl

theorem Page.cast_from_unique {source target : Page}
    (same : source = target) (value : source.Carrier) (unique : ∀ x, x = value) (targetValue : target.Carrier) :
    cast (congrArg Page.Carrier same) value = targetValue := by
  cases same
  exact (unique targetValue).symm

theorem FolioData.pageAt_clamp {origin final : Page} (pages : FolioData origin final) (limit n : Nat)
    (bound : pages.depth - 1 ≤ limit) : pages.pageAt (min n limit) = pages.pageAt n := by
  unfold FolioData.pageAt
  congr 1
  congr 1
  apply Fin.ext
  simp only [FolioData.paddedIndex]
  omega

theorem FolioData.index_eq_of_number {origin final : Page} (pages : FolioData origin final) {a b : pages.Index}
    (same : pages.indexNumber a = pages.indexNumber b) : a = b := by
  apply pages.indexEquivFin.injective
  apply Fin.ext
  simpa only [FolioData.indexEquivFin_val] using same


end Datra.Executable

namespace Datra.Executable.Folio

/-- A fresh singleton origin followed by a finite prefix of a page family.
Binary merge and flattened sequence share this folio constructor. -/
def buildPrefix (origin : Page) (selected : origin.Carrier) (unique : ∀ x, x = selected)
    (pages : Nat → Page) (collapse : Consolidation (pages 0).chain origin.chain)
    (step : ∀ n, Consolidation (pages (n + 1)).chain (pages n).chain) :
    (n : Nat) → Folio origin (pages n)
  | 0 => ⟨(FolioData.singleton origin selected unique).append (pages 0) collapse,
      FolioData.append_valid _ (FolioData.singleton_valid _ _ _) _ _⟩
  | n + 1 => ⟨(buildPrefix origin selected unique pages collapse step n).data.append (pages (n + 1)) (step n),
      FolioData.append_valid _ (buildPrefix origin selected unique pages collapse step n).valid _ _⟩

theorem buildPrefix_length (origin : Page) (selected : origin.Carrier) (unique : ∀ x, x = selected)
    (pages : Nat → Page) (collapse : Consolidation (pages 0).chain origin.chain)
    (step : ∀ n, Consolidation (pages (n + 1)).chain (pages n).chain) (n : Nat) :
    (buildPrefix origin selected unique pages collapse step n).data.length = n + 2 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change (buildPrefix origin selected unique pages collapse step n).data.length + 1 = n + 1 + 2
    rw [ih]

variable (origin : Page) (selected : origin.Carrier) (unique : ∀ x, x = selected)
    (pages : Nat → Page) (collapse : Consolidation (pages 0).chain origin.chain)
    (step : ∀ n, Consolidation (pages (n + 1)).chain (pages n).chain)

theorem buildPrefix_depth (n : Nat) :
    (buildPrefix origin selected unique pages collapse step n).data.depth = n + 2 := by
  rw [← (buildPrefix origin selected unique pages collapse step n).data.length_eq_depth
    (buildPrefix origin selected unique pages collapse step n).valid, buildPrefix_length]

/-- Structural index of the kth non-origin page in a finite prefix. -/
def prefixIndex : (n : Nat) → Fin (n + 1) → (buildPrefix origin selected unique pages collapse step n).data.Index
  | 0, _ => none
  | n + 1, k =>
      if last : k.val = n + 1 then none
      else some (prefixIndex n ⟨k.val, by have := k.isLt; omega⟩)

theorem prefixIndex_number (n : Nat) (k : Fin (n + 1)) :
    (buildPrefix origin selected unique pages collapse step n).data.indexNumber
      (prefixIndex origin selected unique pages collapse step n k) = k.val + 1 := by
  induction n with
  | zero => change 1 = k.val + 1; have := k.isLt; omega
  | succ n ih =>
    by_cases last : k.val = n + 1
    · simp only [prefixIndex, dif_pos last]
      change (buildPrefix origin selected unique pages collapse step n).data.depth = k.val + 1
      rw [buildPrefix_depth, last]
    · simp only [prefixIndex, dif_neg last]
      exact ih ⟨k.val, by have := k.isLt; omega⟩

theorem prefixIndex_page (n : Nat) (k : Fin (n + 1)) :
    (buildPrefix origin selected unique pages collapse step n).data.page
      (prefixIndex origin selected unique pages collapse step n k) = pages k.val := by
  induction n with
  | zero =>
    change pages 0 = pages k.val
    have zero : k.val = 0 := by have := k.isLt; omega
    rw [zero]
  | succ n ih =>
    by_cases last : k.val = n + 1
    · simp only [prefixIndex, dif_pos last]
      change pages (n + 1) = pages k.val
      rw [last]
    · simp only [prefixIndex, dif_neg last]
      exact ih ⟨k.val, by have := k.isLt; omega⟩

theorem buildPrefix_page (n : Nat) (index : (buildPrefix origin selected unique pages collapse step n).data.Index) :
    (buildPrefix origin selected unique pages collapse step n).data.page index =
      if (buildPrefix origin selected unique pages collapse step n).data.indexNumber index = 0 then origin
      else pages ((buildPrefix origin selected unique pages collapse step n).data.indexNumber index - 1) := by
  induction n with
  | zero =>
    cases index with
    | none => rfl
    | some index => cases index; rfl
  | succ n ih =>
    cases index with
    | none =>
      change pages (n + 1) = if (buildPrefix origin selected unique pages collapse step n).data.depth = 0
        then origin else pages ((buildPrefix origin selected unique pages collapse step n).data.depth - 1)
      rw [buildPrefix_depth]
      simp
    | some index => exact ih index

theorem buildPrefix_pageAt_zero (n : Nat) :
    (buildPrefix origin selected unique pages collapse step n).data.pageAt 0 = origin := by
  unfold FolioData.pageAt
  rw [buildPrefix_page, FolioData.indexEquivFin_symm_number]
  simp [FolioData.paddedIndex]

theorem buildPrefix_pageAt_succ (n k : Nat) :
    (buildPrefix origin selected unique pages collapse step n).data.pageAt (k + 1) = pages (min k n) := by
  unfold FolioData.pageAt
  rw [buildPrefix_page, FolioData.indexEquivFin_symm_number]
  simp only [FolioData.paddedIndex, buildPrefix_depth]
  have nonzero : min (k + 1) (n + 2 - 1) ≠ 0 := by omega
  rw [if_neg nonzero]
  congr 1
  omega

end Datra.Executable.Folio
