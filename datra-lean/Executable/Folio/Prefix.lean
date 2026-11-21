import Executable.PageElementLookup

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

/-- Append the remaining family pages in increasing order, retaining the supplied
prefix. The executable builder's `page` and `depth` correspond to `start = page - 1`
and `count = depth - page`; its positive-page bound makes the indices agree. -/
-- ALIGN: FOLIO-EXTEND-PREFIX.
def extendPrefix {origin : Page} (pages : Nat → Page)
    (step : ∀ n, Consolidation (pages (n + 1)).chain (pages n).chain) :
    (start count : Nat) → Folio origin (pages start) → Folio origin (pages (start + count))
  | _, 0, initial => initial
  | start, count + 1, initial =>
      let next : Folio origin (pages (start + 1)) :=
        ⟨initial.data.append (pages (start + 1)) (step start),
          initial.data.append_valid initial.valid _ _⟩
      cast (congrArg (fun n => Folio origin (pages n))
        (show start + 1 + count = start + (count + 1) by omega))
        (extendPrefix pages step (start + 1) count next)

theorem cast_traceLookup {origin : Page} (pages : Nat → Page) {first second : Nat}
    (same : first = second) (initial : Folio origin (pages first)) (page : Nat) (position : Ordinal) :
    (cast (congrArg (fun n => Folio origin (pages n)) same) initial).data.traceLookup page position =
      initial.data.traceLookup page position := by
  cases same
  rfl

theorem cast_length {origin : Page} (pages : Nat → Page) {first second : Nat}
    (same : first = second) (initial : Folio origin (pages first)) :
    (cast (congrArg (fun n => Folio origin (pages n)) same) initial).data.length = initial.data.length := by
  cases same
  rfl

theorem cast_append {origin : Page} (pages : Nat → Page)
    (step : ∀ n, Consolidation (pages (n + 1)).chain (pages n).chain) {first second : Nat}
    (same : first = second) (initial : Folio origin (pages first)) :
    cast (congrArg (fun n => Folio origin (pages (n + 1))) same)
      (⟨initial.data.append (pages (first + 1)) (step first),
        initial.data.append_valid initial.valid _ _⟩ : Folio origin (pages (first + 1))) =
      ⟨(cast (congrArg (fun n => Folio origin (pages n)) same) initial).data.append
          (pages (second + 1)) (step second),
        FolioData.append_valid _ (cast (congrArg (fun n => Folio origin (pages n)) same) initial).valid _ _⟩ := by
  cases same
  rfl

theorem extendPrefix_succ {origin : Page} (pages : Nat → Page)
    (step : ∀ n, Consolidation (pages (n + 1)).chain (pages n).chain)
    (start count : Nat) (initial : Folio origin (pages start)) :
    extendPrefix pages step start (count + 1) initial =
      ⟨(extendPrefix pages step start count initial).data.append (pages (start + count + 1)) (step (start + count)),
        FolioData.append_valid _ (extendPrefix pages step start count initial).valid _ _⟩ := by
  induction count generalizing start with
  | zero => rfl
  | succ count ih =>
      let next : Folio origin (pages (start + 1)) :=
        ⟨initial.data.append (pages (start + 1)) (step start),
          initial.data.append_valid initial.valid _ _⟩
      change cast (congrArg (fun n => Folio origin (pages n))
          (show start + 1 + (count + 1) = start + (count + 1 + 1) by omega))
        (extendPrefix pages step (start + 1) (count + 1) next) = _
      exact (congrArg (cast (congrArg (fun n => Folio origin (pages n))
          (show start + 1 + (count + 1) = start + (count + 1 + 1) by omega)))
        (ih (start + 1) next)).trans
          (cast_append pages step (show start + 1 + count = start + (count + 1) by omega) _)

-- ALIGN: FOLIO-EXTEND-FINAL-TRACE.
theorem extendPrefix_final_trace {origin : Page} (pages : Nat → Page)
    (step : ∀ n, Consolidation (pages (n + 1)).chain (pages n).chain)
    (start count : Nat) (initial : Folio origin (pages start)) (value : (pages (start + count + 1)).Carrier) :
    (extendPrefix pages step start (count + 1) initial).data.genuineTrace value =
      (pages (start + count + 1)).chain.position value ::
        (extendPrefix pages step start count initial).data.genuineTrace ((step (start + count)).map value) := by
  rw [extendPrefix_succ]
  rfl

theorem extendPrefix_length {origin : Page} (pages : Nat → Page)
    (step : ∀ n, Consolidation (pages (n + 1)).chain (pages n).chain)
    (start count : Nat) (initial : Folio origin (pages start)) :
    (extendPrefix pages step start count initial).data.length = initial.data.length + count := by
  induction count generalizing start with
  | zero => rfl
  | succ count ih =>
      let next : Folio origin (pages (start + 1)) :=
        ⟨initial.data.append (pages (start + 1)) (step start),
          initial.data.append_valid initial.valid _ _⟩
      have result := (cast_length pages (show start + 1 + count = start + (count + 1) by omega)
        (extendPrefix pages step (start + 1) count next)).trans (ih (start + 1) next)
      exact result.trans (by change initial.data.length + 1 + count = initial.data.length + (count + 1); omega)

-- ALIGN: FOLIO-EXTEND-LOOKUP-PRESERVED.
theorem extendPrefix_lookup {origin : Page} (pages : Nat → Page)
    (step : ∀ n, Consolidation (pages (n + 1)).chain (pages n).chain)
    (start count : Nat) (initial : Folio origin (pages start))
    (page : Nat) (earlier : page < initial.data.length) (position : Ordinal) :
    (extendPrefix pages step start count initial).data.traceLookup page position =
      initial.data.traceLookup page position := by
  induction count generalizing start with
  | zero => rfl
  | succ count ih =>
      let next : Folio origin (pages (start + 1)) :=
        ⟨initial.data.append (pages (start + 1)) (step start),
          initial.data.append_valid initial.valid _ _⟩
      have bound : page < next.data.length := by
        change page < initial.data.length + 1
        omega
      exact (cast_traceLookup pages (show start + 1 + count = start + (count + 1) by omega)
        (extendPrefix pages step (start + 1) count next) page position).trans
          ((ih (start + 1) next bound).trans
            (initial.data.append_traceLookup_before (pages (start + 1)) (step start) page earlier position))

-- ALIGN: FOLIO-EXTEND-INTERMEDIATE-LOOKUP.
theorem extendPrefix_through_lookup {origin : Page} (pages : Nat → Page)
    (step : ∀ n, Consolidation (pages (n + 1)).chain (pages n).chain)
    (start first remaining : Nat) (initial : Folio origin (pages start))
    (page : Nat) (earlier : page < initial.data.length + first) (position : Ordinal) :
    (extendPrefix pages step start (first + remaining) initial).data.traceLookup page position =
      (extendPrefix pages step start first initial).data.traceLookup page position := by
  induction first generalizing start with
  | zero =>
      exact (congrArg (fun count => (extendPrefix pages step start count initial).data.traceLookup page position)
        (Nat.zero_add remaining)).trans
          (extendPrefix_lookup pages step start remaining initial page earlier position)
  | succ first ih =>
      let next : Folio origin (pages (start + 1)) :=
        ⟨initial.data.append (pages (start + 1)) (step start),
          initial.data.append_valid initial.valid _ _⟩
      have bound : page < next.data.length + first := by
        change page < initial.data.length + 1 + first
        omega
      rw [show first + 1 + remaining = (first + remaining) + 1 by omega]
      exact (cast_traceLookup pages (show start + 1 + (first + remaining) = start + ((first + remaining) + 1) by omega)
        (extendPrefix pages step (start + 1) (first + remaining) next) page position).trans
          ((ih (start + 1) next bound).trans
            (cast_traceLookup pages (show start + 1 + first = start + (first + 1) by omega)
              (extendPrefix pages step (start + 1) first next) page position).symm)

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

/-- Tail-recursive extension agrees with the structural finite-prefix builder. -/
-- ALIGN: FOLIO-EXTEND-PREFIX-INTERPRETATION.
theorem extendPrefix_buildPrefix (origin : Page) (selected : origin.Carrier) (unique : ∀ x, x = selected)
    (pages : Nat → Page) (collapse : Consolidation (pages 0).chain origin.chain)
    (step : ∀ n, Consolidation (pages (n + 1)).chain (pages n).chain) (start count : Nat) :
    extendPrefix pages step start count (buildPrefix origin selected unique pages collapse step start) =
      buildPrefix origin selected unique pages collapse step (start + count) := by
  induction count generalizing start with
  | zero => rfl
  | succ count ih =>
      change cast (congrArg (fun n => Folio origin (pages n))
          (show start + 1 + count = start + (count + 1) by omega))
        (extendPrefix pages step (start + 1) count
          (buildPrefix origin selected unique pages collapse step (start + 1))) = _
      rw [ih]
      have castBuild {first second : Nat} (same : first = second) :
          cast (congrArg (fun n => Folio origin (pages n)) same)
            (buildPrefix origin selected unique pages collapse step first) =
              buildPrefix origin selected unique pages collapse step second := by
        cases same
        rfl
      exact castBuild (by omega)

theorem buildPrefix_lookup_prefix (origin : Page) (selected : origin.Carrier) (unique : ∀ x, x = selected)
    (pages : Nat → Page) (collapse : Consolidation (pages 0).chain origin.chain)
    (step : ∀ n, Consolidation (pages (n + 1)).chain (pages n).chain)
    (first final : Nat) (bound : first ≤ final) (page : Nat) (earlier : page < first + 2) (position : Ordinal) :
    (buildPrefix origin selected unique pages collapse step final).data.traceLookup page position =
      (buildPrefix origin selected unique pages collapse step first).data.traceLookup page position := by
  have found := extendPrefix_lookup pages step first (final - first)
    (buildPrefix origin selected unique pages collapse step first) page
    (by simpa only [buildPrefix_length] using earlier) position
  rw [extendPrefix_buildPrefix] at found
  exact (congrArg (fun n => (buildPrefix origin selected unique pages collapse step n).data.traceLookup page position)
    (Nat.add_sub_of_le bound)).symm.trans found

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
