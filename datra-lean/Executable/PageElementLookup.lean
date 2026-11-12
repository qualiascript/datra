import Executable.PageElements

namespace Datra.Executable.FolioData
variable {origin final : Page}

/-- Checked page-element construction from a page number and ordinal
position, including pages in the repeated full spine. -/
def elementAt (pages : FolioData origin final) (page : Nat) (position : Ordinal) : Option pages.ValidElement :=
  ((pages.pageAt page).chain.chainIndex position).map
    (fun index => ValidElement.ofOccurrence ⟨page, index.object⟩)

theorem elementAt_occurrence (pages : FolioData origin final) (source : pages.Occurrence) :
    pages.elementAt source.page source.toRaw.position = some (ValidElement.ofOccurrence source) := by
  simp [elementAt, Occurrence.toRaw, Chain.chainIndex_position, Chain.chainIndexOf]

-- ALIGN: PE-CHECKED-LOOKUP-ROUNDTRIP.
theorem elementAt_roundtrip (pages : FolioData origin final) (source : pages.ValidElement) :
    pages.elementAt source.val.page source.val.position = some source := by
  obtain ⟨raw, occurrence, same⟩ := source
  subst raw
  exact elementAt_occurrence pages occurrence

-- ALIGN: PE-CHECKED-LOOKUP-BOUNDS.
theorem elementAt_isSome (pages : FolioData origin final) (page : Nat) (position : Ordinal) :
    (pages.elementAt page position).isSome = Ordinal.ordinalLT position (pages.pageAt page).chain.orderType := by
  simp only [elementAt, Option.isSome_map, Chain.chainIndex_isSome]

-- ALIGN: PE-CHECKED-LOOKUP-POSITION.
theorem elementAt_page_position (pages : FolioData origin final) (page : Nat) (position : Ordinal)
    (source : pages.ValidElement) (found : pages.elementAt page position = some source) :
    source.val.page = page ∧ source.val.position = position := by
  obtain ⟨index, lookup, rfl⟩ := Option.map_eq_some_iff.mp found
  refine ⟨rfl, index.position_eq.trans ?_⟩
  unfold Chain.chainIndex at lookup
  split at lookup
  · split at lookup
    · contradiction
    · have same := Option.some.inj lookup
      cases same
      rfl
  · contradiction

theorem ValidElement.normalize_eq_of_page_bound {pages : FolioData origin final}
    (source : pages.ValidElement) (bound : source.val.page ≤ pages.depth - 1) : source.normalize = source := by
  apply ValidElement.eq_of_page_position
  · exact Nat.min_eq_left bound
  · rfl

theorem ValidElement.page_bound_of_normalize_eq {pages : FolioData origin final}
    (source : pages.ValidElement) (normalized : source.normalize = source) : source.val.page ≤ pages.depth - 1 := by
  have same := congrArg (fun x : pages.ValidElement => x.val.page) normalized
  change min source.val.page (pages.depth - 1) = source.val.page at same
  omega

end Datra.Executable.FolioData
