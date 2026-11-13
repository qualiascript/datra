import Executable.PageElements

namespace Datra.Executable

/-- PageElements.Internal.PageElementIndexData retains the selected prefix,
position, and value before the runtime wrapper hides their carrier types. -/
structure PageElementIndexData (origin current : Page) where
  page : Nat
  folioPrefix : Folio origin current
  padding : Nat
  padding_eq : padding + folioPrefix.data.length = page + 1
  position : Ordinal
  value : current.Carrier
  position_eq : current.chain.position value = position

namespace PageElementIndexData
variable {origin current : Page}

/-- The stored prefix supplies both the transported trace and the cell payload. -/
def toRaw {Scope : Type u} (owner : Scope) (selected : PageElementIndexData origin current) :
    PageElement owner where
  page := selected.page
  position := current.chain.position selected.value
  trace := selected.folioPrefix.data.paddedTrace selected.padding selected.value
  cell := ⟨current.Carrier, current.chain, selected.value, selected.folioPrefix.data.depth - 1⟩

-- ALIGN: PE-CONSTRUCTED-POSITION.
theorem toRaw_page_position {Scope : Type u} (owner : Scope)
    (selected : PageElementIndexData origin current) :
    (selected.toRaw owner).page = selected.page ∧
      (selected.toRaw owner).position = selected.position :=
  ⟨rfl, selected.position_eq⟩

-- ALIGN: PE-CONSTRUCTED-TRACE-LENGTH.
theorem toRaw_trace_length {Scope : Type u} (owner : Scope)
    (selected : PageElementIndexData origin current) :
    (selected.toRaw owner).trace.length = selected.page + 1 := by
  simpa only [toRaw, FolioData.paddedTrace, List.length_append, List.length_replicate,
    FolioData.genuineTrace_length, ← selected.folioPrefix.data.length_eq_depth selected.folioPrefix.valid]
    using selected.padding_eq

theorem toRaw_origin_trace {Scope : Type u} (owner : Scope)
    (selected : PageElementIndexData origin current) :
    Trace.traceSuffix (selected.toRaw owner).trace
      [origin.chain.position selected.folioPrefix.data.originValue] = true :=
  selected.folioPrefix.data.paddedTrace_toOrigin selected.padding selected.value

end PageElementIndexData
end Datra.Executable

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

/-- A trace has only one target on a given page. -/
theorem ValidElement.arrow_target_eq {pages : FolioData origin final}
    {source a b : pages.ValidElement} (first : source ⟶ a) (second : source ⟶ b)
    (samePage : a.val.page = b.val.page) : a = b := by
  apply ValidElement.eq_of_page_position samePage
  have firstPosition := ValidElement.positionAtPage_arrow first
  have secondPosition := ValidElement.positionAtPage_arrow second
  rw [samePage] at firstPosition
  exact Option.some.inj (firstPosition.symm.trans secondPosition)

end Datra.Executable.FolioData
