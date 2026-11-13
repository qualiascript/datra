import Executable.PageElements

namespace Datra.Executable.FolioData
variable {origin final : Page}

/-- Every entry of the native recursive trace is the actual interval transport
from the prefix's final page to the selected genuine page. -/
theorem genuineTrace_atIndex (pages : FolioData origin final) (target : pages.Index)
    (value : final.Carrier) :
    ((pages.genuineTrace value).drop (pages.depth - 1 - pages.indexNumber target)).head? =
      some ((pages.page target).chain.position ((pages.lastInterval target).map value)) := by
  induction pages with
  | origin => cases target; rfl
  | snoc count previous next transition ih =>
      cases target with
      | none => simp [genuineTrace, depth, indexNumber, page, lastInterval, Consolidation.identity]
      | some target =>
          have off : previous.depth - previous.indexNumber target =
              (previous.depth - 1 - previous.indexNumber target) + 1 := by
            have := previous.indexNumber_lt target
            omega
          simp only [genuineTrace, depth, Nat.add_sub_cancel, indexNumber, page, lastInterval,
            Consolidation.comp]
          rw [off, List.drop_succ_cons]
          exact ih target (transition.map value)

-- ALIGN: PE-PREFIX-TRACE-TRANSPORT.
theorem paddedTrace_atIndex (pages : FolioData origin final) (padding : Nat)
    (target : pages.Index) (value : final.Carrier) :
    ((pages.paddedTrace padding value).drop
        (padding + pages.depth - 1 - pages.indexNumber target)).head? =
      some ((pages.page target).chain.position ((pages.lastInterval target).map value)) := by
  have off : padding + pages.depth - 1 - pages.indexNumber target =
      padding + (pages.depth - 1 - pages.indexNumber target) := by
    have := pages.indexNumber_lt target
    omega
  rw [paddedTrace, off, ← List.drop_drop]
  simpa using pages.genuineTrace_atIndex target value

-- ALIGN: PE-PADDED-TRACE-POSITION.
theorem paddedTrace_atPadded (pages : FolioData origin final) (padding target : Nat)
    (lower : pages.depth - 1 ≤ target) (upper : target ≤ padding + pages.depth - 1)
    (value : final.Carrier) :
    ((pages.paddedTrace padding value).drop (padding + pages.depth - 1 - target)).head? =
      some (final.chain.position value) := by
  have bound : padding + pages.depth - 1 - target ≤ padding := by
    have := pages.depth_positive
    omega
  rw [paddedTrace, List.drop_append_of_le_length (by simpa using bound), List.drop_replicate]
  cases padding - (padding + pages.depth - 1 - target) <;>
    simp [genuineTrace_head, List.replicate_succ]

end Datra.Executable.FolioData

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
  trace : List Ordinal
  trace_eq : trace = folioPrefix.data.paddedTrace padding value

namespace PageElementIndexData
variable {origin current : Page}

/-- Assemble a certified trace before hiding the prefix's carrier types. -/
def fromGenuine (page : Nat) (folioPrefix : Folio origin current) (padding : Nat)
    (padding_eq : padding + folioPrefix.data.length = page + 1) (value : current.Carrier)
    (genuine : List Ordinal) (genuine_eq : genuine = folioPrefix.data.genuineTrace value) :
    PageElementIndexData origin current where
  page := page
  folioPrefix := folioPrefix
  padding := padding
  padding_eq := padding_eq
  position := current.chain.position value
  value := value
  position_eq := rfl
  trace := List.replicate padding (current.chain.position value) ++ genuine
  trace_eq := by rw [genuine_eq]; rfl

/-- The stored prefix supplies both the transported trace and the cell payload. -/
def toRaw {Scope : Type u} (owner : Scope) (selected : PageElementIndexData origin current) :
    PageElement owner where
  page := selected.page
  position := current.chain.position selected.value
  trace := selected.trace
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
  simpa only [toRaw, selected.trace_eq, FolioData.paddedTrace, List.length_append, List.length_replicate,
    FolioData.genuineTrace_length, ← selected.folioPrefix.data.length_eq_depth selected.folioPrefix.valid]
    using selected.padding_eq

theorem toRaw_origin_trace {Scope : Type u} (owner : Scope)
    (selected : PageElementIndexData origin current) :
    Trace.traceSuffix (selected.toRaw owner).trace
      [origin.chain.position selected.folioPrefix.data.originValue] = true := by
  simpa only [toRaw, selected.trace_eq] using
    selected.folioPrefix.data.paddedTrace_toOrigin selected.padding selected.value

-- ALIGN: PE-CONSTRUCTED-TRACE-HEAD.
theorem toRaw_trace_head {Scope : Type u} (owner : Scope)
    (selected : PageElementIndexData origin current) :
    Trace.traceStartsWith selected.position (selected.toRaw owner).trace = true := by
  rw [Trace.traceStartsWith_iff_head]
  simpa only [toRaw, selected.trace_eq, selected.position_eq] using
    selected.folioPrefix.data.paddedTrace_head selected.padding selected.value

-- ALIGN: PE-INDEX-TRACE-CACHE.
theorem toRaw_trace_computed {Scope : Type u} (owner : Scope)
    (selected : PageElementIndexData origin current) :
    (selected.toRaw owner).trace =
      selected.folioPrefix.data.paddedTrace selected.padding selected.value := selected.trace_eq

/-- Reading a cached trace at a genuine page recovers its folio transport. -/
theorem toRaw_positionAtIndex {Scope : Type u} (owner : Scope)
    (selected : PageElementIndexData origin current) (target : selected.folioPrefix.data.Index) :
    PageElement.positionAtPage (selected.folioPrefix.data.indexNumber target) (selected.toRaw owner) =
      some ((selected.folioPrefix.data.page target).chain.position
        ((selected.folioPrefix.data.lastInterval target).map selected.value)) := by
  have page_eq : selected.page = selected.padding + selected.folioPrefix.data.depth - 1 := by
    have h := selected.padding_eq
    rw [selected.folioPrefix.data.length_eq_depth selected.folioPrefix.valid] at h
    omega
  simpa only [PageElement.positionAtPage, toRaw, selected.trace_eq, page_eq] using
    selected.folioPrefix.data.paddedTrace_atIndex selected.padding target selected.value

theorem toRaw_positionAtPadded {Scope : Type u} (owner : Scope)
    (selected : PageElementIndexData origin current) (target : Nat)
    (lower : selected.folioPrefix.data.depth - 1 ≤ target) (upper : target ≤ selected.page) :
    PageElement.positionAtPage target (selected.toRaw owner) = some selected.position := by
  have page_eq : selected.page = selected.padding + selected.folioPrefix.data.depth - 1 := by
    have h := selected.padding_eq
    rw [selected.folioPrefix.data.length_eq_depth selected.folioPrefix.valid] at h
    omega
  simpa only [PageElement.positionAtPage, toRaw, selected.trace_eq, page_eq,
    selected.position_eq] using selected.folioPrefix.data.paddedTrace_atPadded
      selected.padding target lower (by simpa only [← page_eq] using upper) selected.value

end PageElementIndexData
end Datra.Executable

namespace Datra.Executable.FolioData
variable {origin final : Page}

/-- A stored prefix is obtained only by removing final snoc steps. -/
inductive IsPrefix {origin : Page} : {final current : Page} →
    FolioData origin final → FolioData origin current → Prop
  | refl {final : Page} (pages : FolioData origin final) : IsPrefix pages pages
  | step {previous current : Page} (count : Nat) (pages : FolioData origin previous)
      (next : Page) (transition : Consolidation next.chain previous.chain)
      {selected : FolioData origin current} : IsPrefix pages selected →
      IsPrefix (.snoc count pages next transition) selected

structure SelectedPrefix (pages : FolioData origin final) (page : Nat) where
  current : Page
  folioPrefix : Folio origin current
  padding : Nat
  padding_eq : padding + folioPrefix.data.length = page + 1
  belongs : IsPrefix pages folioPrefix.data

/-- The same recursive prefix selection used by Haskell's page lookup. -/
def selectPrefix : {origin final : Page} → (pages : FolioData origin final) → pages.Valid →
    (page : Nat) → SelectedPrefix pages page
  | _, _, .origin origin count selected unique, valid, page =>
      ⟨origin, ⟨.origin origin count selected unique, valid⟩, page,
        congrArg (page + ·) valid, .refl _⟩
  | _, _, .snoc count previous next transition, valid, page =>
      if h : previous.length ≤ page then
        ⟨next, ⟨.snoc count previous next transition, valid⟩, page - previous.length, by
          change page - previous.length + count = page + 1
          have := valid.2
          omega, .refl _⟩
      else
        let selected := selectPrefix previous valid.1 page
        ⟨selected.current, selected.folioPrefix, selected.padding, selected.padding_eq,
          .step count previous next transition selected.belongs⟩


def prefixTraceLookup (pages : FolioData origin final) (padding : Nat) (position : Ordinal) :
    Option (List Ordinal) :=
  (final.chain.chainIndex position).map (fun index => pages.paddedTrace padding index.object)

def SelectedPrefix.lookupTrace {pages : FolioData origin final} {page : Nat}
    (selected : SelectedPrefix pages page) (position : Ordinal) : Option (List Ordinal) :=
  prefixTraceLookup selected.folioPrefix.data selected.padding position

/-- The canonical scalar observation of native page lookup. -/
def traceLookup {origin final : Page} : FolioData origin final → Nat → Ordinal → Option (List Ordinal)
  | pages@(.origin ..), page, position => prefixTraceLookup pages page position
  | pages@(.snoc _ previous _ _), page, position =>
      if previous.length ≤ page then prefixTraceLookup pages (page - previous.length) position
      else traceLookup previous page position

theorem selectPrefix_traceLookup (pages : FolioData origin final) (valid : pages.Valid)
    (page : Nat) (position : Ordinal) :
    traceLookup pages page position = (selectPrefix pages valid page).lookupTrace position := by
  induction pages with
  | origin =>
      rw [selectPrefix]
      rfl
  | snoc count previous next transition ih =>
      by_cases h : previous.length ≤ page
      · simp only [traceLookup, if_pos h]
        rw [selectPrefix, dif_pos h]
        rfl
      · simp only [traceLookup, if_neg h]
        rw [selectPrefix, dif_neg h]
        exact ih valid.1

/-- The runtime wrapper existentially hides the selected prefix's last carrier. -/
def indexInFolio (pages : FolioData origin final) (valid : pages.Valid)
    (page : Nat) (position : Ordinal) : Option (Σ current, PageElementIndexData origin current) :=
  let selected := selectPrefix pages valid page
  (selected.current.chain.chainIndex position).map fun index =>
    ⟨selected.current, PageElementIndexData.fromGenuine page selected.folioPrefix
      selected.padding selected.padding_eq index.object
      (selected.folioPrefix.data.genuineTrace index.object) rfl⟩

-- ALIGN: PE-LOOKUP-OWNING-TRACE.
theorem indexInFolio_trace (pages : FolioData origin final) (valid : pages.Valid)
    (page : Nat) (position : Ordinal) :
    (indexInFolio pages valid page position).map (fun selected => selected.2.trace) =
      traceLookup pages page position := by
  rw [selectPrefix_traceLookup pages valid page position]
  simp only [indexInFolio, Option.map_map, SelectedPrefix.lookupTrace, prefixTraceLookup, PageElementIndexData.fromGenuine,
    paddedTrace, Function.comp_def]

-- ALIGN: PE-LOOKUP-STORED-PREFIX.
theorem indexInFolio_prefix (pages : FolioData origin final) (valid : pages.Valid)
    (page : Nat) (position : Ordinal) (selected : Σ current, PageElementIndexData origin current)
    (found : indexInFolio pages valid page position = some selected) :
    IsPrefix pages selected.2.folioPrefix.data := by
  obtain ⟨index, _, rfl⟩ := Option.map_eq_some_iff.mp found
  exact (selectPrefix pages valid page).belongs

-- ALIGN: PE-NATIVE-LOOKUP-POSITION.
theorem indexInFolio_page_position (pages : FolioData origin final) (valid : pages.Valid)
    (page : Nat) (position : Ordinal) (selected : Σ current, PageElementIndexData origin current)
    (found : indexInFolio pages valid page position = some selected) :
    selected.2.page = page ∧ selected.2.position = position := by
  obtain ⟨index, lookup, rfl⟩ := Option.map_eq_some_iff.mp found
  exact ⟨rfl, index.position_eq.trans
    ((selectPrefix pages valid page).current.chain.chainIndex_requested position index lookup)⟩

theorem traceLookup_length (pages : FolioData origin final) (valid : pages.Valid)
    (page : Nat) (position : Ordinal) (trace : List Ordinal)
    (found : pages.traceLookup page position = some trace) : trace.length = page + 1 := by
  rw [← indexInFolio_trace pages valid page position] at found
  obtain ⟨selected, indexed, traceEq⟩ := Option.map_eq_some_iff.mp found
  have length := selected.2.toRaw_trace_length ()
  change selected.2.trace.length = selected.2.page + 1 at length
  rw [traceEq, (indexInFolio_page_position pages valid page position selected indexed).1] at length
  exact length

/-- At and beyond the last genuine page, native lookup always uses the entire
stored folio and counts only the repeated final occurrences as padding. -/
theorem traceLookup_final (pages : FolioData origin final) (valid : pages.Valid)
    (page : Nat) (position : Ordinal) (bound : pages.depth - 1 ≤ page) :
    pages.traceLookup page position =
      pages.prefixTraceLookup (page - (pages.depth - 1)) position := by
  cases pages with
  | origin => simp only [traceLookup, depth, Nat.sub_self, Nat.sub_zero]
  | snoc count previous next transition =>
      have lower : previous.length ≤ page := by
        rw [previous.length_eq_depth valid.1]
        simpa only [depth, Nat.add_sub_cancel] using bound
      rw [traceLookup, if_pos lower]
      simp only [depth, Nat.add_sub_cancel, previous.length_eq_depth valid.1]

-- ALIGN: PE-NATIVE-ORIGIN-LOOKUP.
theorem traceLookup_origin (pages : FolioData origin final) (valid : pages.Valid) :
    pages.traceLookup 0 (origin.chain.position pages.originValue) =
      some [origin.chain.position pages.originValue] := by
  induction pages with
  | origin =>
      simp [traceLookup, prefixTraceLookup, originValue, Chain.chainIndex_position,
        Chain.chainIndexOf, paddedTrace, genuineTrace]
  | snoc count previous next transition ih =>
      have positive := previous.length_positive valid.1
      simpa only [traceLookup, show ¬previous.length ≤ 0 by omega, if_false, originValue]
        using ih valid.1

theorem prefixTraceLookup_trim (pages : FolioData origin final) (padding : Nat)
    (position : Ordinal) :
    (pages.prefixTraceLookup padding position).map (Trace.trimTrace pages.depth) =
      pages.prefixTraceLookup 0 position := by
  simp only [prefixTraceLookup, Option.map_map, Function.comp_def, paddedTrace_normalize]
  simp only [paddedTrace, List.replicate_zero, List.nil_append]

-- ALIGN: PE-LOOKUP-NORMALIZATION.
theorem traceLookup_normalize (pages : FolioData origin final) (valid : pages.Valid)
    (page : Nat) (position : Ordinal) :
    pages.traceLookup (min page (pages.depth - 1)) position =
      (pages.traceLookup page position).map (Trace.trimTrace pages.depth) := by
  by_cases bound : page ≤ pages.depth - 1
  · rw [Nat.min_eq_left bound]
    cases found : pages.traceLookup page position with
    | none => rfl
    | some trace =>
        have length := pages.traceLookup_length valid page position trace found
        have positive := pages.depth_positive
        have small : trace.length - pages.depth = 0 := by omega
        simp only [Option.map_some, Trace.trimTrace_eq_drop, Int.toNat_natCast, small, List.drop_zero]
  · have lower : pages.depth - 1 ≤ page := by omega
    rw [Nat.min_eq_right lower, pages.traceLookup_final valid _ position le_rfl,
      pages.traceLookup_final valid page position lower, Nat.sub_self]
    exact (pages.prefixTraceLookup_trim _ position).symm

def traceValid {Scope : Type u} {owner : Scope} (pages : FolioData origin final)
    (source : PageElement owner) : Bool :=
  decide (traceLookup pages source.page source.position = some source.trace)

-- ALIGN: PE-TRACE-VALID-NORMALIZATION.
theorem traceValid_normalize {Scope : Type u} {owner : Scope}
    (pages : FolioData origin final) (valid : pages.Valid) (source : PageElement owner)
    (accepted : pages.traceValid source = true) :
    pages.traceValid (source.normalize (pages.depth - 1) pages.depth) = true := by
  simp only [traceValid, decide_eq_true_eq] at accepted ⊢
  change pages.traceLookup (min source.page (pages.depth - 1)) source.position = _
  rw [pages.traceLookup_normalize valid, accepted]
  rfl

-- ALIGN: PE-TRACE-OWNER-VALIDITY.
theorem traceValid_iff_index {Scope : Type u} {owner : Scope}
    (pages : FolioData origin final) (valid : pages.Valid) (source : PageElement owner) :
    traceValid pages source = true ↔
      ∃ selected, indexInFolio pages valid source.page source.position = some selected ∧
        selected.2.trace = source.trace := by
  rw [traceValid, decide_eq_true_eq, ← indexInFolio_trace pages valid source.page source.position]
  exact Option.map_eq_some_iff

/-- The native owner check supplies the scalar premises needed to read arrows
as transport to the target page. It does not certify the existential payload. -/
-- ALIGN: PE-TRACE-VALID-SHAPE.
theorem traceValid_shape {Scope : Type u} {owner : Scope}
    (pages : FolioData origin final) (valid : pages.Valid) (source : PageElement owner)
    (accepted : pages.traceValid source = true) : source.traceShape := by
  obtain ⟨selected, found, trace⟩ := (traceValid_iff_index pages valid source).mp accepted
  have coordinates := indexInFolio_page_position pages valid source.page source.position selected found
  have length := selected.2.toRaw_trace_length owner
  have head := (Trace.traceStartsWith_iff_head _ _).mp (selected.2.toRaw_trace_head owner)
  change selected.2.trace.length = selected.2.page + 1 at length
  change selected.2.trace.head? = some selected.2.position at head
  exact ⟨by simpa only [trace, coordinates.1] using length,
    by simpa only [trace, coordinates.2] using head⟩

-- ALIGN: PE-OWNER-ARROW-POSITION.
theorem traceValid_arrow_position {Scope : Type u} {owner : Scope}
    (pages : FolioData origin final) (valid : pages.Valid) {source target : PageElement owner}
    (arrow : PageElement.Arrow source target)
    (sourceValid : pages.traceValid source = true) (targetValid : pages.traceValid target = true) :
    PageElement.positionAtPage target.page source = some target.position :=
  arrow.positionAtPage (pages.traceValid_shape valid source sourceValid)
    (pages.traceValid_shape valid target targetValid)

end Datra.Executable.FolioData

namespace Datra.Executable

/-- The native owning folio retained by a Haskell action after hiding its
endpoint carrier types. Its predicate checks scalar lookup, not the payload. -/
structure PageElementDomain {Scope : Type u} (_owner : Scope) where
  origin : Page
  final : Page
  folio : Folio origin final

namespace PageElementDomain
variable {Scope : Type u} {owner : Scope}

def ofFolio {origin final : Page} (owner : Scope) (pages : Folio origin final) :
    PageElementDomain owner := ⟨origin, final, pages⟩

-- ALIGN: PE-ACTION-DOMAIN.
def contains (domain : PageElementDomain owner) (occurrence : PageElement owner) : Bool :=
  domain.folio.data.traceValid occurrence

def finalPage (domain : PageElementDomain owner) : Nat := domain.folio.data.depth - 1

def traceLimit (domain : PageElementDomain owner) : Int := domain.folio.data.depth

-- ALIGN: PE-ACTION-DOMAIN-NORMALIZATION.
theorem normalize_valid (domain : PageElementDomain owner) (occurrence : PageElement owner)
    (valid : domain.contains occurrence = true) :
    domain.contains (occurrence.normalize domain.finalPage domain.traceLimit) = true :=
  domain.folio.data.traceValid_normalize domain.folio.valid occurrence valid

end PageElementDomain
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
  exact ⟨rfl, index.position_eq.trans
    ((pages.pageAt page).chain.chainIndex_requested position index lookup)⟩

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
