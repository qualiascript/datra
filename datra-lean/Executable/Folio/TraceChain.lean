import Executable.PageElementLookup

namespace Datra.Executable.FolioData
variable {origin final : Page}

def traceHead (trace : List Ordinal) : Ordinal := trace.headD (Ordinal.finiteOrdinal 0)

theorem traceHead_of_head {trace : List Ordinal} {position : Ordinal}
    (head : trace.head? = some position) : traceHead trace = position := by
  cases trace <;> simp_all [traceHead]

-- ALIGN: PE-TRACE-ORDER.
def tracePrecedes (earlier later : List Ordinal) : Bool :=
  !(Ordinal.ordinalLT (traceHead later) (traceHead earlier))

theorem tracePrecedes_correct (earlier later : List Ordinal) :
    tracePrecedes earlier later = true ↔
      (traceHead earlier).toSemantics ≤ (traceHead later).toSemantics := by
  have comparison := Ordinal.ordinalLT_correct (traceHead later) (traceHead earlier)
  cases result : Ordinal.ordinalLT (traceHead later) (traceHead earlier) <;>
    simp_all [tracePrecedes, not_lt]

/-- Only the native trace at its own first position belongs to the page. -/
def TraceCarrier (pages : FolioData origin final) (page : Nat) :=
  {trace : List Ordinal // pages.traceLookup page (traceHead trace) = some trace}

def traceChainLookup (pages : FolioData origin final) (valid : pages.Valid)
    (page : Nat) (position : Ordinal) : Option (pages.TraceCarrier page) :=
  match found : pages.traceLookup page position with
  | none => none
  | some trace => some ⟨trace, by
      rw [traceHead_of_head (pages.traceLookup_head valid page position trace found)]
      exact found⟩

theorem traceChainLookup_value (pages : FolioData origin final) (valid : pages.Valid)
    (page : Nat) (position : Ordinal) :
    (pages.traceChainLookup valid page position).map Subtype.val = pages.traceLookup page position := by
  unfold traceChainLookup
  split <;> simp_all

-- ALIGN: PE-TRACE-CHAIN.
def traceChain (pages : FolioData origin final) (valid : pages.Valid) (page : Nat) :
    Chain (pages.TraceCarrier page) where
  orderType := (pages.selectPrefix valid page).current.chain.orderType
  position trace := traceHead trace.val
  lookup := pages.traceChainLookup valid page
  positionBelow trace := by
    have bounded := (pages.selectPrefix_lookup_spec valid page (traceHead trace.val)).2.1
    rw [← selectPrefix_traceLookup, trace.property] at bounded
    exact bounded.symm
  positionInjective := by
    intro first second same
    change traceHead first.val = traceHead second.val at same
    apply Subtype.ext
    apply Option.some.inj
    calc
      some first.val = pages.traceLookup page (traceHead first.val) := first.property.symm
      _ = pages.traceLookup page (traceHead second.val) := by rw [same]
      _ = some second.val := second.property
  positionSurjective position below := by
    have bounded := (pages.selectPrefix_lookup_spec valid page position).2.1
    rw [← selectPrefix_traceLookup, below] at bounded
    cases found : pages.traceLookup page position with
    | none => simp [found] at bounded
    | some trace =>
        let value : pages.TraceCarrier page := ⟨trace, by
          rw [traceHead_of_head (pages.traceLookup_head valid page position trace found)]
          exact found⟩
        refine ⟨value, ?_, traceHead_of_head (pages.traceLookup_head valid page position trace found)⟩
        unfold traceChainLookup
        split
        · rename_i absent
          simp [found] at absent
        · rename_i other same
          apply congrArg some
          apply Subtype.ext
          exact Option.some.inj (same.symm.trans found)

theorem traceChain_order (pages : FolioData origin final) (valid : pages.Valid) (page : Nat) :
    (pages.traceChain valid page).orderType = (pages.pageAt page).chain.orderType := by
  exact congrArg (fun selected : Page => selected.chain.orderType) (pages.selectPrefix_current valid page)

def encodeTrace (pages : FolioData origin final) (valid : pages.Valid) (page : Nat)
    (value : (pages.pageAt page).Carrier) : pages.TraceCarrier page :=
  ⟨pages.traceAt page value, by
    rw [traceHead_of_head (pages.traceAt_head page value)]
    exact pages.traceLookup_occurrence valid ⟨page, value⟩⟩

theorem encodeTrace_position (pages : FolioData origin final) (valid : pages.Valid) (page : Nat)
    (value : (pages.pageAt page).Carrier) :
    (pages.traceChain valid page).position (pages.encodeTrace valid page value) =
      (pages.pageAt page).chain.position value :=
  traceHead_of_head (pages.traceAt_head page value)

theorem tracePrecedes_encodeTrace (pages : FolioData origin final) (valid : pages.Valid)
    (page : Nat) (first second : (pages.pageAt page).Carrier) :
    tracePrecedes (pages.encodeTrace valid page first).val (pages.encodeTrace valid page second).val = true ↔
      ((pages.pageAt page).chain.position first).toSemantics ≤
        ((pages.pageAt page).chain.position second).toSemantics := by
  rw [tracePrecedes_correct]
  change (traceHead (pages.traceAt page first)).toSemantics ≤
    (traceHead (pages.traceAt page second)).toSemantics ↔ _
  rw [traceHead_of_head (pages.traceAt_head page first),
    traceHead_of_head (pages.traceAt_head page second)]

theorem encodeTrace_bijective (pages : FolioData origin final) (valid : pages.Valid) (page : Nat) :
    Function.Bijective (pages.encodeTrace valid page) := by
  constructor
  · intro first second same
    apply (pages.pageAt page).chain.positionInjective
    simpa only [encodeTrace_position] using
      congrArg (pages.traceChain valid page).position same
  · intro trace
    have native := trace.property
    rw [pages.traceLookup_canonical valid] at native
    obtain ⟨index, _, found⟩ := Option.map_eq_some_iff.mp native
    exact ⟨index.object, Subtype.ext found⟩

/-- The native trace carrier is equivalent to the original dependent page;
encoding retains exactly its executable ordinal position. -/
noncomputable def traceEncodingEquiv (pages : FolioData origin final) (valid : pages.Valid) (page : Nat) :
    (pages.pageAt page).Carrier ≃ pages.TraceCarrier page :=
  Equiv.ofBijective (pages.encodeTrace valid page) (pages.encodeTrace_bijective valid page)

noncomputable def traceChainOrderIso (pages : FolioData origin final) (valid : pages.Valid) (page : Nat) :
    (pages.traceChain valid page).toSemantics.Obj ≃o (pages.pageAt page).chain.toSemantics.Obj where
  toEquiv := (pages.traceEncodingEquiv valid page).symm
  map_rel_iff' := by
    intro first second
    have position (trace : pages.TraceCarrier page) :
        (pages.pageAt page).chain.position ((pages.traceEncodingEquiv valid page).symm trace) =
          (pages.traceChain valid page).position trace := by
      rw [← pages.encodeTrace_position valid page]
      exact congrArg (pages.traceChain valid page).position
        ((pages.traceEncodingEquiv valid page).apply_symm_apply trace)
    change ((pages.pageAt page).chain.position _).toSemantics ≤
        ((pages.pageAt page).chain.position _).toSemantics ↔
      ((pages.traceChain valid page).position first).toSemantics ≤
        ((pages.traceChain valid page).position second).toSemantics
    exact iff_of_eq (congrArg₂ (fun x y : Ordinal => x.toSemantics ≤ y.toSemantics)
      (position first) (position second))

/-- A singleton origin is fixed; every longer trace loses its first step. -/
def previousTrace : List Ordinal → List Ordinal
  | _ :: next :: rest => next :: rest
  | trace => trace

theorem previousTrace_traceAt (pages : FolioData origin final) (page : Nat)
    (value : (pages.pageAt (page + 1)).Carrier) :
    previousTrace (pages.traceAt (page + 1) value) =
      pages.traceAt page ((pages.transport (page + 1) page (Nat.le_succ page)).map value) := by
  cases page <;> rfl

-- ALIGN: PE-TRACE-PREVIOUS-VALID.
def TraceCarrier.previous {pages : FolioData origin final} (valid : pages.Valid) (page : Nat)
    (trace : pages.TraceCarrier (page + 1)) : pages.TraceCarrier page :=
  ⟨previousTrace trace.val, by
    obtain ⟨value, rfl⟩ := (pages.encodeTrace_bijective valid (page + 1)).2 trace
    change pages.traceLookup page (traceHead (previousTrace (pages.traceAt (page + 1) value))) =
      some (previousTrace (pages.traceAt (page + 1) value))
    rw [previousTrace_traceAt]
    exact (pages.encodeTrace valid page ((pages.transport (page + 1) page (Nat.le_succ page)).map value)).property⟩

/-- Dropping a native trace step is the original page transport. -/
theorem previous_encodeTrace (pages : FolioData origin final) (valid : pages.Valid) (page : Nat)
    (value : (pages.pageAt (page + 1)).Carrier) :
    (pages.encodeTrace valid (page + 1) value).previous valid page =
      pages.encodeTrace valid page ((pages.transport (page + 1) page (Nat.le_succ page)).map value) := by
  apply Subtype.ext
  exact previousTrace_traceAt pages page value

-- ALIGN: PE-TRACE-PREVIOUS-MONOTONE.
theorem TraceCarrier.previous_monotone {pages : FolioData origin final} (valid : pages.Valid)
    (page : Nat) (first second : pages.TraceCarrier (page + 1))
    (ordered : tracePrecedes first.val second.val = true) :
    tracePrecedes (first.previous valid page).val (second.previous valid page).val = true := by
  obtain ⟨left, rfl⟩ := (pages.encodeTrace_bijective valid (page + 1)).2 first
  obtain ⟨right, rfl⟩ := (pages.encodeTrace_bijective valid (page + 1)).2 second
  rw [previous_encodeTrace, previous_encodeTrace]
  apply (pages.tracePrecedes_encodeTrace valid page _ _).2
  exact (pages.transport (page + 1) page (Nat.le_succ page)).monotone left right
    ((pages.tracePrecedes_encodeTrace valid (page + 1) left right).1 ordered)

/-- Lookup on the preceding page followed by the stored chosen preimage. -/
def nextTraceLookup (pages : FolioData origin final) (page : Nat) (position : Ordinal) :
    Option (List Ordinal) :=
  ((pages.pageAt page).chain.chainIndex position).map (fun index =>
    pages.traceAt (page + 1) ((pages.transport (page + 1) page (Nat.le_succ page)).preimage index.object))

theorem nextTraceLookup_position (pages : FolioData origin final) (page : Nat)
    (value : (pages.pageAt page).Carrier) :
    pages.nextTraceLookup page ((pages.pageAt page).chain.position value) =
      some (pages.traceAt (page + 1)
        ((pages.transport (page + 1) page (Nat.le_succ page)).preimage value)) := by
  simp [nextTraceLookup, Chain.chainIndex_position, Chain.chainIndexOf]

-- ALIGN: PE-TRACE-NEXT-VALID.
def TraceCarrier.next {pages : FolioData origin final} (valid : pages.Valid) (page : Nat)
    (trace : pages.TraceCarrier page) : pages.TraceCarrier (page + 1) :=
  ⟨(pages.nextTraceLookup page (traceHead trace.val)).getD trace.val, by
    obtain ⟨value, rfl⟩ := (pages.encodeTrace_bijective valid page).2 trace
    change pages.traceLookup (page + 1)
      (traceHead ((pages.nextTraceLookup page (traceHead (pages.traceAt page value))).getD
        (pages.traceAt page value))) =
      some ((pages.nextTraceLookup page (traceHead (pages.traceAt page value))).getD
        (pages.traceAt page value))
    rw [traceHead_of_head (pages.traceAt_head page value), nextTraceLookup_position]
    exact (pages.encodeTrace valid (page + 1)
      ((pages.transport (page + 1) page (Nat.le_succ page)).preimage value)).property⟩

theorem next_encodeTrace (pages : FolioData origin final) (valid : pages.Valid) (page : Nat)
    (value : (pages.pageAt page).Carrier) :
    (pages.encodeTrace valid page value).next valid page =
      pages.encodeTrace valid (page + 1)
        ((pages.transport (page + 1) page (Nat.le_succ page)).preimage value) := by
  apply Subtype.ext
  change (pages.nextTraceLookup page (traceHead (pages.traceAt page value))).getD _ = _
  rw [traceHead_of_head (pages.traceAt_head page value), nextTraceLookup_position]
  rfl

-- ALIGN: PE-TRACE-NEXT-INVERSE.
theorem TraceCarrier.previous_next {pages : FolioData origin final} (valid : pages.Valid)
    (page : Nat) (trace : pages.TraceCarrier page) :
    (trace.next valid page).previous valid page = trace := by
  obtain ⟨value, rfl⟩ := (pages.encodeTrace_bijective valid page).2 trace
  rw [next_encodeTrace, previous_encodeTrace, Consolidation.rightInverse]

/-- Construct the native consolidation against chains whose positions are the
canonical trace heads. Both the map and its chosen inverse are retained. -/
-- ALIGN: PE-TRACE-CONSOLIDATION.
def traceTransitionBetween (pages : FolioData origin final) (valid : pages.Valid) (page : Nat)
    (source : Chain (pages.TraceCarrier (page + 1))) (target : Chain (pages.TraceCarrier page))
    (sourcePosition : source.position = fun trace => traceHead trace.val)
    (targetPosition : target.position = fun trace => traceHead trace.val) :
    OrderedConsolidation (pages.TraceCarrier (page + 1)) (pages.TraceCarrier page) :=
  ⟨source, target, Consolidation.restricted _ _ source target
    (fun trace => TraceCarrier.previous valid page trace)
    (fun trace => TraceCarrier.next valid page trace) (by
      intro first second ordered
      rw [sourcePosition] at ordered
      rw [targetPosition]
      exact (tracePrecedes_correct _ _).1
        (TraceCarrier.previous_monotone valid page first second
          ((tracePrecedes_correct _ _).2 ordered)))
    (TraceCarrier.previous_next valid page)⟩

end Datra.Executable.FolioData
