import Executable.PageElementLookup

namespace Datra.Executable.FolioData
variable {origin final : Page}

def traceHead (trace : List Ordinal) : Ordinal := trace.headD (Ordinal.finiteOrdinal 0)

theorem traceHead_of_head {trace : List Ordinal} {position : Ordinal}
    (head : trace.head? = some position) : traceHead trace = position := by
  cases trace <;> simp_all [traceHead]

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

end Datra.Executable.FolioData
