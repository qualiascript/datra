import Executable.Atlas.Sequence.TraceChain

namespace Datra.Executable.AtlasSequence

-- ALIGN: SEQUENCE-CELL-PREVIOUS.
def nativePreviousCell : (members : List Member) → (page : Nat) →
    NativeCarrier members (page + 1) → NativeCarrier members page
  | [], _, cell => cell
  | member :: rest, page, cell =>
      nativePartsEquiv member rest page
        (Sum.map (member.previous page) (nativePreviousCell rest page)
          ((nativePartsEquiv member rest (page + 1)).symm cell))

-- ALIGN: SEQUENCE-CELL-NEXT.
def nativeNextCell : (members : List Member) → (page : Nat) →
    NativeCarrier members page → NativeCarrier members (page + 1)
  | [], _, cell => cell
  | member :: rest, page, cell =>
      nativePartsEquiv member rest (page + 1)
        (Sum.map (member.next page) (nativeNextCell rest page)
          ((nativePartsEquiv member rest page).symm cell))

/-- Each transition is the recursive sum of the native member transitions. -/
-- ALIGN: SEQUENCE-NATIVE-TRANSITION.
def nativeTraceTransition : (members : List Member) → (page : Nat) →
    OrderedConsolidation (NativeCarrier members (page + 1)) (NativeCarrier members page)
  | [], page => OrderedConsolidation.identity (nativePageChain [] page)
  | member :: rest, page =>
      OrderedConsolidation.reindex
        (OrderedConsolidation.sum
          (member.transition page (member.pageChain (page + 1)) (member.pageChain page) rfl rfl)
          (nativeTraceTransition rest page))
        (nativePartsEquiv member rest (page + 1)) (nativePartsEquiv member rest page)

-- ALIGN: SEQUENCE-TRANSITION-STORED-MAP.
theorem nativeTraceTransition_map_eq (members : List Member) (page : Nat) :
    (nativeTraceTransition members page).map.map = nativePreviousCell members page := by
  induction members with
  | nil => rfl
  | cons member rest ih =>
      funext cell
      change nativePartsEquiv member rest page
        (Sum.map (member.previous page) (nativeTraceTransition rest page).map.map
          ((nativePartsEquiv member rest (page + 1)).symm cell)) = _
      rw [ih]
      rfl

-- ALIGN: SEQUENCE-TRANSITION-STORED-PREIMAGE.
theorem nativeTraceTransition_preimage_eq (members : List Member) (page : Nat) :
    (nativeTraceTransition members page).map.preimage = nativeNextCell members page := by
  induction members with
  | nil => rfl
  | cons member rest ih =>
      funext cell
      change nativePartsEquiv member rest (page + 1)
        (Sum.map (member.next page) (nativeTraceTransition rest page).map.preimage
          ((nativePartsEquiv member rest page).symm cell)) = _
      rw [ih]
      rfl

theorem nativeTraceTransition_source (members : List Member) (page : Nat) :
    (nativeTraceTransition members page).source = nativePageChain members (page + 1) := by
  induction members with
  | nil => rfl
  | cons member rest ih =>
      change (Chain.sumChains (member.pageChain (page + 1))
        (nativeTraceTransition rest page).source).reindex _ = _
      rw [ih]
      rfl

theorem nativeTraceTransition_target (members : List Member) (page : Nat) :
    (nativeTraceTransition members page).target = nativePageChain members page := by
  induction members with
  | nil => rfl
  | cons member rest ih =>
      change (Chain.sumChains (member.pageChain page)
        (nativeTraceTransition rest page).target).reindex _ = _
      rw [ih]
      rfl

theorem previousPageCell_trace (index : Nat) (trace : List Ordinal) :
    previousPageCell ⟨index, trace⟩ = ⟨index, FolioData.previousTrace trace⟩ := by
  cases trace with
  | nil => rfl
  | cons first rest => cases rest <;> rfl

-- ALIGN: SEQUENCE-PAGE-PREVIOUS.
theorem nativeTraceTransition_previous (members : List Member) (page : Nat)
    (cell : NativeCarrier members (page + 1)) :
    ((nativeTraceTransition members page).map.map cell).val = previousPageCell cell.val := by
  induction members with
  | nil => have impossible := cell.property; simp [nativeContains] at impossible
  | cons member rest ih =>
      rcases cell with ⟨⟨index, trace⟩, valid⟩
      cases index with
      | zero => exact (previousPageCell_trace 0 trace).symm
      | succ index =>
          change PageCell.mk
            (((nativeTraceTransition rest page).map.map ⟨⟨index, trace⟩, valid⟩).val.member + 1)
            (((nativeTraceTransition rest page).map.map ⟨⟨index, trace⟩, valid⟩).val.trace) = _
          rw [ih, previousPageCell_trace, previousPageCell_trace]

-- ALIGN: SEQUENCE-PAGE-NEXT.
theorem nativeTraceTransition_next (members : List Member) (page : Nat)
    (cell : NativeCarrier members page) (member : Member)
    (found : members[cell.val.member]? = some member) :
    ((nativeTraceTransition members page).map.preimage cell).val =
      ⟨cell.val.member,
        (member.atlas.pages.nextTraceLookup page (FolioData.traceHead cell.val.trace)).getD cell.val.trace⟩ := by
  induction members generalizing member with
  | nil => simp at found
  | cons first rest ih =>
      rcases cell with ⟨⟨index, trace⟩, valid⟩
      cases index with
      | zero =>
          have same : first = member := by simpa using found
          subst member
          rfl
      | succ index =>
          have foundTail : rest[index]? = some member := by simpa using found
          change PageCell.mk
            (((nativeTraceTransition rest page).map.preimage ⟨⟨index, trace⟩, valid⟩).val.member + 1)
            (((nativeTraceTransition rest page).map.preimage ⟨⟨index, trace⟩, valid⟩).val.trace) = _
          rw [ih ⟨⟨index, trace⟩, valid⟩ member foundTail]

def nativePageTransition {count : Nat} (members : Fin count → Atlas) (page : Nat) :
    OrderedConsolidation (ValidPageCell members (page + 1)) (ValidPageCell members page) :=
  (nativeTraceTransition (nativeMembers members) page).reindex
    (nativeCarrierEquiv members (page + 1)) (nativeCarrierEquiv members page)

theorem nativePageTransition_source {count : Nat} (members : Fin count → Atlas) (page : Nat) :
    (nativePageTransition members page).source = pageChain members (page + 1) := by
  change (nativeTraceTransition (nativeMembers members) page).source.reindex _ = _
  rw [nativeTraceTransition_source, nativePageChain_interpretation]

theorem nativePageTransition_target {count : Nat} (members : Fin count → Atlas) (page : Nat) :
    (nativePageTransition members page).target = pageChain members page := by
  change (nativeTraceTransition (nativeMembers members) page).target.reindex _ = _
  rw [nativeTraceTransition_target, nativePageChain_interpretation]

theorem nativePageTransition_map {count : Nat} (members : Fin count → Atlas) (page : Nat)
    (cell : ValidPageCell members (page + 1)) :
    (nativePageTransition members page).map.map cell = (pageTransition members page).map cell := by
  apply Subtype.ext
  exact nativeTraceTransition_previous (nativeMembers members) page
    ((nativeCarrierEquiv members (page + 1)).symm cell)

theorem nativePageTransition_preimage {count : Nat} (members : Fin count → Atlas) (page : Nat)
    (cell : ValidPageCell members page) :
    (nativePageTransition members page).map.preimage cell = (pageTransition members page).preimage cell := by
  obtain ⟨⟨index, value⟩, same⟩ := cell.property
  have cellEq : encodedPageCell members page ⟨index, value⟩ = cell := Subtype.ext same
  rw [← cellEq]
  apply Subtype.ext
  change ((nativeTraceTransition (nativeMembers members) page).map.preimage
    ((nativeCarrierEquiv members page).symm (encodedPageCell members page ⟨index, value⟩))).val = _
  rw [nativeTraceTransition_next _ _ _ ⟨members index⟩ (by simp [nativeMembers, nativeCarrierEquiv, encodedPageCell, pageEncode, index.isLt])]
  change PageCell.mk index.val
    (((members index).pages.nextTraceLookup page
      (FolioData.traceHead ((members index).pages.traceAt page value))).getD _) = _
  rw [FolioData.traceHead_of_head ((members index).pages.traceAt_head page value), FolioData.nextTraceLookup_position]
  exact (nextPageCell_encode members page ⟨index, value⟩).symm

-- ALIGN: SEQUENCE-PAGE-TRANSITION.
def nativePageTransitionTo {count : Nat} (members : Fin count → Atlas) (page : Nat)
    (target : Chain (ValidPageCell members page))
    (targetPosition : ∀ cell, target.position cell = pagePosition members page cell.val) :
    OrderedConsolidation (ValidPageCell members (page + 1)) (ValidPageCell members page) :=
  let mapping := nativePageTransition members page
  let sourcePosition : ∀ cell, pagePosition members (page + 1) cell.val = mapping.source.position cell := by
    intro cell
    rw [nativePageTransition_source, pageChain_position]
  let source := mapping.source.withPosition (fun cell => pagePosition members (page + 1) cell.val) sourcePosition
  mapping.withEndpoints source target sourcePosition (by
    intro cell
    rw [targetPosition, nativePageTransition_target, pageChain_position])

theorem nativePageTransitionTo_source {count : Nat} (members : Fin count → Atlas) (page : Nat)
    (target : Chain (ValidPageCell members page))
    (targetPosition : ∀ cell, target.position cell = pagePosition members page cell.val) :
    (nativePageTransitionTo members page target targetPosition).source = pageChain members (page + 1) := by
  simp only [nativePageTransitionTo, OrderedConsolidation.withEndpoints,
    Chain.withPosition_eq, nativePageTransition_source]

theorem nativePageTransitionTo_target {count : Nat} (members : Fin count → Atlas) (page : Nat)
    (target : Chain (ValidPageCell members page))
    (targetPosition : ∀ cell, target.position cell = pagePosition members page cell.val) :
    (nativePageTransitionTo members page target targetPosition).target = target := rfl

theorem nativePageTransitionTo_map {count : Nat} (members : Fin count → Atlas) (page : Nat)
    (target : Chain (ValidPageCell members page))
    (targetPosition : ∀ cell, target.position cell = pagePosition members page cell.val)
    (cell : ValidPageCell members (page + 1)) :
    (nativePageTransitionTo members page target targetPosition).map.map cell =
      (pageTransition members page).map cell := nativePageTransition_map members page cell

theorem nativePageTransitionTo_preimage {count : Nat} (members : Fin count → Atlas) (page : Nat)
    (target : Chain (ValidPageCell members page))
    (targetPosition : ∀ cell, target.position cell = pagePosition members page cell.val)
    (cell : ValidPageCell members page) :
    (nativePageTransitionTo members page target targetPosition).map.preimage cell =
      (pageTransition members page).preimage cell := nativePageTransition_preimage members page cell

end Datra.Executable.AtlasSequence
