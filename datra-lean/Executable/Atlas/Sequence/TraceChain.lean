import Executable.Atlas.Sequence.Folio

namespace Datra.Executable.AtlasSequence

def nativeContains : List Member → Nat → PageCell → Bool
  | [], _, _ => false
  | member :: _, page, ⟨0, trace⟩ => member.contains page trace
  | _ :: rest, page, ⟨index + 1, trace⟩ => nativeContains rest page ⟨index, trace⟩

abbrev NativeCarrier (members : List Member) (page : Nat) :=
  {cell : PageCell // nativeContains members page cell = true}

def nativePageOrder : List Member → Nat → Ordinal
  | [], _ => Ordinal.finiteOrdinal 0
  | member :: rest, page => Ordinal.addOrdinals (member.pageOrder page) (nativePageOrder rest page)

-- ALIGN: SEQUENCE-PAGE-CELL-POSITION.
def nativePosition : List Member → Nat → PageCell → Ordinal
  | [], _, _ => Ordinal.finiteOrdinal 0
  | _ :: _, _, ⟨0, trace⟩ => FolioData.traceHead trace
  | member :: rest, page, ⟨index + 1, trace⟩ =>
      Ordinal.addOrdinals (member.pageOrder page) (nativePosition rest page ⟨index, trace⟩)

/-- Each cons step tags the first member with zero and increments every tail tag. -/
def nativePartsEquiv (member : Member) (rest : List Member) (page : Nat) :
    Sum (member.Trace page) (NativeCarrier rest page) ≃ NativeCarrier (member :: rest) page where
  toFun
    | .inl trace => ⟨⟨0, trace.val⟩, by simpa [nativeContains, Member.contains] using trace.property⟩
    | .inr cell => ⟨⟨cell.val.member + 1, cell.val.trace⟩, cell.property⟩
  invFun
    | ⟨⟨0, trace⟩, valid⟩ => .inl ⟨trace, by simpa [nativeContains, Member.contains] using valid⟩
    | ⟨⟨index + 1, trace⟩, valid⟩ => .inr ⟨⟨index, trace⟩, valid⟩
  left_inv := by
    rintro (⟨trace, valid⟩ | ⟨⟨index, trace⟩, valid⟩) <;> rfl
  right_inv := by
    rintro ⟨⟨index, trace⟩, valid⟩
    cases index <;> rfl

-- ALIGN: SEQUENCE-PAGE-CHAIN.
-- ALIGN: SEQUENCE-NATIVE-PAGE-CHAIN.
def nativePageChain : (members : List Member) → (page : Nat) → Chain (NativeCarrier members page)
  | [], _ => {
      orderType := Ordinal.finiteOrdinal 0
      position _ := Ordinal.finiteOrdinal 0
      lookup _ := none
      positionBelow cell := by simpa [nativeContains] using cell.property
      positionInjective := by
        intro cell
        have impossible := cell.property
        simp [nativeContains] at impossible
      positionSurjective position below := by
        have bound := (Ordinal.ordinalLT_correct _ _).1 below
        simp at bound }
  | member :: rest, page =>
      (Chain.sumChains (member.pageChain page) (nativePageChain rest page)).reindex
        (nativePartsEquiv member rest page)

theorem nativePageChain_order (members : List Member) (page : Nat) :
    (nativePageChain members page).orderType = nativePageOrder members page := by
  induction members with
  | nil => rfl
  | cons member rest ih =>
      change Ordinal.addOrdinals (member.pageChain page).orderType (nativePageChain rest page).orderType = _
      rw [Member.pageChain_order, ih]
      rfl

theorem nativePageChain_position (members : List Member) (page : Nat)
    (cell : NativeCarrier members page) :
    (nativePageChain members page).position cell = nativePosition members page cell.val := by
  induction members with
  | nil => rfl
  | cons member rest ih =>
      rcases cell with ⟨⟨index, trace⟩, valid⟩
      cases index with
      | zero => rfl
      | succ index =>
          change Ordinal.addOrdinals (member.pageChain page).orderType
            ((nativePageChain rest page).position ⟨⟨index, trace⟩, valid⟩) = _
          rw [Member.pageChain_order, ih]
          rfl

theorem nativeContains_get (members : List Member) (page : Nat) (cell : PageCell) :
    nativeContains members page cell =
      (members[cell.member]?).any (fun member => member.contains page cell.trace) := by
  induction members generalizing cell with
  | nil => simp [nativeContains]
  | cons member rest ih =>
      rcases cell with ⟨index, trace⟩
      cases index <;> simp [nativeContains, ih]

def nativeMembers {count : Nat} (members : Fin count → Atlas) : List Member :=
  List.ofFn (fun index => ⟨members index⟩)

theorem nativeContains_members {count : Nat} (members : Fin count → Atlas) (page : Nat) (cell : PageCell) :
    nativeContains (nativeMembers members) page cell =
      if bounded : cell.member < count then
        (Member.mk (members ⟨cell.member, bounded⟩)).contains page cell.trace else false := by
  rw [nativeContains_get]
  simp only [nativeMembers, List.getElem?_ofFn]
  split <;> rfl

theorem nativeContains_iff_encoded {count : Nat} (members : Fin count → Atlas)
    (page : Nat) (cell : PageCell) :
    nativeContains (nativeMembers members) page cell = true ↔ cell ∈ Set.range (pageEncode members page) := by
  constructor
  · intro valid
    have bounded : cell.member < count := by
      by_contra outside
      simp [nativeContains_members, outside] at valid
    let index : Fin count := ⟨cell.member, bounded⟩
    have canonical : (members index).pages.traceLookup page (FolioData.traceHead cell.trace) = some cell.trace := by
      simpa [nativeContains_members, bounded, Member.contains, index] using valid
    let trace : (members index).pages.TraceCarrier page := ⟨cell.trace, canonical⟩
    obtain ⟨value, same⟩ := (members index).pages.encodeTrace_bijective
      (members index).pagination.folio.valid page |>.2 trace
    refine ⟨⟨index, value⟩, ?_⟩
    apply PageCell.ext
    · rfl
    · exact congrArg Subtype.val same
  · rintro ⟨⟨index, value⟩, rfl⟩
    have canonical := ((members index).pages.encodeTrace
      (members index).pagination.folio.valid page value).property
    simpa [nativeContains_members, pageEncode, index.isLt, Member.contains] using canonical

def nativeCarrierEquiv {count : Nat} (members : Fin count → Atlas) (page : Nat) :
    NativeCarrier (nativeMembers members) page ≃ ValidPageCell members page where
  toFun cell := ⟨cell.val, (nativeContains_iff_encoded members page cell.val).1 cell.property⟩
  invFun cell := ⟨cell.val, (nativeContains_iff_encoded members page cell.val).2 cell.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem nativePageOrder_sum (members : List Member) (page : Nat) :
    nativePageOrder members page = ChainSequence.orderSum (members.map (fun member => member.pageOrder page)) := by
  induction members with
  | nil => rfl
  | cons member rest ih => simp [nativePageOrder, ChainSequence.orderSum, ih]

theorem nativePosition_prefix (members : List Member) (page : Nat) (cell : PageCell)
    (bounded : cell.member < members.length) :
    nativePosition members page cell = Ordinal.addOrdinals
      (ChainSequence.prefixOrder (members.map (fun member => member.pageOrder page)) cell.member)
      (FolioData.traceHead cell.trace) := by
  induction members generalizing cell with
  | nil => simp at bounded
  | cons member rest ih =>
      rcases cell with ⟨index, trace⟩
      cases index with
      | zero => simp [nativePosition]
      | succ index =>
          have bound : index < rest.length := by simpa using bounded
          simpa only [nativePosition, List.map_cons, ChainSequence.prefixOrder_cons_succ,
            ChainSequence.add_assoc] using congrArg (Ordinal.addOrdinals (member.pageOrder page))
              (ih ⟨index, trace⟩ bound)

theorem nativeMembers_orders {count : Nat} (members : Fin count → Atlas) (page : Nat) :
    (nativeMembers members).map (fun member => member.pageOrder page) = pageOrders members page := by
  simp [nativeMembers, pageOrders, Member.pageOrder, componentPage, Function.comp_def]

-- ALIGN: SEQUENCE-PAGE-TRACE-ENCODING.
theorem nativePosition_encode {count : Nat} (members : Fin count → Atlas) (page : Nat)
    (value : PageValue members page) :
    nativePosition (nativeMembers members) page (pageEncode members page value) =
      (componentSum members page).position value := by
  rw [nativePosition_prefix _ _ _ (by simpa [nativeMembers, pageEncode] using value.1.isLt), nativeMembers_orders]
  cases page <;> rfl

theorem nativePageChain_lookup_outside (members : List Member) (page : Nat) (position : Ordinal)
    (outside : Ordinal.ordinalLT position (nativePageChain members page).orderType = false) :
    (nativePageChain members page).lookup position = none := by
  cases members with
  | nil => rfl
  | cons member rest =>
      change ((Chain.sumChains (member.pageChain page) (nativePageChain rest page)).lookup position).map _ = none
      rw [Chain.sumChains_lookup_outside _ _ position outside]
      rfl

-- ALIGN: SEQUENCE-NATIVE-PAGE-INTERPRETATION.
theorem nativePageChain_interpretation {count : Nat} (members : Fin count → Atlas) (page : Nat) :
    (nativePageChain (nativeMembers members) page).reindex (nativeCarrierEquiv members page) = pageChain members page := by
  apply Chain.ext_of_boundedLookup
  · change (nativePageChain (nativeMembers members) page).orderType = _
    rw [nativePageChain_order, nativePageOrder_sum, nativeMembers_orders]
    rfl
  · funext cell
    change (nativePageChain (nativeMembers members) page).position _ = _
    rw [nativePageChain_position]
    obtain ⟨value, same⟩ := cell.property
    change nativePosition (nativeMembers members) page cell.val = _
    rw [← same, nativePosition_encode, pageChain_position, ← same, pagePosition_encode]
  · intro position outside
    change ((nativePageChain (nativeMembers members) page).lookup position).map _ = none
    rw [nativePageChain_lookup_outside _ _ position outside]
    rfl
  · intro position outside
    have absent : ChainSequence.locate (pageOrders members page) position = none := by
      have empty := (ChainSequence.locate_isSome (pageOrders members page) position).trans outside
      cases found : ChainSequence.locate (pageOrders members page) position with
      | none => rfl
      | some value => simp [found] at empty
    simp [pageChain, componentSum, Chain.reindex, ChainSequence.chain, absent]

-- ALIGN: SEQUENCE-FIRST-CELL.
theorem firstPageCell_origin {count : Nat} (positive : 0 < count) (members : Fin count → Atlas) :
    (firstPageCell positive members).val =
      ⟨0, (Member.origin ⟨members ⟨0, positive⟩⟩).val⟩ := by
  apply PageCell.ext
  · rfl
  · exact congrArg Subtype.val ((members ⟨0, positive⟩).pages.encodeTrace_origin
      (members ⟨0, positive⟩).pagination.folio.valid (componentZeroValue (members ⟨0, positive⟩)))

end Datra.Executable.AtlasSequence
