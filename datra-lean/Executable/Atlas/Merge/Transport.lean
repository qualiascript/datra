import Executable.Atlas.Merge.Folio
import Executable.Atlas.Merge.Resolution

namespace Datra.Executable.AtlasMerge

-- ALIGN: MERGE-NATIVE-TRANSPORT.
def nativeTransport : PageCell → PageCell → Bool
  | .left source, .left target => Trace.traceSuffix source target
  | .right source, .right target => Trace.traceSuffix source target
  | _, _ => false

theorem nativeTransport_refl (cell : PageCell) : nativeTransport cell cell = true := by
  cases cell <;> simp [nativeTransport, Trace.traceSuffix_iff]

theorem nativeTransport_trans (source middle target : PageCell)
    (first : nativeTransport source middle = true) (second : nativeTransport middle target = true) :
    nativeTransport source target = true := by
  cases source <;> cases middle <;> cases target <;> simp_all only [nativeTransport, Bool.false_eq_true]
  all_goals
    apply (Trace.traceSuffix_iff _ _).mpr
    exact ((Trace.traceSuffix_iff _ _).mp second).trans ((Trace.traceSuffix_iff _ _).mp first)

theorem previous_nativeTransport (source : PageCell) :
    nativeTransport source (previousPageCell source) = true := by
  cases source <;> exact FolioData.previousTrace_suffix _

theorem prefix_same_page (X Y : Atlas) (page : Nat) (source target : ValidPageCell X Y page)
    (suffix : Trace.traceSuffix ((prefixFolio X Y page).data.genuineTrace source)
      ((prefixFolio X Y page).data.genuineTrace target) = true) : source = target := by
  have same := Trace.traceSuffix_same_length _ _ suffix (by simp only [FolioData.genuineTrace_length])
  have heads := congrArg List.head? same
  apply (pageChain X Y page).positionInjective
  exact Option.some.inj (by simpa only [FolioData.genuineTrace_head] using heads)

-- ALIGN: MERGE-PREFIX-NATIVE-TRANSPORT.
theorem prefix_nativeTransport (X Y : Atlas) (sourcePage targetPage : Nat)
    (precedes : targetPage ≤ sourcePage)
    (source : ValidPageCell X Y sourcePage) (target : ValidPageCell X Y targetPage)
    (suffix : Trace.traceSuffix ((prefixFolio X Y sourcePage).data.genuineTrace source)
      ((prefixFolio X Y targetPage).data.genuineTrace target) = true) :
    nativeTransport source.val target.val = true := by
  induction sourcePage generalizing targetPage with
  | zero =>
      have equal : targetPage = 0 := Nat.eq_zero_of_le_zero precedes
      subst targetPage
      rw [prefix_same_page X Y 0 source target suffix]
      exact nativeTransport_refl _
  | succ page ih =>
      by_cases equal : targetPage = page + 1
      · subst targetPage
        rw [prefix_same_page X Y (page + 1) source target suffix]
        exact nativeTransport_refl _
      · have earlier : targetPage ≤ page := by omega
        have shorter : ((prefixFolio X Y targetPage).data.genuineTrace target).length <
            ((prefixFolio X Y (page + 1)).data.genuineTrace source).length := by
          simp only [FolioData.genuineTrace_length,
            ← FolioData.length_eq_depth _ (prefixFolio X Y targetPage).valid,
            ← FolioData.length_eq_depth _ (prefixFolio X Y (page + 1)).valid, prefixFolio_length]
          omega
        have dropped := Trace.traceSuffix_drop_head _ _ suffix shorter
        rw [prefixFolio_trace_succ] at dropped
        exact nativeTransport_trans _ _ _ (previous_nativeTransport source.val)
          (ih targetPage earlier (previousValidCell X Y page source) target dropped)

-- ALIGN: MERGE-PADDED-PREVIOUS-POSITION.
theorem paddedPreviousPosition (X Y : Atlas) (page : Nat)
    (padded : mergeDepth X Y ≤ page + 1) (cell : ValidPageCell X Y (page + 1)) :
    pagePosition X Y (page + 1) cell.val =
      pagePosition X Y page (previousValidCell X Y page cell).val := by
  have leftPadded : X.pages.length ≤ page + 1 := (Nat.le_max_left _ _).trans padded
  have rightPadded : Y.pages.length ≤ page + 1 := (Nat.le_max_right _ _).trans padded
  rcases cell with ⟨cell, accepted⟩
  cases cell with
  | left positions =>
      have head := FolioData.paddedPreviousHead X.pages X.pagination.folio.valid (page + 1) leftPadded
        ⟨positions, leftTrace_accepted X Y (page + 1) positions accepted⟩
      exact head.symm
  | right positions =>
      have head := FolioData.paddedPreviousHead Y.pages Y.pagination.folio.valid (page + 1) rightPadded
        ⟨positions, rightTrace_accepted X Y (page + 1) positions accepted⟩
      have order := FolioData.pageOrderType_padded X.pages X.pagination.folio.valid (page + 1) leftPadded
      change Ordinal.addOrdinals (X.pages.pageAt (page + 1)).chain.orderType (FolioData.traceHead positions) =
        Ordinal.addOrdinals (X.pages.pageAt page).chain.orderType (FolioData.traceHead (FolioData.previousTrace positions))
      rw [show (page + 1) - 1 = page by omega] at order
      rw [order, head]

-- ALIGN: MERGE-FULL-CELL-LOOKUP.
theorem folio_cellLookup_all (X Y : Atlas) (page : Nat) (cell : ValidPageCell X Y page) :
    (folio X Y).data.traceLookup (page + 1) (pagePosition X Y page cell.val) =
      some ((prefixFolio X Y page).data.genuineTrace cell) := by
  have positive : 0 < mergeDepth X Y :=
    (X.pages.length_positive X.pagination.folio.valid).trans_le (Nat.le_max_left _ _)
  induction page with
  | zero => exact folio_cellLookup_prefix X Y 1 (by omega) positive cell
  | succ page ih =>
      by_cases genuine : page + 2 ≤ mergeDepth X Y
      · exact folio_cellLookup_prefix X Y (page + 2) (by omega) genuine cell
      · have padded : mergeDepth X Y ≤ page + 1 := by omega
        have position := paddedPreviousPosition X Y page padded cell
        have found := ih (previousValidCell X Y page cell)
        have bound : (folio X Y).data.length ≤ page + 2 := by
          rw [folio_length]
          change mergeDepth X Y + 1 ≤ page + 2
          omega
        rw [prefixFolio_trace_succ]
        apply FolioData.traceLookup_padded_step (folio X Y).data (folio X Y).valid (page + 2) bound
        simpa only [Nat.add_sub_cancel, position] using found

-- ALIGN: MERGE-RAW-TRACE-VALIDITY.
def rawTraceValid {Scope : Type} {owner : Scope} (X Y : Atlas) (occurrence : PageElement owner) : Prop :=
  (folio X Y).data.traceLookup occurrence.page occurrence.position = some occurrence.trace

-- ALIGN: MERGE-RAW-NATIVE-WITNESS.
theorem lookup_native (X Y : Atlas) (page : Nat) (position : Ordinal) (positions : List Ordinal)
    (found : (folio X Y).data.traceLookup (page + 1) position = some positions) :
    ∃ cell : ValidPageCell X Y page, pagePosition X Y page cell.val = position := by
  induction page generalizing positions with
  | zero =>
      have positive : 0 < mergeDepth X Y :=
        (X.pages.length_positive X.pagination.folio.valid).trans_le (Nat.le_max_left _ _)
      rw [folio_pageLookup_prefix X Y 1 (by omega) positive] at found
      rw [FolioData.traceLookup_final _ (prefixFolio X Y 0).valid _ _ (by
        rw [prefixFolio_depth])] at found
      obtain ⟨index, present, _⟩ := Option.map_eq_some_iff.mp found
      exact ⟨index.object, index.position_eq.trans
        ((pageChain X Y 0).chainIndex_requested position index present)⟩
  | succ page ih =>
      by_cases genuine : page + 2 ≤ mergeDepth X Y
      · rw [folio_pageLookup_prefix X Y (page + 2) (by omega) genuine] at found
        rw [show page + 2 - 1 = page + 1 by omega] at found
        rw [FolioData.traceLookup_final _ (prefixFolio X Y (page + 1)).valid _ _ (by
          rw [prefixFolio_depth]; omega)] at found
        obtain ⟨index, present, _⟩ := Option.map_eq_some_iff.mp found
        exact ⟨index.object, index.position_eq.trans
          ((pageChain X Y (page + 1)).chainIndex_requested position index present)⟩
      · have bound : (folio X Y).data.length ≤ page + 2 := by
          rw [folio_length]; change mergeDepth X Y + 1 ≤ page + 2; omega
        have previous := FolioData.traceLookup_padded_previous (folio X Y).data (folio X Y).valid
          (page + 2) bound position positions found
        obtain ⟨cell, same⟩ := ih (FolioData.previousTrace positions) (by simpa using previous)
        refine ⟨nextValidCell X Y page cell, ?_⟩
        rw [paddedPreviousPosition X Y page (by omega),
          show previousValidCell X Y page (nextValidCell X Y page cell) = cell from
            (pageTransition X Y page).rightInverse cell]
        exact same

-- ALIGN: MERGE-RAW-RESOLVABLE.
theorem occurrence_resolvable {Scope : Type} {owner : Scope} (X Y : Atlas)
    (occurrence : PageElement owner) (valid : rawTraceValid X Y occurrence) :
    positionResolvable X Y occurrence.page occurrence.position = true := by
  cases pageEq : occurrence.page with
  | zero => rfl
  | succ page =>
      obtain ⟨cell, same⟩ := lookup_native X Y page occurrence.position occurrence.trace (by
        simpa only [rawTraceValid, pageEq] using valid)
      rw [positionResolvable, ← same]
      exact congrArg Option.isSome ((pageChain X Y page).chainIndex_position cell)

theorem occurrence_trace {Scope : Type} {owner : Scope} (X Y : Atlas)
    (occurrence : PageElement owner) (valid : rawTraceValid X Y occurrence)
    (positive : 0 < occurrence.page)
    (cell : ValidPageCell X Y (occurrence.page - 1))
    (position : pagePosition X Y (occurrence.page - 1) cell.val = occurrence.position) :
    occurrence.trace = (prefixFolio X Y (occurrence.page - 1)).data.genuineTrace cell := by
  have lookup := folio_cellLookup_all X Y (occurrence.page - 1) cell
  rw [Nat.sub_add_cancel positive, position, valid] at lookup
  exact Option.some.inj lookup

-- ALIGN: MERGE-ARROW-NATIVE-TRANSPORT.
theorem arrow_nativeTransport {Scope : Type} {owner : Scope} (X Y : Atlas)
    {source target : PageElement owner} (arrow : PageElement.Arrow source target)
    (sourceValid : rawTraceValid X Y source) (targetValid : rawTraceValid X Y target)
    (positive : 0 < target.page)
    (sourceCell : ValidPageCell X Y (source.page - 1))
    (targetCell : ValidPageCell X Y (target.page - 1))
    (sourcePosition : pagePosition X Y (source.page - 1) sourceCell.val = source.position)
    (targetPosition : pagePosition X Y (target.page - 1) targetCell.val = target.position) :
    nativeTransport sourceCell.val targetCell.val = true := by
  have precedes := arrow.precedes
  have sourceTrace := occurrence_trace X Y source sourceValid (positive.trans_le precedes)
    sourceCell sourcePosition
  have targetTrace := occurrence_trace X Y target targetValid positive
    targetCell targetPosition
  apply prefix_nativeTransport X Y (source.page - 1) (target.page - 1)
    (Nat.sub_le_sub_right precedes 1) sourceCell targetCell
  rw [← sourceTrace, ← targetTrace]
  exact arrow.transported

def resolvedAt {Scope : Type} {owner : Scope} (X Y : Atlas) (occurrence : PageElement owner) :
    SourceCell X Y → Prop
  | .origin => occurrence.page = 0
  | .left source => source.val.page + 1 = occurrence.page ∧
      pagePosition X Y source.val.page (.left source.val.trace) = occurrence.position
  | .right source => source.val.page + 1 = occurrence.page ∧
      pagePosition X Y source.val.page (.right source.val.trace) = occurrence.position

theorem resolvePageCell_resolvedAt {Scope : Type} {owner : Scope} (X Y : Atlas)
    (occurrence : PageElement owner) (page : Nat) (cell : ValidPageCell X Y page)
    (pageEq : page + 1 = occurrence.page)
    (positionEq : pagePosition X Y page cell.val = occurrence.position) :
    resolvedAt X Y occurrence (resolvePageCell X Y page cell) := by
  obtain ⟨value, same⟩ := cell.property
  have encoded : encodedPageCell X Y page value = cell := Subtype.ext same
  rw [← encoded] at positionEq ⊢
  cases value with
  | inl value =>
      rw [resolvePageCell_left]
      exact ⟨pageEq, positionEq⟩
  | inr value =>
      rw [resolvePageCell_right]
      exact ⟨pageEq, positionEq⟩

theorem resolveCellAt_resolvedAt {Scope : Type} {owner : Scope} (X Y : Atlas)
    (occurrence : PageElement owner) (selected : SourceCell X Y)
    (found : resolveCellAt X Y occurrence.page occurrence.position = some selected) :
    resolvedAt X Y occurrence selected := by
  cases pageEq : occurrence.page with
  | zero =>
      simp only [pageEq, resolveCellAt, Option.some.injEq] at found
      subst selected
      exact pageEq
  | succ page =>
      rw [pageEq, resolveCellAt] at found
      cases indexFound : (pageChain X Y page).chainIndex occurrence.position with
      | none => simp [indexFound] at found
      | some index =>
          simp only [indexFound, Option.bind_some, withNativeCell_resolve, Option.some.injEq] at found
          rw [← found]
          exact resolvePageCell_resolvedAt X Y occurrence page index.object pageEq.symm
            (index.position_eq.trans ((pageChain X Y page).chainIndex_requested _ index indexFound))

theorem leftSource_native (X Y : Atlas) (source : X.Element) :
    PageCell.left source.val.trace ∈ Set.range (pageEncode X Y source.val.page) := by
  rcases source with ⟨_, occurrence, rfl⟩
  exact ⟨.inl occurrence.value, rfl⟩

theorem rightSource_native (X Y : Atlas) (source : Y.Element) :
    PageCell.right source.val.trace ∈ Set.range (pageEncode X Y source.val.page) := by
  rcases source with ⟨_, occurrence, rfl⟩
  exact ⟨.inr occurrence.value, rfl⟩

-- ALIGN: MERGE-RESOLVED-TRANSPORT.
theorem resolvedTransport {Scope : Type} {owner : Scope} (X Y : Atlas)
    {source target : PageElement owner} (arrow : PageElement.Arrow source target)
    (sourceValid : rawTraceValid X Y source) (targetValid : rawTraceValid X Y target)
    (selectedSource selectedTarget : SourceCell X Y)
    (sourceAt : resolvedAt X Y source selectedSource) (targetAt : resolvedAt X Y target selectedTarget) :
    sourceTransport selectedSource selectedTarget := by
  have order : target.page ≤ source.page := arrow.precedes
  cases selectedSource <;> cases selectedTarget <;> simp only [resolvedAt, sourceTransport] at *
  all_goals try omega
  all_goals
    rename_i s t
    have sourcePage : s.val.page = source.page - 1 := by omega
    have targetPage : t.val.page = target.page - 1 := by omega
    have positive : 0 < target.page := by omega
    let sourceCell : ValidPageCell X Y (source.page - 1) := by
      first
      | exact ⟨.left s.val.trace, sourcePage ▸ leftSource_native X Y s⟩
      | exact ⟨.right s.val.trace, sourcePage ▸ rightSource_native X Y s⟩
    let targetCell : ValidPageCell X Y (target.page - 1) := by
      first
      | exact ⟨.left t.val.trace, targetPage ▸ leftSource_native X Y t⟩
      | exact ⟨.right t.val.trace, targetPage ▸ rightSource_native X Y t⟩
    have transported := arrow_nativeTransport X Y arrow sourceValid targetValid positive
      sourceCell targetCell
      (by simpa only [sourceCell, ← sourcePage] using sourceAt.2)
      (by simpa only [targetCell, ← targetPage] using targetAt.2)
    dsimp only [sourceCell, targetCell, nativeTransport] at transported
    first
    | exact ⟨by change t.val.page ≤ s.val.page; omega, transported⟩
    | exact Bool.noConfusion transported

def resolvedContains {Scope : Type} {owner : Scope} {cell : PageElementCell}
    (X Y : Atlas) (occurrence : PageElement owner) (datum : Datum cell) : Bool :=
  match resolveCellAt X Y occurrence.page occurrence.position with
  | none => false
  | some selected => contains selected datum

-- ALIGN: MERGE-RAW-MEMBERSHIP-PRESERVED.
theorem resolvedContains_preserved {Scope : Type} {owner : Scope} {a b : PageElementCell}
    (X Y : Atlas) {source target : PageElement owner} (arrow : PageElement.Arrow source target)
    (sourceValid : rawTraceValid X Y source) (targetValid : rawTraceValid X Y target)
    (datum : Datum a) (accepted : resolvedContains X Y source datum = true) :
    resolvedContains X Y target (retag (target := b) datum) = true := by
  have targetPresent : (resolveCellAt X Y target.page target.position).isSome = true := by
    rw [resolveCellAt_isSome]
    exact occurrence_resolvable X Y target targetValid
  cases sourceFound : resolveCellAt X Y source.page source.position with
  | none => simp [resolvedContains, sourceFound] at accepted
  | some selectedSource =>
      cases targetFound : resolveCellAt X Y target.page target.position with
      | none => simp [targetFound] at targetPresent
      | some selectedTarget =>
          have transported := resolvedTransport X Y arrow sourceValid targetValid selectedSource selectedTarget
            (resolveCellAt_resolvedAt X Y source selectedSource sourceFound)
            (resolveCellAt_resolvedAt X Y target selectedTarget targetFound)
          simpa only [resolvedContains, targetFound] using
            contains_transport_retag (b := b) ((sourceTransport_iff _ _).mp transported) datum
              (by simpa only [resolvedContains, sourceFound] using accepted)

end Datra.Executable.AtlasMerge
