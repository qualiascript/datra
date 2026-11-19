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

-- ALIGN: MERGE-RAW-TRACE-VALIDITY.
def rawTraceValid {Scope : Type} {owner : Scope} (X Y : Atlas) (occurrence : PageElement owner) : Prop :=
  (folio X Y).data.traceLookup occurrence.page occurrence.position = some occurrence.trace

theorem genuineOccurrence_trace {Scope : Type} {owner : Scope} (X Y : Atlas)
    (occurrence : PageElement owner) (valid : rawTraceValid X Y occurrence)
    (positive : 0 < occurrence.page) (bound : occurrence.page ≤ mergeDepth X Y)
    (cell : ValidPageCell X Y (occurrence.page - 1))
    (position : pagePosition X Y (occurrence.page - 1) cell.val = occurrence.position) :
    occurrence.trace = (prefixFolio X Y (occurrence.page - 1)).data.genuineTrace cell := by
  have lookup := folio_cellLookup_prefix X Y occurrence.page positive bound cell
  rw [position, valid] at lookup
  exact Option.some.inj lookup

-- ALIGN: MERGE-GENUINE-ARROW-NATIVE-TRANSPORT.
theorem genuineArrow_nativeTransport {Scope : Type} {owner : Scope} (X Y : Atlas)
    {source target : PageElement owner} (arrow : PageElement.Arrow source target)
    (sourceValid : rawTraceValid X Y source) (targetValid : rawTraceValid X Y target)
    (positive : 0 < target.page) (bound : source.page ≤ mergeDepth X Y)
    (sourceCell : ValidPageCell X Y (source.page - 1))
    (targetCell : ValidPageCell X Y (target.page - 1))
    (sourcePosition : pagePosition X Y (source.page - 1) sourceCell.val = source.position)
    (targetPosition : pagePosition X Y (target.page - 1) targetCell.val = target.position) :
    nativeTransport sourceCell.val targetCell.val = true := by
  have precedes := arrow.precedes
  have sourceTrace := genuineOccurrence_trace X Y source sourceValid (positive.trans_le precedes)
    bound sourceCell sourcePosition
  have targetTrace := genuineOccurrence_trace X Y target targetValid positive
    (precedes.trans bound) targetCell targetPosition
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

theorem leftSource_native (X Y : Atlas) (source : X.Element) :
    PageCell.left source.val.trace ∈ Set.range (pageEncode X Y source.val.page) := by
  rcases source with ⟨_, occurrence, rfl⟩
  exact ⟨.inl occurrence.value, rfl⟩

theorem rightSource_native (X Y : Atlas) (source : Y.Element) :
    PageCell.right source.val.trace ∈ Set.range (pageEncode X Y source.val.page) := by
  rcases source with ⟨_, occurrence, rfl⟩
  exact ⟨.inr occurrence.value, rfl⟩

-- ALIGN: MERGE-RESOLVED-FINITE-TRANSPORT.
theorem resolvedFiniteTransport {Scope : Type} {owner : Scope} (X Y : Atlas)
    {source target : PageElement owner} (arrow : PageElement.Arrow source target)
    (sourceValid : rawTraceValid X Y source) (targetValid : rawTraceValid X Y target)
    (bound : source.page ≤ mergeDepth X Y) (selectedSource selectedTarget : SourceCell X Y)
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
    have transported := genuineArrow_nativeTransport X Y arrow sourceValid targetValid positive bound
      sourceCell targetCell
      (by simpa only [sourceCell, ← sourcePage] using sourceAt.2)
      (by simpa only [targetCell, ← targetPage] using targetAt.2)
    dsimp only [sourceCell, targetCell, nativeTransport] at transported
    first
    | exact ⟨by change t.val.page ≤ s.val.page; omega, transported⟩
    | exact Bool.noConfusion transported

end Datra.Executable.AtlasMerge
