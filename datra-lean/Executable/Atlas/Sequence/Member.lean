import Executable.Atlas.Derived
import Executable.Folio.TraceChain

namespace Datra.Executable.AtlasSequence

/-- One existential runtime member, retaining its complete executable Atlas. -/
structure Member where
  atlas : Atlas

namespace Member

/-- The standard nonempty-list constructor retains its first member and tail. -/
-- ALIGN: SEQUENCE-MEMBER-LIST.
def memberList (members : Member × List Member) : List Member := members.1 :: members.2

theorem memberList_positive (members : Member × List Member) : 0 < (memberList members).length := by
  simp [memberList]

-- ALIGN: SEQUENCE-MEMBER-LENGTH.
def length (member : Member) : Nat := member.atlas.pages.length

theorem length_positive (member : Member) : 0 < member.length :=
  member.atlas.pages.length_positive member.atlas.pagination.folio.valid

-- ALIGN: SEQUENCE-MEMBER-PAGE-MEMBERSHIP.
def contains (member : Member) (page : Nat) (positions : List Ordinal) : Bool :=
  member.atlas.pages.traceLookup page (FolioData.traceHead positions) == some positions

abbrev Trace (member : Member) (page : Nat) := member.atlas.pages.TraceCarrier page

/-- Resolve precisely the accepted trace of this existential member. -/
-- ALIGN: SEQUENCE-MEMBER-TRACE-RESOLUTION.
def withTrace {result : Type*} (member : Member) (page : Nat) (positions : member.Trace page)
    (useCell : (source : member.atlas.Element) → source.val.page = page →
      source.val.position = FolioData.traceHead positions.val → source.val.trace = positions.val → result) :
    Option result :=
  member.atlas.withCellTrace page positions useCell

theorem withTrace_isSome {result : Type*} (member : Member) (page : Nat) (positions : member.Trace page)
    (useCell : (source : member.atlas.Element) → source.val.page = page →
      source.val.position = FolioData.traceHead positions.val → source.val.trace = positions.val → result) :
    (member.withTrace page positions useCell).isSome = true :=
  member.atlas.withCellTrace_isSome page positions useCell

theorem contains_iff (member : Member) (page : Nat) (positions : List Ordinal) :
    member.contains page positions = true ↔
      member.atlas.pages.traceLookup page (FolioData.traceHead positions) = some positions := by
  simp [contains]

-- ALIGN: SEQUENCE-MEMBER-PAGE-ORDER.
def pageOrder (member : Member) (page : Nat) : Ordinal :=
  (member.atlas.pages.pageAt page).chain.orderType

-- ALIGN: SEQUENCE-MEMBER-PAGE-CHAIN.
def pageChain (member : Member) (page : Nat) : Chain (member.Trace page) :=
  member.atlas.pages.traceChain member.atlas.pagination.folio.valid page

theorem pageChain_order (member : Member) (page : Nat) :
    (member.pageChain page).orderType = member.pageOrder page :=
  member.atlas.pages.traceChain_order member.atlas.pagination.folio.valid page

/-- The native chain represents the original member page, including padded pages. -/
noncomputable def pageChainOrderIso (member : Member) (page : Nat) :
    (member.pageChain page).toSemantics.Obj ≃o (member.atlas.pages.pageAt page).chain.toSemantics.Obj :=
  member.atlas.pages.traceChainOrderIso member.atlas.pagination.folio.valid page

-- ALIGN: SEQUENCE-MEMBER-PAGE-ORIGIN.
def origin (member : Member) : member.Trace 0 :=
  member.atlas.pages.traceOrigin member.atlas.pagination.folio.valid

-- ALIGN: SEQUENCE-MEMBER-PAGE-PREVIOUS.
def previous (member : Member) (page : Nat) (trace : member.Trace (page + 1)) : member.Trace page :=
  trace.previous member.atlas.pagination.folio.valid page

-- ALIGN: SEQUENCE-MEMBER-PAGE-NEXT.
def next (member : Member) (page : Nat) (trace : member.Trace page) : member.Trace (page + 1) :=
  trace.next member.atlas.pagination.folio.valid page

theorem previous_next (member : Member) (page : Nat) (trace : member.Trace page) :
    member.previous page (member.next page trace) = trace :=
  FolioData.TraceCarrier.previous_next member.atlas.pagination.folio.valid page trace

-- ALIGN: SEQUENCE-MEMBER-PAGE-TRANSITION.
def transition (member : Member) (page : Nat)
    (source : Chain (member.Trace (page + 1))) (target : Chain (member.Trace page))
    (sourcePosition : source.position = fun trace => FolioData.traceHead trace.val)
    (targetPosition : target.position = fun trace => FolioData.traceHead trace.val) :
    OrderedConsolidation (member.Trace (page + 1)) (member.Trace page) :=
  member.atlas.pages.traceTransitionBetween member.atlas.pagination.folio.valid page
    source target sourcePosition targetPosition

-- ALIGN: SEQUENCE-MEMBER-STORED-MAP.
theorem transition_map (member : Member) (page : Nat)
    (source : Chain (member.Trace (page + 1))) (target : Chain (member.Trace page))
    (sourcePosition : source.position = fun trace => FolioData.traceHead trace.val)
    (targetPosition : target.position = fun trace => FolioData.traceHead trace.val) :
    (member.transition page source target sourcePosition targetPosition).map.map = member.previous page := rfl

-- ALIGN: SEQUENCE-MEMBER-STORED-PREIMAGE.
theorem transition_preimage (member : Member) (page : Nat)
    (source : Chain (member.Trace (page + 1))) (target : Chain (member.Trace page))
    (sourcePosition : source.position = fun trace => FolioData.traceHead trace.val)
    (targetPosition : target.position = fun trace => FolioData.traceHead trace.val) :
    (member.transition page source target sourcePosition targetPosition).map.preimage = member.next page := rfl

end Member
end Datra.Executable.AtlasSequence
