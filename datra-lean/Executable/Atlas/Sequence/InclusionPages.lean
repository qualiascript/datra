import Executable.Atlas.Sequence.InclusionObjects

namespace Datra.Executable.AtlasSequence
open CategoryTheory

variable {count : Nat}

def SourceCell.page {members : Fin count → Atlas} : SourceCell members → Nat
  | .origin => 0
  | .member _ source => source.val.page + 1

theorem sourceOccurrence_page (positive : 0 < count) (members : Fin count → Atlas) (source : SourceCell members) :
    (sourceOccurrence positive members source).page = source.page := by
  cases source with
  | origin => rfl
  | member index source =>
    change source.occurrence.toRaw.page + 1 = _
    rw [FolioData.ValidElement.occurrence_toRaw]
    rfl

theorem resolveOccurrence_page (positive : 0 < count) (members : Fin count → Atlas)
    (source : (pagination positive members).pages.Occurrence) :
    (resolveOccurrence positive members source).page = source.page := by
  rw [← sourceOccurrence_page positive members, sourceOccurrence_resolve]

/-- Resolution retains the unique target of a member trace on each page. -/
theorem Transport.target_eq {members : Fin count → Atlas} {source a b : SourceCell members}
    (first : Transport source a) (second : Transport source b) (samePage : a.page = b.page) : a = b := by
  cases first with
  | origin => cases second; rfl
  | toOrigin index source =>
    cases second with
    | toOrigin => rfl
    | member _ arrow => change 0 = _ + 1 at samePage; omega
  | member index first =>
    cases second with
    | toOrigin => change _ + 1 = 0 at samePage; omega
    | member _ second =>
      have same := FolioData.ValidElement.arrow_target_eq first second (Nat.add_right_cancel samePage)
      cases same
      rfl

theorem resolveStoredElement_member_normalized (positive : 0 < count) (members : Fin count → Atlas)
    (index : Fin count) (source : (members index).Element) (normal : source.normalize = source) :
    resolveStoredElement positive members (memberElement positive members index source) = .member index source := by
  rw [resolveStoredElement_runtime, memberElement_normalized positive members index source normal]
  simp only [memberElement, FolioData.ValidElement.occurrence_ofOccurrence,
    resolveOccurrence_member, FolioData.ValidElement.ofOccurrence_occurrence]

/-- The sequence's actual interval has the same resolved target as the
member arrow. Uniqueness of trace targets then identifies that interval. -/
def memberArrowOfNormalized (positive : 0 < count) (members : Fin count → Atlas) (index : Fin count)
    {source target : (members index).Element} (arrow : source ⟶ target)
    (sourceNormal : source.normalize = source) (targetNormal : target.normalize = target) :
    memberElement positive members index source ⟶ memberElement positive members index target := by
  let X := atlasSequence positive members
  let a := memberElement positive members index source
  let b := memberElement positive members index target
  have precedes : b.val.page ≤ a.val.page := by
    dsimp only [a, b]
    rw [memberElement_page, memberElement_page]
    exact Nat.add_le_add_right arrow.precedes 1
  let reached : X.pages.Occurrence := ⟨b.val.page,
    (X.pages.transport a.val.page b.val.page precedes).map a.occurrence.value⟩
  let c := FolioData.ValidElement.ofOccurrence reached
  have actual : a ⟶ c := by
    have result := X.pages.transportArrow a.val.page b.val.page precedes a.occurrence.value
    change FolioData.ValidElement.ofOccurrence a.occurrence ⟶ c at result
    rwa [FolioData.ValidElement.ofOccurrence_occurrence] at result
  have bNormal : b.normalize = b := memberElement_normalized positive members index target targetNormal
  have cNormal : c.normalize = c := FolioData.ValidElement.normalize_eq_of_page_bound c
    (FolioData.ValidElement.page_bound_of_normalize_eq b bNormal)
  have resolved := resolveStoredElement_arrow positive members actual
  rw [resolveStoredElement_member_normalized positive members index source sourceNormal] at resolved
  have targetResolution := resolveStoredElement_runtime positive members c
  rw [cNormal] at targetResolution
  rw [targetResolution] at resolved
  have targetEq : resolveOccurrence positive members c.occurrence = .member index target :=
    Transport.target_eq resolved (.member index arrow) (by
      rw [resolveOccurrence_page]
      change (memberElement positive members index target).val.page = target.val.page + 1
      exact memberElement_page positive members index target)
  have bResolution : resolveOccurrence positive members b.occurrence = .member index target := by
    simp only [b, memberElement, FolioData.ValidElement.occurrence_ofOccurrence,
      resolveOccurrence_member, FolioData.ValidElement.ofOccurrence_occurrence]
  have occurrences : c.occurrence = b.occurrence := by
    apply (occurrenceEquiv positive members).injective
    exact targetEq.trans bResolution.symm
  have equal : c = b := by
    simpa only [FolioData.ValidElement.ofOccurrence_occurrence] using
      congrArg FolioData.ValidElement.ofOccurrence occurrences
  rwa [equal] at actual

-- ALIGN: SEQUENCE-MEMBER-ARROW.
def memberArrow (positive : 0 < count) (members : Fin count → Atlas) (index : Fin count)
    {source target : (members index).Element} (arrow : source ⟶ target) :
    normalizedObject (memberElement positive members index) source ⟶
      normalizedObject (memberElement positive members index) target :=
  FolioData.ValidElement.normalizeArrow
    (memberArrowOfNormalized positive members index (FolioData.ValidElement.normalizeArrow arrow)
      source.normalize_idempotent target.normalize_idempotent)

end Datra.Executable.AtlasSequence
