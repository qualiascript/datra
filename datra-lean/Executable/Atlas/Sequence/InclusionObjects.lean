import Executable.Atlas.Sequence.Data
import Executable.PageElementLookup

namespace Datra.Executable.AtlasSequence
open CategoryTheory

variable {count : Nat}

def memberElement (positive : 0 < count) (members : Fin count → Atlas) (index : Fin count)
    (source : (members index).Element) : (atlasSequence positive members).Element :=
  FolioData.ValidElement.ofOccurrence (memberOccurrence positive members index source.occurrence)

theorem memberElement_page (positive : 0 < count) (members : Fin count → Atlas) (index : Fin count)
    (source : (members index).Element) :
    (memberElement positive members index source).val.page = source.val.page + 1 := by
  change source.occurrence.toRaw.page + 1 = _
  rw [FolioData.ValidElement.occurrence_toRaw]

theorem memberElement_position (positive : 0 < count) (members : Fin count → Atlas) (index : Fin count)
    (source : (members index).Element) :
    (memberElement positive members index source).val.position =
      Ordinal.addOrdinals (ChainSequence.prefixOrder (pageOrders members source.val.page) index.val)
        source.val.position := by
  have result := memberOccurrence_position positive members index source.occurrence
  change (memberElement positive members index source).val.position =
    Ordinal.addOrdinals (ChainSequence.prefixOrder (pageOrders members source.occurrence.toRaw.page) index.val)
      source.occurrence.toRaw.position at result
  rwa [FolioData.ValidElement.occurrence_toRaw] at result

/-- The runtime inclusion's checked page lookup succeeds, including on
full-spine padding pages. -/
theorem memberElement_lookup (positive : 0 < count) (members : Fin count → Atlas) (index : Fin count)
    (source : (members index).Element) :
    (atlasSequence positive members).pages.elementAt (source.val.page + 1)
      (Ordinal.addOrdinals (ChainSequence.prefixOrder (pageOrders members source.val.page) index.val)
        source.val.position) = some (memberElement positive members index source) := by
  rw [← memberElement_page positive members index source, ← memberElement_position positive members index source]
  exact FolioData.elementAt_roundtrip _ _

theorem memberElement_normalized (positive : 0 < count) (members : Fin count → Atlas) (index : Fin count)
    (source : (members index).Element) (normal : source.normalize = source) :
    (memberElement positive members index source).normalize = memberElement positive members index source := by
  apply FolioData.ValidElement.normalize_eq_of_page_bound
  rw [memberElement_page]
  change source.val.page + 1 ≤ (prefixFolio positive members (sequenceDepth members - 1)).data.depth - 1
  rw [prefixFolio_depth]
  have bound := FolioData.ValidElement.page_bound_of_normalize_eq source normal
  change source.val.page ≤ (members index).pages.depth - 1 at bound
  have depth := memberClamp_bound members index
  omega

/-- Subtract the exact prefix, check the member's local bound, then perform
the same checked page lookup as the executable inclusion inverse. -/
def memberObjectPreimage (positive : 0 < count) (members : Fin count → Atlas) (index : Fin count)
    (target : (atlasSequence positive members).Element) : Option (members index).Element :=
  if target.val.page = 0 then none
  else (Ordinal.subtractOrdinal (ChainSequence.prefixOrder (pageOrders members (target.val.page - 1)) index.val)
    target.val.position).bind (fun position =>
      if Ordinal.ordinalLT position (componentPage members (target.val.page - 1) index).chain.orderType then
        (members index).pages.elementAt (target.val.page - 1) position
      else none)

theorem memberObjectPreimage_roundtrip (positive : 0 < count) (members : Fin count → Atlas) (index : Fin count)
    (source : (members index).Element) :
    memberObjectPreimage positive members index (memberElement positive members index source) = some source := by
  simp only [memberObjectPreimage, memberElement_page, Nat.add_eq_zero_iff, Nat.one_ne_zero,
    and_false, if_false, Nat.add_sub_cancel, memberElement_position]
  rw [Ordinal.subtractOrdinal_add, Option.bind_some]
  have below : Ordinal.ordinalLT source.val.position (componentPage members source.val.page index).chain.orderType = true := by
    change Ordinal.ordinalLT source.val.position ((members index).pages.pageAt source.val.page).chain.orderType = true
    rw [← (members index).pages.elementAt_isSome, FolioData.elementAt_roundtrip]
    rfl
  rw [memberElement_page, Nat.add_sub_cancel, below, if_pos rfl]
  exact FolioData.elementAt_roundtrip _ _

theorem memberObjectPreimage_sound (positive : 0 < count) (members : Fin count → Atlas) (index : Fin count)
    (target : (atlasSequence positive members).Element) (source : (members index).Element)
    (found : memberObjectPreimage positive members index target = some source) :
    memberElement positive members index source = target := by
  unfold memberObjectPreimage at found
  split at found
  · contradiction
  · rename_i positivePage
    obtain ⟨position, subtracted, lookup⟩ := Option.bind_eq_some_iff.mp found
    split at lookup
    · have spec := FolioData.elementAt_page_position (members index).pages _ _ source lookup
      apply FolioData.ValidElement.eq_of_page_position
      · rw [memberElement_page, spec.1]
        omega
      · rw [memberElement_position, spec.1, spec.2]
        exact Ordinal.subtractOrdinal_sound _ _ _ subtracted
    · contradiction

theorem memberElement_distinct (positive : 0 < count) (members : Fin count → Atlas)
    (i j : Fin count) (different : i ≠ j) (a : (members i).Element) (b : (members j).Element) :
    memberElement positive members i a ≠ memberElement positive members j b := by
  intro same
  have resolved := congrArg (fun source : (atlasSequence positive members).Element =>
    resolveOccurrence positive members source.occurrence) same
  simp only [memberElement, FolioData.ValidElement.occurrence_ofOccurrence,
    resolveOccurrence_member, FolioData.ValidElement.ofOccurrence_occurrence] at resolved
  cases resolved
  exact different rfl

theorem memberObjectPreimage_other (positive : 0 < count) (members : Fin count → Atlas)
    (i j : Fin count) (different : i ≠ j) (source : (members j).Element) :
    memberObjectPreimage positive members i (memberElement positive members j source) = none := by
  cases found : memberObjectPreimage positive members i (memberElement positive members j source) with
  | none => rfl
  | some candidate =>
    exact False.elim (memberElement_distinct positive members i j different candidate source
      (memberObjectPreimage_sound positive members i _ candidate found))

def memberTransposalElement (positive : 0 < count) (members : Fin count → Atlas) (index : Fin count)
    (source : (members index).TransposalElement) : (atlasSequence positive members).TransposalElement :=
  ⟨memberElement positive members index source.val, memberElement_normalized positive members index source.val source.property⟩

def memberTransposalPreimage (positive : 0 < count) (members : Fin count → Atlas) (index : Fin count)
    (target : (atlasSequence positive members).TransposalElement) : Option (members index).TransposalElement :=
  (memberObjectPreimage positive members index target.val).map (Atlas.transposalElement (members index))

theorem memberTransposalPreimage_roundtrip (positive : 0 < count) (members : Fin count → Atlas) (index : Fin count)
    (source : (members index).TransposalElement) :
    memberTransposalPreimage positive members index (memberTransposalElement positive members index source) = some source := by
  unfold memberTransposalPreimage memberTransposalElement
  rw [memberObjectPreimage_roundtrip, Option.map_some]
  exact congrArg some (Subtype.ext source.property)

def memberObjectInsertion (positive : 0 < count) (members : Fin count → Atlas) (index : Fin count) :
    DomanialInsertion (members index).TransposalElement (atlasSequence positive members).TransposalElement where
  map := memberTransposalElement positive members index
  preimage := memberTransposalPreimage positive members index
  leftInverse := memberTransposalPreimage_roundtrip positive members index

end Datra.Executable.AtlasSequence
