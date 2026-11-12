import Executable.Atlas.Merge.DataInterpretation
import Executable.Ordinal.Subtraction
import Executable.PageElementLookup

namespace Datra.Executable.AtlasMerge
open CategoryTheory

def leftElement (X Y : Atlas) (source : X.Element) : (atlasMerge X Y).Element :=
  FolioData.ValidElement.ofOccurrence (leftOccurrence X Y source.occurrence)

def rightElement (X Y : Atlas) (source : Y.Element) : (atlasMerge X Y).Element :=
  FolioData.ValidElement.ofOccurrence (rightOccurrence X Y source.occurrence)

theorem leftElement_page (X Y : Atlas) (source : X.Element) :
    (leftElement X Y source).val.page = source.val.page + 1 := by
  change source.occurrence.toRaw.page + 1 = _
  rw [FolioData.ValidElement.occurrence_toRaw]

theorem rightElement_page (X Y : Atlas) (source : Y.Element) :
    (rightElement X Y source).val.page = source.val.page + 1 := by
  change source.occurrence.toRaw.page + 1 = _
  rw [FolioData.ValidElement.occurrence_toRaw]

theorem leftElement_position (X Y : Atlas) (source : X.Element) :
    (leftElement X Y source).val.position = source.val.position :=
  (leftOccurrence_position X Y source.occurrence).trans
    (congrArg PageElement.position source.occurrence_toRaw)

theorem rightElement_position (X Y : Atlas) (source : Y.Element) :
    (rightElement X Y source).val.position =
      Ordinal.addOrdinals (componentPage X source.val.page).chain.orderType source.val.position := by
  have result := rightOccurrence_position X Y source.occurrence
  change (rightElement X Y source).val.position =
    Ordinal.addOrdinals (componentPage X source.occurrence.toRaw.page).chain.orderType
      source.occurrence.toRaw.position at result
  rwa [FolioData.ValidElement.occurrence_toRaw] at result

/-- The runtime page lookup used by the left inclusion always succeeds and
reconstructs the exact full trace, including padding. -/
-- ALIGN: MERGE-LEFT-CHECKED-LOOKUP.
theorem leftElement_lookup (X Y : Atlas) (source : X.Element) :
    (atlasMerge X Y).pages.elementAt (source.val.page + 1) source.val.position =
      some (leftElement X Y source) := by
  rw [← leftElement_page X Y source, ← leftElement_position X Y source]
  exact FolioData.elementAt_roundtrip _ _

-- ALIGN: MERGE-RIGHT-CHECKED-LOOKUP.
theorem rightElement_lookup (X Y : Atlas) (source : Y.Element) :
    (atlasMerge X Y).pages.elementAt (source.val.page + 1)
      (Ordinal.addOrdinals (componentPage X source.val.page).chain.orderType source.val.position) =
      some (rightElement X Y source) := by
  rw [← rightElement_page X Y source, ← rightElement_position X Y source]
  exact FolioData.elementAt_roundtrip _ _

theorem leftElement_normalized (X Y : Atlas) (source : X.Element) (normal : source.normalize = source) :
    (leftElement X Y source).normalize = leftElement X Y source := by
  apply FolioData.ValidElement.normalize_eq_of_page_bound
  rw [leftElement_page]
  change source.val.page + 1 ≤ (prefixFolio X Y (mergeDepth X Y - 1)).data.depth - 1
  rw [prefixFolio_depth]
  have bound := FolioData.ValidElement.page_bound_of_normalize_eq source normal
  change source.val.page ≤ X.pages.depth - 1 at bound
  have depth := leftDepth_bound X Y
  omega

theorem rightElement_normalized (X Y : Atlas) (source : Y.Element) (normal : source.normalize = source) :
    (rightElement X Y source).normalize = rightElement X Y source := by
  apply FolioData.ValidElement.normalize_eq_of_page_bound
  rw [rightElement_page]
  change source.val.page + 1 ≤ (prefixFolio X Y (mergeDepth X Y - 1)).data.depth - 1
  rw [prefixFolio_depth]
  have bound := FolioData.ValidElement.page_bound_of_normalize_eq source normal
  change source.val.page ≤ Y.pages.depth - 1 at bound
  have depth := rightDepth_bound X Y
  omega

def leftObjectPreimage (X Y : Atlas) (target : (atlasMerge X Y).Element) : Option X.Element :=
  if target.val.page = 0 then none
  else X.pages.elementAt (target.val.page - 1) target.val.position

def rightObjectPreimage (X Y : Atlas) (target : (atlasMerge X Y).Element) : Option Y.Element :=
  if target.val.page = 0 then none
  else (Ordinal.subtractOrdinal (componentPage X (target.val.page - 1)).chain.orderType
    target.val.position).bind (fun position => Y.pages.elementAt (target.val.page - 1) position)

-- ALIGN: MERGE-LEFT-OBJECT-ROUNDTRIP.
theorem leftObjectPreimage_roundtrip (X Y : Atlas) (source : X.Element) :
    leftObjectPreimage X Y (leftElement X Y source) = some source := by
  simp only [leftObjectPreimage, leftElement_page, Nat.add_eq_zero_iff, Nat.one_ne_zero,
    and_false, if_false, Nat.add_sub_cancel, leftElement_position]
  exact FolioData.elementAt_roundtrip _ _

-- ALIGN: MERGE-RIGHT-OBJECT-ROUNDTRIP.
theorem rightObjectPreimage_roundtrip (X Y : Atlas) (source : Y.Element) :
    rightObjectPreimage X Y (rightElement X Y source) = some source := by
  have offset : (componentPage X ((rightElement X Y source).val.page - 1)).chain.orderType =
      (componentPage X source.val.page).chain.orderType :=
    congrArg (fun page => (componentPage X page).chain.orderType)
      ((congrArg (· - 1) (rightElement_page X Y source)).trans (Nat.add_sub_cancel _ _))
  simp only [rightObjectPreimage, rightElement_page X Y source, Nat.add_eq_zero_iff, Nat.one_ne_zero,
    and_false, if_false, Nat.add_sub_cancel, rightElement_position]
  rw [offset, Ordinal.subtractOrdinal_add]
  exact FolioData.elementAt_roundtrip _ _

-- ALIGN: MERGE-LEFT-OBJECT-INVERSE-SOUND.
theorem leftObjectPreimage_sound (X Y : Atlas) (target : (atlasMerge X Y).Element)
    (source : X.Element) (found : leftObjectPreimage X Y target = some source) :
    leftElement X Y source = target := by
  unfold leftObjectPreimage at found
  split at found
  · contradiction
  · rename_i positive
    have spec := FolioData.elementAt_page_position X.pages _ _ source found
    apply FolioData.ValidElement.eq_of_page_position
    · rw [leftElement_page, spec.1]
      omega
    · exact (leftElement_position X Y source).trans spec.2

-- ALIGN: MERGE-RIGHT-OBJECT-INVERSE-SOUND.
theorem rightObjectPreimage_sound (X Y : Atlas) (target : (atlasMerge X Y).Element)
    (source : Y.Element) (found : rightObjectPreimage X Y target = some source) :
    rightElement X Y source = target := by
  unfold rightObjectPreimage at found
  split at found
  · contradiction
  · rename_i positive
    obtain ⟨position, subtracted, lookup⟩ := Option.bind_eq_some_iff.mp found
    have spec := FolioData.elementAt_page_position Y.pages _ _ source lookup
    apply FolioData.ValidElement.eq_of_page_position
    · rw [rightElement_page, spec.1]
      omega
    · rw [rightElement_position, spec.1, spec.2]
      exact Ordinal.subtractOrdinal_sound _ _ _ subtracted

theorem leftElement_ne_rightElement (X Y : Atlas) (left : X.Element) (right : Y.Element) :
    leftElement X Y left ≠ rightElement X Y right := by
  intro same
  have resolved := congrArg (fun source : (atlasMerge X Y).Element =>
    resolveOccurrence X Y source.occurrence) same
  simp only [leftElement, rightElement, FolioData.ValidElement.occurrence_ofOccurrence,
    resolveOccurrence_left, resolveOccurrence_right] at resolved
  cases resolved

-- ALIGN: MERGE-LEFT-OBJECT-OPPOSITE-REJECT.
theorem leftObjectPreimage_right (X Y : Atlas) (source : Y.Element) :
    leftObjectPreimage X Y (rightElement X Y source) = none := by
  cases found : leftObjectPreimage X Y (rightElement X Y source) with
  | none => rfl
  | some candidate =>
    exact False.elim (leftElement_ne_rightElement X Y candidate source
      (leftObjectPreimage_sound X Y _ candidate found))

-- ALIGN: MERGE-RIGHT-OBJECT-OPPOSITE-REJECT.
theorem rightObjectPreimage_left (X Y : Atlas) (source : X.Element) :
    rightObjectPreimage X Y (leftElement X Y source) = none := by
  cases found : rightObjectPreimage X Y (leftElement X Y source) with
  | none => rfl
  | some candidate =>
    exact False.elim (leftElement_ne_rightElement X Y source candidate
      (rightObjectPreimage_sound X Y _ candidate found).symm)

def leftTransposalElement (X Y : Atlas) (source : X.TransposalElement) : (atlasMerge X Y).TransposalElement :=
  ⟨leftElement X Y source.val, leftElement_normalized X Y source.val source.property⟩

def rightTransposalElement (X Y : Atlas) (source : Y.TransposalElement) : (atlasMerge X Y).TransposalElement :=
  ⟨rightElement X Y source.val, rightElement_normalized X Y source.val source.property⟩

def leftTransposalPreimage (X Y : Atlas) (target : (atlasMerge X Y).TransposalElement) : Option X.TransposalElement :=
  (leftObjectPreimage X Y target.val).map (Atlas.transposalElement X)

def rightTransposalPreimage (X Y : Atlas) (target : (atlasMerge X Y).TransposalElement) : Option Y.TransposalElement :=
  (rightObjectPreimage X Y target.val).map (Atlas.transposalElement Y)

-- ALIGN: MERGE-LEFT-NORMALIZED-OBJECT-ROUNDTRIP.
theorem leftTransposalPreimage_roundtrip (X Y : Atlas) (source : X.TransposalElement) :
    leftTransposalPreimage X Y (leftTransposalElement X Y source) = some source := by
  unfold leftTransposalPreimage leftTransposalElement
  rw [leftObjectPreimage_roundtrip, Option.map_some]
  exact congrArg some (Subtype.ext source.property)

-- ALIGN: MERGE-RIGHT-NORMALIZED-OBJECT-ROUNDTRIP.
theorem rightTransposalPreimage_roundtrip (X Y : Atlas) (source : Y.TransposalElement) :
    rightTransposalPreimage X Y (rightTransposalElement X Y source) = some source := by
  unfold rightTransposalPreimage rightTransposalElement
  rw [rightObjectPreimage_roundtrip, Option.map_some]
  exact congrArg some (Subtype.ext source.property)

-- ALIGN: MERGE-LEFT-OBJECT-INSERTION.
def leftObjectInsertion (X Y : Atlas) : DomanialInsertion X.TransposalElement (atlasMerge X Y).TransposalElement where
  map := leftTransposalElement X Y
  preimage := leftTransposalPreimage X Y
  leftInverse := leftTransposalPreimage_roundtrip X Y

-- ALIGN: MERGE-RIGHT-OBJECT-INSERTION.
def rightObjectInsertion (X Y : Atlas) : DomanialInsertion Y.TransposalElement (atlasMerge X Y).TransposalElement where
  map := rightTransposalElement X Y
  preimage := rightTransposalPreimage X Y
  leftInverse := rightTransposalPreimage_roundtrip X Y

end Datra.Executable.AtlasMerge
