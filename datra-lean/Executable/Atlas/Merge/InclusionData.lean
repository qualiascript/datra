import Executable.Atlas.Merge.InclusionPages

namespace Datra.Executable.AtlasMerge
open CategoryTheory

/-- Clamp only beyond the given limit, which may exceed the component's own
finite depth. This retains the genuine intermediate pages of a larger merge. -/
def clampedElement (X : Atlas) (limit : Nat) (bound : X.pages.depth - 1 ≤ limit)
    (source : X.Element) : X.Element :=
  FolioData.ValidElement.ofOccurrence ⟨min source.occurrence.page limit,
    cast (congrArg Page.Carrier (componentPage_clamp X limit source.occurrence.page bound).symm)
      source.occurrence.value⟩

theorem clampedElement_page (X : Atlas) (limit : Nat) (bound : X.pages.depth - 1 ≤ limit)
    (source : X.Element) :
    (clampedElement X limit bound source).val.page = min source.val.page limit := by
  change min source.occurrence.toRaw.page limit = _
  rw [FolioData.ValidElement.occurrence_toRaw]

theorem clampedElement_position (X : Atlas) (limit : Nat) (bound : X.pages.depth - 1 ≤ limit)
    (source : X.Element) :
    (clampedElement X limit bound source).val.position = source.val.position := by
  exact (pagePosition_cast (componentPage_clamp X limit source.occurrence.page bound).symm
    source.occurrence.value).trans (congrArg PageElement.position source.occurrence_toRaw)

theorem clampedElement_normalize (X : Atlas) (limit : Nat) (bound : X.pages.depth - 1 ≤ limit)
    (source : X.Element) : (clampedElement X limit bound source).normalize = source.normalize := by
  apply FolioData.ValidElement.eq_of_page_position
  · change min (clampedElement X limit bound source).val.page (X.pages.depth - 1) =
      min source.val.page (X.pages.depth - 1)
    rw [clampedElement_page]
    omega
  · exact clampedElement_position X limit bound source

theorem clampedElement_containsRank (X : Atlas) (limit : Nat) (bound : X.pages.depth - 1 ≤ limit)
    (source : X.Element) (rank : Nat) :
    X.cellContainsRank (clampedElement X limit bound source) rank = X.cellContainsRank source rank := by
  rw [← X.cellContainsRank_normalize, clampedElement_normalize, X.cellContainsRank_normalize]

theorem leftElement_normalize_clamp (X Y : Atlas) (source : X.Element) :
    (leftElement X Y source).normalize =
      leftElement X Y (clampedElement X (mergeDepth X Y - 1) (leftDepth_bound X Y) source) := by
  apply FolioData.ValidElement.eq_of_page_position
  · change min (leftElement X Y source).val.page
        ((prefixFolio X Y (mergeDepth X Y - 1)).data.depth - 1) = _
    rw [prefixFolio_depth, leftElement_page, leftElement_page, clampedElement_page]
    omega
  · exact (leftElement_position X Y source).trans
      ((clampedElement_position X _ _ source).symm.trans (leftElement_position X Y _).symm)

theorem rightElement_normalize_clamp (X Y : Atlas) (source : Y.Element) :
    (rightElement X Y source).normalize =
      rightElement X Y (clampedElement Y (mergeDepth X Y - 1) (rightDepth_bound X Y) source) := by
  apply FolioData.ValidElement.eq_of_page_position
  · change min (rightElement X Y source).val.page
        ((prefixFolio X Y (mergeDepth X Y - 1)).data.depth - 1) = _
    rw [prefixFolio_depth, rightElement_page, rightElement_page, clampedElement_page]
    omega
  · change (rightElement X Y source).val.position = _
    rw [rightElement_position, rightElement_position, clampedElement_page, clampedElement_position,
      componentPage_clamp X _ _ (leftDepth_bound X Y)]

theorem resolveStoredElement_left (X Y : Atlas) (source : X.Element) :
    resolveStoredElement X Y (leftElement X Y source) =
      .left (clampedElement X (mergeDepth X Y - 1) (leftDepth_bound X Y) source) := by
  rw [resolveStoredElement_runtime, leftElement_normalize_clamp]
  simp only [leftElement, FolioData.ValidElement.occurrence_ofOccurrence, resolveOccurrence_left,
    FolioData.ValidElement.ofOccurrence_occurrence]

theorem resolveStoredElement_right (X Y : Atlas) (source : Y.Element) :
    resolveStoredElement X Y (rightElement X Y source) =
      .right (clampedElement Y (mergeDepth X Y - 1) (rightDepth_bound X Y) source) := by
  rw [resolveStoredElement_runtime, rightElement_normalize_clamp]
  simp only [rightElement, FolioData.ValidElement.occurrence_ofOccurrence, resolveOccurrence_right,
    FolioData.ValidElement.ofOccurrence_occurrence]

-- ALIGN: MERGE-LEFT-INDEXED-MEMBERSHIP.
theorem leftDatum_valid_iff (X Y : Atlas) (source : X.Element)
    (datum : Datum (leftElement X Y source).val.cell) :
    datum.Valid X Y ↔ contains (SourceCell.left (Y := Y) source) datum = true := by
  rw [Datum.valid_iff, resolveStoredElement_left]
  cases datum <;> simp only [contains, clampedElement_containsRank]

-- ALIGN: MERGE-RIGHT-INDEXED-MEMBERSHIP.
theorem rightDatum_valid_iff (X Y : Atlas) (source : Y.Element)
    (datum : Datum (rightElement X Y source).val.cell) :
    datum.Valid X Y ↔ contains (SourceCell.right (X := X) source) datum = true := by
  rw [Datum.valid_iff, resolveStoredElement_right]
  cases datum <;> simp only [contains, clampedElement_containsRank]

def leftIndexedEquiv (X Y : Atlas) (source : X.Element) :
    IndexedDatum X Y (leftElement X Y source).val.cell ≃
      CertifiedDatum (SourceCell.left (Y := Y) source) (leftElement X Y source).val.cell where
  toFun datum := ⟨datum.val, (leftDatum_valid_iff X Y source datum.val).mp datum.property⟩
  invFun datum := ⟨datum.val, (leftDatum_valid_iff X Y source datum.val).mpr datum.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

def rightIndexedEquiv (X Y : Atlas) (source : Y.Element) :
    IndexedDatum X Y (rightElement X Y source).val.cell ≃
      CertifiedDatum (SourceCell.right (X := X) source) (rightElement X Y source).val.cell where
  toFun datum := ⟨datum.val, (rightDatum_valid_iff X Y source datum.val).mp datum.property⟩
  invFun datum := ⟨datum.val, (rightDatum_valid_iff X Y source datum.val).mpr datum.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

-- ALIGN: MERGE-LEFT-INDEXED-COMPONENT.
def leftIndexedComponent (X Y : Atlas) (source : X.Element) :
    DomanialInsertion (X.cellData source.val.cell)
      ((atlasMerge X Y).cellData (leftElement X Y source).val.cell) where
  map datum := (leftIndexedEquiv X Y source).symm ((leftComponent X Y source _).map datum)
  preimage datum := (leftComponent X Y source _).preimage (leftIndexedEquiv X Y source datum)
  leftInverse datum := by simp only [Equiv.apply_symm_apply, DomanialInsertion.leftInverse]

-- ALIGN: MERGE-RIGHT-INDEXED-COMPONENT.
def rightIndexedComponent (X Y : Atlas) (source : Y.Element) :
    DomanialInsertion (Y.cellData source.val.cell)
      ((atlasMerge X Y).cellData (rightElement X Y source).val.cell) where
  map datum := (rightIndexedEquiv X Y source).symm ((rightComponent X Y source _).map datum)
  preimage datum := (rightComponent X Y source _).preimage (rightIndexedEquiv X Y source datum)
  leftInverse datum := by simp only [Equiv.apply_symm_apply, DomanialInsertion.leftInverse]

-- ALIGN: MERGE-LEFT-MORPHISM.
def leftMorphism (X Y : Atlas) : PrimitiveAtlasMorphism X (atlasMerge X Y) where
  object := leftElement X Y
  component := leftIndexedComponent X Y
  arrow := leftArrow X Y
  naturality := by
    intro source target arrow datum
    apply Subtype.ext
    change Datum.left (X.originImageRank target.normalize
      ((X.data.action.normalizedMap arrow).map datum)) =
        Datum.left (X.originImageRank source.normalize datum)
    rw [X.originImageRank_normalize, X.originImageRank_normalize]
    exact congrArg Datum.left (congrArg (extentDominion X).rank (X.originImage_map arrow datum))

-- ALIGN: MERGE-RIGHT-MORPHISM.
def rightMorphism (X Y : Atlas) : PrimitiveAtlasMorphism Y (atlasMerge X Y) where
  object := rightElement X Y
  component := rightIndexedComponent X Y
  arrow := rightArrow X Y
  naturality := by
    intro source target arrow datum
    apply Subtype.ext
    change Datum.right (Y.originImageRank target.normalize
      ((Y.data.action.normalizedMap arrow).map datum)) =
        Datum.right (Y.originImageRank source.normalize datum)
    rw [Y.originImageRank_normalize, Y.originImageRank_normalize]
    exact congrArg Datum.right (congrArg (extentDominion Y).rank (Y.originImage_map arrow datum))

end Datra.Executable.AtlasMerge
