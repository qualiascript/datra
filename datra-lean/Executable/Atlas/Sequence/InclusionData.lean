import Executable.Atlas.Sequence.InclusionPages
import Executable.Atlas.Clamping

namespace Datra.Executable.AtlasSequence
open CategoryTheory

variable {count : Nat}

theorem memberElement_normalize_clamp (positive : 0 < count) (members : Fin count → Atlas)
    (index : Fin count) (source : (members index).Element) :
    (memberElement positive members index source).normalize =
      memberElement positive members index
        (clampedElement (members index) (sequenceDepth members - 1) (memberClamp_bound members index) source) := by
  apply FolioData.ValidElement.eq_of_page_position
  · change min (memberElement positive members index source).val.page
        ((prefixFolio positive members (sequenceDepth members - 1)).data.depth - 1) = _
    rw [prefixFolio_depth, memberElement_page, memberElement_page, clampedElement_page]
    omega
  · change (memberElement positive members index source).val.position = _
    rw [memberElement_position, memberElement_position, clampedElement_page, clampedElement_position,
      pageOrders_clamp]

theorem resolveStoredElement_member (positive : 0 < count) (members : Fin count → Atlas)
    (index : Fin count) (source : (members index).Element) :
    resolveStoredElement positive members (memberElement positive members index source) =
      .member index (clampedElement (members index) (sequenceDepth members - 1) (memberClamp_bound members index) source) := by
  rw [resolveStoredElement_runtime, memberElement_normalize_clamp]
  simp only [memberElement, FolioData.ValidElement.occurrence_ofOccurrence, resolveOccurrence_member,
    FolioData.ValidElement.ofOccurrence_occurrence]

/-- A component inclusion retains precisely its member tag and the source
cell's accepted origin ranks, including padding inside a deeper sequence. -/
-- ALIGN: SEQUENCE-MEMBER-INDEXED-MEMBERSHIP.
theorem memberDatum_valid_iff (positive : 0 < count) (members : Fin count → Atlas)
    (index : Fin count) (source : (members index).Element)
    (datum : Datum (memberElement positive members index source).val.cell) :
    datum.Valid positive members ↔ contains (SourceCell.member index source) datum = true := by
  rw [Datum.valid_iff, resolveStoredElement_member]
  simp only [contains, clampedElement_containsRank]

def memberIndexedEquiv (positive : 0 < count) (members : Fin count → Atlas)
    (index : Fin count) (source : (members index).Element) :
    IndexedDatum positive members (memberElement positive members index source).val.cell ≃
      CertifiedDatum (SourceCell.member index source) (memberElement positive members index source).val.cell where
  toFun datum := ⟨datum.val, (memberDatum_valid_iff positive members index source datum.val).mp datum.property⟩
  invFun datum := ⟨datum.val, (memberDatum_valid_iff positive members index source datum.val).mpr datum.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

-- ALIGN: SEQUENCE-MEMBER-INDEXED-COMPONENT.
def memberIndexedComponent (positive : 0 < count) (members : Fin count → Atlas)
    (index : Fin count) (source : (members index).Element) :
    DomanialInsertion ((members index).cellData source.val.cell)
      ((atlasSequence positive members).cellData (memberElement positive members index source).val.cell) where
  map datum := (memberIndexedEquiv positive members index source).symm ((memberComponent members index source _).map datum)
  preimage datum := (memberComponent members index source _).preimage (memberIndexedEquiv positive members index source datum)
  leftInverse datum := by simp only [Equiv.apply_symm_apply, DomanialInsertion.leftInverse]

-- ALIGN: SEQUENCE-MEMBER-MORPHISM.
def memberMorphism (positive : 0 < count) (members : Fin count → Atlas) (index : Fin count) :
    PrimitiveAtlasMorphism (members index) (atlasSequence positive members) where
  object := memberElement positive members index
  component := memberIndexedComponent positive members index
  arrow := memberArrow positive members index
  naturality := by
    intro source target arrow datum
    apply Subtype.ext
    change Datum.mk index.val ((members index).originImageRank target.normalize
      (((members index).data.action.normalizedMap arrow).map datum)) =
        Datum.mk index.val ((members index).originImageRank source.normalize datum)
    rw [Atlas.originImageRank_normalize, Atlas.originImageRank_normalize]
    exact congrArg (Datum.mk index.val)
      (congrArg ((members index).dataAt (FolioData.ValidElement.originElement (members index).pages)).rank
        ((members index).originImage_map arrow datum))

end Datra.Executable.AtlasSequence
