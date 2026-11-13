import Executable.Atlas.Sequence.InclusionData
import Executable.Atlas.OrderShift

namespace Datra.Executable.AtlasSequence
open CategoryTheory

variable {count : Nat}

-- ALIGN: SEQUENCE-MEMBER-TRANSPOSAL.
def memberTransposal (positive : 0 < count) (members : Fin count → Atlas) (index : Fin count) :
    Atlas.Transposal (members index) (atlasSequence positive members) where
  hom := .primitive (.primitive (memberMorphism positive members index))
  objectInsertion := memberObjectInsertion positive members index
  object_eq source := by
    apply Subtype.ext
    change memberElement positive members index source.val =
      normalizedObject (memberElement positive members index) source.val
    rw [normalizedObject, source.property, memberElement_normalized positive members index source.val source.property]

-- ALIGN: SEQUENCE-MEMBER-ORDER.
theorem member_preservesOrder (positive : 0 < count) (members : Fin count → Atlas) (index : Fin count)
    (x y : (members index).TransposalElement) (ordered : Atlas.TransposalElement.lt x y = true) :
    Atlas.TransposalElement.lt (memberTransposalElement positive members index x)
      (memberTransposalElement positive members index y) = true := by
  apply preservesOrderOfShift (memberElement positive members index) 1 (memberElement_page positive members index)
    (memberElement_normalized positive members index) (memberArrow positive members index) _ x y ordered
  intro a b same ordered
  rw [memberElement_position, memberElement_position, same]
  exact Ordinal.ordinalAddRightBelow _ _ _ ordered

-- ALIGN: SEQUENCE-MEMBER-ORDERED-TRANSPOSAL.
def memberOrderedTransposal (positive : 0 < count) (members : Fin count → Atlas) (index : Fin count) :
    Atlas.OrderedTransposal (members index) (atlasSequence positive members) :=
  .primitive (memberTransposal positive members index) (member_preservesOrder positive members index)

end Datra.Executable.AtlasSequence
