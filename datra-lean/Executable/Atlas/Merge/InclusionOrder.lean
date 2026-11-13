import Executable.Atlas.Merge.InclusionData
import Executable.Atlas.OrderShift

namespace Datra.Executable.AtlasMerge
open CategoryTheory

-- ALIGN: MERGE-LEFT-TRANSPOSAL.
def leftTransposal (X Y : Atlas) : Atlas.Transposal X (atlasMerge X Y) where
  hom := .primitive (.primitive (leftMorphism X Y))
  objectInsertion := leftObjectInsertion X Y
  object_eq source := by
    apply Subtype.ext
    change leftElement X Y source.val = normalizedObject (leftElement X Y) source.val
    rw [normalizedObject, source.property, leftElement_normalized X Y source.val source.property]

-- ALIGN: MERGE-RIGHT-TRANSPOSAL.
def rightTransposal (X Y : Atlas) : Atlas.Transposal Y (atlasMerge X Y) where
  hom := .primitive (.primitive (rightMorphism X Y))
  objectInsertion := rightObjectInsertion X Y
  object_eq source := by
    apply Subtype.ext
    change rightElement X Y source.val = normalizedObject (rightElement X Y) source.val
    rw [normalizedObject, source.property, rightElement_normalized X Y source.val source.property]

-- ALIGN: MERGE-LEFT-ORDER.
theorem left_preservesOrder (X Y : Atlas) (x y : X.TransposalElement)
    (ordered : Atlas.TransposalElement.lt x y = true) :
    Atlas.TransposalElement.lt (leftTransposalElement X Y x) (leftTransposalElement X Y y) = true := by
  apply preservesOrderOfShift (leftElement X Y) 1 (leftElement_page X Y)
    (leftElement_normalized X Y) (leftArrow X Y) _ x y ordered
  intro a b _ ordered
  simpa only [leftElement_position] using ordered

-- ALIGN: MERGE-RIGHT-ORDER.
theorem right_preservesOrder (X Y : Atlas) (x y : Y.TransposalElement)
    (ordered : Atlas.TransposalElement.lt x y = true) :
    Atlas.TransposalElement.lt (rightTransposalElement X Y x) (rightTransposalElement X Y y) = true := by
  apply preservesOrderOfShift (rightElement X Y) 1 (rightElement_page X Y)
    (rightElement_normalized X Y) (rightArrow X Y) _ x y ordered
  intro a b same ordered
  rw [rightElement_position, rightElement_position, same]
  exact Ordinal.ordinalAddRightBelow _ _ _ ordered

-- ALIGN: MERGE-LEFT-ORDERED-TRANSPOSAL.
def leftOrderedTransposal (X Y : Atlas) : Atlas.OrderedTransposal X (atlasMerge X Y) :=
  .primitive (leftTransposal X Y) (left_preservesOrder X Y)

-- ALIGN: MERGE-RIGHT-ORDERED-TRANSPOSAL.
def rightOrderedTransposal (X Y : Atlas) : Atlas.OrderedTransposal Y (atlasMerge X Y) :=
  .primitive (rightTransposal X Y) (right_preservesOrder X Y)

end Datra.Executable.AtlasMerge
