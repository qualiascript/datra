import Executable.Atlas.Merge.InclusionData
import Executable.Atlas.OrderedTransposal

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

/-- A constant page shift preserves the common comparison page. It suffices
that the normalized arrow operation transports both traces there and that the
position map preserves strict order within each page. -/
private theorem preservesOrderOfShift {X Z : Atlas} (object : X.Element → Z.Element) (shift : Nat)
    (page : ∀ source, (object source).val.page = source.val.page + shift)
    (normal : ∀ source, source.normalize = source → (object source).normalize = object source)
    (arrow : ∀ {source target}, (source ⟶ target) →
      (normalizedObject object source ⟶ normalizedObject object target))
    (position : ∀ a b, a.val.page = b.val.page →
      Ordinal.ordinalLT a.val.position b.val.position = true →
      Ordinal.ordinalLT (object a).val.position (object b).val.position = true)
    (x y : X.TransposalElement) (ordered : Atlas.TransposalElement.lt x y = true) :
    PageElement.elementLT (object x.val).val (object y.val).val = true := by
  let m := X.toSemantics.Fo.commonBase x.toSemantics.1 y.toSemantics.1
  let a : X.toSemantics.El :=
    ⟨m, X.toSemantics.Fo.cellDiagram.map
      (X.toSemantics.Fo.toCommonLeft x.toSemantics.1 y.toSemantics.1) x.toSemantics.2⟩
  let b : X.toSemantics.El :=
    ⟨m, X.toSemantics.Fo.cellDiagram.map
      (X.toSemantics.Fo.toCommonRight x.toSemantics.1 y.toSemantics.1) y.toSemantics.2⟩
  let fx : x.toSemantics ⟶ a := CategoryOfElements.homMk _ _
    (X.toSemantics.Fo.toCommonLeft x.toSemantics.1 y.toSemantics.1) rfl
  let fy : y.toSemantics ⟶ b := CategoryOfElements.homMk _ _
    (X.toSemantics.Fo.toCommonRight x.toSemantics.1 y.toSemantics.1) rfl
  let F := FolioData.ValidElement.fromFinite X.pages
  have ax : x.val ⟶ F.obj a := by
    have f := F.map fx
    rw [Atlas.TransposalElement.fromFinite_toSemantics] at f
    exact f
  have by_ : y.val ⟶ F.obj b := by
    have f := F.map fy
    rw [Atlas.TransposalElement.fromFinite_toSemantics] at f
    exact f
  have common : (F.obj a).val.page = min x.val.val.page y.val.val.page := by
    rw [← x.fromFinite_toSemantics, ← y.fromFinite_toSemantics]
    rfl
  have same : (F.obj a).val.page = (F.obj b).val.page := rfl
  have axPos := FolioData.ValidElement.positionAtPage_arrow ax
  have byPos := FolioData.ValidElement.positionAtPage_arrow by_
  rw [← same] at byPos
  change (match PageElement.positionAtPage (min x.val.val.page y.val.val.page) x.val.val,
      PageElement.positionAtPage (min x.val.val.page y.val.val.page) y.val.val with
    | some u, some v => Ordinal.ordinalLT u v
    | _, _ => false) = true at ordered
  rw [← common, axPos, byPos] at ordered
  have na : (F.obj a).normalize = F.obj a := FolioData.ValidElement.normalize_fromFinite _ _
  have nb : (F.obj b).normalize = F.obj b := FolioData.ValidElement.normalize_fromFinite _ _
  have mappedAx : object x.val ⟶ object (F.obj a) := by
    have result := arrow ax
    simpa only [normalizedObject, x.property, na,
      normal x.val x.property, normal (F.obj a) na] using result
  have mappedBy : object y.val ⟶ object (F.obj b) := by
    have result := arrow by_
    simpa only [normalizedObject, y.property, nb,
      normal y.val y.property, normal (F.obj b) nb] using result
  have mappedAxPos := FolioData.ValidElement.positionAtPage_arrow mappedAx
  have mappedByPos := FolioData.ValidElement.positionAtPage_arrow mappedBy
  have mappedCommon : (object (F.obj a)).val.page =
      min (object x.val).val.page (object y.val).val.page := by
    rw [page, page, page, common]
    omega
  have mappedSame : (object (F.obj b)).val.page = (object (F.obj a)).val.page := by
    rw [page, page, same]
  rw [mappedSame] at mappedByPos
  unfold PageElement.elementLT
  dsimp only
  rw [← mappedCommon, mappedAxPos, mappedByPos]
  exact position (F.obj a) (F.obj b) same ordered

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
