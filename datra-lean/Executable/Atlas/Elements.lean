import Executable.Atlas.Data

namespace Datra.Executable.Atlas
open CategoryTheory

/-- The hidden transposal-element constructor retains only genuine cells.
Its normalization invariant is established by the public constructor. -/
def TransposalElement (X : Atlas) := {x : X.Element // x.normalize = x}

def transposalElement (X : Atlas) (x : X.Element) : X.TransposalElement :=
  ⟨x.normalize, x.normalize_idempotent⟩

def withTransposalElement {X : Atlas} {Result : Sort*} (x : X.TransposalElement)
    (useElement : X.Element → Result) : Result := useElement x.val

namespace TransposalElement

def equal {X : Atlas} (x y : X.TransposalElement) : Bool :=
  x.val.val.page == y.val.val.page && x.val.val.position == y.val.val.position

theorem equal_iff {X : Atlas} (x y : X.TransposalElement) : equal x y = true ↔ x = y := by
  constructor
  · intro h
    simp only [equal, Bool.and_eq_true, beq_iff_eq] at h
    exact Subtype.ext (FolioData.ValidElement.eq_of_page_position h.1 h.2)
  · rintro rfl
    simp [equal]

noncomputable def toSemantics {X : Atlas} (x : X.TransposalElement) : X.toSemantics.El :=
  X.pages.toSemantics.collapseElements.obj
    ((FolioData.ValidElement.elementsEquivalence X.pages).functor.obj x.val)

theorem fromFinite_toSemantics {X : Atlas} (x : X.TransposalElement) :
    (FolioData.ValidElement.fromFinite X.pages).obj x.toSemantics = x.val :=
  (FolioData.ValidElement.fromFinite_collapse x.val).trans x.property

noncomputable def fromSemantics (X : Atlas) (x : X.toSemantics.El) : X.TransposalElement :=
  ⟨(FolioData.ValidElement.fromFinite X.pages).obj x,
    FolioData.ValidElement.normalize_fromFinite X.pages x⟩

-- ALIGN: ATLAS-TRANSPOSE-ELEMENT-EQUIVALENCE.
noncomputable def semanticsEquiv (X : Atlas) : X.TransposalElement ≃ X.toSemantics.El where
  toFun := toSemantics
  invFun := fromSemantics X
  left_inv x := Subtype.ext x.fromFinite_toSemantics
  right_inv x := by
    apply FolioData.ValidElement.fromFinite_injective X.pages
    exact (fromSemantics X x).fromFinite_toSemantics

@[simp] theorem toSemantics_fromSemantics (X : Atlas) (x : X.toSemantics.El) :
    (fromSemantics X x).toSemantics = x := (semanticsEquiv X).right_inv x

/-- Move the dependent datum along the checked equality of genuine cells. -/
noncomputable def dataToSemantics {X : Atlas} (x : X.TransposalElement)
    (datum : X.cellData x.val.val.cell) : X.toSemantics.Da.obj x.toSemantics := by
  change X.cellData ((FolioData.ValidElement.fromFinite X.pages).obj x.toSemantics).val.cell
  exact cast (congrArg (fun y : X.Element => X.cellData y.val.cell)
    x.fromFinite_toSemantics.symm) datum

end TransposalElement
end Datra.Executable.Atlas
