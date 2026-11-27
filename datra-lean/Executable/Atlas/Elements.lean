import Executable.Atlas.Data
import Executable.PageElementLookup

namespace Datra.Executable.Atlas
open CategoryTheory

/-- The hidden transposal-element constructor retains only genuine cells.
Its normalization invariant is established by the public constructor. -/
def TransposalElement (X : Atlas) := {x : X.Element // x.normalize = x}

def transposalElement (X : Atlas) (x : X.Element) : X.TransposalElement :=
  ⟨x.normalize, x.normalize_idempotent⟩

def withTransposalElement {X : Atlas} {Result : Sort*} (x : X.TransposalElement)
    (useElement : X.Element → Result) : Result := useElement x.val

/-- The executable existential stores a raw occurrence. Its scalar owner test
is explicit; identifying its payload with an owning cell is separate evidence. -/
structure TransposalElementData (X : Atlas) where
  source : PageElement X.pages

namespace TransposalElementData

def valid (X : Atlas) (element : TransposalElementData X) : Prop :=
  X.pages.traceValid element.source = true ∧
    element.source.normalize (X.pages.depth - 1) X.pages.depth = element.source

def ofSource (X : Atlas) (source : PageElement X.pages) : TransposalElementData X :=
  ⟨source.normalize (X.pages.depth - 1) X.pages.depth⟩

-- ALIGN: ATLAS-TRANSPOSAL-OWNED-ELEMENT.
theorem at_valid (X : Atlas) (source : PageElement X.pages)
    (accepted : X.pages.traceValid source = true) :
    valid X (ofSource X source) ∧
      (ofSource X source).source = source.normalize (X.pages.depth - 1) X.pages.depth :=
  ⟨⟨X.pages.traceValid_normalize X.pagination.folio.valid source accepted,
      PageElement.normalize_idempotent _ _ source⟩, rfl⟩

-- ALIGN: ATLAS-TRANSPOSAL-OWNED-ELIMINATION.
def withOwned {X : Atlas} {Result : Sort*} (element : TransposalElementData X)
    (accepted : valid X element)
    (useSource : (source : PageElement X.pages) →
      X.pages.traceValid source = true →
      source.normalize (X.pages.depth - 1) X.pages.depth = source →
      source = element.source → Result) : Result :=
  useSource element.source accepted.1 accepted.2 rfl

def ofElement {X : Atlas} (element : X.TransposalElement) : TransposalElementData X :=
  ⟨element.val.val⟩

theorem ofElement_valid {X : Atlas} (element : X.TransposalElement) :
    valid X (ofElement element) :=
  ⟨element.val.traceValid X.pagination.folio.valid, congrArg Subtype.val element.property⟩

theorem at_ofElement (X : Atlas) (source : X.Element) :
    ofSource X source.val = ofElement (transposalElement X source) := rfl

end TransposalElementData

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
