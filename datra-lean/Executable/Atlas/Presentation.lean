import Executable.Atlas.Membership

namespace Datra.Executable

/-- The checked construction data are independent of the scope introduced
when the runtime Atlas is allocated. Ownership and laws stay with the action. -/
structure AtlasPresentation where
  pagination : Pagination
  cellData : PageElementCell → Type
  action : AtlasMembershipAction pagination.pages cellData
  ownership : action.FolioOwner
  laws : letI := ownership; action.Laws

/-- The runtime allocation retains the raw membership action and its laws.
The owner is a phantom scope; interpretation into `Atlas` passes to accepted
carriers only after this stored representation has been retained. -/
structure AtlasAllocation (_owner : Type) where
  storedPresentation : AtlasPresentation

namespace AtlasAllocation

-- ALIGN: ATLAS-OWNER-DESCRIPTION.
def atlasDescription {Owner : Type} (value : AtlasAllocation Owner) : AtlasPresentation :=
  value.storedPresentation

/-- Membership uses the raw stored action at the normalized occurrence. -/
def acceptsDatum {Owner : Type} (value : AtlasAllocation Owner)
    (occurrence : PageElement value.atlasDescription.pagination.pages)
    (datum : value.atlasDescription.cellData occurrence.cell) : Bool :=
  value.storedPresentation.action.acceptsAt
    (value.storedPresentation.pagination.pages.depth - 1)
    value.storedPresentation.pagination.pages.depth occurrence datum

abbrev AcceptedDatum {Owner : Type} (value : AtlasAllocation Owner)
    (occurrence : PageElement value.atlasDescription.pagination.pages) :=
  {datum : value.atlasDescription.cellData occurrence.cell //
    value.acceptsDatum occurrence datum = true}

-- ALIGN: ATLAS-DESCRIPTION-MEMBERSHIP.
theorem descriptionMembership {Owner : Type} (value : AtlasAllocation Owner)
    (occurrence : PageElement value.atlasDescription.pagination.pages)
    (datum : value.atlasDescription.cellData occurrence.cell) :
    value.acceptsDatum occurrence datum =
      value.atlasDescription.action.membership.accepts
        (occurrence.normalize (value.atlasDescription.pagination.pages.depth - 1)
          value.atlasDescription.pagination.pages.depth) datum := rfl

/-- Interpret the stored raw action through the canonical accepted carriers. -/
def toAtlas {Owner : Type} (value : AtlasAllocation Owner) : Atlas :=
  let presentation := value.atlasDescription
  letI := presentation.ownership
  AtlasMembershipAction.toCanonicalAtlas presentation.pagination presentation.action presentation.laws

/-- The categorical carrier and the runtime membership subtype contain the
same raw data. Only the proof of membership changes. -/
def acceptedCarrierEquiv {Owner : Type} (value : AtlasAllocation Owner)
    (occurrence : value.toAtlas.Element) :
    value.toAtlas.cellData occurrence.val.cell ≃ value.AcceptedDatum occurrence.val :=
  letI := value.atlasDescription.ownership
  value.atlasDescription.action.canonicalCarrierEquiv occurrence

@[simp] theorem acceptedCarrierEquiv_val {Owner : Type} (value : AtlasAllocation Owner)
    (occurrence : value.toAtlas.Element) (datum : value.toAtlas.cellData occurrence.val.cell) :
    (value.acceptedCarrierEquiv occurrence datum).val = datum.val := rfl

@[simp] theorem acceptedCarrierEquiv_symm_val {Owner : Type} (value : AtlasAllocation Owner)
    (occurrence : value.toAtlas.Element)
    (datum : value.AcceptedDatum occurrence.val) :
    ((value.acceptedCarrierEquiv occurrence).symm datum).val = datum.val := rfl

end AtlasAllocation

namespace AtlasPresentation
open CategoryTheory

-- ALIGN: ATLAS-PREDICATE-PRESENTATION.
def ofAction (pagination : Pagination) {cellData : PageElementCell → Type}
    (action : AtlasMembershipAction pagination.pages cellData) [owner : action.FolioOwner]
    (laws : action.Laws) : AtlasPresentation :=
  ⟨pagination, cellData, action, owner, laws⟩

-- ALIGN: ATLAS-PRESENTATION-ALLOCATION.
def allocateStored {Owner : Type} (presentation : AtlasPresentation) : AtlasAllocation Owner :=
  ⟨presentation⟩

-- ALIGN: ATLAS-ALLOCATION-DESCRIPTION.
theorem allocateStored_description {Owner : Type} (presentation : AtlasPresentation) :
    (presentation.allocateStored (Owner := Owner)).atlasDescription = presentation := rfl

/-- The category-level Atlas interprets the exact retained allocation. -/
def allocate (presentation : AtlasPresentation) : Atlas :=
  (presentation.allocateStored (Owner := Unit)).toAtlas

-- ALIGN: ATLAS-PRESENTATION-PAGINATION.
theorem allocate_pagination (presentation : AtlasPresentation) :
    presentation.allocate.pagination = presentation.pagination := rfl

-- ALIGN: ATLAS-PRESENTATION-CONTINUATION.
def withAllocated {Result : Type} (presentation : AtlasPresentation) (useAtlas : Atlas → Result) : Result :=
  useAtlas presentation.allocate

theorem allocate_ofAction (pagination : Pagination) {cellData : PageElementCell → Type}
    (action : AtlasMembershipAction pagination.pages cellData) [action.FolioOwner] (laws : action.Laws) :
    (ofAction pagination action laws).allocate =
      AtlasMembershipAction.toCanonicalAtlas pagination action laws := rfl

/-- Allocation preserves the accepted data functor through the existing
canonical-carrier interpretation, without adding a law or changing an arrow. -/
def allocateFunctorIso (presentation : AtlasPresentation) :
    letI := presentation.ownership
    presentation.allocate.data.toFunctor ≅ presentation.action.acceptedFunctor presentation.laws :=
  letI := presentation.ownership
  AtlasMembershipAction.canonicalFunctorIso presentation.pagination presentation.action presentation.laws

end AtlasPresentation
end Datra.Executable
