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

namespace AtlasPresentation
open CategoryTheory

-- ALIGN: ATLAS-PREDICATE-PRESENTATION.
def ofAction (pagination : Pagination) {cellData : PageElementCell → Type}
    (action : AtlasMembershipAction pagination.pages cellData) [owner : action.FolioOwner]
    (laws : action.Laws) : AtlasPresentation :=
  ⟨pagination, cellData, action, owner, laws⟩

-- ALIGN: ATLAS-PRESENTATION-ALLOCATION.
def allocate (presentation : AtlasPresentation) : Atlas :=
  letI := presentation.ownership
  AtlasMembershipAction.toCanonicalAtlas presentation.pagination presentation.action presentation.laws

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
