import Executable.Atlas.Presentation

namespace Datra.Executable

/-- A fixed, pure object recipe retains its source pagination. Its resulting
Atlas carries the checked data family and laws; the recipe and source determine
one object, matching the runtime construction's nominal derived scope. -/
structure AtlasDataConstruction where
  object : Atlas → Atlas
  pagination : ∀ owner, (object owner).pagination = owner.pagination

namespace AtlasDataConstruction

/-- Interpret a construction instance by allocating its checked presentations. -/
def ofPresentations (recipe : Atlas → AtlasPresentation)
    (ownsPagination : ∀ owner, (recipe owner).pagination = owner.pagination) : AtlasDataConstruction where
  object owner := (recipe owner).allocate
  pagination owner := (AtlasPresentation.allocate_pagination (recipe owner)).trans (ownsPagination owner)

-- ALIGN: ATLAS-DATA-CONSTRUCTION.
def constructAtlasData (construction : AtlasDataConstruction) (owner : Atlas) : Atlas :=
  construction.object owner

-- ALIGN: ATLAS-DATA-CONSTRUCTION-PAGINATION.
theorem constructAtlasData_pagination (construction : AtlasDataConstruction) (owner : Atlas) :
    (construction.constructAtlasData owner).pagination = owner.pagination := construction.pagination owner

theorem ofPresentations_construct (recipe : Atlas → AtlasPresentation)
    (ownsPagination : ∀ owner, (recipe owner).pagination = owner.pagination) (owner : Atlas) :
    (ofPresentations recipe ownsPagination).constructAtlasData owner = (recipe owner).allocate := rfl

end AtlasDataConstruction

/-- A complete fixed recipe takes no runtime configuration. Its presentation
determines the pagination and action together, as in the public Haskell class. -/
structure AtlasConstruction where
  presentation : AtlasPresentation

namespace AtlasConstruction

-- ALIGN: ATLAS-FIXED-CONSTRUCTION.
def constructAtlas (recipe : AtlasConstruction) : Atlas := recipe.presentation.allocate

-- ALIGN: ATLAS-FIXED-CONSTRUCTION-PAGINATION.
theorem constructAtlas_pagination (recipe : AtlasConstruction) :
    recipe.constructAtlas.pagination = recipe.presentation.pagination :=
  AtlasPresentation.allocate_pagination recipe.presentation

theorem constructAtlas_eq (recipe : AtlasConstruction) :
    recipe.constructAtlas = recipe.presentation.allocate := rfl

end AtlasConstruction
end Datra.Executable
