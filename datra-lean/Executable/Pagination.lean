import Executable.PageElements.Construction

namespace Datra.Executable

open CategoryTheory
universe s t

/-- A pagination supplies the owner index for its valid page elements. -/
structure Pagination where
  origin : Page
  final : Page
  folio : Folio origin final

abbrev Pagination.pages (P : Pagination) := P.folio.data

abbrev Pagination.Element (P : Pagination) := P.pages.ValidElement

/-- Wrapping an already owned category preserves its folio and valid elements. -/
-- ALIGN: PAGINATION-FROM-PAGE-ELEMENTS.
def Pagination.fromPageElements {origin final : Page} (elements : Folio origin final) :
    Pagination := ⟨origin, final, elements⟩

theorem Pagination.fromPageElements_folio {origin final : Page}
    (elements : Folio origin final) :
    (Pagination.fromPageElements elements).folio = elements := rfl

theorem Pagination.fromPageElements_elements {origin final : Page}
    (elements : Folio origin final) :
    (Pagination.fromPageElements elements).Element = elements.data.ValidElement := rfl

noncomputable def Pagination.toSemantics (P : Pagination) : Datra.Semantics.Pag := ⟨P.pages.toSemantics⟩

/-- Pagination morphisms store an object operation and its arrow witness. -/
structure PaginationMorphism (source target : Pagination) where
  mapObject : source.Element → target.Element
  mapArrow : ∀ {x y}, (x ⟶ y) → (mapObject x ⟶ mapObject y)

namespace PaginationMorphism
variable {source middle target : Pagination}

def toFunctor (f : PaginationMorphism source target) : source.Element ⥤ target.Element where
  obj := f.mapObject
  map := f.mapArrow

def identity (P : Pagination) : PaginationMorphism P P := ⟨id, id⟩

def comp (first : PaginationMorphism source middle) (second : PaginationMorphism middle target) :
    PaginationMorphism source target :=
  ⟨second.mapObject ∘ first.mapObject, fun f => second.mapArrow (first.mapArrow f)⟩

noncomputable def toTallFunctor (f : PaginationMorphism source target) :
    source.pages.toSemantics.TallEl ⥤ target.pages.toSemantics.TallEl :=
  (FolioData.ValidElement.elementsEquivalence source.pages).inverse ⋙ f.toFunctor ⋙
    (FolioData.ValidElement.elementsEquivalence target.pages).functor

end PaginationMorphism

instance : Category Pagination where
  Hom := PaginationMorphism
  id := PaginationMorphism.identity
  comp := PaginationMorphism.comp
  id_comp := fun _ => rfl
  comp_id := fun _ => rfl
  assoc := fun _ _ _ => rfl

end Datra.Executable
