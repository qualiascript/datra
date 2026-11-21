import Executable.PageElements

namespace Datra.Executable

/-- A fixed class dictionary selects one complete folio. There is no runtime
configuration argument; its owned occurrence category is indexed by that folio. -/
structure PageElementsConstruction (origin final : Page) where
  folio : Folio origin final

namespace PageElementsConstruction
universe u
variable {origin final : Page}

-- ALIGN: PE-FIXED-CONSTRUCTION.
def constructPageElements (recipe : PageElementsConstruction origin final) :
    Folio origin final := recipe.folio

theorem constructPageElements_folio (recipe : PageElementsConstruction origin final) :
    recipe.constructPageElements = recipe.folio := rfl

/-- Generative runtime allocation retains the supplied folio. The abstract
owner is represented by this exact folio in the executable category model. -/
def withPageElements {Result : Sort u} (pages : Folio origin final)
    (useCategory : Folio origin final → Result) : Result := useCategory pages

-- ALIGN: PE-GENERATIVE-FOLIO.
theorem withPageElements_folio (pages : Folio origin final) :
    withPageElements pages id = pages := rfl

end PageElementsConstruction

end Datra.Executable
