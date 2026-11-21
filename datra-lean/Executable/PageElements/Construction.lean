import Executable.PageElements

namespace Datra.Executable

/-- A fixed class dictionary selects one complete folio. There is no runtime
configuration argument; its owned occurrence category is indexed by that folio. -/
structure PageElementsConstruction (origin final : Page) where
  folio : Folio origin final

namespace PageElementsConstruction
variable {origin final : Page}

-- ALIGN: PE-FIXED-CONSTRUCTION.
def constructPageElements (recipe : PageElementsConstruction origin final) :
    Folio origin final := recipe.folio

theorem constructPageElements_folio (recipe : PageElementsConstruction origin final) :
    recipe.constructPageElements = recipe.folio := rfl

end PageElementsConstruction

end Datra.Executable
