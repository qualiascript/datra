import Executable.Atlas.Data
import Executable.PageElementLookup
import Executable.Atlas.Syntax

namespace Datra.Executable

/-- Hiding the nominal indices retains the complete computational owner. -/
structure AtlasOwner where
  value : Atlas

def atlasOwner (owner : Atlas) : AtlasOwner := ⟨owner⟩

/-- The raw witness retains an actual owning Atlas. Nominal object indices do
not replace this value in the elimination contract. -/
structure AtlasWitness where
  owner : Atlas

def atlasWitness (owner : Atlas) : AtlasWitness := ⟨owner⟩

def atlasWitnessOwner (witness : AtlasWitness) : AtlasOwner := atlasOwner witness.owner

-- ALIGN: ATLAS-WITNESS-CONSTRUCTION.
theorem atlasWitness_owner (owner : Atlas) :
    atlasWitnessOwner (atlasWitness owner) = atlasOwner owner := rfl

-- ALIGN: ATLAS-WITNESS-ELIMINATION.
def withAtlasWitness {Result : Sort*} (witness : AtlasWitness)
    (useOwner : Unit → (owner : Atlas) → atlasOwner owner = atlasWitnessOwner witness → Result) : Result :=
  useOwner (AtlasEquality.erase (⟨rfl⟩ : AtlasEquality witness.owner witness.owner)) witness.owner rfl

namespace AtlasWitness

def elementValid (witness : AtlasWitness) (element : PageElement witness.owner.pages) : Bool :=
  witness.owner.pages.traceValid element

def normalizeElement (witness : AtlasWitness) (element : PageElement witness.owner.pages) :
    PageElement witness.owner.pages :=
  element.normalize (witness.owner.pages.depth - 1) witness.owner.pages.depth

-- ALIGN: ATLAS-WITNESS-OWNER-AGREEMENT.
theorem owner_agrees (witness : AtlasWitness) (owner : Atlas)
    (ownerMatches : atlasOwner owner = atlasWitnessOwner witness)
    (source : PageElement witness.owner.pages) :
    witness.elementValid source = owner.pages.traceValid source ∧
      witness.normalizeElement source = source.normalize (owner.pages.depth - 1) owner.pages.depth := by
  have owner_eq : owner = witness.owner := congrArg AtlasOwner.value ownerMatches
  subst owner
  exact ⟨rfl, rfl⟩

theorem normalizeElement_valid (witness : AtlasWitness) (element : PageElement witness.owner.pages)
    (valid : witness.elementValid element = true) :
    witness.elementValid (witness.normalizeElement element) = true ∧
      witness.normalizeElement (witness.normalizeElement element) = witness.normalizeElement element :=
  ⟨witness.owner.pages.traceValid_normalize witness.owner.pagination.folio.valid element valid,
    PageElement.normalize_idempotent _ _ element⟩

-- ALIGN: ATLAS-WITNESS-NORMALIZATION.
theorem normalizeElement_laws (witness : AtlasWitness) (element : PageElement witness.owner.pages) :
    (witness.elementValid element = true → witness.elementValid (witness.normalizeElement element) = true) ∧
      witness.normalizeElement (witness.normalizeElement element) = witness.normalizeElement element :=
  ⟨fun valid => (normalizeElement_valid witness element valid).1,
    PageElement.normalize_idempotent _ _ element⟩

end AtlasWitness
end Datra.Executable
