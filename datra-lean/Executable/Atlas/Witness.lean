import Executable.Atlas.Data
import Executable.Atlas.Membership
import Executable.PageElementLookup
import Executable.Atlas.Syntax

namespace Datra.Executable

/-- Hiding the nominal indices retains the complete computational owner. -/
structure AtlasOwner where
  value : Atlas

def atlasOwner (owner : Atlas) : AtlasOwner := ⟨owner⟩

/-- The runtime owner before interpreting membership as an accepted carrier.
Retaining the raw action is necessary to compare its predicates and partial
inverses; equality of the interpreted Atlas alone does not recover them. -/
structure RawAtlasOwner where
  pagination : Pagination
  cellData : PageElementCell → Type
  action : AtlasMembershipAction pagination.pages cellData
  folioOwner : action.FolioOwner
  laws : @AtlasMembershipAction.Laws _ _ _ _ action folioOwner

namespace RawAtlasOwner
open CategoryTheory

instance (owner : RawAtlasOwner) : owner.action.FolioOwner := owner.folioOwner

def toAtlas (owner : RawAtlasOwner) : Atlas :=
  owner.action.toCanonicalAtlas owner.pagination owner.laws

def toOwner (owner : RawAtlasOwner) : AtlasOwner := atlasOwner owner.toAtlas

def accepts (owner : RawAtlasOwner) (occurrence : PageElement owner.pagination.pages)
    (datum : owner.cellData occurrence.cell) : Bool :=
  owner.action.acceptsAt (owner.pagination.pages.depth - 1) owner.pagination.pages.depth occurrence datum

-- ALIGN: ATLAS-OWNERS-DATUM-AGREEMENT.
theorem membership_agrees (first second : RawAtlasOwner) (same : first = second)
    (source : PageElement first.pagination.pages) (target : PageElement second.pagination.pages)
    (sameOccurrence : HEq source target) : HEq (first.accepts source) (second.accepts target) := by
  cases same
  cases eq_of_heq sameOccurrence
  rfl

-- ALIGN: ATLAS-OWNERS-DATA-MAP-AGREEMENT.
theorem mapData_agree (first second : RawAtlasOwner) (same : first = second)
    {source target : first.pagination.pages.ValidElement}
    {otherSource otherTarget : second.pagination.pages.ValidElement}
    (sameSource : HEq source otherSource) (sameTarget : HEq target otherTarget)
    (arrow : source ⟶ target) (otherArrow : otherSource ⟶ otherTarget) :
    HEq (first.action.normalizedMap arrow) (second.action.normalizedMap otherArrow) := by
  cases same
  cases eq_of_heq sameSource
  cases eq_of_heq sameTarget
  cases Subsingleton.elim arrow otherArrow
  rfl

theorem interpretation_agrees (first second : RawAtlasOwner) (same : first = second) :
    first.toOwner = second.toOwner := congrArg toOwner same

end RawAtlasOwner

/-- The raw witness retains an actual owning Atlas. Nominal object indices do
not replace this value in the elimination contract. -/
structure AtlasWitness where
  owner : Atlas

def atlasWitness (owner : Atlas) : AtlasWitness := ⟨owner⟩

def atlasWitnessOwner (witness : AtlasWitness) : AtlasOwner := atlasOwner witness.owner

-- ALIGN: ATLAS-WITNESS-INDEXED-OWNER.
-- ALIGN: ATLAS-WITNESS-CONSTRUCTION.
-- ALIGN: ATLAS-WITNESS-RAW-CONSTRUCTION.
theorem atlasWitness_owner (owner : Atlas) :
    atlasWitnessOwner (atlasWitness owner) = atlasOwner owner := rfl

-- ALIGN: ATLAS-WITNESS-ELIMINATION.
-- ALIGN: ATLAS-WITNESS-RAW-ELIMINATION.
def withAtlasWitness {Result : Sort*} (witness : AtlasWitness)
    (useOwner : Unit → (owner : Atlas) → atlasOwner owner = atlasWitnessOwner witness → Result) : Result :=
  useOwner (AtlasEquality.erase (⟨rfl⟩ : AtlasEquality witness.owner witness.owner)) witness.owner rfl

/-- Construction and dependent elimination recover the same complete owner. -/
theorem withAtlasWitness_construct (owner : Atlas) :
    withAtlasWitness (atlasWitness owner) (fun _ recovered _ => atlasOwner recovered) = atlasOwner owner := rfl

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
