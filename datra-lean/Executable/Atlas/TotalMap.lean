import Executable.Atlas.Map
import Executable.Atlas.Presentation

namespace Datra.Executable

/-- The runtime certificate names an inhabitant and proves equality for every
value of its carrier. A restricted region requires this carrier to be the
accepted subtype, rather than merely the ambient Haskell datum type. -/
structure SingletonDominion (Carrier : Type*) where
  value : Carrier
  unique : ∀ candidate, candidate = value

namespace SingletonDominion

theorem ext {Carrier : Type*} {left right : SingletonDominion Carrier}
    (same : left.value = right.value) : left = right := by
  cases left
  cases right
  cases same
  rfl

-- ALIGN: SINGLETON-DOMINION-UNIQUENESS.
theorem singletonDominionUnique {Carrier : Type*} (certificate : SingletonDominion Carrier)
    (candidate : Carrier) : candidate = certificate.value := certificate.unique candidate

-- ALIGN: SINGLETON-DOMINION-CONSTRUCTION.
def singletonDominion {Carrier : Type*} (selected : Carrier)
    (unique : ∀ candidate, candidate = selected) : SingletonDominion Carrier :=
  ⟨selected, unique⟩

@[simp] theorem singletonDominion_value {Carrier : Type*} (selected : Carrier)
    (unique : ∀ candidate, candidate = selected) :
    (singletonDominion selected unique).value = selected := rfl

theorem nonempty_subsingleton {Carrier : Type*} (certificate : SingletonDominion Carrier) :
    Nonempty Carrier ∧ Subsingleton Carrier :=
  ⟨⟨certificate.value⟩, ⟨fun left right =>
    (certificate.unique left).trans (certificate.unique right).symm⟩⟩

/-- Change the presentation of the certified carrier without choosing a new
inhabitant or requiring a new uniqueness proof. -/
def reindex {A B : Type*} (certificate : SingletonDominion A) (equiv : A ≃ B) :
    SingletonDominion B :=
  ⟨equiv certificate.value, fun candidate => by
    simpa using congrArg equiv (certificate.unique (equiv.symm candidate))⟩

@[simp] theorem reindex_value {A B : Type*} (certificate : SingletonDominion A) (equiv : A ≃ B) :
    (certificate.reindex equiv).value = equiv certificate.value := rfl

@[simp] theorem reindex_symm {A B : Type*} (certificate : SingletonDominion A) (equiv : A ≃ B) :
    (certificate.reindex equiv).reindex equiv.symm = certificate :=
  ext (equiv.symm_apply_apply certificate.value)

end SingletonDominion

def AtlasMap.regionValid {X : Atlas} (_value : AtlasMap X) (region : X.Element) : Bool :=
  decide (region.val.page = X.pages.depth - 1)

/-- Singleton certificates quantify only over accepted data at an owning,
genuine final-page occurrence. The Atlas carrier encodes datum membership. -/
structure TotalAtlasMap (X : Atlas) where
  underlying : AtlasMap X
  regionSingleton : (region : X.Element) → underlying.regionValid region = true →
    SingletonDominion (X.cellData region.val.cell)

namespace TotalAtlasMap
variable {X : Atlas}

-- ALIGN: TOTAL-ATLAS-MAP-INTERPRETATION.
theorem isTotalAtlasMap (value : TotalAtlasMap X) :
    Datra.Semantics.IsTotalAtlasMap value.underlying.toSemantics := by
  intro region
  obtain ⟨index, rfl⟩ := X.territoryIndexEquiv.surjective region
  have final : value.underlying.regionValid (X.territoryElement index) = true := by
    apply decide_eq_true
    change (FolioData.ValidElement.lastElement X.pages index).val.page = _
    rw [FolioData.ValidElement.lastElement_interpretation,
      FolioData.ValidElement.fromFinite_page]
    rfl
  have singleton := (value.regionSingleton (X.territoryElement index) final).nonempty_subsingleton
  change Nonempty (Datra.Semantics.territory X.toSemantics (X.territoryIndexToSemantics index)) ∧
    Subsingleton (Datra.Semantics.territory X.toSemantics (X.territoryIndexToSemantics index))
  rw [← X.territory_interpretation index]
  exact singleton

noncomputable def toSemantics (value : TotalAtlasMap X) : Datra.Semantics.TotalAtlasMap :=
  ⟨value.underlying.toSemantics, value.isTotalAtlasMap⟩

/-- On genuine occurrences the written totality predicate supplies exactly
the required inhabited singleton carrier, in the reverse direction as well. -/
theorem regionSingleton_exists (owner : AtlasMap X)
    (total : Datra.Semantics.IsTotalAtlasMap owner.toSemantics)
    (region : X.Element) (final : owner.regionValid region = true) :
    Nonempty (SingletonDominion (X.cellData region.val.cell)) := by
  have atFinal : region.val.page = X.pages.depth - 1 := by
    simpa only [AtlasMap.regionValid, decide_eq_true_eq] using final
  obtain ⟨index, rfl⟩ := FolioData.ValidElement.lastElement_surjective X.pages region atFinal
  have singleton := total (X.territoryIndexToSemantics index)
  change Nonempty (Datra.Semantics.territory X.toSemantics (X.territoryIndexToSemantics index)) ∧
    Subsingleton (Datra.Semantics.territory X.toSemantics (X.territoryIndexToSemantics index)) at singleton
  rw [← X.territory_interpretation index] at singleton
  obtain ⟨selected⟩ := singleton.1
  exact ⟨⟨selected, fun candidate => singleton.2.allEq candidate selected⟩⟩

/-- This reverse interpretation is mathematical, not a replacement for the
explicit executable singleton evidence required by the Haskell constructor. -/
noncomputable def ofSemantics (owner : AtlasMap X)
    (total : Datra.Semantics.IsTotalAtlasMap owner.toSemantics) : TotalAtlasMap X where
  underlying := owner
  regionSingleton region final := Classical.choice (regionSingleton_exists owner total region final)

@[simp] theorem ofSemantics_owner (owner : AtlasMap X)
    (total : Datra.Semantics.IsTotalAtlasMap owner.toSemantics) :
    (ofSemantics owner total).underlying = owner := rfl

theorem ofSemantics_roundTrip (value : TotalAtlasMap X) :
    ofSemantics value.underlying value.isTotalAtlasMap = value := by
  cases value with
  | mk owner singleton =>
    apply congrArg (TotalAtlasMap.mk owner)
    funext region final
    apply SingletonDominion.ext
    exact (singleton region final).unique _

end TotalAtlasMap

namespace AtlasAllocation

/-- The runtime predicate checks the retained Atlas's scalar trace lookup
and the final genuine page, before interpreting a raw occurrence. -/
-- ALIGN: ATLAS-MAP-FINAL-REGION.
def finalRegionValid {Owner : Type} (allocation : AtlasAllocation Owner)
    (region : PageElement allocation.atlasDescription.pagination.pages) : Bool :=
  allocation.atlasDescription.pagination.pages.traceValid region &&
    decide (region.page = allocation.atlasDescription.pagination.pages.depth - 1)

theorem finalRegionValid_validElement {Owner : Type} (allocation : AtlasAllocation Owner)
    (valueMap : AtlasMap allocation.toAtlas) (region : allocation.toAtlas.Element) :
    allocation.finalRegionValid region.val = valueMap.regionValid region := by
  have trace := region.traceValid allocation.atlasDescription.ownership.valid
  simp only [finalRegionValid, trace, Bool.true_and, AtlasMap.regionValid]
  rfl

abbrev RegionSingletons {Owner : Type} (allocation : AtlasAllocation Owner) :=
  (region : PageElement allocation.atlasDescription.pagination.pages) →
    allocation.finalRegionValid region = true → SingletonDominion (allocation.AcceptedDatum region)

end AtlasAllocation

/-- The stored Haskell certificate quantifies over raw page elements satisfying
the runtime region predicate and returns a singleton of the accepted raw data.
The allocation parameter retains the exact owner and membership presentation. -/
structure TotalAtlasMapData {Owner : Type} (allocation : AtlasAllocation Owner) where
  owner : AtlasMap allocation.toAtlas
  singleton : allocation.RegionSingletons

namespace TotalAtlasMapData
variable {Owner : Type} {allocation : AtlasAllocation Owner}

-- ALIGN: TOTAL-ATLAS-MAP-CONSTRUCTION.
def package (owner : AtlasMap allocation.toAtlas)
    (singleton : allocation.RegionSingletons) : TotalAtlasMapData allocation :=
  ⟨owner, singleton⟩

-- ALIGN: TOTAL-ATLAS-MAP-ELIMINATION.
def withTotalAtlasMap {Result : Sort*} (value : TotalAtlasMapData allocation)
    (useMap : AtlasMap allocation.toAtlas → allocation.RegionSingletons → Result) : Result :=
  useMap value.owner value.singleton

theorem withTotalAtlasMap_package {Result : Sort*} (owner : AtlasMap allocation.toAtlas)
    (singleton : allocation.RegionSingletons)
    (useMap : AtlasMap allocation.toAtlas → allocation.RegionSingletons → Result) :
    withTotalAtlasMap (package owner singleton) useMap = useMap owner singleton := rfl

/-- Interpret the stored raw certificate through the accepted-carrier
equivalence. The selected datum and the owning Atlas map are retained. -/
def toTotalAtlasMap (value : TotalAtlasMapData allocation) : TotalAtlasMap allocation.toAtlas where
  underlying := value.owner
  regionSingleton region final :=
    (value.singleton region.val
      ((allocation.finalRegionValid_validElement value.owner region).trans final)).reindex
      (allocation.acceptedCarrierEquiv region).symm

@[simp] theorem toTotalAtlasMap_owner (value : TotalAtlasMapData allocation) :
    value.toTotalAtlasMap.underlying = value.owner := rfl

theorem selectedDatum_preserved (value : TotalAtlasMapData allocation)
    (region : allocation.toAtlas.Element) (final : value.owner.regionValid region = true) :
    (value.toTotalAtlasMap.regionSingleton region final).value.val =
      (value.singleton region.val
        ((allocation.finalRegionValid_validElement value.owner region).trans final)).value.val := rfl

theorem singleton_roundTrip (value : TotalAtlasMapData allocation)
    (region : allocation.toAtlas.Element) (final : value.owner.regionValid region = true) :
    (value.toTotalAtlasMap.regionSingleton region final).reindex
        (allocation.acceptedCarrierEquiv region) =
      value.singleton region.val
        ((allocation.finalRegionValid_validElement value.owner region).trans final) :=
  SingletonDominion.ext ((allocation.acceptedCarrierEquiv region).apply_symm_apply _)

-- ALIGN: TOTAL-ATLAS-MAP-RAW-INTERPRETATION.
theorem isTotalAtlasMap (value : TotalAtlasMapData allocation) :
    Datra.Semantics.IsTotalAtlasMap value.owner.toSemantics :=
  value.toTotalAtlasMap.isTotalAtlasMap

noncomputable def toSemantics (value : TotalAtlasMapData allocation) : Datra.Semantics.TotalAtlasMap :=
  value.toTotalAtlasMap.toSemantics

end TotalAtlasMapData

end Datra.Executable
