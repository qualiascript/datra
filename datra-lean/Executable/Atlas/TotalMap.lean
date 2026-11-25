import Executable.Atlas.Map

namespace Datra.Executable

/-- The runtime certificate names an inhabitant and proves equality for every
value of its carrier. A restricted region requires this carrier to be the
accepted subtype, rather than merely the ambient Haskell datum type. -/
structure SingletonDominion (Carrier : Type*) where
  value : Carrier
  unique : ∀ candidate, candidate = value

namespace SingletonDominion

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

/-- Uniqueness of the ambient type alone does not establish nonemptiness of
the accepted region. Its selected value must also satisfy membership. -/
def restrict {Carrier : Type*} (certificate : SingletonDominion Carrier)
    (accepts : Carrier → Prop) (accepted : accepts certificate.value) :
    SingletonDominion {datum : Carrier // accepts datum} :=
  ⟨⟨certificate.value, accepted⟩, fun candidate =>
    Subtype.ext (certificate.unique candidate.val)⟩

end SingletonDominion

-- ALIGN: ATLAS-MAP-FINAL-REGION.
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

-- ALIGN: TOTAL-ATLAS-MAP-CONSTRUCTION.
def totalAtlasMap (valueMap : AtlasMap X)
    (proveSingleton : (region : X.Element) → valueMap.regionValid region = true →
      SingletonDominion (X.cellData region.val.cell)) : TotalAtlasMap X :=
  ⟨valueMap, proveSingleton⟩

@[simp] theorem totalAtlasMap_underlying (valueMap : AtlasMap X)
    (proveSingleton : (region : X.Element) → valueMap.regionValid region = true →
      SingletonDominion (X.cellData region.val.cell)) :
    (totalAtlasMap valueMap proveSingleton).underlying = valueMap := rfl

-- ALIGN: TOTAL-ATLAS-MAP-ELIMINATION.
def withTotalAtlasMap {Result : Sort*} (value : TotalAtlasMap X)
    (useMap : (owner : AtlasMap X) →
      ((region : X.Element) → owner.regionValid region = true →
        SingletonDominion (X.cellData region.val.cell)) → Result) : Result :=
  useMap value.underlying value.regionSingleton

theorem withTotalAtlasMap_construct {Result : Sort*} (valueMap : AtlasMap X)
    (proveSingleton : (region : X.Element) → valueMap.regionValid region = true →
      SingletonDominion (X.cellData region.val.cell))
    (useMap : (owner : AtlasMap X) →
      ((region : X.Element) → owner.regionValid region = true →
        SingletonDominion (X.cellData region.val.cell)) → Result) :
    withTotalAtlasMap (totalAtlasMap valueMap proveSingleton) useMap =
      useMap valueMap proveSingleton := rfl

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

end TotalAtlasMap

end Datra.Executable
