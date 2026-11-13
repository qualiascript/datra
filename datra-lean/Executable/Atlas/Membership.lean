import Executable.Atlas.Data
import Executable.PageElementLookup

namespace Datra.Executable

universe u

/-- The first-order package used to retain the identity of a rank-2 runtime
membership predicate. The unrestricted constructor describes an ambient type
whose values are already all legitimate data. -/
inductive AtlasMembership {Scope : Type u} (owner : Scope)
    (cellData : PageElementCell → Type) where
  | all
  | predicate (accepts : (occurrence : PageElement owner) → cellData occurrence.cell → Bool)

-- ALIGN: ATLAS-MEMBERSHIP-PREDICATE.
def AtlasMembership.accepts {Scope : Type u} {owner : Scope}
    {cellData : PageElementCell → Type} (membership : AtlasMembership owner cellData)
    (occurrence : PageElement owner) (datum : cellData occurrence.cell) : Bool :=
  match membership with
  | .all => true
  | .predicate accepts => accepts occurrence datum

theorem AtlasMembership.accepts_cast {Scope : Type u} {owner : Scope}
    {cellData : PageElementCell → Type} (membership : AtlasMembership owner cellData)
    {source target : PageElement owner} (same : source = target) (datum : cellData target.cell) :
    membership.accepts source (cast (congrArg cellData (congrArg PageElement.cell same).symm) datum) =
      membership.accepts target datum := by cases same; rfl

abbrev AtlasMembership.Carrier {Scope : Type u} {owner : Scope}
    {cellData : PageElementCell → Type} (membership : AtlasMembership owner cellData)
    (occurrence : PageElement owner) :=
  {datum : cellData occurrence.cell // membership.accepts occurrence datum = true}

/-- The runtime action before interpreting its accepted carriers as the
indexed data family of an Atlas. Lookup and transport require the stored
folio domain; both insertion directions retain cell membership. -/
structure AtlasMembershipAction {Scope : Type u} (owner : Scope)
    (cellData : PageElementCell → Type) where
  domain : PageElementDomain owner
  membership : AtlasMembership owner cellData
  dataAt : (occurrence : PageElement owner) → domain.contains occurrence = true → Dominion (membership.Carrier occurrence)
  mapData : {source target : PageElement owner} →
    domain.contains source = true → domain.contains target = true → source.Arrow target →
    DomanialInsertion (membership.Carrier source) (membership.Carrier target)

-- ALIGN: ATLAS-MEMBERSHIP-ACTION.
def AtlasMembershipAction.package {Scope : Type u} {owner : Scope}
    {cellData : PageElementCell → Type} (domain : PageElementDomain owner)
    (membership : AtlasMembership owner cellData)
    (dataAt : (occurrence : PageElement owner) → domain.contains occurrence = true → Dominion (membership.Carrier occurrence))
    (mapData : {source target : PageElement owner} →
      domain.contains source = true → domain.contains target = true → source.Arrow target →
      DomanialInsertion (membership.Carrier source) (membership.Carrier target)) :
    AtlasMembershipAction owner cellData := ⟨domain, membership, dataAt, mapData⟩

-- ALIGN: ATLAS-DATUM-MEMBERSHIP.
def AtlasMembershipAction.acceptsAt {Scope : Type u} {owner : Scope}
    {cellData : PageElementCell → Type} (action : AtlasMembershipAction owner cellData)
    (finalPage : Nat) (traceLimit : Int) (occurrence : PageElement owner)
    (datum : cellData occurrence.cell) : Bool :=
  action.membership.accepts (occurrence.normalize finalPage traceLimit) datum

-- ALIGN: ATLAS-DATUM-MEMBERSHIP-NORMALIZATION.
theorem AtlasMembershipAction.acceptsAt_normalize {Scope : Type u} {owner : Scope}
    {cellData : PageElementCell → Type} (action : AtlasMembershipAction owner cellData)
    (finalPage : Nat) (traceLimit : Int) (occurrence : PageElement owner)
    (datum : cellData occurrence.cell) :
    action.acceptsAt finalPage traceLimit (occurrence.normalize finalPage traceLimit) datum =
      action.acceptsAt finalPage traceLimit occurrence datum := by
  unfold acceptsAt
  cases occurrence
  dsimp only [PageElement.normalize]
  rw [min_assoc, min_self, Trace.trimTraceIdempotent]

theorem AtlasMembershipAction.map_accepted {Scope : Type u} {owner : Scope}
    {cellData : PageElementCell → Type} (action : AtlasMembershipAction owner cellData)
    {source target : PageElement owner}
    (sourceValid : action.domain.contains source = true)
    (targetValid : action.domain.contains target = true) (arrow : source.Arrow target)
    (datum : action.membership.Carrier source) :
    action.membership.accepts target ((action.mapData sourceValid targetValid arrow).map datum).val = true :=
  ((action.mapData sourceValid targetValid arrow).map datum).property

theorem AtlasMembershipAction.preimage_accepted {Scope : Type u} {owner : Scope}
    {cellData : PageElementCell → Type} (action : AtlasMembershipAction owner cellData)
    {source target : PageElement owner}
    (sourceValid : action.domain.contains source = true)
    (targetValid : action.domain.contains target = true) (arrow : source.Arrow target)
    (datum : action.membership.Carrier target) (candidate : action.membership.Carrier source)
    (_found : (action.mapData sourceValid targetValid arrow).preimage datum = some candidate) :
    action.membership.accepts source candidate.val = true := candidate.property

-- ALIGN: ATLAS-DATA-COHERENCE-INSERTION.
def AtlasMembershipAction.coherenceInsertion {Scope : Type u} {owner : Scope}
    {cellData : PageElementCell → Type} (action : AtlasMembershipAction owner cellData)
    (finalPage : Nat) (traceLimit : Int) (occurrence : PageElement owner) :
    DomanialInsertion (action.membership.Carrier (occurrence.normalize finalPage traceLimit))
      (action.membership.Carrier (occurrence.normalize finalPage traceLimit)) :=
  DomanialInsertion.identity _

/-- The identity implementation agrees with the stored normalized arrow
action whenever that action satisfies the Atlas coherence obligation. -/
-- ALIGN: ATLAS-DATA-COHERENCE-AGREEMENT.
theorem AtlasMembershipAction.coherenceInsertion_agrees {Scope : Type u} {owner : Scope}
    {cellData : PageElementCell → Type} (action : AtlasMembershipAction owner cellData)
    (finalPage : Nat) (traceLimit : Int) (occurrence : PageElement owner)
    (datum : action.membership.Carrier (occurrence.normalize finalPage traceLimit))
    (sourceValid : action.domain.contains (occurrence.normalize finalPage traceLimit) = true)
    (targetValid : action.domain.contains
      ((occurrence.normalize finalPage traceLimit).normalize finalPage traceLimit) = true)
    (coherent : ((action.mapData sourceValid targetValid (PageElement.normalizeArrow finalPage traceLimit
      (occurrence.toNormalized finalPage traceLimit))).map datum).val = datum.val) :
    ((action.coherenceInsertion finalPage traceLimit occurrence).map datum).val =
      ((action.mapData sourceValid targetValid (PageElement.normalizeArrow finalPage traceLimit
        (occurrence.toNormalized finalPage traceLimit))).map datum).val :=
  coherent.symm

end Datra.Executable

namespace Datra.Executable.AtlasMembershipAction
open CategoryTheory

variable {origin final : Page} {pages : FolioData origin final}
  {cellData : PageElementCell → Type}

/-- The stored action domain is exactly the owning pagination's checked folio. -/
class FolioOwner (action : AtlasMembershipAction pages cellData) : Prop where
  valid : pages.Valid
  domain_eq : action.domain = PageElementDomain.ofFolio pages ⟨pages, valid⟩

/-- Packaging an action for the actual folio supplies the ownership certificate
without an additional law about the action's callbacks. -/
theorem package_folioOwner (valid : pages.Valid)
    (membership : AtlasMembership pages cellData)
    (dataAt : (occurrence : PageElement pages) → pages.traceValid occurrence = true →
      Dominion (membership.Carrier occurrence))
    (mapData : {source target : PageElement pages} →
      pages.traceValid source = true → pages.traceValid target = true → source.Arrow target →
      DomanialInsertion (membership.Carrier source) (membership.Carrier target)) :
    FolioOwner (package (PageElementDomain.ofFolio pages ⟨pages, valid⟩) membership dataAt mapData) :=
  ⟨valid, rfl⟩

theorem validElement (action : AtlasMembershipAction pages cellData) [owner : FolioOwner action]
    (occurrence : pages.ValidElement) : action.domain.contains occurrence.val = true := by
  rw [owner.domain_eq]
  exact occurrence.traceValid owner.valid

def dataAtValid (action : AtlasMembershipAction pages cellData) [FolioOwner action]
    (occurrence : pages.ValidElement) : Dominion (action.membership.Carrier occurrence.val) :=
  action.dataAt occurrence.val (action.validElement occurrence)

def mapValid (action : AtlasMembershipAction pages cellData) [FolioOwner action]
    {source target : pages.ValidElement} (arrow : source ⟶ target) :
    DomanialInsertion (action.membership.Carrier source.val) (action.membership.Carrier target.val) :=
  action.mapData (action.validElement source) (action.validElement target) arrow

theorem normalize_valid (action : AtlasMembershipAction pages cellData) [owner : FolioOwner action]
    (occurrence : PageElement pages) (valid : action.domain.contains occurrence = true) :
    action.domain.contains (occurrence.normalize (pages.depth - 1) pages.depth) = true := by
  rw [owner.domain_eq] at valid ⊢
  exact pages.traceValid_normalize owner.valid occurrence valid

/-- The accepted data family used by the indexed Atlas model. -/
abbrev IndexedCarrier (accepts : (cell : PageElementCell) → cellData cell → Prop)
    (cell : PageElementCell) := {datum : cellData cell // accepts cell datum}

/-- Agreement between an occurrence predicate and an indexed carrier. Raw
predicates need not have this property; normalization supplies it for the
canonical accepted family below. -/
def CellCompatible (action : AtlasMembershipAction pages cellData)
    (accepts : (cell : PageElementCell) → cellData cell → Prop) : Prop :=
  ∀ (occurrence : pages.ValidElement) (datum : cellData occurrence.val.cell),
    action.membership.accepts occurrence.val datum = true ↔ accepts occurrence.val.cell datum

def carrierEquiv (action : AtlasMembershipAction pages cellData)
    (accepts : (cell : PageElementCell) → cellData cell → Prop)
    (compatible : action.CellCompatible accepts) (occurrence : pages.ValidElement) :
    action.membership.Carrier occurrence.val ≃ IndexedCarrier accepts occurrence.val.cell where
  toFun datum := ⟨datum.val, (compatible occurrence datum.val).mp datum.property⟩
  invFun datum := ⟨datum.val, (compatible occurrence datum.val).mpr datum.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Interpret the retained predicate as the actual carrier type. No data are
added or removed: the equivalences only change their membership proofs. -/
def toIndexed (action : AtlasMembershipAction pages cellData) [FolioOwner action]
    (accepts : (cell : PageElementCell) → cellData cell → Prop)
    (compatible : action.CellCompatible accepts) : AtlasAction pages (IndexedCarrier accepts) where
  dataAt occurrence := (action.dataAtValid occurrence).reindex
    (action.carrierEquiv accepts compatible occurrence)
  mapData {source target} arrow := (action.mapValid arrow).reindex
    (action.carrierEquiv accepts compatible source) (action.carrierEquiv accepts compatible target)

theorem toIndexed_rank (action : AtlasMembershipAction pages cellData) [FolioOwner action]
    (accepts : (cell : PageElementCell) → cellData cell → Prop)
    (compatible : action.CellCompatible accepts) (occurrence : pages.ValidElement)
    (datum : action.membership.Carrier occurrence.val) :
    ((action.toIndexed accepts compatible).dataAt occurrence).rank
        (action.carrierEquiv accepts compatible occurrence datum) =
      (action.dataAtValid occurrence).rank datum := by
  exact Dominion.reindex_rank _ _ _

theorem toIndexed_unrank (action : AtlasMembershipAction pages cellData) [FolioOwner action]
    (accepts : (cell : PageElementCell) → cellData cell → Prop)
    (compatible : action.CellCompatible accepts) (occurrence : pages.ValidElement) (n : Nat) :
    (((action.toIndexed accepts compatible).dataAt occurrence).unrank n).map Subtype.val =
      ((action.dataAtValid occurrence).unrank n).map Subtype.val := by
  simp [toIndexed, Dominion.reindex, Option.map_map, carrierEquiv]

theorem toIndexed_map (action : AtlasMembershipAction pages cellData) [FolioOwner action]
    (accepts : (cell : PageElementCell) → cellData cell → Prop)
    (compatible : action.CellCompatible accepts) {source target : pages.ValidElement}
    (arrow : source ⟶ target) (datum : IndexedCarrier accepts source.val.cell) :
    (((action.toIndexed accepts compatible).mapData arrow).map datum).val =
      ((action.mapValid arrow).map
        ((action.carrierEquiv accepts compatible source).symm datum)).val := rfl

theorem toIndexed_preimage (action : AtlasMembershipAction pages cellData) [FolioOwner action]
    (accepts : (cell : PageElementCell) → cellData cell → Prop)
    (compatible : action.CellCompatible accepts) {source target : pages.ValidElement}
    (arrow : source ⟶ target) (datum : IndexedCarrier accepts target.val.cell) :
    (((action.toIndexed accepts compatible).mapData arrow).preimage datum).map Subtype.val =
      ((action.mapValid arrow).preimage
        ((action.carrierEquiv accepts compatible target).symm datum)).map Subtype.val := by
  simp [toIndexed, DomanialInsertion.reindex, Option.map_map, carrierEquiv]

/-- Apply the stored raw action with precisely the owning folio's bounds. -/
def normalizedMap (action : AtlasMembershipAction pages cellData) [FolioOwner action]
    {source target : pages.ValidElement} (arrow : source ⟶ target) :
    DomanialInsertion (action.membership.Carrier source.normalize.val)
      (action.membership.Carrier target.normalize.val) :=
  action.mapValid (FolioData.ValidElement.normalizeArrow arrow)

theorem toIndexed_normalizedMap (action : AtlasMembershipAction pages cellData) [FolioOwner action]
    (accepts : (cell : PageElementCell) → cellData cell → Prop)
    (compatible : action.CellCompatible accepts) {source target : pages.ValidElement}
    (arrow : source ⟶ target) (datum : IndexedCarrier accepts source.val.cell) :
    (((action.toIndexed accepts compatible).normalizedMap arrow).map datum).val =
      ((action.normalizedMap arrow).map
        ((action.carrierEquiv accepts compatible source.normalize).symm datum)).val := rfl

theorem toIndexed_normalizedRank (action : AtlasMembershipAction pages cellData) [FolioOwner action]
    (accepts : (cell : PageElementCell) → cellData cell → Prop)
    (compatible : action.CellCompatible accepts) (occurrence : pages.ValidElement)
    (datum : IndexedCarrier accepts occurrence.val.cell) :
    ((action.toIndexed accepts compatible).dataAt occurrence.normalize).rank datum =
      (action.dataAtValid occurrence.normalize).rank
        ((action.carrierEquiv accepts compatible occurrence.normalize).symm datum) := rfl

theorem toIndexed_normalizedUnrank (action : AtlasMembershipAction pages cellData) [FolioOwner action]
    (accepts : (cell : PageElementCell) → cellData cell → Prop)
    (compatible : action.CellCompatible accepts) (occurrence : pages.ValidElement) (n : Nat) :
    (((action.toIndexed accepts compatible).dataAt occurrence.normalize).unrank n).map Subtype.val =
      ((action.dataAtValid occurrence.normalize).unrank n).map Subtype.val :=
  action.toIndexed_unrank accepts compatible occurrence.normalize n

theorem toIndexed_normalizedPreimage (action : AtlasMembershipAction pages cellData) [FolioOwner action]
    (accepts : (cell : PageElementCell) → cellData cell → Prop)
    (compatible : action.CellCompatible accepts) {source target : pages.ValidElement}
    (arrow : source ⟶ target) (datum : IndexedCarrier accepts target.val.cell) :
    (((action.toIndexed accepts compatible).normalizedMap arrow).preimage datum).map Subtype.val =
      ((action.normalizedMap arrow).preimage
        ((action.carrierEquiv accepts compatible target.normalize).symm datum)).map Subtype.val :=
  action.toIndexed_preimage accepts compatible (FolioData.ValidElement.normalizeArrow arrow) datum

/-- The runtime AtlasData obligations, stated on accepted data and comparing
the underlying values as LiquidHaskell does. Only valid folio occurrences
are needed by the interpretation. -/
structure Laws (action : AtlasMembershipAction pages cellData) [FolioOwner action] : Prop where
  identity : ∀ (source : pages.ValidElement)
    (datum : action.membership.Carrier source.normalize.val),
    ((action.normalizedMap (𝟙 source)).map datum).val = datum.val
  composition : ∀ {source middle target : pages.ValidElement}
    (first : source ⟶ middle) (second : middle ⟶ target)
    (datum : action.membership.Carrier source.normalize.val),
    ((action.normalizedMap (first ≫ second)).map datum).val =
      ((action.normalizedMap second).map ((action.normalizedMap first).map datum)).val
  coherence : ∀ (source : pages.ValidElement)
    (datum : action.membership.Carrier source.normalize.val),
    ((action.normalizedMap source.toNormalized).map datum).val = datum.val
  disjoint : ∀ {left right root : pages.ValidElement},
    left.val.page = right.val.page → left.val.position ≠ right.val.position →
    left.val.page ≤ pages.depth - 1 → root.val.page = 0 →
    (leftToOrigin : left ⟶ root) → (rightToOrigin : right ⟶ root) →
    (leftDatum : action.membership.Carrier left.normalize.val) →
    (rightDatum : action.membership.Carrier right.normalize.val) →
    ((action.normalizedMap leftToOrigin).map leftDatum).val ≠
      ((action.normalizedMap rightToOrigin).map rightDatum).val

/-- Transport the four checked runtime laws to the indexed Atlas. This uses
only equality of the erased values, since membership proofs are irrelevant. -/
-- ALIGN: ATLAS-MEMBERSHIP-LAWS-INTERPRETATION.
def toIndexedData (action : AtlasMembershipAction pages cellData) [FolioOwner action]
    (accepts : (cell : PageElementCell) → cellData cell → Prop)
    (compatible : action.CellCompatible accepts) (laws : action.Laws) :
    AtlasData pages (IndexedCarrier accepts) where
  action := action.toIndexed accepts compatible
  identity source datum := by
    apply Subtype.ext
    exact laws.identity source ((action.carrierEquiv accepts compatible source.normalize).symm datum)
  composition first second datum := by
    apply Subtype.ext
    exact laws.composition first second
      ((action.carrierEquiv accepts compatible _).symm datum)
  coherence source datum := by
    apply Subtype.ext
    exact laws.coherence source ((action.carrierEquiv accepts compatible source.normalize).symm datum)
  disjoint samePage distinct bounded atOrigin leftArrow rightArrow leftDatum rightDatum := by
    intro same
    have erased := congrArg Subtype.val same
    exact laws.disjoint samePage distinct bounded atOrigin leftArrow rightArrow
      ((action.carrierEquiv accepts compatible _).symm leftDatum)
      ((action.carrierEquiv accepts compatible _).symm rightDatum)
      erased

/-- The accepted-carrier bridge reuses the established finite-spine
interpretation, including the written pagewise-disjointness definition. -/
noncomputable def toSemantics (action : AtlasMembershipAction pages cellData) [FolioOwner action]
    (accepts : (cell : PageElementCell) → cellData cell → Prop)
    (compatible : action.CellCompatible accepts) (laws : action.Laws) : Datra.Semantics.Atl :=
  (action.toIndexedData accepts compatible laws).toSemantics

def toAtlas (pagination : Pagination) (action : AtlasMembershipAction pagination.pages cellData) [FolioOwner action]
    (accepts : (cell : PageElementCell) → cellData cell → Prop)
    (compatible : action.CellCompatible accepts) (laws : action.Laws) : Atlas where
  pagination := pagination
  cellData := IndexedCarrier accepts
  data := action.toIndexedData accepts compatible laws

theorem toAtlas_semantics (pagination : Pagination)
    (action : AtlasMembershipAction pagination.pages cellData) [FolioOwner action]
    (accepts : (cell : PageElementCell) → cellData cell → Prop)
    (compatible : action.CellCompatible accepts) (laws : action.Laws) :
    (toAtlas pagination action accepts compatible laws).toSemantics =
      action.toSemantics accepts compatible laws := rfl

/-- The public action always uses normalized occurrences and arrows. Recording
that wrapper as an action lets its accepted family depend only on genuine
cells, even if a supplied raw predicate varies on padding occurrences. -/
def normalize (action : AtlasMembershipAction pages cellData) [FolioOwner action] : AtlasMembershipAction pages cellData where
  domain := action.domain
  membership := .predicate (action.acceptsAt (pages.depth - 1) pages.depth)
  dataAt occurrence valid := action.dataAt (occurrence.normalize (pages.depth - 1) pages.depth)
    (action.normalize_valid occurrence valid)
  mapData {source target} sourceValid targetValid arrow := action.mapData
    (action.normalize_valid source sourceValid) (action.normalize_valid target targetValid)
    (PageElement.normalizeArrow (pages.depth - 1) pages.depth arrow)

instance (action : AtlasMembershipAction pages cellData) [owner : FolioOwner action] :
    FolioOwner action.normalize where
  valid := owner.valid
  domain_eq := owner.domain_eq

/-- The canonical genuine-cell carrier is defined without a choice of
representative or a decision procedure over arbitrary raw cell tags. -/
def AcceptedCell (action : AtlasMembershipAction pages cellData) (cell : PageElementCell)
    (datum : cellData cell) : Prop :=
  ∃ occurrence : pages.ValidElement, ∃ same : occurrence.val.cell = cell,
    action.acceptsAt (pages.depth - 1) pages.depth occurrence.val
      (cast (congrArg cellData same.symm) datum) = true

theorem acceptsAt_cell_eq (action : AtlasMembershipAction pages cellData)
    {source target : pages.ValidElement} (same : source.val.cell = target.val.cell)
    (datum : cellData target.val.cell) :
    action.acceptsAt (pages.depth - 1) pages.depth source.val
        (cast (congrArg cellData same.symm) datum) =
      action.acceptsAt (pages.depth - 1) pages.depth target.val datum :=
  action.membership.accepts_cast
    (congrArg Subtype.val ((FolioData.ValidElement.cell_eq_iff_normalize_eq source target).mp same)) datum

theorem normalized_compatible (action : AtlasMembershipAction pages cellData) [FolioOwner action] :
    action.normalize.CellCompatible action.AcceptedCell := by
  intro occurrence datum
  constructor
  · intro accepted
    exact ⟨occurrence, rfl, accepted⟩
  · rintro ⟨other, same, accepted⟩
    exact (action.acceptsAt_cell_eq same datum).symm.trans accepted

theorem Laws.normalized {action : AtlasMembershipAction pages cellData} [FolioOwner action] (laws : action.Laws) :
    action.normalize.Laws where
  identity source datum := laws.identity source.normalize datum
  composition first second datum := laws.composition
    (FolioData.ValidElement.normalizeArrow first) (FolioData.ValidElement.normalizeArrow second) datum
  coherence source datum := laws.coherence source.normalize datum
  disjoint {left right root} samePage distinct _bounded atOrigin leftArrow rightArrow leftDatum rightDatum := by
    exact laws.disjoint (left := left.normalize) (right := right.normalize) (root := root.normalize)
      (congrArg (fun page => min page (pages.depth - 1)) samePage) distinct (min_le_right _ _)
      (show min _ (pages.depth - 1) = 0 by simp [atOrigin])
      (FolioData.ValidElement.normalizeArrow leftArrow)
      (FolioData.ValidElement.normalizeArrow rightArrow) leftDatum rightDatum

/-- Every law-bearing runtime membership action has a canonical indexed Atlas
interpretation. Cell compatibility follows from normalization and folio
validity; it is not a further assumption on the user's membership predicate. -/
-- ALIGN: ATLAS-MEMBERSHIP-ATLAS-INTERPRETATION.
def toCanonicalAtlas (pagination : Pagination)
    (action : AtlasMembershipAction pagination.pages cellData) [FolioOwner action] (laws : action.Laws) : Atlas :=
  toAtlas pagination action.normalize action.AcceptedCell action.normalized_compatible laws.normalized

def canonicalCarrierEquiv (action : AtlasMembershipAction pages cellData) [FolioOwner action]
    (occurrence : pages.ValidElement) :
    IndexedCarrier action.AcceptedCell occurrence.val.cell ≃
      action.membership.Carrier occurrence.normalize.val :=
  (action.normalize.carrierEquiv action.AcceptedCell action.normalized_compatible occurrence).symm

theorem rank_congr (action : AtlasMembershipAction pages cellData)
    {source target : PageElement pages} (same : source = target)
    {sourceValid : action.domain.contains source = true}
    {targetValid : action.domain.contains target = true}
    (a : action.membership.Carrier source) (b : action.membership.Carrier target)
    (values : HEq a.val b.val) : (action.dataAt source sourceValid).rank a = (action.dataAt target targetValid).rank b := by
  cases same
  have sameDatum : a = b := Subtype.ext (eq_of_heq values)
  cases sameDatum
  rfl

theorem unrank_congr (action : AtlasMembershipAction pages cellData)
    {source target : PageElement pages} (same : source = target)
    {sourceValid : action.domain.contains source = true}
    {targetValid : action.domain.contains target = true} (n : Nat) :
    HEq (((action.dataAt source sourceValid).unrank n).map Subtype.val)
      (((action.dataAt target targetValid).unrank n).map Subtype.val) := by cases same; rfl

theorem map_congr (action : AtlasMembershipAction pages cellData)
    {source target source' target' : PageElement pages}
    (sameSource : source = source') (sameTarget : target = target')
    {sourceValid : action.domain.contains source = true}
    {targetValid : action.domain.contains target = true}
    {sourceValid' : action.domain.contains source' = true}
    {targetValid' : action.domain.contains target' = true}
    (arrow : source.Arrow target) (arrow' : source'.Arrow target')
    (a : action.membership.Carrier source) (b : action.membership.Carrier source')
    (values : HEq a.val b.val) :
    HEq ((action.mapData sourceValid targetValid arrow).map a).val ((action.mapData sourceValid' targetValid' arrow').map b).val := by
  cases sameSource
  cases sameTarget
  have sameDatum : a = b := Subtype.ext (eq_of_heq values)
  have sameArrow : arrow = arrow' := Subsingleton.elim _ _
  cases sameDatum
  cases sameArrow
  rfl

theorem preimage_congr (action : AtlasMembershipAction pages cellData)
    {source target source' target' : PageElement pages}
    (sameSource : source = source') (sameTarget : target = target')
    {sourceValid : action.domain.contains source = true}
    {targetValid : action.domain.contains target = true}
    {sourceValid' : action.domain.contains source' = true}
    {targetValid' : action.domain.contains target' = true}
    (arrow : source.Arrow target) (arrow' : source'.Arrow target')
    (a : action.membership.Carrier target) (b : action.membership.Carrier target')
    (values : HEq a.val b.val) :
    HEq (((action.mapData sourceValid targetValid arrow).preimage a).map Subtype.val)
      (((action.mapData sourceValid' targetValid' arrow').preimage b).map Subtype.val) := by
  cases sameSource
  cases sameTarget
  have sameDatum : a = b := Subtype.ext (eq_of_heq values)
  have sameArrow : arrow = arrow' := Subsingleton.elim _ _
  cases sameDatum
  cases sameArrow
  rfl

-- ALIGN: ATLAS-MEMBERSHIP-RANK-INTERPRETATION.
theorem canonical_rank (pagination : Pagination)
    (action : AtlasMembershipAction pagination.pages cellData) [FolioOwner action] (laws : action.Laws)
    (occurrence : pagination.Element) (datum : IndexedCarrier action.AcceptedCell occurrence.val.cell) :
    ((toCanonicalAtlas pagination action laws).dataAt occurrence).rank datum =
      (action.dataAtValid occurrence.normalize).rank (action.canonicalCarrierEquiv occurrence datum) := by
  apply action.rank_congr (congrArg Subtype.val occurrence.normalize_idempotent)
  rfl

-- ALIGN: ATLAS-MEMBERSHIP-UNRANK-INTERPRETATION.
theorem canonical_unrank (pagination : Pagination)
    (action : AtlasMembershipAction pagination.pages cellData) [FolioOwner action] (laws : action.Laws)
    (occurrence : pagination.Element) (n : Nat) :
    (((toCanonicalAtlas pagination action laws).dataAt occurrence).unrank n).map Subtype.val =
      ((action.dataAtValid occurrence.normalize).unrank n).map Subtype.val := by
  have preserved := action.normalize.toIndexed_normalizedUnrank
    action.AcceptedCell action.normalized_compatible occurrence n
  change (((action.normalize.toIndexed action.AcceptedCell action.normalized_compatible).dataAt
    occurrence.normalize).unrank n).map Subtype.val = _
  rw [preserved]
  exact eq_of_heq (action.unrank_congr (congrArg Subtype.val occurrence.normalize_idempotent) n)

-- ALIGN: ATLAS-MEMBERSHIP-MAP-INTERPRETATION.
theorem canonical_map (pagination : Pagination)
    (action : AtlasMembershipAction pagination.pages cellData) [FolioOwner action] (laws : action.Laws)
    {source target : pagination.Element} (arrow : source ⟶ target)
    (datum : IndexedCarrier action.AcceptedCell source.val.cell) :
    (((toCanonicalAtlas pagination action laws).data.action.normalizedMap arrow).map datum).val =
      ((action.normalizedMap arrow).map (action.canonicalCarrierEquiv source datum)).val := by
  apply eq_of_heq
  apply action.map_congr (congrArg Subtype.val source.normalize_idempotent)
    (congrArg Subtype.val target.normalize_idempotent)
  rfl

-- ALIGN: ATLAS-MEMBERSHIP-PREIMAGE-INTERPRETATION.
theorem canonical_preimage (pagination : Pagination)
    (action : AtlasMembershipAction pagination.pages cellData) [FolioOwner action] (laws : action.Laws)
    {source target : pagination.Element} (arrow : source ⟶ target)
    (datum : IndexedCarrier action.AcceptedCell target.val.cell) :
    (((toCanonicalAtlas pagination action laws).data.action.normalizedMap arrow).preimage datum).map Subtype.val =
      ((action.normalizedMap arrow).preimage (action.canonicalCarrierEquiv target datum)).map Subtype.val := by
  have preserved := action.normalize.toIndexed_normalizedPreimage
    action.AcceptedCell action.normalized_compatible arrow datum
  change (((action.normalize.toIndexed action.AcceptedCell action.normalized_compatible).normalizedMap
    arrow).preimage datum).map Subtype.val = _
  rw [preserved]
  apply eq_of_heq
  apply action.preimage_congr (congrArg Subtype.val source.normalize_idempotent)
    (congrArg Subtype.val target.normalize_idempotent)
  rfl

/-- The public runtime data action, with the accepted subtype retained at
each normalized occurrence. -/
def acceptedFunctor (action : AtlasMembershipAction pages cellData) [FolioOwner action] (laws : action.Laws) :
    pages.ValidElement ⥤ Datra.Semantics.DomIns where
  obj occurrence := ⟨(action.dataAtValid occurrence.normalize).toSemantics⟩
  map arrow := (action.normalizedMap arrow).toSemantics
  map_id occurrence := by
    apply Function.Embedding.ext
    intro datum
    exact Subtype.ext (laws.identity occurrence datum)
  map_comp first second := by
    apply Function.Embedding.ext
    intro datum
    exact Subtype.ext (laws.composition first second datum)

/-- The canonical indexed model and the runtime accepted-carrier functor
are naturally isomorphic through maps that retain the underlying data. -/
-- ALIGN: ATLAS-MEMBERSHIP-FUNCTOR-ISOMORPHISM.
def canonicalFunctorIso (pagination : Pagination)
    (action : AtlasMembershipAction pagination.pages cellData) [FolioOwner action] (laws : action.Laws) :
    (toCanonicalAtlas pagination action laws).data.toFunctor ≅ action.acceptedFunctor laws :=
  NatIso.ofComponents (fun occurrence =>
    { hom := (action.canonicalCarrierEquiv occurrence).toEmbedding
      inv := (action.canonicalCarrierEquiv occurrence).symm.toEmbedding
      hom_inv_id := by
        apply Function.Embedding.ext
        intro datum
        exact (action.canonicalCarrierEquiv occurrence).symm_apply_apply datum
      inv_hom_id := by
        apply Function.Embedding.ext
        intro datum
        exact (action.canonicalCarrierEquiv occurrence).apply_symm_apply datum })
    (by
      intro source target arrow
      apply Function.Embedding.ext
      intro datum
      exact Subtype.ext (canonical_map pagination action laws arrow datum))

end Datra.Executable.AtlasMembershipAction
