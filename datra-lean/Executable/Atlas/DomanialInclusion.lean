import Executable.Atlas.StableTransversal
import Executable.Atlas.Construction
import Executable.Atlas.Map
import Executable.Chain.Singleton

namespace Datra.Executable.DomanialInclusion
open CategoryTheory
universe u

/-- The constant cell family retains the Haskell wrapper and its phantom cell. -/
structure CellData (A : Type) (_cell : PageElementCell) where
  value : A

-- ALIGN: DOMINC-CELL-RECONSTRUCTION.
theorem cellData_reconstruct {A : Type} {cell : PageElementCell} (datum : CellData A cell) :
    CellData.mk datum.value = datum := rfl

-- ALIGN: DOMINC-CELL-PROJECTION.
def dominionCellProjection {A : Type} {cell : PageElementCell} :
    DomanialInsertion (CellData A cell) A where
  map := CellData.value
  preimage value := some ⟨value⟩
  leftInverse _ := rfl

def coalitionComponentPreimage {A B : Type} {cell : PageElementCell}
    (backward : B → Option A) (datum : B) : Option (CellData A cell) :=
  DomanialInsertion.composePartialInverses dominionCellProjection.preimage backward datum

def mapCellData {A B : Type} {source target : PageElementCell} (f : A → B)
    (datum : CellData A source) : CellData B target := ⟨f datum.value⟩

-- ALIGN: DOMINC-FUNCTOR-IDENTITY.
theorem mapCellData_identity {A : Type} {cell : PageElementCell} (datum : CellData A cell) :
    mapCellData id datum = datum := rfl

-- ALIGN: DOMINC-FUNCTOR-COMPOSITION.
theorem mapCellData_composition {A B C : Type} {source middle target : PageElementCell}
    (first : A → B) (second : B → C) (datum : CellData A source) :
    mapCellData (source := middle) (target := target) second (mapCellData first datum) =
      mapCellData (second ∘ first) datum := rfl

/-- The data component requires an inverse on all target data. A coalition's
inverse alone accepts only covered values, so it cannot perform this job. -/
-- ALIGN: DOMINC-COMPONENT-INVERSE.
def coalitionComponentInsertion {A : Type} {X : Atlas} {source : PageElementCell}
    (target : X.Element) (forward : A → X.CertifiedCoalitionElement)
    (arrow : ∀ value, (forward value).val.source ⟶ target)
    (backward : X.cellData target.val.cell → Option A)
    (leftInverse : ∀ value,
      backward (Atlas.coalitionElementAt (forward value).val target (arrow value)) = some value) :
    DomanialInsertion (CellData A source) (X.cellData target.val.cell) where
  map datum := Atlas.coalitionElementAt (forward datum.value).val target (arrow datum.value)
  preimage := coalitionComponentPreimage backward
  leftInverse datum := by
    change (backward (Atlas.coalitionElementAt (forward datum.value).val target
      (arrow datum.value))).bind (fun value => some (CellData.mk value)) = some datum
    rw [leftInverse]
    rfl

-- ALIGN: DOMINC-COMPONENT-PREIMAGE.
theorem coalitionComponentInsertion_preimage {A : Type} {X : Atlas} {source : PageElementCell}
    (target : X.Element) (forward : A → X.CertifiedCoalitionElement)
    (arrow : ∀ value, (forward value).val.source ⟶ target)
    (backward : X.cellData target.val.cell → Option A)
    (leftInverse : ∀ value,
      backward (Atlas.coalitionElementAt (forward value).val target (arrow value)) = some value)
    (datum : X.cellData target.val.cell) :
    (coalitionComponentInsertion (source := source) target forward arrow backward leftInverse).preimage datum =
    (backward datum).map CellData.mk := by
  cases decoded : backward datum <;>
    simp [coalitionComponentInsertion, coalitionComponentPreimage,
      DomanialInsertion.composePartialInverses, dominionCellProjection, decoded]

-- ALIGN: DOMINC-COMPONENT-FUNCTIONS.
theorem coalitionComponentInsertion_functions {A : Type} {X : Atlas} {source : PageElementCell}
    (target : X.Element) (forward : A → X.CertifiedCoalitionElement)
    (arrow : ∀ value, (forward value).val.source ⟶ target)
    (backward : X.cellData target.val.cell → Option A)
    (leftInverse : ∀ value,
      backward (Atlas.coalitionElementAt (forward value).val target (arrow value)) = some value) :
    (coalitionComponentInsertion (source := source) target forward arrow backward leftInverse).map =
        (fun datum => Atlas.coalitionElementAt (forward datum.value).val target (arrow datum.value)) ∧
      (coalitionComponentInsertion (source := source) target forward arrow backward leftInverse).preimage =
        DomanialInsertion.composePartialInverses dominionCellProjection.preimage backward := ⟨rfl, rfl⟩

def homToValue {A B : Type} {cell : PageElementCell} (f : CellData A cell → B) (value : A) : B :=
  f ⟨value⟩

def homFromValue {A B : Type} {cell : PageElementCell} (f : A → B) (datum : CellData A cell) : B :=
  f datum.value

-- ALIGN: DOMINC-HOM-LEFT-INVERSE.
theorem homLeftInverse {A B : Type} {cell : PageElementCell} (f : CellData A cell → B)
    (datum : CellData A cell) : homFromValue (homToValue f) datum = f datum := rfl

-- ALIGN: DOMINC-HOM-RIGHT-INVERSE.
theorem homRightInverse {A B : Type} {cell : PageElementCell} (f : A → B) (value : A) :
    homToValue (homFromValue (cell := cell) f) value = f value := rfl

-- ALIGN: DOMINC-HOM-NATURALITY-LEFT.
theorem homNaturalityLeft {A A' B : Type} {cell : PageElementCell} (before : A' → A)
    (f : CellData A cell → B) (value : A') :
    homToValue (f ∘ mapCellData (source := cell) before) value = homToValue f (before value) := rfl

-- ALIGN: DOMINC-HOM-NATURALITY-RIGHT.
theorem homNaturalityRight {A B C : Type} {cell : PageElementCell} (f : CellData A cell → B)
    (after : B → C) (value : A) : homToValue (after ∘ f) value = after (homToValue f value) := rfl

def emptyDominion : Dominion Empty := ⟨Empty.elim, fun _ => none, fun x => nomatch x⟩

def singletonPage : Page := ⟨Unit, Chain.singletonChain⟩

def onePageFolio : Folio singletonPage singletonPage :=
  ⟨FolioData.singleton singletonPage () (fun x => by cases x; rfl),
    FolioData.singleton_valid _ _ _⟩

def onePageRecipe : PageElementsConstruction singletonPage singletonPage := ⟨onePageFolio⟩

def onePagePagination : Pagination :=
  Pagination.fromPageElements onePageRecipe.constructPageElements

theorem onePagePagination_folio : onePagePagination.folio = onePageFolio := rfl

-- ALIGN: DOMINC-ONE-PAGE-FOLIO.
theorem onePageFolio_depth : onePageFolio.data.depth = 1 := rfl

-- ALIGN: DOMINC-ONE-PAGE-PAGINATION.
theorem onePagePagination_depth : onePagePagination.pages.depth = 1 := rfl

theorem onePage_position (element : onePagePagination.Element) :
    element.val.position = Ordinal.finiteOrdinal 0 := by
  obtain ⟨occurrence, h⟩ := element.property
  rw [← h]
  rfl

-- ALIGN: DOMINC-CONSTANT-DOMINION.
def constantDominion {A : Type} (D : Dominion A) (cell : PageElementCell) : Dominion (CellData A cell) where
  rank datum := D.rank datum.value
  unrank n := (D.unrank n).map CellData.mk
  coherence datum := by simp only [D.coherence, Option.map_some]

-- ALIGN: DOMINC-CONSTANT-ROUNDTRIP.
theorem constantDominion_roundTrip {A : Type} (D : Dominion A) {cell : PageElementCell}
    (datum : CellData A cell) :
    (constantDominion D cell).unrank ((constantDominion D cell).rank datum) = some datum :=
  (constantDominion D cell).coherence datum

-- ALIGN: DOMINC-IDENTITY-INSERTION.
def identityCellInsertion {A : Type} {source target : PageElementCell} :
    DomanialInsertion (CellData A source) (CellData A target) where
  map := mapCellData id
  preimage datum := some (mapCellData id datum)
  leftInverse _ := rfl

-- ALIGN: DOMINC-IDENTITY-ROUNDTRIP.
theorem identityCellInsertion_roundTrip {A : Type} {source target : PageElementCell}
    (datum : CellData A source) :
    (identityCellInsertion (target := target)).preimage (identityCellInsertion.map datum) = some datum :=
  (identityCellInsertion (target := target)).leftInverse datum

/-- The normalized constant action has all four constructor laws on any
one-page pagination. Disjointness uses equal-page transport to the origin. -/
def constantAtlasData {A : Type} (pagination : Pagination)
    (onePage : pagination.pages.depth = 1) (D : Dominion A) :
    AtlasData pagination.pages (CellData A) where
  action := { dataAt := fun element => constantDominion D element.val.cell
              mapData := fun _ => identityCellInsertion }
  identity := fun _ _ => rfl
  composition := fun _ _ _ => rfl
  coherence := fun _ _ => rfl
  disjoint := by
    intro left right origin hpage hne hbound horigin leftArrow rightArrow
    have leftPage : left.val.page = origin.val.page := by omega
    have rightPage : right.val.page = origin.val.page := by omega
    have shape (x : pagination.Element) : x.val.traceShape :=
      ⟨FolioData.ValidElement.trace_length x, FolioData.ValidElement.trace_head x⟩
    have leftPosition := leftArrow.samePagePosition (shape left) (shape origin) leftPage
    have rightPosition := rightArrow.samePagePosition (shape right) (shape origin) rightPage
    exact (hne (leftPosition.trans rightPosition.symm)).elim

/-- The runtime predicate accepts every value of the constant carrier. Erasing
its proof changes neither the datum nor either executable insertion direction. -/
def constantAcceptedEquiv {A : Type} (cell : PageElementCell) :
    {_datum : CellData A cell // true = true} ≃ CellData A cell where
  toFun := Subtype.val
  invFun datum := ⟨datum, rfl⟩
  left_inv _ := rfl
  right_inv _ := rfl

def constantMembershipAction {A : Type} (pagination : Pagination) (D : Dominion A) :
    AtlasMembershipAction pagination.pages (CellData A) :=
  AtlasMembershipAction.packagePredicate
    (PageElementDomain.ofFolio pagination.pages pagination.folio)
    (fun _ _ => true)
    (fun occurrence _ => (constantDominion D occurrence.cell).reindex
      (constantAcceptedEquiv occurrence.cell).symm)
    (fun {source target} _ _ _ => identityCellInsertion.reindex
      (constantAcceptedEquiv source.cell).symm (constantAcceptedEquiv target.cell).symm)

instance constantMembershipAction_owner {A : Type} (pagination : Pagination) (D : Dominion A) :
    (constantMembershipAction pagination D).FolioOwner :=
  ⟨pagination.folio.valid, rfl⟩

-- ALIGN: DOMINC-CONSTANT-RANK.
theorem constantMembershipAction_rank {A : Type} (pagination : Pagination) (D : Dominion A)
    (occurrence : PageElement pagination.pages)
    (valid : (constantMembershipAction pagination D).domain.contains occurrence = true)
    (datum : (constantMembershipAction pagination D).membership.Carrier occurrence) :
    ((constantMembershipAction pagination D).dataAt occurrence valid).rank datum =
      (constantDominion D occurrence.cell).rank datum.val := rfl

/-- Successful and off-image decoder results are retained after erasing the
always-true membership proof. -/
-- ALIGN: DOMINC-CONSTANT-UNRANK.
theorem constantMembershipAction_unrank {A : Type} (pagination : Pagination) (D : Dominion A)
    (occurrence : PageElement pagination.pages)
    (valid : (constantMembershipAction pagination D).domain.contains occurrence = true)
    (index : Nat) :
    (((constantMembershipAction pagination D).dataAt occurrence valid).unrank index).map Subtype.val =
      (constantDominion D occurrence.cell).unrank index := by
  change (((constantDominion D occurrence.cell).unrank index).map
    (constantAcceptedEquiv occurrence.cell).symm).map Subtype.val = _
  cases (constantDominion D occurrence.cell).unrank index <;> rfl

-- ALIGN: DOMINC-CONSTANT-MAP.
theorem constantMembershipAction_map {A : Type} (pagination : Pagination) (D : Dominion A)
    {source target : PageElement pagination.pages}
    (sourceValid : (constantMembershipAction pagination D).domain.contains source = true)
    (targetValid : (constantMembershipAction pagination D).domain.contains target = true)
    (arrow : source.Arrow target)
    (datum : (constantMembershipAction pagination D).membership.Carrier source) :
    (((constantMembershipAction pagination D).mapData sourceValid targetValid arrow).map datum).val =
      identityCellInsertion.map datum.val := rfl

-- ALIGN: DOMINC-CONSTANT-PREIMAGE.
theorem constantMembershipAction_preimage {A : Type} (pagination : Pagination) (D : Dominion A)
    {source target : PageElement pagination.pages}
    (sourceValid : (constantMembershipAction pagination D).domain.contains source = true)
    (targetValid : (constantMembershipAction pagination D).domain.contains target = true)
    (arrow : source.Arrow target)
    (datum : (constantMembershipAction pagination D).membership.Carrier target) :
    (((constantMembershipAction pagination D).mapData sourceValid targetValid arrow).preimage datum).map
      Subtype.val = (identityCellInsertion (source := source.cell)).preimage datum.val := rfl

def constantMembershipLaws {A : Type} (pagination : Pagination)
    (onePage : pagination.pages.depth = 1) (D : Dominion A) :
    (constantMembershipAction pagination D).Laws where
  identity _ _ := rfl
  composition _ _ _ := rfl
  coherence _ _ := rfl
  disjoint samePage distinct bounded atOrigin leftArrow rightArrow leftDatum rightDatum :=
    (constantAtlasData pagination onePage D).disjoint samePage distinct bounded atOrigin
      leftArrow rightArrow leftDatum.val rightDatum.val

/-- The actual predicate-action presentation used by the checked Haskell
constructor, including its ownership certificate and normalized laws. -/
-- ALIGN: DOMINC-CONSTANT-LAWS.
def constantPresentation {A : Type} (pagination : Pagination)
    (onePage : pagination.pages.depth = 1) (D : Dominion A) : AtlasPresentation :=
  AtlasPresentation.ofAction pagination (constantMembershipAction pagination D)
    (constantMembershipLaws pagination onePage D)

theorem constantPresentation_pagination {A : Type} (pagination : Pagination)
    (onePage : pagination.pages.depth = 1) (D : Dominion A) :
    (constantPresentation pagination onePage D).pagination = pagination := rfl

/-- Removing the always-true membership proof recovers the constant functor
used by the Dominion-inclusion interpretation. -/
def constantPresentation_functorIso {A : Type} (pagination : Pagination)
    (onePage : pagination.pages.depth = 1) (D : Dominion A) :
    (constantPresentation pagination onePage D).allocate.data.toFunctor ≅
      (constantAtlasData pagination onePage D).toFunctor :=
  (constantPresentation pagination onePage D).allocateFunctorIso ≪≫
    NatIso.ofComponents (fun occurrence =>
      { hom := (constantAcceptedEquiv occurrence.val.cell).toEmbedding
        inv := (constantAcceptedEquiv occurrence.val.cell).symm.toEmbedding
        hom_inv_id := by apply Function.Embedding.ext; intro datum; rfl
        inv_hom_id := by apply Function.Embedding.ext; intro datum; rfl })
      (by intro source target arrow; apply Function.Embedding.ext; intro datum; rfl)

def dominionAtlas {A : Type} (D : Dominion A) : Atlas where
  pagination := onePagePagination
  cellData := CellData A
  data := constantAtlasData onePagePagination rfl D

def dominionPresentation {A : Type} (D : Dominion A) : AtlasPresentation :=
  constantPresentation onePagePagination onePagePagination_depth D

-- ALIGN: DOMINC-OWNED-PRESENTATION.
theorem dominionPresentation_onePage {A : Type} (D : Dominion A) :
    (dominionPresentation D).pagination.pages.depth = 1 := rfl

-- ALIGN: DOMINC-PRESENTATION-INTERPRETATION.
def dominionPresentation_functorIso {A : Type} (D : Dominion A) :
    (dominionPresentation D).allocate.data.toFunctor ≅ (dominionAtlas D).data.toFunctor :=
  constantPresentation_functorIso onePagePagination onePagePagination_depth D

/-- The owner retains the raw constant carrier and action, before interpretation
passes to accepted carriers. Both directions of transport preserve the value. -/
structure DominionAtlas (A : Type) where
  allocation : AtlasAllocation Unit
  carrier : allocation.atlasDescription.cellData = CellData A
  onePage : allocation.atlasDescription.pagination.pages.depth = 1
  membershipConstant : allocation.atlasDescription.action.membership =
    .predicate (fun _ _ => true)
  mapIdentity :
    let action := allocation.atlasDescription.action
    ∀ {source target : PageElement allocation.atlasDescription.pagination.pages}
      (sourceValid : action.domain.contains source = true)
      (targetValid : action.domain.contains target = true) (arrow : source.Arrow target)
      (datum : action.membership.Carrier source),
      cast (congrFun carrier target.cell) ((action.mapData sourceValid targetValid arrow).map datum).val =
        mapCellData id (cast (congrFun carrier source.cell) datum.val)
  preimageIdentity :
    let action := allocation.atlasDescription.action
    ∀ {source target : PageElement allocation.atlasDescription.pagination.pages}
      (sourceValid : action.domain.contains source = true)
      (targetValid : action.domain.contains target = true) (arrow : source.Arrow target)
      (datum : action.membership.Carrier target),
      (((action.mapData sourceValid targetValid arrow).preimage datum).map Subtype.val).map
          (cast (congrFun carrier source.cell)) =
        (identityCellInsertion (source := source.cell)).preimage
          (cast (congrFun carrier target.cell) datum.val)

def DominionAtlas.atlas {A : Type} (owner : DominionAtlas A) : Atlas := owner.allocation.toAtlas

theorem DominionAtlas.acceptsAll {A : Type} (owner : DominionAtlas A)
    (occurrence : PageElement owner.allocation.atlasDescription.pagination.pages)
    (datum : owner.allocation.atlasDescription.cellData occurrence.cell) :
    owner.allocation.atlasDescription.action.membership.accepts occurrence datum = true := by
  rw [owner.membershipConstant]
  rfl

-- ALIGN: DOMINC-OWNER-MEMBERSHIP.
theorem DominionAtlas.acceptsDatum {A : Type} (owner : DominionAtlas A)
    (occurrence : PageElement owner.allocation.atlasDescription.pagination.pages)
    (datum : owner.allocation.atlasDescription.cellData occurrence.cell) :
    owner.allocation.acceptsDatum occurrence datum = true := by
  rw [AtlasAllocation.descriptionMembership]
  exact owner.acceptsAll
    (occurrence.normalize (owner.allocation.atlasDescription.pagination.pages.depth - 1)
      owner.allocation.atlasDescription.pagination.pages.depth) datum

/-- The constant datum together with membership in its actual retained owner. -/
abbrev DominionAtlas.AcceptedConstantDatum {A : Type} (owner : DominionAtlas A)
    (source : PageElement owner.allocation.atlasDescription.pagination.pages) :=
  {datum : CellData A source.cell // owner.allocation.acceptsDatum source
    (cast (congrFun owner.carrier source.cell).symm datum) = true}

def DominionAtlas.acceptedConstantEquiv {A : Type} (owner : DominionAtlas A)
    (source : PageElement owner.allocation.atlasDescription.pagination.pages) :
    CellData A source.cell ≃ owner.AcceptedConstantDatum source where
  toFun datum := ⟨datum, owner.acceptsDatum source _⟩
  invFun := Subtype.val
  left_inv _ := rfl
  right_inv _ := rfl

-- ALIGN: DOMINC-ACCEPTED-PREIMAGE.
def acceptedDominionPreimage {A B : Type} (owner : DominionAtlas A)
    (source : PageElement owner.allocation.atlasDescription.pagination.pages)
    (backward : B → Option (CellData A source.cell)) (datum : B) :
    Option (owner.AcceptedConstantDatum source) :=
  (backward datum).map (owner.acceptedConstantEquiv source)

theorem acceptedDominionPreimage_value {A B : Type} (owner : DominionAtlas A)
    (source : PageElement owner.allocation.atlasDescription.pagination.pages)
    (backward : B → Option (CellData A source.cell)) (datum : B) :
    (acceptedDominionPreimage owner source backward datum).map Subtype.val = backward datum := by
  unfold acceptedDominionPreimage
  cases backward datum <;> rfl

/-- Rechecking source membership preserves both executable directions. -/
-- ALIGN: DOMINC-ACCEPTED-COMPONENT.
def acceptDominionComponent {A B : Type} (owner : DominionAtlas A)
    (source : PageElement owner.allocation.atlasDescription.pagination.pages)
    (insertion : DomanialInsertion (CellData A source.cell) B) :
    DomanialInsertion (owner.AcceptedConstantDatum source) B :=
  insertion.reindex (owner.acceptedConstantEquiv source) (Equiv.refl B)

theorem acceptDominionComponent_map {A B : Type} (owner : DominionAtlas A)
    (source : PageElement owner.allocation.atlasDescription.pagination.pages)
    (insertion : DomanialInsertion (CellData A source.cell) B)
    (datum : owner.AcceptedConstantDatum source) :
    (acceptDominionComponent owner source insertion).map datum = insertion.map datum.val := rfl

theorem acceptDominionComponent_preimage {A B : Type} (owner : DominionAtlas A)
    (source : PageElement owner.allocation.atlasDescription.pagination.pages)
    (insertion : DomanialInsertion (CellData A source.cell) B) (datum : B) :
    ((acceptDominionComponent owner source insertion).preimage datum).map Subtype.val =
      insertion.preimage datum :=
  acceptedDominionPreimage_value owner source insertion.preimage datum

-- ALIGN: DOMINC-OWNER-CARDINALITY.
theorem DominionAtlas.cardinality {A : Type} (owner : DominionAtlas A) :
    owner.atlas.pages.depth = 1 := owner.onePage

/-- Share the constructor certificates for a concrete constant presentation. -/
def retainConstantAllocation {A : Type} (D : Dominion A) (allocation : AtlasAllocation Unit)
    (same : allocation.atlasDescription = dominionPresentation D) : DominionAtlas A := by
  rcases allocation with ⟨presentation⟩
  change presentation = dominionPresentation D at same
  subst presentation
  exact {
    allocation := (dominionPresentation D).allocateStored
    carrier := rfl
    onePage := rfl
    membershipConstant := rfl
    mapIdentity := fun _ _ _ _ => rfl
    preimageIdentity := fun _ _ _ _ => rfl }

-- ALIGN: DOMINC-OWNER-ALLOCATION.
def retainedDominionAtlas {A : Type} (D : Dominion A) : DominionAtlas A :=
  retainConstantAllocation D (dominionPresentation D).allocateStored rfl

/-- The canonical constructor uses the same fixed presentation through the
public recipe allocator, retaining its cardinality certificate. -/
def canonicalDominionRecipe {A : Type} (D : Dominion A) : AtlasConstruction :=
  ⟨dominionPresentation D⟩

-- ALIGN: DOMINC-CANONICAL-ALLOCATION.
def canonicalDominionAtlas {A : Type} (D : Dominion A) : DominionAtlas A :=
  retainConstantAllocation D (canonicalDominionRecipe D).presentation.allocateStored rfl

theorem canonicalDominionAtlas_allocated {A : Type} (D : Dominion A) :
    (canonicalDominionAtlas D).atlas = (canonicalDominionRecipe D).constructAtlas := rfl

theorem canonicalDominionAtlas_eq {A : Type} (D : Dominion A) :
    canonicalDominionAtlas D = retainedDominionAtlas D := rfl

def retainedDominionAtlas_functorIso {A : Type} (D : Dominion A) :
    (retainedDominionAtlas D).atlas.data.toFunctor ≅ (dominionAtlas D).data.toFunctor :=
  dominionPresentation_functorIso D

/-- The source occurrence does not change the selected owning target cell. -/
-- ALIGN: DOMINC-CONSTANT-OBJECT.
def constantObject {Source : Sort u} {Y : Atlas} (target : Y.Element) (_source : Source) : Y.Element := target

theorem constantObject_trace_valid {Source : Sort u} {Y : Atlas} (target : Y.Element) (source : Source) :
    Y.pages.traceValid (constantObject target source).val = true :=
  FolioData.ValidElement.traceValid Y.pagination.folio.valid target

/-- Both normalized images are the same occurrence, for every pair of sources. -/
-- ALIGN: DOMINC-CONSTANT-PAGE-LAW.
def constantObjectArrow {Source : Sort u} {Y : Atlas} (target : Y.Element) (source destination : Source) :
    (constantObject target source).normalize ⟶
      (constantObject target destination).normalize := 𝟙 target.normalize

/-- Construct the component at the selected dependent target, retaining
source membership and the decoder on all target values. -/
-- ALIGN: DOMINC-MAPPED-COMPONENT.
def constantComponentInsertion {A : Type} (owner : DominionAtlas A) {X : Atlas}
    (target : X.Element)
    (mapObject : PageElement owner.allocation.atlasDescription.pagination.pages → X.Element)
    (constant : ∀ source, mapObject source = target)
    (forward : A → X.CertifiedCoalitionElement)
    (arrow : ∀ value, (forward value).val.source ⟶ target)
    (backward : ∀ occurrence : X.Element, X.cellData occurrence.val.cell → Option A)
    (leftInverse : ∀ (occurrence : X.Element) (same : occurrence = target) value,
      backward occurrence (Atlas.coalitionElementAt (forward value).val occurrence
        (arrow value ≫ eqToHom same.symm)) = some value)
    (source : PageElement owner.allocation.atlasDescription.pagination.pages) :
    DomanialInsertion (owner.AcceptedConstantDatum source) (X.cellData (mapObject source).val.cell) :=
  acceptDominionComponent owner source
    (coalitionComponentInsertion (mapObject source) forward
      (fun value => arrow value ≫ eqToHom (constant source).symm)
      (backward (mapObject source)) (leftInverse (mapObject source) (constant source)))

theorem constantComponentInsertion_preimage {A : Type} (owner : DominionAtlas A) {X : Atlas}
    (target : X.Element)
    (mapObject : PageElement owner.allocation.atlasDescription.pagination.pages → X.Element)
    (constant : ∀ source, mapObject source = target)
    (forward : A → X.CertifiedCoalitionElement)
    (arrow : ∀ value, (forward value).val.source ⟶ target)
    (backward : ∀ occurrence : X.Element, X.cellData occurrence.val.cell → Option A)
    (leftInverse : ∀ (occurrence : X.Element) (same : occurrence = target) value,
      backward occurrence (Atlas.coalitionElementAt (forward value).val occurrence
        (arrow value ≫ eqToHom same.symm)) = some value)
    (source : PageElement owner.allocation.atlasDescription.pagination.pages)
    (datum : X.cellData (mapObject source).val.cell) :
    ((constantComponentInsertion owner target mapObject constant forward arrow backward leftInverse source).preimage datum).map
      Subtype.val = (backward (mapObject source) datum).map CellData.mk := by
  unfold constantComponentInsertion
  rw [acceptDominionComponent_preimage]
  exact coalitionComponentInsertion_preimage _ _ _ _ _ _

/-- The primitive data action of the inclusion hom correspondence. The
component inverse is defined on all origin data, including uncovered data. -/
def coalitionMorphism {A : Type} (D : Dominion A) (X : Atlas)
    (forward : A → X.CertifiedCoalitionElement)
    (backward : X.cellData (FolioData.ValidElement.originElement X.pages).val.cell → Option A)
    (leftInverse : ∀ value, backward (forward value).value.val = some value) :
    PrimitiveAtlasMorphism (dominionAtlas D) X where
  object := constantObject (FolioData.ValidElement.originElement X.pages)
  component _ := coalitionComponentInsertion _ forward
    (fun value => (forward value).val.source.toOrigin) backward leftInverse
  arrow := fun {source destination} _ =>
    constantObjectArrow (FolioData.ValidElement.originElement X.pages) source destination
  naturality := by
    intro x y f datum
    dsimp only [constantObject, constantObjectArrow]
    exact (X.data.identity (FolioData.ValidElement.originElement X.pages).normalize
      (forward datum.value).value.val).symm

/-- The cached coverage presentation does not change the forward origin datum. -/
theorem coalitionMorphism_component {A : Type} (D : Dominion A) (X : Atlas)
    (forward : A → X.CertifiedCoalitionElement)
    (backward : X.cellData (FolioData.ValidElement.originElement X.pages).val.cell → Option A)
    (leftInverse : ∀ value, backward (forward value).value.val = some value)
    (source : (dominionAtlas D).Element) (datum : (dominionAtlas D).cellData source.val.cell) :
    ((coalitionMorphism D X forward backward leftInverse).component source).map datum =
      (forward datum.value).value.val := rfl

theorem onePage_normalized_final (X : Atlas) (onePage : X.pages.depth = 1) (source : X.Element) :
    source.normalize.val.page = X.coverageFinalPage := by
  change min source.val.page (X.pages.depth - 1) = X.pages.depth - 1
  simp [onePage]

/-- The executable witness stores the source datum at its normalized occurrence,
which is a final region in a one-page Atlas. -/
def onePageCoverage (X : Atlas) (onePage : X.pages.depth = 1) (source : X.Element)
    (datum : X.cellData source.val.cell) : X.CoverageWitness :=
  X.atlasCoverageWitness source source datum datum ⟨onePage_normalized_final X onePage source, rfl⟩

-- ALIGN: DOMINC-ONE-PAGE-COVERAGE.
theorem onePageCoverage_spec (X : Atlas) (onePage : X.pages.depth = 1) (source : X.Element)
    (datum : X.cellData source.val.cell) :
    X.coverageWitnessCovers source datum (onePageCoverage X onePage source datum) = true := by
  have normalized := (X.atlasCoverageWitness_spec source source datum datum
    ⟨onePage_normalized_final X onePage source, rfl⟩).2
  apply Atlas.coverageWitnessAlongArrow source.toNormalized datum
  simpa only [X.data.coherence] using normalized

/-- Supply the certified one-page witness to the public Atlas-map constructor. -/
-- ALIGN: DOMINC-OWNER-MAP.
def dominionAtlasMap {A : Type} (owner : DominionAtlas A) : AtlasMap owner.atlas :=
  AtlasMap.atlasMap owner.atlas (fun datum =>
    let covers := onePageCoverage_spec owner.atlas owner.onePage _ datum
    ⟨onePageCoverage owner.atlas owner.onePage _ datum,
      Atlas.coverageWitnessCovers_valid covers, covers⟩)

theorem dominionAtlasMap_covered {A : Type} (owner : DominionAtlas A) (source : owner.atlas.Element)
    (datum : owner.atlas.cellData source.val.cell) : owner.atlas.Covered source datum :=
  (dominionAtlasMap owner).allCovered source datum

/-- The accepted-carrier interpretation retains exactly the constant values. -/
def DominionAtlas.carrierEquiv {A : Type} (owner : DominionAtlas A)
    (source : owner.atlas.Element) : owner.atlas.cellData source.val.cell ≃ CellData A source.val.cell :=
  letI := owner.allocation.atlasDescription.ownership
  (owner.allocation.atlasDescription.action.canonicalCarrierEquiv source).trans {
    toFun datum := cast (congrFun owner.carrier source.val.cell) datum.val
    invFun datum :=
      let raw := cast (congrFun owner.carrier source.val.cell).symm datum
      ⟨raw, owner.acceptsAll source.normalize.val raw⟩
    left_inv datum := by apply Subtype.ext; simp
    right_inv datum := by simp }

/-- Reindex the constant carrier into the canonical accepted-carrier model. -/
def DominionAtlas.datum {A : Type} (owner : DominionAtlas A)
    (source : owner.atlas.Element) (value : A) : owner.atlas.cellData source.val.cell :=
  (owner.carrierEquiv source).symm ⟨value⟩

theorem DominionAtlas.datum_value {A : Type} (owner : DominionAtlas A)
    (source : owner.atlas.Element) (value : A) :
    owner.carrierEquiv source (owner.datum source value) = ⟨value⟩ :=
  (owner.carrierEquiv source).apply_symm_apply _

/-- Normalized transport still acts as the identity on the constant value. -/
theorem DominionAtlas.carrierEquiv_map {A : Type} (owner : DominionAtlas A)
    {source target : owner.atlas.Element} (arrow : source ⟶ target)
    (datum : owner.atlas.cellData source.val.cell) :
    owner.carrierEquiv target ((owner.atlas.data.action.normalizedMap arrow).map datum) =
      mapCellData id (owner.carrierEquiv source datum) := by
  let presentation := owner.allocation.atlasDescription
  letI := presentation.ownership
  change cast (congrFun owner.carrier target.val.cell)
      (((presentation.action.toCanonicalAtlas presentation.pagination presentation.laws).data.action.normalizedMap arrow).map datum).val = _
  rw [AtlasMembershipAction.canonical_map]
  exact owner.mapIdentity _ _ (FolioData.ValidElement.normalizeArrow arrow)
    (presentation.action.canonicalCarrierEquiv source datum)

theorem DominionAtlas.carrierEquiv_preimage {A : Type} (owner : DominionAtlas A)
    {source target : owner.atlas.Element} (arrow : source ⟶ target)
    (datum : owner.atlas.cellData target.val.cell) :
    ((owner.atlas.data.action.normalizedMap arrow).preimage datum).map (owner.carrierEquiv source) =
      (identityCellInsertion (source := source.val.cell)).preimage (owner.carrierEquiv target datum) := by
  let presentation := owner.allocation.atlasDescription
  letI := presentation.ownership
  calc
    _ = (((owner.atlas.data.action.normalizedMap arrow).preimage datum).map
        (fun value => value.val)).map (cast (congrFun owner.carrier source.val.cell)) := by
      simp only [Option.map_map, Function.comp_def]
      rfl
    _ = _ := by
      change ((((presentation.action.toCanonicalAtlas presentation.pagination presentation.laws).data.action.normalizedMap arrow).preimage datum).map
        Subtype.val).map (cast (congrFun owner.carrier source.val.cell)) = _
      exact (congrArg (Option.map (cast (congrFun owner.carrier source.val.cell)))
        (AtlasMembershipAction.canonical_preimage presentation.pagination presentation.action
          presentation.laws arrow datum)).trans
        (owner.preimageIdentity _ _ (FolioData.ValidElement.normalizeArrow arrow)
          (presentation.action.canonicalCarrierEquiv target datum))

/-- Transport is the complete identity insertion under the constant-carrier
identification, including every partial-inverse lookup. -/
-- ALIGN: DOMINC-OWNER-MAP-IDENTITY.
theorem DominionAtlas.mapDataIdentity {A : Type} (owner : DominionAtlas A)
    {source target : owner.atlas.Element} (arrow : source ⟶ target) :
    (owner.atlas.data.action.normalizedMap arrow).reindex
      (owner.carrierEquiv source) (owner.carrierEquiv target) = identityCellInsertion := by
  apply DomanialInsertion.ext
  · funext datum
    change owner.carrierEquiv target
      ((owner.atlas.data.action.normalizedMap arrow).map
        ((owner.carrierEquiv source).symm datum)) = _
    rw [owner.carrierEquiv_map]
    simp only [Equiv.apply_symm_apply]
    rfl
  · funext datum
    change ((owner.atlas.data.action.normalizedMap arrow).preimage
      ((owner.carrierEquiv target).symm datum)).map (owner.carrierEquiv source) = _
    rw [owner.carrierEquiv_preimage]
    simp only [Equiv.apply_symm_apply]

/-- A fixed target component commutes with the retained source action and the
normalized target identity. This is the inclusion assembler's data law. -/
-- ALIGN: DOMINC-COMPONENT-NATURALITY.
theorem constantComponentNaturality {A : Type} (owner : DominionAtlas A) {X : Atlas}
    (target : X.Element) (forward : A → X.cellData target.val.cell)
    {source destination : owner.atlas.Element} (arrow : source ⟶ destination)
    (datum : owner.atlas.cellData source.val.cell) :
    forward (owner.carrierEquiv destination
      ((owner.atlas.data.action.normalizedMap arrow).map datum)).value =
      (X.data.action.normalizedMap (𝟙 target.normalize)).map
        (forward (owner.carrierEquiv source datum).value) := by
  rw [owner.carrierEquiv_map, X.data.identity]
  rfl

-- ALIGN: DOMINC-OWNER-COALITION.
def dominionCoalitionElement {A : Type} (owner : DominionAtlas A) (value : A) :
    owner.atlas.CertifiedCoalitionElement :=
  let source := FolioData.ValidElement.originElement owner.atlas.pages
  let datum := owner.datum source value
  Atlas.coalitionElement_checked source rfl datum
    (onePageCoverage owner.atlas owner.onePage source datum)
    (onePageCoverage_spec owner.atlas owner.onePage source datum)

theorem dominionCoalitionElement_source {A : Type} (owner : DominionAtlas A) (value : A) :
    (dominionCoalitionElement owner value).val.source =
      FolioData.ValidElement.originElement owner.atlas.pages := rfl

def coalitionValue {A : Type} (owner : DominionAtlas A)
    (element : owner.atlas.CertifiedCoalitionElement) : A :=
  let viewed := Atlas.viewCoalitionElement element.val
  (owner.carrierEquiv viewed.1 viewed.2).value

-- ALIGN: DOMINC-COALITION-VALUE-ROUNDTRIP.
theorem dominionCoalitionElement_value {A : Type} (owner : DominionAtlas A) (value : A) :
    coalitionValue owner (dominionCoalitionElement owner value) = value :=
  congrArg CellData.value (owner.datum_value _ value)

theorem coalitionValue_origin {A : Type} (owner : DominionAtlas A)
    (element : owner.atlas.CertifiedCoalitionElement) :
    coalitionValue owner element =
      (owner.carrierEquiv (FolioData.ValidElement.originElement owner.atlas.pages)
        element.value.val).value := by
  exact (congrArg CellData.value
    (owner.carrierEquiv_map element.val.source.toOrigin element.val.datum)).symm

theorem coalitionValue_eq_iff {A : Type} (owner : DominionAtlas A)
    (left right : owner.atlas.CertifiedCoalitionElement) :
    coalitionValue owner left = coalitionValue owner right ↔ left.value = right.value := by
  rw [coalitionValue_origin, coalitionValue_origin]
  constructor
  · intro same
    apply Subtype.ext
    apply (owner.carrierEquiv _).injective
    exact congrArg CellData.mk same
  · intro same
    rw [same]

/-- Reconstruction preserves the canonical coalition carrier itself. -/
-- ALIGN: DOMINC-COALITION-RECONSTRUCTION.
theorem dominionCoalitionElement_reconstruct {A : Type} (owner : DominionAtlas A)
    (element : owner.atlas.CertifiedCoalitionElement) :
    dominionCoalitionElement owner (coalitionValue owner element) = element := by
  apply Atlas.CertifiedCoalitionElement.ext
  apply (coalitionValue_eq_iff owner _ _).mp
  exact dominionCoalitionElement_value owner _

/-- The allocated Dominion's coalition equivalence retains the executable
constructor and value projection over the canonical carrier. -/
-- ALIGN: DOMINC-COALITION-EQUIVALENCE.
def allocatedCoalitionEquiv {A : Type} (owner : DominionAtlas A) : owner.atlas.Coalition ≃ A where
  toFun := coalitionValue owner
  invFun := dominionCoalitionElement owner
  left_inv := dominionCoalitionElement_reconstruct owner
  right_inv := dominionCoalitionElement_value owner

-- ALIGN: DOMINC-CHECKED-COALITION-UNIT.
def dominionCoalitionUnit {A : Type} (owner : DominionAtlas A) :
    DomanialInsertion A owner.atlas.CertifiedCoalitionElement where
  map := dominionCoalitionElement owner
  preimage element := some (coalitionValue owner element)
  leftInverse value := congrArg some (dominionCoalitionElement_value owner value)

-- ALIGN: DOMINC-CHECKED-COALITION-COUNIT.
def dominionCoalitionCounit {A : Type} (owner : DominionAtlas A) :
    DomanialInsertion owner.atlas.CertifiedCoalitionElement A where
  map := coalitionValue owner
  preimage value := some (dominionCoalitionElement owner value)
  leftInverse element := congrArg some (dominionCoalitionElement_reconstruct owner element)

-- ALIGN: DOMINC-COALITION-LEFT-INVERSE.
theorem coaDomInc_leftInverse {A : Type} (owner : DominionAtlas A)
    (element : owner.atlas.CertifiedCoalitionElement) :
    (dominionCoalitionCounit owner).preimage ((dominionCoalitionCounit owner).map element) =
      some element :=
  (dominionCoalitionCounit owner).leftInverse element

-- ALIGN: DOMINC-COALITION-RIGHT-INVERSE.
theorem coaDomInc_rightInverse {A : Type} (owner : DominionAtlas A) (value : A) :
    (dominionCoalitionUnit owner).preimage ((dominionCoalitionUnit owner).map value) = some value :=
  (dominionCoalitionUnit owner).leftInverse value

-- ALIGN: DOMINC-COVERAGE.
theorem dominionAtlas_covered {A : Type} (D : Dominion A) (element : (dominionAtlas D).Element)
    (datum : (dominionAtlas D).cellData element.val.cell) : (dominionAtlas D).Covered element datum :=
  let covers := onePageCoverage_spec (dominionAtlas D) rfl element datum
  Atlas.coverageWitnessCovers_sound (Atlas.coverageWitnessCovers_valid covers) covers

def dominionCoalitionValue {A : Type} (D : Dominion A) (value : A) : (dominionAtlas D).CoalitionValue :=
  ⟨⟨value⟩, dominionAtlas_covered D _ _⟩

def coalitionValueEquiv {A : Type} (D : Dominion A) : (dominionAtlas D).CoalitionValue ≃ A where
  toFun c := c.val.value
  invFun := dominionCoalitionValue D
  left_inv _ := rfl
  right_inv _ := rfl

def coaDomIncUnit {A : Type} (D : Dominion A) : DomanialInsertion A (dominionAtlas D).CoalitionValue where
  map := (coalitionValueEquiv D).symm
  preimage c := some (coalitionValueEquiv D c)
  leftInverse _ := rfl

theorem onePage_normalized_unique (element : onePagePagination.Element) :
    element.normalize = FolioData.ValidElement.originElement onePagePagination.pages := by
  apply FolioData.ValidElement.eq_of_page_position
  · change min element.val.page 0 = 0
    exact Nat.min_zero _
  · exact (onePage_position element.normalize).trans (onePage_position _).symm

theorem semanticElement_unique {A : Type} (D : Dominion A) (element : (dominionAtlas D).toSemantics.El) :
    element = (dominionAtlas D).toSemantics.Fo.originElement := by
  apply FolioData.ValidElement.fromFinite_injective onePagePagination.pages
  exact (FolioData.ValidElement.normalize_fromFinite _ element).symm.trans
    ((onePage_normalized_unique _).trans (FolioData.ValidElement.originElement_interpretation _))

noncomputable def interpretationHom {A : Type} (D : Dominion A) :
    (dominionAtlas D).toSemantics ⟶ Datra.Semantics.dominionAtlas ⟨D.toSemantics⟩ where
  Pa := (Functor.const _).obj Datra.Semantics.onePageFolio.originElement
  Da :=
    { app := fun _ => ⟨CellData.value, fun a b h => by cases a; cases b; cases h; rfl⟩
      naturality := by intros; apply Function.Embedding.ext; intro datum; rfl }

noncomputable def interpretationInv {A : Type} (D : Dominion A) :
    Datra.Semantics.dominionAtlas ⟨D.toSemantics⟩ ⟶ (dominionAtlas D).toSemantics where
  Pa := (Functor.const _).obj (dominionAtlas D).toSemantics.Fo.originElement
  Da :=
    { app := fun _ => ⟨CellData.mk, fun _ _ h => congrArg CellData.value h⟩
      naturality := by intros; apply Function.Embedding.ext; intro datum; rfl }

-- ALIGN: DOMINC-ATLAS-INTERPRETATION.
noncomputable def interpretationIso {A : Type} (D : Dominion A) :
    (dominionAtlas D).toSemantics ≅ Datra.Semantics.dominionAtlas ⟨D.toSemantics⟩ where
  hom := interpretationHom D
  inv := interpretationInv D
  hom_inv_id := by
    have hp : (interpretationHom D ≫ interpretationInv D).Pa =
        (𝟙 (dominionAtlas D).toSemantics : Datra.Semantics.AtlHom _ _).Pa :=
      CategoryTheory.Functor.ext (fun x => (semanticElement_unique D x).symm)
    apply Datra.Semantics.AtlHom.ext _ _ hp
    apply Datra.Semantics.NatTrans.hext_right _ _ (congrArg (fun P => P ⋙ (dominionAtlas D).toSemantics.Da) hp)
    intro x
    rw [semanticElement_unique D x]
    rfl
  inv_hom_id := by
    have hp : (interpretationInv D ≫ interpretationHom D).Pa =
        (𝟙 (Datra.Semantics.dominionAtlas ⟨D.toSemantics⟩) : Datra.Semantics.AtlHom _ _).Pa :=
      CategoryTheory.Functor.ext (fun x => (Datra.Semantics.onePage_cell_unique x).symm)
    apply Datra.Semantics.AtlHom.ext _ _ hp
    apply Datra.Semantics.NatTrans.hext_right _ _
      (congrArg (fun P => P ⋙ (Datra.Semantics.dominionAtlas ⟨D.toSemantics⟩).Da) hp)
    intro x
    rw [Datra.Semantics.onePage_cell_unique x]
    rfl

theorem dominionElement_unique {A : Type} (D : Dominion A)
    (element : (dominionAtlas D).TransposalElement) :
    element = Atlas.stableOrigin (dominionAtlas D) := by
  apply Subtype.ext
  exact element.property.symm.trans ((onePage_normalized_unique element.val).trans
    (onePage_normalized_unique (FolioData.ValidElement.originElement onePagePagination.pages)).symm)

def coalitionHom {A : Type} (D : Dominion A) (X : Atlas)
    (forward : A → X.CertifiedCoalitionElement)
    (backward : X.cellData (FolioData.ValidElement.originElement X.pages).val.cell → Option A)
    (leftInverse : ∀ value, backward (forward value).value.val = some value) :
    Atlas.Hom (dominionAtlas D) X :=
  .primitive (.primitive (coalitionMorphism D X forward backward leftInverse))

def coalitionTransposal {A : Type} (D : Dominion A) (X : Atlas)
    (forward : A → X.CertifiedCoalitionElement)
    (backward : X.cellData (FolioData.ValidElement.originElement X.pages).val.cell → Option A)
    (leftInverse : ∀ value, backward (forward value).value.val = some value) :
    Atlas.Transposal (dominionAtlas D) X :=
  Atlas.transposal (coalitionHom D X forward backward leftInverse)
    (fun target => if Atlas.TransposalElement.equal target (Atlas.stableOrigin X)
      then some (Atlas.stableOrigin (dominionAtlas D)) else none)
    (by
      intro source
      change (if Atlas.TransposalElement.equal (Atlas.stableOrigin X) (Atlas.stableOrigin X)
        then some (Atlas.stableOrigin (dominionAtlas D)) else none) = some source
      rw [(Atlas.TransposalElement.equal_iff _ _).mpr rfl]
      exact congrArg some (dominionElement_unique D source).symm)

def coalitionOrdered {A : Type} (D : Dominion A) (X : Atlas)
    (forward : A → X.CertifiedCoalitionElement)
    (backward : X.cellData (FolioData.ValidElement.originElement X.pages).val.cell → Option A)
    (leftInverse : ∀ value, backward (forward value).value.val = some value) :
    Atlas.OrderedTransposal (dominionAtlas D) X :=
  .primitive (coalitionTransposal D X forward backward leftInverse) (by
    intro source target h
    rw [dominionElement_unique D source, dominionElement_unique D target] at h
    change false = true at h
    cases h)

def coalitionTransversal {A : Type} (D : Dominion A) (X : Atlas)
    (forward : A → X.CertifiedCoalitionElement)
    (backward : X.cellData (FolioData.ValidElement.originElement X.pages).val.cell → Option A)
    (leftInverse : ∀ value, backward (forward value).value.val = some value) :
    Atlas.Transversal (dominionAtlas D) X :=
  Atlas.atlasTransversal (coalitionOrdered D X forward backward leftInverse) (fun covered =>
    ⟨(forward covered.val.datum.value).coveredElement.val.witness,
      (forward covered.val.datum.value).coveredElement.property.1, by
        change X.coverageWitnessCovers
          (FolioData.ValidElement.originElement X.pages).normalize
          (forward covered.val.datum.value).value.val
          (forward covered.val.datum.value).coveredElement.val.witness = true
        have h := Atlas.coalitionElementAt_coverage
          (forward covered.val.datum.value)
          (FolioData.ValidElement.originElement X.pages)
          (forward covered.val.datum.value).val.source.toOrigin
        simpa only [Atlas.coverageWitnessCovers, X.originImageRank_normalize] using h⟩)

theorem coalitionTransversal_stable {A : Type} (D : Dominion A) (X : Atlas)
    (forward : A → X.CertifiedCoalitionElement)
    (backward : X.cellData (FolioData.ValidElement.originElement X.pages).val.cell → Option A)
    (leftInverse : ∀ value, backward (forward value).value.val = some value) :
    Atlas.stableOriginPreserved (coalitionTransversal D X forward backward leftInverse) = true :=
  (Atlas.TransposalElement.equal_iff _ _).mpr rfl

theorem coalitionTransversal_value {A : Type} (D : Dominion A) (X : Atlas)
    (forward : A → X.CertifiedCoalitionElement)
    (backward : X.cellData (FolioData.ValidElement.originElement X.pages).val.cell → Option A)
    (leftInverse : ∀ value, backward (forward value).value.val = some value) (value : A) :
    Atlas.mapCoalitionValue (coalitionTransversal D X forward backward leftInverse)
      (dominionCoalitionValue D value) = (forward value).value := by
  apply Subtype.ext
  change X.originImage (FolioData.ValidElement.originElement X.pages).normalize
    (forward value).value.val = (forward value).value.val
  rw [X.originImage_normalize, Atlas.originImage_origin]

/-- The executable inverse half of the hom correspondence retains both
partial inverses: one on covered coalition values, and one on all origin data. -/
def coaToDomInc {A : Type} (D : Dominion A) (X : Atlas)
    (insertion : DomanialInsertion A X.CoalitionValue)
    (backward : X.cellData (FolioData.ValidElement.originElement X.pages).val.cell → Option A)
    (leftInverse : ∀ value, backward (insertion.map value).val = some value) :
    Atlas.StableTransversal (dominionAtlas D) X :=
  let forward := fun value => (insertion.map value).presentation
  let componentInverse : ∀ value, backward (forward value).value.val = some value := by
    simpa only [forward, Atlas.CoalitionValue.presentation_value] using leftInverse
  let transversal := coalitionTransversal D X forward backward componentInverse
  .primitive transversal (coalitionTransversal_stable D X forward backward componentInverse)
    (fun target => (insertion.preimage target).map (dominionCoalitionValue D)) (by
      intro source
      change (insertion.preimage
        (Atlas.mapCoalitionValue transversal (dominionCoalitionValue D source.val.value))).map
          (dominionCoalitionValue D) = some source
      rw [coalitionTransversal_value, Atlas.CoalitionValue.presentation_value, insertion.leftInverse]
      rfl)

theorem coaToDomInc_coalition_map {A : Type} (D : Dominion A) (X : Atlas)
    (insertion : DomanialInsertion A X.CoalitionValue)
    (backward : X.cellData (FolioData.ValidElement.originElement X.pages).val.cell → Option A)
    (leftInverse : ∀ value, backward (insertion.map value).val = some value) (value : A) :
    ((coaToDomInc D X insertion backward leftInverse).coalitionInsertion).map
      (dominionCoalitionValue D value) = insertion.map value := by
  change Atlas.mapCoalitionValue _ (dominionCoalitionValue D value) = _
  rw [coalitionTransversal_value, Atlas.CoalitionValue.presentation_value]

theorem coaToDomInc_coalition_preimage {A : Type} (D : Dominion A) (X : Atlas)
    (insertion : DomanialInsertion A X.CoalitionValue)
    (backward : X.cellData (FolioData.ValidElement.originElement X.pages).val.cell → Option A)
    (leftInverse : ∀ value, backward (insertion.map value).val = some value) (target : X.CoalitionValue) :
    ((coaToDomInc D X insertion backward leftInverse).coalitionInsertion).preimage target =
      (insertion.preimage target).map (dominionCoalitionValue D) := rfl

-- ALIGN: DOMINC-HOM-TO.
def domIncToCoa {A : Type} (D : Dominion A) {X : Atlas}
    (arrow : Atlas.StableTransversal (dominionAtlas D) X) : DomanialInsertion A X.CoalitionValue :=
  (coaDomIncUnit D).comp arrow.coalitionInsertion

/-- The forward hom map recovers the supplied insertion, including its
observable partial inverse on every covered target value. -/
-- ALIGN: DOMINC-HOM-RIGHT-INVERSE-FULL.
theorem domIncToCoa_coaToDomInc {A : Type} (D : Dominion A) (X : Atlas)
    (insertion : DomanialInsertion A X.CoalitionValue)
    (backward : X.cellData (FolioData.ValidElement.originElement X.pages).val.cell → Option A)
    (leftInverse : ∀ value, backward (insertion.map value).val = some value) :
    domIncToCoa D (coaToDomInc D X insertion backward leftInverse) = insertion := by
  apply DomanialInsertion.ext
  · funext value
    exact coaToDomInc_coalition_map D X insertion backward leftInverse value
  · funext target
    change ((insertion.preimage target).map (dominionCoalitionValue D)).bind
      (fun value => some ((coalitionValueEquiv D) value)) = insertion.preimage target
    cases insertion.preimage target <;> rfl

def dominionMap {A B : Type} (source : Dominion A) (target : Dominion B)
    (insertion : DomanialInsertion A B) : Atlas.StableTransversal (dominionAtlas source) (dominionAtlas target) :=
  coaToDomInc source (dominionAtlas target) (insertion.comp (coaDomIncUnit target))
    (fun datum => insertion.preimage datum.value) insertion.leftInverse

noncomputable def coalitionInsertionToSemantics {A : Type} (D : Dominion A) (X : Atlas)
    (insertion : DomanialInsertion A X.CoalitionValue) :
    (⟨D.toSemantics⟩ : Datra.Semantics.DomIns) ⟶ Datra.Semantics.Coa.obj
      (WideSubcategory.mk (WideSubcategory.mk X.toSemantics) : Datra.Semantics.StaAtlTrav) :=
  insertion.toSemantics.trans (Atlas.CoalitionValue.semanticsEquiv X).toEmbedding

theorem coalitionHom_page {A : Type} (D : Dominion A) (X : Atlas)
    (forward : A → X.CertifiedCoalitionElement)
    (backward : X.cellData (FolioData.ValidElement.originElement X.pages).val.cell → Option A)
    (leftInverse : ∀ value, backward (forward value).value.val = some value)
    (source : (dominionAtlas D).toSemantics.El) :
    (coalitionHom D X forward backward leftInverse).finiteSemantics.Pa.obj source =
      X.toSemantics.Fo.originElement := by
  have h := (coalitionTransposal D X forward backward leftInverse).mapObject_interpretation
    (Atlas.TransposalElement.fromSemantics (dominionAtlas D) source)
  change (Atlas.stableOrigin X).toSemantics =
    (coalitionHom D X forward backward leftInverse).finiteSemantics.Pa.obj
      (Atlas.TransposalElement.fromSemantics (dominionAtlas D) source).toSemantics at h
  simpa only [Atlas.stableOrigin_interpretation, Atlas.TransposalElement.toSemantics_fromSemantics] using h.symm

/-- The semantic arrow agrees on the page functor and the dependent data
component, after removing the executable one-page cell wrapper. -/
-- ALIGN: DOMINC-HOM-FROM.
theorem coaToDomInc_interpretation {A : Type} (D : Dominion A) (X : Atlas)
    (insertion : DomanialInsertion A X.CoalitionValue)
    (backward : X.cellData (FolioData.ValidElement.originElement X.pages).val.cell → Option A)
    (leftInverse : ∀ value, backward (insertion.map value).val = some value) :
    (coaToDomInc D X insertion backward leftInverse).toSemantics.val.val =
      interpretationHom D ≫
        (Datra.Semantics.coaToDomInc (coalitionInsertionToSemantics D X insertion)).val.val := by
  apply Atlas.semanticHom_ext
  · exact CategoryTheory.Functor.ext (fun source => coalitionHom_page D X _ _ _ source)
  · intro source
    apply Atlas.fromSemanticData_injective X
    change Atlas.fromSemanticData X
      (Atlas.mapSemanticData (coalitionHom D X _ _ _).finiteSemantics source) = _
    rw [Atlas.Hom.mapData_interpretation]
    change (coalitionHom D X _ _ _).mapData (Atlas.fromSemanticData (dominionAtlas D) source) =
      Atlas.fromSemanticData X ⟨X.toSemantics.Fo.originElement,
        Atlas.originDatumEquiv X (insertion.map source.2.value).val⟩
    rw [Atlas.fromSemanticOriginData]
    change (⟨(FolioData.ValidElement.originElement X.pages).normalize,
      (insertion.map source.2.value).presentation.value.val⟩ : X.DataElement) = _
    simp only [Atlas.CoalitionValue.presentation_value]
    apply Sigma.ext
    · change (FolioData.ValidElement.originElement X.pages).normalize =
        FolioData.ValidElement.originElement X.pages
      rw [FolioData.ValidElement.originElement_interpretation, FolioData.ValidElement.normalize_fromFinite]
    · rfl

-- ALIGN: DOMINC-MAP.
theorem dominionMap_interpretation {A B : Type} (source : Dominion A) (target : Dominion B)
    (insertion : DomanialInsertion A B) :
    (dominionMap source target insertion).toSemantics.val.val =
      interpretationHom source ≫ Datra.Semantics.dominionMap insertion.toSemantics ≫ interpretationInv target := by
  apply Atlas.semanticHom_ext
  · exact CategoryTheory.Functor.ext (fun element => coalitionHom_page source (dominionAtlas target) _ _ _ element)
  · intro datum
    apply Atlas.fromSemanticData_injective (dominionAtlas target)
    change Atlas.fromSemanticData (dominionAtlas target)
      (Atlas.mapSemanticData (coalitionHom source (dominionAtlas target) _ _ _).finiteSemantics datum) = _
    rw [Atlas.Hom.mapData_interpretation]
    change (⟨(FolioData.ValidElement.originElement onePagePagination.pages).normalize,
      (((insertion.comp (coaDomIncUnit target)).map datum.2.value).presentation).value.val⟩ :
        (dominionAtlas target).DataElement) = _
    simp only [Atlas.CoalitionValue.presentation_value]
    apply Sigma.ext
    · change (FolioData.ValidElement.originElement onePagePagination.pages).normalize =
        (FolioData.ValidElement.fromFinite onePagePagination.pages).obj
          (dominionAtlas target).toSemantics.Fo.originElement
      rw [FolioData.ValidElement.originElement_interpretation, FolioData.ValidElement.normalize_fromFinite]
      rfl
    · rfl

-- ALIGN: DOMINC-MAP-IDENTITY.
theorem dominionMap_identity {A : Type} (D : Dominion A) :
    (dominionMap D D (DomanialInsertion.identity A)).toSemantics =
      𝟙 (WideSubcategory.mk (WideSubcategory.mk (dominionAtlas D).toSemantics) :
        Datra.Semantics.StaAtlTrav) := by
  apply Subtype.ext
  apply Subtype.ext
  change (dominionMap D D (DomanialInsertion.identity A)).toSemantics.val.val =
    𝟙 (dominionAtlas D).toSemantics
  rw [dominionMap_interpretation]
  change interpretationHom D ≫ 𝟙 _ ≫ interpretationInv D = _
  simpa only [Category.id_comp] using (interpretationIso D).hom_inv_id

-- ALIGN: DOMINC-MAP-COMPOSITION.
theorem dominionMap_composition {A B C : Type} (source : Dominion A) (middle : Dominion B)
    (target : Dominion C) (first : DomanialInsertion A B) (second : DomanialInsertion B C) :
    (dominionMap source target (first.comp second)).toSemantics =
      (dominionMap source middle first).toSemantics ≫ (dominionMap middle target second).toSemantics := by
  apply Subtype.ext
  apply Subtype.ext
  change (dominionMap source target (first.comp second)).toSemantics.val.val =
    (dominionMap source middle first).toSemantics.val.val ≫
      (dominionMap middle target second).toSemantics.val.val
  simp only [dominionMap_interpretation]
  change interpretationHom source ≫
      (Datra.Semantics.dominionMap (X := ⟨source.toSemantics⟩) (Y := ⟨middle.toSemantics⟩) first.toSemantics ≫
        Datra.Semantics.dominionMap second.toSemantics) ≫ interpretationInv target = _
  have cancel : interpretationInv middle ≫ interpretationHom middle = 𝟙 _ :=
    (interpretationIso middle).inv_hom_id
  simp only [Category.assoc]
  rw [← Category.assoc (interpretationInv middle) (interpretationHom middle), cancel, Category.id_comp]

theorem semanticElementLT_false {A : Type} (D : Dominion A)
    (x y : (dominionAtlas D).toSemantics.El) :
    ¬ Datra.Semantics.elementLT (dominionAtlas D).toSemantics x y := by
  intro h
  have same := (semanticElement_unique D x).trans (semanticElement_unique D y).symm
  subst y
  let m := (dominionAtlas D).toSemantics.Fo.commonBase x.1 x.1
  letI : LinearOrder ((dominionAtlas D).toSemantics.Fo.Cell m) :=
    (((dominionAtlas D).toSemantics.Fo.core.obj m.unop).unop).linearOrder
  exact lt_irrefl _ h

/-- The one-page interpretation is an isomorphism in the stable-transversal
category, retaining the object restrictions used by the inclusion adjunction. -/
-- ALIGN: DOMINC-STABLE-ISOMORPHISM.
noncomputable def interpretationStableIso {A : Type} (D : Dominion A) :
    (WideSubcategory.mk (WideSubcategory.mk (dominionAtlas D).toSemantics) :
      Datra.Semantics.StaAtlTrav) ≅ Datra.Semantics.DomInc.obj ⟨D.toSemantics⟩ where
  hom := ⟨⟨interpretationHom D, ⟨⟨
    (fun x y _ => (semanticElement_unique D x).trans (semanticElement_unique D y).symm),
    (fun x y h => (semanticElementLT_false D x y h).elim)⟩,
    (fun _ => Datra.Semantics.atlasMap_all_covered
      (Datra.Semantics.dominionAtlas_isMap ⟨D.toSemantics⟩) _ _)⟩⟩, rfl⟩
  inv := ⟨⟨interpretationInv D, ⟨⟨
    (fun x y _ => (Datra.Semantics.onePage_cell_unique x).trans
      (Datra.Semantics.onePage_cell_unique y).symm),
    (fun x y h => (Datra.Semantics.onePage_elementLT_false ⟨D.toSemantics⟩ x y h).elim)⟩,
    (fun c => ((dominionAtlas D).covered_interpretation _ _).mp
      (dominionAtlas_covered D _ _))⟩⟩, rfl⟩
  hom_inv_id := by
    apply Subtype.ext
    apply Subtype.ext
    exact (interpretationIso D).hom_inv_id
  inv_hom_id := by
    apply Subtype.ext
    apply Subtype.ext
    exact (interpretationIso D).inv_hom_id

theorem coalitionUnit_interpretation {A : Type} (D : Dominion A) (value : A) :
    Atlas.CoalitionValue.semanticsEquiv (dominionAtlas D) (dominionCoalitionValue D value) =
      Datra.Semantics.Coa.map (interpretationStableIso D).inv
        ((Datra.Semantics.coaDomIncIso ⟨D.toSemantics⟩).inv value) := by
  apply Subtype.ext
  rfl

-- ALIGN: DOMINC-HOM-TO-INTERPRETATION.
theorem domIncToCoa_interpretation {A : Type} (D : Dominion A) {X : Atlas}
    (f : Atlas.StableTransversal (dominionAtlas D) X) :
    coalitionInsertionToSemantics D X (domIncToCoa D f) =
      Datra.Semantics.domIncToCoa ((interpretationStableIso D).inv ≫ f.toSemantics) := by
  apply Function.Embedding.ext
  intro value
  change Atlas.CoalitionValue.semanticsEquiv X
      (f.coalitionInsertion.map (dominionCoalitionValue D value)) =
    Datra.Semantics.Coa.map ((interpretationStableIso D).inv ≫ f.toSemantics)
      ((Datra.Semantics.coaDomIncIso ⟨D.toSemantics⟩).inv value)
  rw [f.coalitionInsertion_interpretation, coalitionUnit_interpretation,
    Datra.Semantics.Coa.map_comp]
  rfl

theorem coaToDomInc_semantics {A : Type} (D : Dominion A) (X : Atlas)
    (insertion : DomanialInsertion A X.CoalitionValue)
    (backward : X.cellData (FolioData.ValidElement.originElement X.pages).val.cell → Option A)
    (leftInverse : ∀ value, backward (insertion.map value).val = some value) :
    (coaToDomInc D X insertion backward leftInverse).toSemantics =
      (interpretationStableIso D).hom ≫
        Datra.Semantics.coaToDomInc (coalitionInsertionToSemantics D X insertion) := by
  apply Subtype.ext
  apply Subtype.ext
  exact coaToDomInc_interpretation D X insertion backward leftInverse

theorem dominionMap_semantics {A B : Type} (source : Dominion A) (target : Dominion B)
    (insertion : DomanialInsertion A B) :
    (dominionMap source target insertion).toSemantics =
      (interpretationStableIso source).hom ≫ Datra.Semantics.DomInc.map insertion.toSemantics ≫
        (interpretationStableIso target).inv := by
  apply Subtype.ext
  apply Subtype.ext
  exact dominionMap_interpretation source target insertion

/-- Transport the written adjunction along the proved one-page isomorphism.
Its inverse is implemented on the executable side when a component inverse
on all target origin data is supplied. -/
noncomputable def dominionHomEquiv {A : Type} (D : Dominion A) (X : Atlas) :
    ((WideSubcategory.mk (WideSubcategory.mk (dominionAtlas D).toSemantics) :
      Datra.Semantics.StaAtlTrav) ⟶ WideSubcategory.mk (WideSubcategory.mk X.toSemantics)) ≃
    ((⟨D.toSemantics⟩ : Datra.Semantics.DomIns) ⟶ Datra.Semantics.Coa.obj
      (WideSubcategory.mk (WideSubcategory.mk X.toSemantics))) :=
  ((interpretationStableIso D).homCongr (Iso.refl _)).trans
    (Datra.Semantics.domIncCoaHomEquiv ⟨D.toSemantics⟩
      (WideSubcategory.mk (WideSubcategory.mk X.toSemantics)))

-- ALIGN: DOMINC-HOM-EQUIV-TO.
theorem dominionHomEquiv_to {A : Type} (D : Dominion A) {X : Atlas}
    (f : Atlas.StableTransversal (dominionAtlas D) X) :
    dominionHomEquiv D X f.toSemantics = coalitionInsertionToSemantics D X (domIncToCoa D f) := by
  change Datra.Semantics.domIncToCoa ((interpretationStableIso D).inv ≫ f.toSemantics ≫ 𝟙 _) = _
  rw [Category.comp_id]
  exact (domIncToCoa_interpretation D f).symm

-- ALIGN: DOMINC-HOM-EQUIV-FROM.
theorem dominionHomEquiv_from {A : Type} (D : Dominion A) (X : Atlas)
    (insertion : DomanialInsertion A X.CoalitionValue)
    (backward : X.cellData (FolioData.ValidElement.originElement X.pages).val.cell → Option A)
    (leftInverse : ∀ value, backward (insertion.map value).val = some value) :
    (dominionHomEquiv D X).symm (coalitionInsertionToSemantics D X insertion) =
      (coaToDomInc D X insertion backward leftInverse).toSemantics := by
  change (interpretationStableIso D).hom ≫
    Datra.Semantics.coaToDomInc (coalitionInsertionToSemantics D X insertion) ≫ 𝟙 _ = _
  rw [Category.comp_id]
  exact (coaToDomInc_semantics D X insertion backward leftInverse).symm

/-- Reconstructing an executable stable arrow recovers its full semantic
arrow. Off-image inverse choices are not part of the written hom-set. -/
-- ALIGN: DOMINC-HOM-LEFT-INVERSE-FULL.
theorem coaToDomInc_domIncToCoa {A : Type} (D : Dominion A) {X : Atlas}
    (f : Atlas.StableTransversal (dominionAtlas D) X)
    (backward : X.cellData (FolioData.ValidElement.originElement X.pages).val.cell → Option A)
    (leftInverse : ∀ value, backward ((domIncToCoa D f).map value).val = some value) :
    (coaToDomInc D X (domIncToCoa D f) backward leftInverse).toSemantics = f.toSemantics := by
  rw [← dominionHomEquiv_from, ← dominionHomEquiv_to]
  exact (dominionHomEquiv D X).symm_apply_apply f.toSemantics

theorem domIncToCoa_naturality_right {A : Type} (D : Dominion A) {X Y : Atlas}
    (first : Atlas.StableTransversal (dominionAtlas D) X)
    (second : Atlas.StableTransversal X Y) :
    domIncToCoa D (Atlas.StableTransversal.comp second first) =
      (domIncToCoa D first).comp second.coalitionInsertion := by
  unfold domIncToCoa
  rw [Atlas.StableTransversal.coalitionInsertion_comp]
  exact (DomanialInsertion.comp_assoc _ _ _).symm

theorem domIncToCoa_naturality_left {A B : Type} (source : Dominion A) (middle : Dominion B)
    (insertion : DomanialInsertion A B) {X : Atlas}
    (f : Atlas.StableTransversal (dominionAtlas middle) X) :
    domIncToCoa source (Atlas.StableTransversal.comp f (dominionMap source middle insertion)) =
      insertion.comp (domIncToCoa middle f) := by
  rw [domIncToCoa_naturality_right]
  unfold dominionMap
  rw [domIncToCoa_coaToDomInc]
  exact DomanialInsertion.comp_assoc _ _ _

-- ALIGN: DOMINC-HOM-NATURALITY-LEFT-FULL.
theorem dominionHomEquiv_naturality_left {A B : Type} (source : Dominion A) (middle : Dominion B)
    (insertion : DomanialInsertion A B) {X : Atlas}
    (f : Atlas.StableTransversal (dominionAtlas middle) X) :
    dominionHomEquiv source X ((dominionMap source middle insertion).toSemantics ≫ f.toSemantics) =
      insertion.toSemantics ≫ dominionHomEquiv middle X f.toSemantics := by
  rw [← Atlas.StableTransversal.toSemantics_comp, dominionHomEquiv_to,
    domIncToCoa_naturality_left, dominionHomEquiv_to]
  rfl

-- ALIGN: DOMINC-HOM-NATURALITY-RIGHT-FULL.
theorem dominionHomEquiv_naturality_right {A : Type} (D : Dominion A) {X Y : Atlas}
    (first : Atlas.StableTransversal (dominionAtlas D) X)
    (second : Atlas.StableTransversal X Y) :
    dominionHomEquiv D Y (first.toSemantics ≫ second.toSemantics) =
      dominionHomEquiv D X first.toSemantics ≫ Datra.Semantics.Coa.map second.toSemantics := by
  rw [← Atlas.StableTransversal.toSemantics_comp, dominionHomEquiv_to,
    domIncToCoa_naturality_right, dominionHomEquiv_to]
  apply Function.Embedding.ext
  intro value
  exact second.coalitionInsertion_interpretation ((domIncToCoa D first).map value)

end Datra.Executable.DomanialInclusion
