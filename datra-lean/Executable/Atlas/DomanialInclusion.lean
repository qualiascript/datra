import Executable.Atlas.StableTransversal

namespace Datra.Executable.DomanialInclusion
open CategoryTheory

/-- The constant cell family retains the Haskell wrapper and its phantom cell. -/
structure CellData (A : Type) (_cell : PageElementCell) where
  value : A

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
    (target : X.Element) (forward : A → X.CoalitionElement)
    (arrow : ∀ value, (forward value).source ⟶ target)
    (backward : X.cellData target.val.cell → Option A)
    (leftInverse : ∀ value,
      backward (Atlas.coalitionElementAt (forward value) target (arrow value)) = some value) :
    DomanialInsertion (CellData A source) (X.cellData target.val.cell) where
  map datum := Atlas.coalitionElementAt (forward datum.value) target (arrow datum.value)
  preimage datum := (backward datum).map CellData.mk
  leftInverse datum := by simp only [leftInverse, Option.map_some]

theorem coalitionComponentInsertion_preimage {A : Type} {X : Atlas} {source : PageElementCell}
    (target : X.Element) (forward : A → X.CoalitionElement)
    (arrow : ∀ value, (forward value).source ⟶ target)
    (backward : X.cellData target.val.cell → Option A)
    (leftInverse : ∀ value,
      backward (Atlas.coalitionElementAt (forward value) target (arrow value)) = some value)
    (datum : X.cellData target.val.cell) :
    (coalitionComponentInsertion (source := source) target forward arrow backward leftInverse).preimage datum =
      (backward datum).map CellData.mk := rfl

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

def singletonChain : Chain Unit where
  orderType := Ordinal.finiteOrdinal 1
  position := fun _ => Ordinal.finiteOrdinal 0
  lookup position := if position = Ordinal.finiteOrdinal 0 then some () else none
  positionBelow _ := by decide
  positionInjective _ _ _ := Subsingleton.elim _ _
  positionSurjective position below := by
    have h : position.toSemantics < 1 := by
      simpa only [Ordinal.finiteOrdinal_denote, Nat.cast_one] using (Ordinal.ordinalLT_correct _ _).mp below
    have hz : position = Ordinal.finiteOrdinal 0 := Ordinal.toSemantics_injective (by
      simpa only [Ordinal.finiteOrdinal_denote, Nat.cast_zero] using _root_.Ordinal.lt_one_iff_zero.mp h)
    subst position
    exact ⟨(), by simp, rfl⟩

def singletonPage : Page := ⟨Unit, singletonChain⟩

def onePageFolio : Folio singletonPage singletonPage :=
  ⟨FolioData.singleton singletonPage () (fun x => by cases x; rfl),
    FolioData.singleton_valid _ _ _⟩

def onePagePagination : Pagination := ⟨singletonPage, singletonPage, onePageFolio⟩

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

def identityCellInsertion {A : Type} {source target : PageElementCell} :
    DomanialInsertion (CellData A source) (CellData A target) where
  map := mapCellData id
  preimage datum := some (mapCellData id datum)
  leftInverse _ := rfl

def dominionAtlas {A : Type} (D : Dominion A) : Atlas where
  pagination := onePagePagination
  cellData := CellData A
  data :=
    { action := { dataAt := fun element => constantDominion D element.val.cell
                  mapData := fun _ => identityCellInsertion }
      identity := fun _ _ => rfl
      composition := fun _ _ _ => rfl
      coherence := fun _ _ => rfl
      disjoint := by
        intro left right origin hpage hne
        exact (hne ((onePage_position left).trans (onePage_position right).symm)).elim }

/-- The primitive data action of the inclusion hom correspondence. The
component inverse is defined on all origin data, including uncovered data. -/
def coalitionMorphism {A : Type} (D : Dominion A) (X : Atlas)
    (forward : A → X.CertifiedCoalitionElement)
    (backward : X.cellData (FolioData.ValidElement.originElement X.pages).val.cell → Option A)
    (leftInverse : ∀ value, backward (forward value).value.val = some value) :
    PrimitiveAtlasMorphism (dominionAtlas D) X where
  object _ := FolioData.ValidElement.originElement X.pages
  component _ := coalitionComponentInsertion _ (fun value => (forward value).val)
    (fun value => (forward value).val.source.toOrigin) backward leftInverse
  arrow _ := 𝟙 _
  naturality := by
    intro x y f datum
    rw [X.data.identity]
    rfl

/-- The cached coverage presentation does not change the forward origin datum. -/
theorem coalitionMorphism_component {A : Type} (D : Dominion A) (X : Atlas)
    (forward : A → X.CertifiedCoalitionElement)
    (backward : X.cellData (FolioData.ValidElement.originElement X.pages).val.cell → Option A)
    (leftInverse : ∀ value, backward (forward value).value.val = some value)
    (source : (dominionAtlas D).Element) (datum : (dominionAtlas D).cellData source.val.cell) :
    ((coalitionMorphism D X forward backward leftInverse).component source).map datum =
      (forward datum.value).value.val := rfl

-- ALIGN: DOMINC-COVERAGE.
theorem dominionAtlas_covered {A : Type} (D : Dominion A) (element : (dominionAtlas D).Element)
    (datum : (dominionAtlas D).cellData element.val.cell) : (dominionAtlas D).Covered element datum :=
  ⟨singletonChain.chainIndexOf (), ⟨datum.value⟩, rfl⟩

def dominionCoalitionValue {A : Type} (D : Dominion A) (value : A) : (dominionAtlas D).CoalitionValue :=
  ⟨⟨value⟩, dominionAtlas_covered D _ _⟩

-- ALIGN: DOMINC-COALITION-EQUIVALENCE.
def coalitionValueEquiv {A : Type} (D : Dominion A) : (dominionAtlas D).CoalitionValue ≃ A where
  toFun c := c.val.value
  invFun := dominionCoalitionValue D
  left_inv _ := rfl
  right_inv _ := rfl

def coaDomIncCounit {A : Type} (D : Dominion A) : DomanialInsertion (dominionAtlas D).CoalitionValue A where
  map := coalitionValueEquiv D
  preimage value := some ((coalitionValueEquiv D).symm value)
  leftInverse c := congrArg some ((coalitionValueEquiv D).left_inv c)

def coaDomIncUnit {A : Type} (D : Dominion A) : DomanialInsertion A (dominionAtlas D).CoalitionValue where
  map := (coalitionValueEquiv D).symm
  preimage c := some (coalitionValueEquiv D c)
  leftInverse _ := rfl

-- ALIGN: DOMINC-COALITION-LEFT-INVERSE.
theorem coaDomInc_leftInverse {A : Type} (D : Dominion A) (c : (dominionAtlas D).CoalitionValue) :
    (coaDomIncCounit D).preimage ((coaDomIncCounit D).map c) = some c :=
  (coaDomIncCounit D).leftInverse c

-- ALIGN: DOMINC-COALITION-RIGHT-INVERSE.
theorem coaDomInc_rightInverse {A : Type} (D : Dominion A) (value : A) :
    (coaDomIncUnit D).preimage ((coaDomIncUnit D).map value) = some value := rfl

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
  .primitive (coalitionOrdered D X forward backward leftInverse) (fun covered =>
    ⟨(forward covered.val.datum.value).val.witness,
      (forward covered.val.datum.value).property.1.1, by
        change X.coverageWitnessCovers
          (FolioData.ValidElement.originElement X.pages).normalize
          (forward covered.val.datum.value).value.val
          (forward covered.val.datum.value).val.witness = true
        have h := Atlas.coalitionElementAt_coverage
          (forward covered.val.datum.value).val
          (FolioData.ValidElement.originElement X.pages)
          (forward covered.val.datum.value).val.source.toOrigin
          (forward covered.val.datum.value).property.1
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
