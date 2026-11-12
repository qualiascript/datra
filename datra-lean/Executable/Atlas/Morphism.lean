import Executable.Atlas.Elements
import Executable.Atlas.Normalized

namespace Datra.Executable
open CategoryTheory CategoryTheory.Idempotents
universe v w

/-- Materialized operations and symbolic arrows are distinct types. A symbolic
primitive may contain a whole materialized operation, as it does in Haskell. -/
inductive AtlasMorphism {Object : Type v} (Primitive : Object → Object → Type w) :
    Object → Object → Type (max v w)
  | primitive {X Y} : Primitive X Y → AtlasMorphism Primitive X Y
  | identity {X} : AtlasMorphism Primitive X X
  | composite {X Y Z} : AtlasMorphism Primitive Y Z → AtlasMorphism Primitive X Y →
      AtlasMorphism Primitive X Z

namespace AtlasMorphism
variable {Object : Type v} {Primitive : Object → Object → Type w}

noncomputable def evaluate (object : Object → NormalizedAtlas)
    (primitive : ∀ {X Y}, Primitive X Y → (object X ⟶ object Y))
    {X Y : Object} : AtlasMorphism Primitive X Y → (object X ⟶ object Y)
  | .primitive f => primitive f
  | .identity => 𝟙 _
  | .composite second first => evaluate object primitive first ≫ evaluate object primitive second

-- ALIGN: ATLAS-MATERIALIZED-IDENTITY.
theorem evaluate_identity (object : Object → NormalizedAtlas)
    (primitive : ∀ {X Y}, Primitive X Y → (object X ⟶ object Y)) (X : Object) :
    (evaluate object primitive (.identity : AtlasMorphism Primitive X X)).f = (object X).p := rfl

-- ALIGN: ATLAS-MATERIALIZED-COMPOSITION.
theorem evaluate_composite (object : Object → NormalizedAtlas)
    (primitive : ∀ {X Y}, Primitive X Y → (object X ⟶ object Y))
    {X Y Z : Object} (second : AtlasMorphism Primitive Y Z) (first : AtlasMorphism Primitive X Y) :
    (evaluate object primitive (.composite second first)).f =
      (evaluate object primitive first).f ≫ (object Y).p ≫ (evaluate object primitive second).f :=
  normalized_composition _ _

end AtlasMorphism

namespace AtlasHom
variable {Object : Type v} {Primitive : Object → Object → Type w}

def materialize {X Y : Object} : AtlasHom (AtlasMorphism Primitive) X Y → AtlasMorphism Primitive X Y
  | .primitive operation => operation
  | .identity => .identity
  | .composite second first => .composite second.materialize first.materialize

-- ALIGN: ATLASHOM-MATERIALIZE.
theorem evaluate_materialize (object : Object → NormalizedAtlas)
    (primitive : ∀ {X Y}, Primitive X Y → (object X ⟶ object Y))
    {X Y : Object} (hom : AtlasHom (AtlasMorphism Primitive) X Y) :
    AtlasMorphism.evaluate object primitive hom.materialize =
      evaluate object (AtlasMorphism.evaluate object primitive) hom := by
  induction hom with
  | primitive => rfl
  | identity => rfl
  | composite second first ih₂ ih₁ =>
      simp only [materialize, AtlasMorphism.evaluate, evaluate, ih₁, ih₂]

theorem materialize_presheafCompose (object : Object → NormalizedAtlas)
    (primitive : ∀ {X Y}, Primitive X Y → (object X ⟶ object Y))
    {X Y Z : Object} (second : AtlasHom (AtlasMorphism Primitive) Y Z)
    (first : AtlasHom (AtlasMorphism Primitive) X Y) :
    AtlasMorphism.evaluate object primitive (presheafCompose second first).materialize =
      AtlasMorphism.evaluate object primitive first.materialize ≫
        AtlasMorphism.evaluate object primitive second.materialize := by
  simp only [evaluate_materialize, evaluate_presheafCompose]

end AtlasHom
end Datra.Executable
namespace Datra.Executable
open CategoryTheory

/-- The primitive object operation is normalized at both boundaries. -/
def normalizedObject {X Y : Atlas} (object : X.Element → Y.Element) (x : X.Element) : Y.Element :=
  (object x.normalize).normalize

/-- The object-map symbol is interpreted by `object`. Its dependent component
retains the corresponding target cell, and its two witnesses are the checked
page-arrow and normalized data-naturality contracts. -/
structure PrimitiveAtlasMorphism (X Y : Atlas) where
  object : X.Element → Y.Element
  component : (x : X.Element) →
    DomanialInsertion (X.cellData x.val.cell) (Y.cellData (object x).val.cell)
  arrow : ∀ {x y : X.Element}, (x ⟶ y) →
    (normalizedObject object x ⟶ normalizedObject object y)
  naturality : ∀ {x y : X.Element} (f : x ⟶ y) (datum : X.cellData x.val.cell),
    (component y.normalize).map ((X.data.action.normalizedMap f).map datum) =
      (Y.data.action.normalizedMap (arrow f)).map ((component x.normalize).map datum)

namespace PrimitiveAtlasMorphism
variable {X Y : Atlas}

-- ALIGN: ATLAS-PRIMITIVE-PAGE-FUNCTOR.
def pageFunctor (f : PrimitiveAtlasMorphism X Y) : X.Element ⥤ Y.Element where
  obj := normalizedObject f.object
  map := f.arrow
  map_id := fun _ => Subsingleton.elim _ _
  map_comp := fun _ _ => Subsingleton.elim _ _

-- ALIGN: ATLAS-PRIMITIVE-NATURALITY.
def dataTransformation (f : PrimitiveAtlasMorphism X Y) :
    X.data.toFunctor ⟶ f.pageFunctor ⋙ Y.data.toFunctor where
  app x := (f.component x.normalize).toSemantics
  naturality {x y} q := by
    apply Function.Embedding.ext
    intro datum
    exact f.naturality q datum

theorem source_normalized (f : PrimitiveAtlasMorphism X Y) (x : X.Element) :
    f.pageFunctor.obj x.normalize = f.pageFunctor.obj x := by
  simp only [pageFunctor, normalizedObject, FolioData.ValidElement.normalize_idempotent]

theorem target_normalized (f : PrimitiveAtlasMorphism X Y) (x : X.Element) :
    (f.pageFunctor.obj x).normalize = f.pageFunctor.obj x :=
  FolioData.ValidElement.normalize_idempotent _

theorem component_normalized (f : PrimitiveAtlasMorphism X Y) (x : X.Element) :
    HEq (f.component x.normalize.normalize) (f.component x.normalize) := by
  rw [FolioData.ValidElement.normalize_idempotent]

noncomputable def finitePageFunctor (f : PrimitiveAtlasMorphism X Y) :
    X.toSemantics.El ⥤ Y.toSemantics.El :=
  FolioData.ValidElement.fromFinite X.pages ⋙ f.pageFunctor ⋙
    (FolioData.ValidElement.elementsEquivalence Y.pages).functor ⋙ Y.pages.toSemantics.collapseElements

private theorem finiteTarget_eq (f : PrimitiveAtlasMorphism X Y) (x : X.Element) :
    (FolioData.ValidElement.fromFinite Y.pages).obj (Y.pages.toSemantics.collapseElements.obj
      ((FolioData.ValidElement.elementsEquivalence Y.pages).functor.obj (f.pageFunctor.obj x))) =
      f.pageFunctor.obj x :=
  (FolioData.ValidElement.fromFinite_collapse _).trans (f.target_normalized x)

noncomputable def finiteDataTransformation (f : PrimitiveAtlasMorphism X Y) :
    X.toSemantics.Da ⟶ f.finitePageFunctor ⋙ Y.toSemantics.Da where
  app x := f.dataTransformation.app ((FolioData.ValidElement.fromFinite X.pages).obj x) ≫
    Y.data.toFunctor.map (eqToHom (f.finiteTarget_eq _).symm)
  naturality := by
    intro x y q
    let I := FolioData.ValidElement.fromFinite X.pages
    let J := FolioData.ValidElement.fromFinite Y.pages
    let R := (FolioData.ValidElement.elementsEquivalence Y.pages).functor ⋙
      Y.pages.toSemantics.collapseElements
    change X.data.toFunctor.map (I.map q) ≫
        (f.dataTransformation.app (I.obj y) ≫ Y.data.toFunctor.map (eqToHom (f.finiteTarget_eq _).symm)) =
      (f.dataTransformation.app (I.obj x) ≫ Y.data.toFunctor.map (eqToHom (f.finiteTarget_eq _).symm)) ≫
        Y.data.toFunctor.map (J.map (R.map (f.pageFunctor.map (I.map q))))
    rw [← Category.assoc, f.dataTransformation.naturality, Category.assoc]
    simp only [Functor.comp_map]
    have he : f.pageFunctor.map (I.map q) ≫ eqToHom (f.finiteTarget_eq _).symm =
        eqToHom (f.finiteTarget_eq _).symm ≫ J.map (R.map (f.pageFunctor.map (I.map q))) :=
      Subsingleton.elim _ _
    rw [← Y.data.toFunctor.map_comp, he, Y.data.toFunctor.map_comp, Category.assoc]

-- ALIGN: ATLAS-PRIMITIVE-INTERPRETATION.
noncomputable def toSemantics (f : PrimitiveAtlasMorphism X Y) : X.toSemantics ⟶ Y.toSemantics where
  Pa := f.finitePageFunctor
  Da := f.finiteDataTransformation

noncomputable def toNormalized (f : PrimitiveAtlasMorphism X Y) :
    normalizedAtlas X.toSemantics ⟶ normalizedAtlas Y.toSemantics := normalizedHom f.toSemantics

-- ALIGN: ATLAS-PRIMITIVE-PAGE-INTERPRETATION.
theorem page_interpretation (f : PrimitiveAtlasMorphism X Y) (x : X.Element) :
    f.toSemantics.tall.Pa.obj ((FolioData.ValidElement.elementsEquivalence X.pages).functor.obj x) =
      (FolioData.ValidElement.elementsEquivalence Y.pages).functor.obj (f.pageFunctor.obj x) := by
  change Y.pages.toSemantics.includeElements.obj (Y.pages.toSemantics.collapseElements.obj
    ((FolioData.ValidElement.elementsEquivalence Y.pages).functor.obj
      (f.pageFunctor.obj ((FolioData.ValidElement.fromFinite X.pages).obj
        (X.pages.toSemantics.collapseElements.obj
          ((FolioData.ValidElement.elementsEquivalence X.pages).functor.obj x)))))) = _
  rw [FolioData.ValidElement.fromFinite_collapse, f.source_normalized,
    ← FolioData.ValidElement.normalize_toSemantics, f.target_normalized]

-- ALIGN: ATLAS-PRIMITIVE-DATA-INTERPRETATION.
theorem data_interpretation (f : PrimitiveAtlasMorphism X Y) (x : X.toSemantics.El) :
    HEq (f.finiteDataTransformation.app x)
      (f.dataTransformation.app ((FolioData.ValidElement.fromFinite X.pages).obj x)) :=
  Datra.Semantics.embedding_comp_map_eqToHom_heq Y.data.toFunctor (f.finiteTarget_eq _).symm _

end PrimitiveAtlasMorphism
end Datra.Executable

namespace Datra.Executable.Atlas
open CategoryTheory

/-- The concrete materialized and symbolic types instantiate the shared syntax
with checked primitive actions on owned executable Atlases. -/
abbrev Morphism := AtlasMorphism PrimitiveAtlasMorphism
abbrev Hom := AtlasHom Morphism

noncomputable def Morphism.toSemantics {X Y : Atlas} (f : Morphism X Y) :
    normalizedAtlas X.toSemantics ⟶ normalizedAtlas Y.toSemantics :=
  AtlasMorphism.evaluate (Object := Atlas) (Primitive := PrimitiveAtlasMorphism)
    (fun X : Atlas => normalizedAtlas X.toSemantics) (@PrimitiveAtlasMorphism.toNormalized) f

def Hom.materialize {X Y : Atlas} (f : Hom X Y) : Morphism X Y := AtlasHom.materialize f

noncomputable def Hom.toSemantics {X Y : Atlas} (f : Hom X Y) :
    normalizedAtlas X.toSemantics ⟶ normalizedAtlas Y.toSemantics :=
  Morphism.toSemantics (Hom.materialize f)

/-- Evaluate the runtime object operation without passing through Mathlib. -/
def Morphism.mapObject {X Y : Atlas} : Morphism X Y → X.Element → Y.Element
  | .primitive operation, x => normalizedObject operation.object x
  | .identity, x => x.normalize
  | .composite second first, x => (Morphism.mapObject second) ((Morphism.mapObject first) x)

theorem Morphism.mapObject_source_normalized {X Y : Atlas} (f : Morphism X Y) (x : X.Element) :
    f.mapObject x.normalize = f.mapObject x := by
  induction f with
  | primitive f => exact f.source_normalized x
  | identity => exact x.normalize_idempotent
  | composite second first ih₂ ih₁ =>
      simp only [mapObject, ih₁]

theorem Morphism.mapObject_target_normalized {X Y : Atlas} (f : Morphism X Y) (x : X.Element) :
    (f.mapObject x).normalize = f.mapObject x := by
  induction f with
  | primitive f => exact f.target_normalized x
  | identity => exact x.normalize_idempotent
  | composite second first ih₂ ih₁ => exact ih₂ ((Morphism.mapObject first) x)

-- ALIGN: ATLAS-MATERIALIZED-OBJECT-INTERPRETATION.
theorem Morphism.mapObject_interpretation {X Y : Atlas} (f : Morphism X Y) (x : X.Element) :
    (FolioData.ValidElement.elementsEquivalence Y.pages).functor.obj (f.mapObject x) =
      f.toSemantics.f.Pa.obj ((FolioData.ValidElement.elementsEquivalence X.pages).functor.obj x) := by
  induction f with
  | primitive f => exact (f.page_interpretation x).symm
  | identity => exact FolioData.ValidElement.normalize_toSemantics x
  | composite second first ih₂ ih₁ =>
      change (FolioData.ValidElement.elementsEquivalence _).functor.obj
        ((Morphism.mapObject second) ((Morphism.mapObject first) x)) =
        (Morphism.toSemantics second).f.Pa.obj ((Morphism.toSemantics first).f.Pa.obj
          ((FolioData.ValidElement.elementsEquivalence _).functor.obj x))
      rw [ih₂, ih₁]

def Hom.mapObject {X Y : Atlas} (f : Hom X Y) (x : X.Element) : Y.Element :=
  f.materialize.mapObject x

def TransposalElement.mapMorphism {X Y : Atlas} (f : Morphism X Y) (x : X.TransposalElement) :
    Y.TransposalElement := ⟨f.mapObject x.val, f.mapObject_target_normalized x.val⟩

def TransposalElement.mapHom {X Y : Atlas} (f : Hom X Y) (x : X.TransposalElement) :
    Y.TransposalElement := mapMorphism f.materialize x

theorem TransposalElement.mapHom_evaluate {X Y : Atlas} (f : Hom X Y) (x : X.TransposalElement) :
    mapHom f x = AtlasHom.evaluate (fun X : Atlas => X.TransposalElement)
      (@mapMorphism) f x := by
  induction f with
  | primitive f => rfl
  | identity => exact Subtype.ext x.property
  | composite second first ih₂ ih₁ =>
      change mapHom second (mapHom first x) = _
      rw [ih₂, ih₁]
      rfl

theorem TransposalElement.mapHom_compose {X Y Z : Atlas} (second : Hom Y Z) (first : Hom X Y)
    (x : X.TransposalElement) :
    mapHom (AtlasHom.composeAtlasHoms second first) x = mapHom second (mapHom first x) := by
  simp only [mapHom_evaluate, AtlasHom.evaluate_composeAtlasHoms]
  rfl

noncomputable def Hom.finiteSemantics {X Y : Atlas} (f : Hom X Y) : X.toSemantics ⟶ Y.toSemantics :=
  restrictTall f.toSemantics.f

-- ALIGN: ATLAS-SYMBOLIC-OBJECT-INTERPRETATION.
theorem TransposalElement.mapHom_interpretation {X Y : Atlas} (f : Hom X Y)
    (x : X.TransposalElement) :
    (mapHom f x).toSemantics = f.finiteSemantics.Pa.obj x.toSemantics := by
  have hx := FolioData.ValidElement.normalize_toSemantics x.val
  rw [x.property] at hx
  unfold toSemantics mapHom
  change Y.pages.toSemantics.collapseElements.obj
      ((FolioData.ValidElement.elementsEquivalence Y.pages).functor.obj (f.materialize.mapObject x.val)) =
    Y.pages.toSemantics.collapseElements.obj (f.toSemantics.f.Pa.obj
      (X.pages.toSemantics.includeElements.obj
        (X.pages.toSemantics.collapseElements.obj
          ((FolioData.ValidElement.elementsEquivalence X.pages).functor.obj x.val))))
  rw [f.materialize.mapObject_interpretation]
  exact congrArg (fun z => Y.pages.toSemantics.collapseElements.obj (f.toSemantics.f.Pa.obj z)) hx

-- ALIGN: ATLAS-CONCRETE-IDENTITY.
theorem Hom.identity_coherence (X : Atlas) :
    (Hom.toSemantics (.identity : Hom X X)).f = X.toSemantics.coherence := rfl

-- ALIGN: ATLAS-CONCRETE-COMPOSITION.
theorem Hom.composition {X Y Z : Atlas} (second : Hom Y Z) (first : Hom X Y) :
    Hom.toSemantics (AtlasHom.presheafCompose second first) =
      Hom.toSemantics first ≫ Hom.toSemantics second :=
  AtlasHom.materialize_presheafCompose (fun X : Atlas => normalizedAtlas X.toSemantics)
    (@PrimitiveAtlasMorphism.toNormalized) second first

theorem Hom.categoricalComposition {X Y Z : Atlas} (second : Hom Y Z) (first : Hom X Y) :
    Hom.toSemantics (AtlasHom.composeAtlasHoms second first) =
      Hom.toSemantics first ≫ Hom.toSemantics second := by
  simp only [Hom.toSemantics, Hom.materialize, Morphism.toSemantics,
    AtlasHom.evaluate_materialize, AtlasHom.evaluate_composeAtlasHoms]

theorem Hom.normalized_finiteSemantics {X Y : Atlas} (f : Hom X Y) :
    normalizedHom f.finiteSemantics = f.toSemantics :=
  (normalizedHomEquiv X.toSemantics Y.toSemantics).apply_symm_apply f.toSemantics

theorem Hom.finiteSemantics_identity (X : Atlas) :
    Hom.finiteSemantics (.identity : Hom X X) = 𝟙 X.toSemantics :=
  restrictTall_tall (𝟙 X.toSemantics)

theorem Hom.finiteSemantics_compose {X Y Z : Atlas} (second : Hom Y Z) (first : Hom X Y) :
    Hom.finiteSemantics (AtlasHom.composeAtlasHoms second first) =
      first.finiteSemantics ≫ second.finiteSemantics := by
  apply finiteToNormalized.map_injective
  change normalizedHom _ = normalizedHom _
  rw [Hom.normalized_finiteSemantics, Hom.categoricalComposition]
  exact (congrArg₂ (fun f g => f ≫ g) first.normalized_finiteSemantics.symm
    second.normalized_finiteSemantics.symm).trans
      (finiteToNormalized.map_comp first.finiteSemantics second.finiteSemantics).symm

/-- The dependent insertion returned by mapAtlasMorphismData. Its partial
inverse is retained, including through composition. -/
def Morphism.component {X Y : Atlas} : (f : Morphism X Y) → (x : X.Element) →
    DomanialInsertion (X.cellData x.val.cell) (Y.cellData (f.mapObject x).val.cell)
  | .primitive operation, x => operation.component x.normalize
  | .identity, _ => DomanialInsertion.identity _
  | .composite second first, x =>
      (Morphism.component first x).comp
        (Morphism.component second (Morphism.mapObject first x))

abbrev DataElement (X : Atlas) := (x : X.Element) × X.cellData x.val.cell
abbrev SemanticDataElement (X : Atlas) := (x : X.toSemantics.El) × X.toSemantics.Da.obj x

def Morphism.mapData {X Y : Atlas} (f : Morphism X Y) (source : X.DataElement) : Y.DataElement :=
  ⟨f.mapObject source.1, (f.component source.1).map source.2⟩

noncomputable def fromSemanticData (X : Atlas) (source : X.SemanticDataElement) : X.DataElement :=
  ⟨(FolioData.ValidElement.fromFinite X.pages).obj source.1, source.2⟩

def mapSemanticData {X Y : Atlas} (f : X.toSemantics ⟶ Y.toSemantics)
    (source : X.SemanticDataElement) : Y.SemanticDataElement :=
  ⟨f.Pa.obj source.1, f.Da.app source.1 source.2⟩

noncomputable def Morphism.finiteSemantics {X Y : Atlas} : Morphism X Y → (X.toSemantics ⟶ Y.toSemantics)
  | .primitive operation => operation.toSemantics
  | .identity => 𝟙 _
  | .composite second first => Morphism.finiteSemantics first ≫ Morphism.finiteSemantics second

theorem Morphism.normalized_finiteSemantics {X Y : Atlas} (f : Morphism X Y) :
    normalizedHom f.finiteSemantics = f.toSemantics := by
  induction f with
  | primitive => rfl
  | identity => rfl
  | composite second first ih₂ ih₁ =>
      change normalizedHom (Morphism.finiteSemantics first ≫ Morphism.finiteSemantics second) = _
      rw [show normalizedHom (Morphism.finiteSemantics first ≫ Morphism.finiteSemantics second) =
          normalizedHom (Morphism.finiteSemantics first) ≫ normalizedHom (Morphism.finiteSemantics second)
          from finiteToNormalized.map_comp _ _]
      rw [ih₁, ih₂]
      rfl

-- ALIGN: ATLAS-MATERIALIZED-DATA-INTERPRETATION.
theorem Morphism.mapData_interpretation {X Y : Atlas} (f : Morphism X Y) (source : X.SemanticDataElement) :
    fromSemanticData Y (mapSemanticData f.finiteSemantics source) =
      f.mapData (fromSemanticData X source) := by
  induction f with
  | @primitive A B operation =>
      obtain ⟨x, datum⟩ := source
      apply Sigma.ext
      · exact operation.finiteTarget_eq ((FolioData.ValidElement.fromFinite _).obj x)
      · have map_eqToHom_apply {C : Type 1} [Category.{0} C] (G : C ⥤ Datra.Semantics.DomIns)
            {a b : C} (h : a = b) (value : G.obj a) :
            HEq (G.map (eqToHom h) value) value := by
          cases h
          simp only [eqToHom_refl]
          rw [G.map_id]
          rfl
        change HEq
          (B.data.toFunctor.map (eqToHom (operation.finiteTarget_eq _).symm)
            ((operation.component ((FolioData.ValidElement.fromFinite _).obj x).normalize).map datum))
          ((operation.component ((FolioData.ValidElement.fromFinite _).obj x).normalize).map datum)
        exact map_eqToHom_apply _ (operation.finiteTarget_eq _).symm _
  | identity =>
      obtain ⟨x, datum⟩ := source
      apply Sigma.ext
      · exact (FolioData.ValidElement.normalize_fromFinite _ x).symm
      · rfl
  | composite second first ih₂ ih₁ =>
      change fromSemanticData _ (mapSemanticData (Morphism.finiteSemantics second)
          (mapSemanticData (Morphism.finiteSemantics first) source)) =
        Morphism.mapData second (Morphism.mapData first (fromSemanticData _ source))
      rw [ih₂, ih₁]

theorem Hom.finiteSemantics_materialize {X Y : Atlas} (f : Hom X Y) :
    f.finiteSemantics = f.materialize.finiteSemantics := by
  change restrictTall f.materialize.toSemantics.f = _
  rw [← f.materialize.normalized_finiteSemantics]
  exact restrictTall_tall _

def Hom.mapData {X Y : Atlas} (f : Hom X Y) (source : X.DataElement) : Y.DataElement :=
  f.materialize.mapData source

-- ALIGN: ATLASHOM-DATA-INTERPRETATION.
theorem Hom.mapData_interpretation {X Y : Atlas} (f : Hom X Y) (source : X.SemanticDataElement) :
    fromSemanticData Y (mapSemanticData f.finiteSemantics source) =
      f.mapData (fromSemanticData X source) := by
  rw [f.finiteSemantics_materialize]
  exact f.materialize.mapData_interpretation source

end Datra.Executable.Atlas
