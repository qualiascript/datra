import Semantics
import Executable.Atlas.Syntax

namespace Datra.Executable
open CategoryTheory CategoryTheory.Idempotents

/-- The runtime identity lives in the split-idempotent category of tall Atlases. -/
abbrev NormalizedAtlas := Karoubi Datra.Semantics.TallAtlas

noncomputable def normalizedAtlas (X : Datra.Semantics.Atl) : NormalizedAtlas :=
  ⟨X.tall, X.coherence, X.coherence_idempotent⟩

noncomputable def normalizedHom {X Y : Datra.Semantics.Atl} (f : X ⟶ Y) :
    normalizedAtlas X ⟶ normalizedAtlas Y :=
  ⟨f.tall, by
    change X.coherence ≫ f.tall ≫ Y.coherence = f.tall
    rw [← Category.assoc, Datra.Semantics.AtlHom.coherence_left, Datra.Semantics.AtlHom.coherence_right]⟩

/-- The finite interpretation lands at the particular normalization idempotent,
not at the raw identity of the tall Atlas. -/
noncomputable def finiteToNormalized : Datra.Semantics.Atl ⥤ NormalizedAtlas where
  obj := normalizedAtlas
  map := normalizedHom
  map_id _ := rfl
  map_comp f g := Karoubi.hom_ext _ _ (Datra.Semantics.AtlHom.tall_comp f g)

-- ALIGN: ATLAS-IDENTITY-COHERENCE.
theorem normalized_identity (X : Datra.Semantics.Atl) :
    (𝟙 (normalizedAtlas X) : normalizedAtlas X ⟶ normalizedAtlas X).f =
      X.coherence := rfl

-- ALIGN: ATLAS-COMPOSE-COHERENCE.
theorem normalized_composition {X Y Z : NormalizedAtlas}
    (first : X ⟶ Y) (second : Y ⟶ Z) :
    (first ≫ second).f = first.f ≫ Y.p ≫ second.f := by simp

namespace AtlasHom
universe v w u
variable {Object : Type v} {Primitive : Object → Object → Type w}
variable {C : Type u} [Category C]

/-- Interpret syntax in any category. Instantiating C with NormalizedAtlas
makes the identity case coherence and the composite case middle-coherent. -/
def evaluate (object : Object → C)
    (primitive : ∀ {X Y}, Primitive X Y → (object X ⟶ object Y))
    {X Y : Object} : AtlasHom Primitive X Y → (object X ⟶ object Y)
  | .primitive f => primitive f
  | .identity => 𝟙 _
  | .composite second first => evaluate object primitive first ≫ evaluate object primitive second

-- ALIGN: ATLASHOM-MATERIALIZE-COMPOSE.
theorem evaluate_presheafCompose (object : Object → C)
    (primitive : ∀ {X Y}, Primitive X Y → (object X ⟶ object Y))
    {X Y Z : Object} (second : AtlasHom Primitive Y Z) (first : AtlasHom Primitive X Y) :
    evaluate object primitive (presheafCompose second first) =
      evaluate object primitive first ≫ evaluate object primitive second := by
  induction first with
  | identity => simp [presheafCompose, evaluate]
  | primitive _ => rfl
  | composite middle first ih _ =>
      simp only [presheafCompose, evaluate, ih, Category.assoc]

theorem evaluate_composeAtlasHoms (object : Object → C)
    (primitive : ∀ {X Y}, Primitive X Y → (object X ⟶ object Y))
    {X Y Z : Object} (second : AtlasHom Primitive Y Z) (first : AtlasHom Primitive X Y) :
    evaluate object primitive (composeAtlasHoms second first) =
      evaluate object primitive first ≫ evaluate object primitive second := by
  induction first with
  | identity => cases second <;> simp [composeAtlasHoms, evaluate]
  | primitive _ => cases second <;> simp [composeAtlasHoms, evaluate]
  | composite middle first ih _ =>
      cases second <;> simp_all [composeAtlasHoms, evaluate, Category.assoc]

/-- Both Haskell compositions have the same interpretation, despite differing
as syntax when the left operand is identity. -/
theorem compositions_agree (object : Object → C)
    (primitive : ∀ {X Y}, Primitive X Y → (object X ⟶ object Y))
    {X Y Z : Object} (second : AtlasHom Primitive Y Z) (first : AtlasHom Primitive X Y) :
    evaluate object primitive (presheafCompose second first) =
      evaluate object primitive (composeAtlasHoms second first) := by
  rw [evaluate_presheafCompose, evaluate_composeAtlasHoms]
end AtlasHom

end Datra.Executable

namespace Datra.Executable
open CategoryTheory

/-- Restrict a tall data transformation to genuine source cells, then collapse
its target cells to the finite target presentation. -/
noncomputable def restrictTall {X Y : Datra.Semantics.Atl} (f : X.tall ⟶ Y.tall) : X ⟶ Y where
  Pa := X.Fo.includeElements ⋙ f.Pa ⋙ Y.Fo.collapseElements
  Da :=
    { app := fun x =>
        X.Da.map (eqToHom (X.Fo.collapse_include_obj x).symm) ≫
          f.Da.app (X.Fo.includeElements.obj x)
      naturality := by
        intro x y q
        dsimp
        rw [← Category.assoc]
        have he : q ≫ eqToHom (X.Fo.collapse_include_obj y).symm =
            eqToHom (X.Fo.collapse_include_obj x).symm ≫
              X.Fo.collapseElements.map (X.Fo.includeElements.map q) := Subsingleton.elim _ _
        rw [← X.Da.map_comp, he, X.Da.map_comp, Category.assoc]
        have hn := f.Da.naturality (X.Fo.includeElements.map q)
        change X.Da.map (X.Fo.collapseElements.map (X.Fo.includeElements.map q)) ≫
          f.Da.app (X.Fo.includeElements.obj y) =
          f.Da.app (X.Fo.includeElements.obj x) ≫
            Y.Da.map (Y.Fo.collapseElements.map (f.Pa.map (X.Fo.includeElements.map q))) at hn
        rw [hn, Category.assoc] }

end Datra.Executable

namespace Datra.Executable
open CategoryTheory

-- ALIGN: ATLAS-RESTRICT-TALL.
theorem restrictTall_tall {X Y : Datra.Semantics.Atl} (f : X ⟶ Y) : restrictTall f.tall = f := by
  have hPa : (restrictTall f.tall).Pa = f.Pa := by
    exact CategoryTheory.Functor.ext (F := (restrictTall f.tall).Pa) (G := f.Pa)
      (fun x => by
        change Y.Fo.collapseElements.obj (Y.Fo.includeElements.obj
          (f.Pa.obj (X.Fo.collapseElements.obj (X.Fo.includeElements.obj x)))) = f.Pa.obj x
        rw [Y.Fo.collapse_include_obj, X.Fo.collapse_include_obj])
  apply Datra.Semantics.AtlHom.ext _ _ hPa
  apply Datra.Semantics.NatTrans.hext_right _ _ (congrArg (fun P => P ⋙ Y.Da) hPa)
  intro x
  let x₀ := X.Fo.collapseElements.obj (X.Fo.includeElements.obj x)
  let ex : x = x₀ := (X.Fo.collapse_include_obj x).symm
  let ey : f.Pa.obj x₀ = Y.Fo.collapseElements.obj (Y.Fo.includeElements.obj (f.Pa.obj x₀)) :=
    (Y.Fo.collapse_include_obj _).symm
  let ez := (congrArg f.Pa.obj ex).trans ey
  change HEq (X.Da.map (eqToHom ex) ≫
    (f.Da.app x₀ ≫ Y.Da.map (eqToHom ey))) (f.Da.app x)
  rw [← Category.assoc, f.Da.naturality, Category.assoc]
  simp only [Functor.comp_map]
  rw [← Y.Da.map_comp]
  have he : f.Pa.map (eqToHom ex) ≫ eqToHom ey = eqToHom ez := Subsingleton.elim _ _
  rw [he]
  exact Datra.Semantics.embedding_comp_map_eqToHom_heq Y.Da ez _

instance finiteToNormalized_faithful : finiteToNormalized.Faithful where
  map_injective {X Y} f g h := by
    have ht : f.tall = g.tall := congrArg CategoryTheory.Idempotents.Karoubi.Hom.f h
    have hr := congrArg restrictTall ht
    simpa only [restrictTall_tall] using hr

end Datra.Executable

namespace Datra.Executable
open CategoryTheory CategoryTheory.Idempotents

-- ALIGN: ATLAS-TALL-RESTRICT.
theorem tall_restrictTall {X Y : Datra.Semantics.Atl} (f : X.tall ⟶ Y.tall) :
    (restrictTall f).tall = X.coherence ≫ f ≫ Y.coherence := by
  apply Datra.Semantics.TallAtlasHom.ext
  · rfl
  · change HEq (restrictTall f).tall.Da
      (Datra.Semantics.TallAtlasHom.comp (Datra.Semantics.TallAtlasHom.comp X.coherence f) Y.coherence).Da
    apply heq_of_eq
    ext x
    simp [restrictTall, Datra.Semantics.AtlHom.tall, Datra.Semantics.AtlHom.tallPa, Datra.Semantics.AtlHom.tallDa,
      Datra.Semantics.Atl.coherence, Datra.Semantics.AtlHom.identity, Datra.Semantics.TallAtlasHom.comp, Category.assoc]
    rfl

instance finiteToNormalized_full : finiteToNormalized.Full where
  map_surjective {X Y} f := by
    refine ⟨restrictTall f.f, ?_⟩
    apply Karoubi.hom_ext
    change (restrictTall f.f).tall = f.f
    rw [tall_restrictTall]
    exact f.comm

/-- The normalized full-spine morphisms between finite presentations have
exactly the finite morphisms as representatives. -/
noncomputable def normalizedHomEquiv (X Y : Datra.Semantics.Atl) :
    (X ⟶ Y) ≃ (normalizedAtlas X ⟶ normalizedAtlas Y) where
  toFun := normalizedHom
  invFun := fun f => restrictTall f.f
  left_inv := restrictTall_tall
  right_inv f := by
    apply Karoubi.hom_ext
    change (restrictTall f.f).tall = f.f
    rw [tall_restrictTall]
    exact f.comm

end Datra.Executable

namespace Datra.Executable
open CategoryTheory

/-- Canonical finite presentations, with their normalized full-spine morphisms.
Arbitrary unrelated idempotents in the ambient Karoubi category are excluded. -/
abbrev FiniteSpineAtlas := InducedCategory NormalizedAtlas normalizedAtlas

noncomputable def finiteToSpine : Datra.Semantics.Atl ⥤ FiniteSpineAtlas where
  obj X := X
  map := normalizedHom
  map_id X := finiteToNormalized.map_id X
  map_comp f g := finiteToNormalized.map_comp f g

instance finiteToSpine_isEquivalence : finiteToSpine.IsEquivalence where
  faithful := ⟨fun h => finiteToNormalized.map_injective h⟩
  full := ⟨fun f => ⟨restrictTall f.f, (normalizedHomEquiv _ _).apply_symm_apply f⟩⟩
  essSurj := ⟨fun X => ⟨X, ⟨Iso.refl X⟩⟩⟩

-- ALIGN: ATLAS-FINITE-NORMALIZED-EQUIVALENCE.
noncomputable def finiteSpineEquivalence : Datra.Semantics.Atl ≌ FiniteSpineAtlas :=
  finiteToSpine.asEquivalence

end Datra.Executable
