import Executable.Atlas.DomanialInclusion

namespace Datra.Executable.EmptyAtlas
open CategoryTheory

/-- The empty Haskell data family retains its phantom cell index. -/
inductive Datum (_cell : PageElementCell) : Type

def absurdDatum {cell : PageElementCell} {Result : Sort*} (datum : Datum cell) : Result :=
  nomatch datum

def dominionAt (cell : PageElementCell) : Dominion (Datum cell) where
  rank := absurdDatum
  unrank _ := none
  coherence datum := absurdDatum datum

def dataMap {source target : PageElementCell} : DomanialInsertion (Datum source) (Datum target) where
  map := absurdDatum
  preimage _ := none
  leftInverse datum := absurdDatum datum

/-- One singleton page, an uninhabited datum family, and the empty partial
inverse on every data arrow, exactly as the runtime empty Atlas constructor. -/
def emptyAtlas : Atlas where
  pagination := DomanialInclusion.onePagePagination
  cellData := Datum
  data :=
    { action := { dataAt := fun occurrence => dominionAt occurrence.val.cell
                  mapData := fun _ => dataMap }
      identity := fun _ datum => absurdDatum datum
      composition := fun _ _ datum => absurdDatum datum
      coherence := fun _ datum => absurdDatum datum
      disjoint := fun _ _ _ _ _ _ datum => absurdDatum datum }

/-- The rank-polymorphic Haskell eliminator is indexed by the generated
Atlas in Lean, so its callback cannot confuse it with a different owner. -/
-- ALIGN: EMPTY-ATLAS-CONSTRUCTOR.
def withEmptyAtlas {Result : Sort*} (useAtlas : (X : Atlas) → X = emptyAtlas → Result) : Result :=
  useAtlas emptyAtlas rfl

-- ALIGN: EMPTY-ATLAS-NO-DATA.
theorem emptyAtlas_noData (source : emptyAtlas.Element) (datum : emptyAtlas.cellData source.val.cell) : False :=
  absurdDatum datum

-- ALIGN: EMPTY-ATLAS-UNRANK.
theorem emptyAtlas_unrank (source : emptyAtlas.Element) (n : Nat) :
    (emptyAtlas.dataAt source).unrank n = none := rfl

-- ALIGN: EMPTY-ATLAS-PREIMAGE.
theorem emptyAtlas_preimage {source target : emptyAtlas.Element} (arrow : source ⟶ target)
    (datum : emptyAtlas.cellData target.val.cell) :
    (emptyAtlas.data.action.normalizedMap arrow).preimage datum = none := rfl

noncomputable def inclusionHom :
    emptyAtlas.toSemantics ⟶ (DomanialInclusion.dominionAtlas DomanialInclusion.emptyDominion).toSemantics where
  Pa := 𝟭 _
  Da :=
    { app := fun _ => ⟨absurdDatum, fun datum _ _ => absurdDatum datum⟩
      naturality := by intros; apply Function.Embedding.ext; intro datum; exact absurdDatum datum }

noncomputable def inclusionInv :
    (DomanialInclusion.dominionAtlas DomanialInclusion.emptyDominion).toSemantics ⟶ emptyAtlas.toSemantics where
  Pa := 𝟭 _
  Da :=
    { app := fun _ => ⟨fun datum => Empty.elim datum.value, fun datum _ _ => Empty.elim datum.value⟩
      naturality := by intros; apply Function.Embedding.ext; intro datum; exact Empty.elim datum.value }

noncomputable def inclusionIso :
    emptyAtlas.toSemantics ≅ (DomanialInclusion.dominionAtlas DomanialInclusion.emptyDominion).toSemantics where
  hom := inclusionHom
  inv := inclusionInv
  hom_inv_id := by
    apply Atlas.semanticHom_ext
    · exact CategoryTheory.Functor.ext (fun _ => rfl)
    · intro datum
      exact absurdDatum datum.2
  inv_hom_id := by
    apply Atlas.semanticHom_ext
    · exact CategoryTheory.Functor.ext (fun _ => rfl)
    · intro datum
      exact Empty.elim datum.2.value

/-- The executable empty Atlas denotes the written `DomInc(∅)` object. -/
-- ALIGN: EMPTY-ATLAS-INTERPRETATION.
noncomputable def interpretationIso : emptyAtlas.toSemantics ≅ Datra.Semantics.AtlI :=
  inclusionIso ≪≫ DomanialInclusion.interpretationIso DomanialInclusion.emptyDominion

noncomputable def inclusionStableIso :
    (WideSubcategory.mk (WideSubcategory.mk emptyAtlas.toSemantics) : Datra.Semantics.StaAtlTrav) ≅
    WideSubcategory.mk (WideSubcategory.mk
      (DomanialInclusion.dominionAtlas DomanialInclusion.emptyDominion).toSemantics) where
  hom := ⟨⟨inclusionHom, ⟨⟨Function.injective_id, fun _ _ h => h⟩,
    fun c => absurdDatum c.datum⟩⟩, rfl⟩
  inv := ⟨⟨inclusionInv, ⟨⟨Function.injective_id, fun _ _ h => h⟩,
    fun c => Empty.elim c.datum.value⟩⟩, rfl⟩
  hom_inv_id := by
    apply Subtype.ext
    apply Subtype.ext
    exact inclusionIso.hom_inv_id
  inv_hom_id := by
    apply Subtype.ext
    apply Subtype.ext
    exact inclusionIso.inv_hom_id

-- ALIGN: EMPTY-ATLAS-STABLE-INTERPRETATION.
noncomputable def interpretationStableIso :
    (WideSubcategory.mk (WideSubcategory.mk emptyAtlas.toSemantics) : Datra.Semantics.StaAtlTrav) ≅
      Datra.Semantics.DomInc.obj Datra.Semantics.emptyDominion :=
  inclusionStableIso ≪≫ DomanialInclusion.interpretationStableIso DomanialInclusion.emptyDominion

end Datra.Executable.EmptyAtlas
