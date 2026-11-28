import Executable.Atlas.Data
import Executable.Folio.Comparison

namespace Datra.Executable
open CategoryTheory

noncomputable section

/-- A finite folio comparison with rank-preserving data equivalences. When
both data actions preserve ranks, these equivalences give an Atlas isomorphism. -/
structure Atlas.RankComparison (source : Atlas) (target : Datra.Semantics.Atl) where
  folio : FolioData.Comparison source.pages target.Fo
  dataEquiv : ∀ x : source.toSemantics.El,
    source.toSemantics.Da.obj x ≃ target.Da.obj (folio.elementEquiv x)
  data_rank : ∀ x datum,
    (target.Da.obj (folio.elementEquiv x)).toDom.rank (dataEquiv x datum) =
      (source.toSemantics.Da.obj x).toDom.rank datum
  source_map_rank : ∀ {x y : source.toSemantics.El} (arrow : x ⟶ y) datum,
    (source.toSemantics.Da.obj y).toDom.rank (source.toSemantics.Da.map arrow datum) =
      (source.toSemantics.Da.obj x).toDom.rank datum
  target_map_rank : ∀ {x y : target.El} (arrow : x ⟶ y) datum,
    (target.Da.obj y).toDom.rank (target.Da.map arrow datum) =
      (target.Da.obj x).toDom.rank datum

theorem hom_eq_of_page_rank {A B : Datra.Semantics.Atl} (f g : Datra.Semantics.AtlHom A B)
    (pages : f.Pa = g.Pa)
    (ranks : ∀ source datum,
      (B.Da.obj (f.Pa.obj source)).toDom.rank (f.Da.app source datum) =
        (B.Da.obj (g.Pa.obj source)).toDom.rank (g.Da.app source datum)) : f = g := by
  cases f with
  | mk fp fd =>
    cases g with
    | mk gp gd =>
      dsimp only at pages
      subst gp
      apply Datra.Semantics.AtlHom.ext
      · rfl
      · apply heq_of_eq
        ext source datum
        exact (B.Da.obj (fp.obj source)).toDom.rank.injective (ranks source datum)

namespace Atlas.RankComparison
variable {source : Atlas} {target : Datra.Semantics.Atl}

theorem naturality (comparison : source.RankComparison target)
    {x y : source.toSemantics.El} (arrow : x ⟶ y) (datum : source.toSemantics.Da.obj x) :
    comparison.dataEquiv y (source.toSemantics.Da.map arrow datum) =
      target.Da.map (comparison.folio.elements.map arrow) (comparison.dataEquiv x datum) := by
  apply (target.Da.obj (comparison.folio.elementEquiv y)).toDom.rank.injective
  rw [comparison.data_rank, comparison.target_map_rank]
  exact (comparison.source_map_rank arrow datum).trans (comparison.data_rank x datum).symm

def hom (comparison : source.RankComparison target) : source.toSemantics ⟶ target where
  Pa := comparison.folio.elements
  Da :=
    { app := fun x => (comparison.dataEquiv x).toEmbedding
      naturality := by
        intro x y arrow
        apply Function.Embedding.ext
        exact comparison.naturality arrow }

theorem inverse_rank (comparison : source.RankComparison target) (x : source.toSemantics.El)
    (datum : target.Da.obj (comparison.folio.elementEquiv x)) :
    (source.toSemantics.Da.obj x).toDom.rank ((comparison.dataEquiv x).symm datum) =
      (target.Da.obj (comparison.folio.elementEquiv x)).toDom.rank datum := by
  have result := comparison.data_rank x ((comparison.dataEquiv x).symm datum)
  simpa only [Equiv.apply_symm_apply] using result.symm

def invData (comparison : source.RankComparison target) (y : target.El) :
    target.Da.obj y ↪ source.toSemantics.Da.obj (comparison.folio.elementEquiv.symm y) :=
  (target.Da.map (eqToHom (comparison.folio.elementEquiv.apply_symm_apply y).symm)).trans
    (comparison.dataEquiv (comparison.folio.elementEquiv.symm y)).symm.toEmbedding

theorem invData_rank (comparison : source.RankComparison target) (y : target.El)
    (datum : target.Da.obj y) :
    (source.toSemantics.Da.obj (comparison.folio.elementEquiv.symm y)).toDom.rank
      (comparison.invData y datum) = (target.Da.obj y).toDom.rank datum :=
  (comparison.inverse_rank _ _).trans (comparison.target_map_rank _ datum)

def inv (comparison : source.RankComparison target) : target ⟶ source.toSemantics where
  Pa := comparison.folio.elementsInverse
  Da :=
    { app := comparison.invData
      naturality := by
        intro x y arrow
        apply Function.Embedding.ext
        intro datum
        apply (source.toSemantics.Da.obj (comparison.folio.elementEquiv.symm y)).toDom.rank.injective
        change (source.toSemantics.Da.obj (comparison.folio.elementEquiv.symm y)).toDom.rank
            (comparison.invData y (target.Da.map arrow datum)) =
          (source.toSemantics.Da.obj (comparison.folio.elementEquiv.symm y)).toDom.rank
            (source.toSemantics.Da.map (comparison.folio.elementsInverse.map arrow)
              (comparison.invData x datum))
        rw [comparison.invData_rank, comparison.source_map_rank, comparison.target_map_rank]
        exact (comparison.invData_rank x datum).symm }

def iso (comparison : source.RankComparison target) : source.toSemantics ≅ target where
  hom := comparison.hom
  inv := comparison.inv
  hom_inv_id := by
    apply hom_eq_of_page_rank
    · exact CategoryTheory.Functor.ext (fun x => comparison.folio.elementEquiv.symm_apply_apply x)
    · intro x datum
      exact (comparison.invData_rank _ _).trans (comparison.data_rank x datum)
  inv_hom_id := by
    apply hom_eq_of_page_rank
    · exact CategoryTheory.Functor.ext (fun y => comparison.folio.elementEquiv.apply_symm_apply y)
    · intro y datum
      exact (comparison.data_rank _ _).trans (comparison.invData_rank y datum)

end Atlas.RankComparison
end
end Datra.Executable
