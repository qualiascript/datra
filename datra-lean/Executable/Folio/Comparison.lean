import Executable.Folio

namespace Datra.Executable.FolioData
open CategoryTheory Opposite

noncomputable section

variable {origin final : Page}

/-- A finite folio comparison identifies page indices and cells and commutes
with every interval. It induces an equivalence of element categories. -/
structure Comparison (source : FolioData origin final) (target : Datra.Semantics.Folio) where
  length_eq : source.depth = target.length
  cell : ∀ n, (source.page (source.indexEquivFin.symm ((Fin.castOrderIso length_eq).symm n))).Carrier ≃
    (target.core.obj n).unop.Obj
  natural : ∀ {i j : Fin target.length} (precedes : i ≤ j)
    (value : (source.page (source.indexEquivFin.symm ((Fin.castOrderIso length_eq).symm j))).Carrier),
    cell i ((source.interval (source.indexEquivFin.symm ((Fin.castOrderIso length_eq).symm j))
      (source.indexEquivFin.symm ((Fin.castOrderIso length_eq).symm i))
      (by simpa only [indexEquivFin_symm_number] using (Fin.castOrderIso length_eq).symm.monotone precedes)).map value) =
      (target.core.map (homOfLE precedes)).unop (cell j value)

namespace Comparison
variable {source : FolioData origin final} {target : Datra.Semantics.Folio}

def index (comparison : Comparison source target) : Fin source.depth ≃o Fin target.length :=
  Fin.castOrderIso comparison.length_eq

def elementEquiv (comparison : Comparison source target) : source.toSemantics.El ≃ target.El where
  toFun value := ⟨op (comparison.index value.1.unop), comparison.cell (comparison.index value.1.unop) value.2⟩
  invFun value := ⟨op (comparison.index.symm value.1.unop), (comparison.cell value.1.unop).symm value.2⟩
  left_inv value := by
    obtain ⟨⟨n⟩, value⟩ := value
    apply Sigma.ext
    · exact congrArg op (comparison.index.symm_apply_apply n)
    · exact heq_of_eq ((comparison.cell (comparison.index n)).symm_apply_apply value)
  right_inv value := by
    obtain ⟨⟨n⟩, value⟩ := value
    apply Sigma.ext
    · exact congrArg op (comparison.index.apply_symm_apply n)
    · exact heq_of_eq ((comparison.cell n).apply_symm_apply value)

def elements (comparison : Comparison source target) : source.toSemantics.El ⥤ target.El where
  obj := comparison.elementEquiv
  map {a b} arrow := CategoryOfElements.homMk _ _
    (homOfLE (comparison.index.monotone (leOfHom arrow.val.unop))).op (by
      have natural := comparison.natural (comparison.index.monotone (leOfHom arrow.val.unop)) a.2
      have transported := arrow.property
      change (source.interval _ _ _).map a.2 = b.2 at transported
      exact natural.symm.trans (congrArg (comparison.cell (comparison.index b.1.unop)) transported))
  map_id _ := Subsingleton.elim _ _
  map_comp _ _ := Subsingleton.elim _ _

def elementsInverse (comparison : Comparison source target) : target.El ⥤ source.toSemantics.El where
  obj := comparison.elementEquiv.symm
  map {a b} arrow := CategoryOfElements.homMk _ _
    (homOfLE (comparison.index.symm.monotone (leOfHom arrow.val.unop))).op (by
      apply (comparison.cell b.1.unop).injective
      have natural := comparison.natural (leOfHom arrow.val.unop) ((comparison.cell a.1.unop).symm a.2)
      simp only [Equiv.apply_symm_apply] at natural
      exact (natural.trans arrow.property).trans ((comparison.cell b.1.unop).apply_symm_apply b.2).symm)
  map_id _ := Subsingleton.elim _ _
  map_comp _ _ := Subsingleton.elim _ _

def elementsEquivalence (comparison : Comparison source target) : source.toSemantics.El ≌ target.El where
  functor := comparison.elements
  inverse := comparison.elementsInverse
  unitIso := NatIso.ofComponents (fun value => eqToIso (comparison.elementEquiv.symm_apply_apply value).symm)
    (fun _ => Subsingleton.elim _ _)
  counitIso := NatIso.ofComponents (fun value => eqToIso (comparison.elementEquiv.apply_symm_apply value))
    (fun _ => Subsingleton.elim _ _)
  functor_unitIso_comp _ := Subsingleton.elim _ _

end Comparison
end
end Datra.Executable.FolioData
