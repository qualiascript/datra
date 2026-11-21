import Executable.Atlas.Merge.InclusionOrder

namespace Datra.Executable.AtlasMerge
open CategoryTheory

theorem leftMorphism_finiteObject (X Y : Atlas) (source : X.toSemantics.El) :
    (leftMorphism X Y).toSemantics.Pa.obj source =
      (finiteElementsInverse X Y).obj
        (Datra.Semantics.bouquetLeftElement X.toSemantics Y.toSemantics source) := by
  apply FolioData.ValidElement.fromFinite_injective (atlasMerge X Y).pages
  change (FolioData.ValidElement.fromFinite (atlasMerge X Y).pages).obj
    ((atlasMerge X Y).pages.toSemantics.collapseElements.obj
      ((FolioData.ValidElement.elementsEquivalence (atlasMerge X Y).pages).functor.obj
        ((leftMorphism X Y).pageFunctor.obj
          ((FolioData.ValidElement.fromFinite X.pages).obj source)))) = _
  rw [FolioData.ValidElement.fromFinite_collapse]
  change ((leftElement X Y ((FolioData.ValidElement.fromFinite X.pages).obj source).normalize).normalize).normalize = _
  rw [FolioData.ValidElement.normalize_fromFinite, FolioData.ValidElement.normalize_idempotent,
    leftElement_fromFinite, FolioData.ValidElement.normalize_fromFinite]

theorem rightMorphism_finiteObject (X Y : Atlas) (source : Y.toSemantics.El) :
    (rightMorphism X Y).toSemantics.Pa.obj source =
      (finiteElementsInverse X Y).obj
        (Datra.Semantics.bouquetRightElement X.toSemantics Y.toSemantics source) := by
  apply FolioData.ValidElement.fromFinite_injective (atlasMerge X Y).pages
  change (FolioData.ValidElement.fromFinite (atlasMerge X Y).pages).obj
    ((atlasMerge X Y).pages.toSemantics.collapseElements.obj
      ((FolioData.ValidElement.elementsEquivalence (atlasMerge X Y).pages).functor.obj
        ((rightMorphism X Y).pageFunctor.obj
          ((FolioData.ValidElement.fromFinite Y.pages).obj source)))) = _
  rw [FolioData.ValidElement.fromFinite_collapse]
  change ((rightElement X Y ((FolioData.ValidElement.fromFinite Y.pages).obj source).normalize).normalize).normalize = _
  rw [FolioData.ValidElement.normalize_fromFinite, FolioData.ValidElement.normalize_idempotent,
    rightElement_fromFinite, FolioData.ValidElement.normalize_fromFinite]

-- ALIGN: MERGE-LEFT-MORPHISM-RANK.
theorem leftMorphism_rank (X Y : Atlas) (source : X.toSemantics.El)
    (datum : X.toSemantics.Da.obj source) :
    ((atlasMerge X Y).toSemantics.Da.obj ((leftMorphism X Y).toSemantics.Pa.obj source)).toDom.rank
      ((leftMorphism X Y).toSemantics.Da.app source datum) =
        2 * X.originImageRank ((FolioData.ValidElement.fromFinite X.pages).obj source) datum := by
  change 2 * X.originImageRank ((FolioData.ValidElement.fromFinite X.pages).obj source).normalize datum = _
  rw [X.originImageRank_normalize]

-- ALIGN: MERGE-RIGHT-MORPHISM-RANK.
theorem rightMorphism_rank (X Y : Atlas) (source : Y.toSemantics.El)
    (datum : Y.toSemantics.Da.obj source) :
    ((atlasMerge X Y).toSemantics.Da.obj ((rightMorphism X Y).toSemantics.Pa.obj source)).toDom.rank
      ((rightMorphism X Y).toSemantics.Da.app source datum) =
        2 * Y.originImageRank ((FolioData.ValidElement.fromFinite Y.pages).obj source) datum + 1 := by
  change 2 * Y.originImageRank ((FolioData.ValidElement.fromFinite Y.pages).obj source).normalize datum + 1 = _
  rw [Y.originImageRank_normalize]

/-- The whole left inclusion, including its dependent data transformation,
commutes with the comparison to the written bouquet Atlas. -/
-- ALIGN: MERGE-LEFT-MORPHISM-INTERPRETATION.
theorem leftMorphism_interpretation (X Y : Atlas) :
    (leftMorphism X Y).toSemantics ≫ (interpretationIso X Y).hom =
      Datra.Semantics.bouquetLeftHom X.toSemantics Y.toSemantics := by
  apply hom_eq_of_page_rank
  · refine CategoryTheory.Functor.ext (fun source => ?_)
    change finiteElementEquiv X Y ((leftMorphism X Y).toSemantics.Pa.obj source) = _
    rw [leftMorphism_finiteObject]
    exact (finiteElementEquiv X Y).apply_symm_apply _
  · intro source datum
    change ((Datra.Semantics.bouquetAtlas X.toSemantics Y.toSemantics).Da.obj
      (finiteElementEquiv X Y ((leftMorphism X Y).toSemantics.Pa.obj source))).toDom.rank
      (finiteDataEquiv X Y _ ((leftMorphism X Y).toSemantics.Da.app source datum)) = _
    rw [finiteDataEquiv_rank, leftMorphism_rank, X.originImageRank_interpretation]
    rfl

/-- The right inclusion obeys the same square with the right-tagged data map. -/
-- ALIGN: MERGE-RIGHT-MORPHISM-INTERPRETATION.
theorem rightMorphism_interpretation (X Y : Atlas) :
    (rightMorphism X Y).toSemantics ≫ (interpretationIso X Y).hom =
      Datra.Semantics.bouquetRightHom X.toSemantics Y.toSemantics := by
  apply hom_eq_of_page_rank
  · refine CategoryTheory.Functor.ext (fun source => ?_)
    change finiteElementEquiv X Y ((rightMorphism X Y).toSemantics.Pa.obj source) = _
    rw [rightMorphism_finiteObject]
    exact (finiteElementEquiv X Y).apply_symm_apply _
  · intro source datum
    change ((Datra.Semantics.bouquetAtlas X.toSemantics Y.toSemantics).Da.obj
      (finiteElementEquiv X Y ((rightMorphism X Y).toSemantics.Pa.obj source))).toDom.rank
      (finiteDataEquiv X Y _ ((rightMorphism X Y).toSemantics.Da.app source datum)) = _
    rw [finiteDataEquiv_rank, rightMorphism_rank, Y.originImageRank_interpretation]
    rfl

-- ALIGN: MERGE-LEFT-ORDERED-INTERPRETATION.
theorem leftOrderedTransposal_interpretation (X Y : Atlas) :
    (leftOrderedTransposal X Y).underlying.hom.finiteSemantics ≫ (interpretationIso X Y).hom =
      Datra.Semantics.bouquetLeftHom X.toSemantics Y.toSemantics := by
  rw [Atlas.Hom.finiteSemantics_materialize]
  exact leftMorphism_interpretation X Y

-- ALIGN: MERGE-RIGHT-ORDERED-INTERPRETATION.
theorem rightOrderedTransposal_interpretation (X Y : Atlas) :
    (rightOrderedTransposal X Y).underlying.hom.finiteSemantics ≫ (interpretationIso X Y).hom =
      Datra.Semantics.bouquetRightHom X.toSemantics Y.toSemantics := by
  rw [Atlas.Hom.finiteSemantics_materialize]
  exact rightMorphism_interpretation X Y

end Datra.Executable.AtlasMerge
