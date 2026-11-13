import Executable.Atlas.Merge.InclusionObjects

namespace Datra.Executable.AtlasMerge
open CategoryTheory Opposite

theorem finitePageEquiv_symm_succ_encode (X Y : Atlas)
    (n : Fin (Datra.Semantics.bouquetDepth X.toSemantics.Fo Y.toSemantics.Fo))
    (value : Sum (componentPage X n.val).Carrier (componentPage Y n.val).Carrier) :
    (finitePageEquiv X Y n.succ).symm (toLex value) =
      cast (congrArg Page.Carrier (storedIndex_succ_page X Y n).symm)
        (encodedPageCell X Y n.val value) :=
  (Equiv.symm_apply_eq (finitePageEquiv X Y n.succ)).mpr (finitePageEquiv_succ_encode X Y n value).symm

theorem finitePageEquiv_left_position (X Y : Atlas)
    (n : Fin (Datra.Semantics.bouquetDepth X.toSemantics.Fo Y.toSemantics.Fo))
    (value : (componentPage X n.val).Carrier) :
    ((pagination X Y).pages.page (storedIndex X Y n.succ)).chain.position
      ((finitePageEquiv X Y n.succ).symm (toLex (.inl value))) =
      (componentPage X n.val).chain.position value := by
  rw [finitePageEquiv_symm_succ_encode]
  exact (Page.cast_position (storedIndex_succ_page X Y n).symm
    (encodedPageCell X Y n.val (.inl value))).trans (pagePosition_encode X Y n.val (.inl value))

theorem finitePageEquiv_right_position (X Y : Atlas)
    (n : Fin (Datra.Semantics.bouquetDepth X.toSemantics.Fo Y.toSemantics.Fo))
    (value : (componentPage Y n.val).Carrier) :
    ((pagination X Y).pages.page (storedIndex X Y n.succ)).chain.position
      ((finitePageEquiv X Y n.succ).symm (toLex (.inr value))) =
      Ordinal.addOrdinals (componentPage X n.val).chain.orderType
        ((componentPage Y n.val).chain.position value) := by
  rw [finitePageEquiv_symm_succ_encode]
  exact (Page.cast_position (storedIndex_succ_page X Y n).symm
    (encodedPageCell X Y n.val (.inr value))).trans (pagePosition_encode X Y n.val (.inr value))

-- ALIGN: MERGE-LEFT-OBJECT-INTERPRETATION.
theorem leftElement_fromFinite (X Y : Atlas) (source : X.toSemantics.El) :
    leftElement X Y ((FolioData.ValidElement.fromFinite X.pages).obj source) =
      (FolioData.ValidElement.fromFinite (atlasMerge X Y).pages).obj
        ((finiteElementsInverse X Y).obj (Datra.Semantics.bouquetLeftElement X.toSemantics Y.toSemantics source)) := by
  apply FolioData.ValidElement.eq_of_page_position
  · rw [leftElement_page]
    rfl
  · rw [leftElement_position]
    let target := (finiteElementsInverse X Y).obj
      (Datra.Semantics.bouquetLeftElement X.toSemantics Y.toSemantics source)
    have position := FolioData.ValidElement.fromFinite_position (atlasMerge X Y).pages target.1.unop target.2
    exact ((finitePageEquiv_left_position X Y
      (Datra.Semantics.bouquetLeftPred X.toSemantics Y.toSemantics source.1.unop)
      (X.pages.toSemantics.includeElements.obj source).2).symm).trans position.symm

-- ALIGN: MERGE-RIGHT-OBJECT-INTERPRETATION.
theorem rightElement_fromFinite (X Y : Atlas) (source : Y.toSemantics.El) :
    rightElement X Y ((FolioData.ValidElement.fromFinite Y.pages).obj source) =
      (FolioData.ValidElement.fromFinite (atlasMerge X Y).pages).obj
        ((finiteElementsInverse X Y).obj (Datra.Semantics.bouquetRightElement X.toSemantics Y.toSemantics source)) := by
  apply FolioData.ValidElement.eq_of_page_position
  · rw [rightElement_page]
    rfl
  · rw [rightElement_position]
    let target := (finiteElementsInverse X Y).obj
      (Datra.Semantics.bouquetRightElement X.toSemantics Y.toSemantics source)
    have position := FolioData.ValidElement.fromFinite_position (atlasMerge X Y).pages target.1.unop target.2
    exact ((finitePageEquiv_right_position X Y
      (Datra.Semantics.bouquetRightPred X.toSemantics Y.toSemantics source.1.unop)
      (Y.pages.toSemantics.includeElements.obj source).2).symm).trans position.symm

/-- A finite page comparison supplies the normalized raw-arrow certificate.
Only the two proposition fields of that certificate enter executable code. -/
private noncomputable def arrowFromFinite {X Z : Atlas} (object : X.Element → Z.Element)
    (pages : X.toSemantics.El ⥤ Z.toSemantics.El)
    (agrees : ∀ source, object ((FolioData.ValidElement.fromFinite X.pages).obj source) =
      (FolioData.ValidElement.fromFinite Z.pages).obj (pages.obj source))
    {source target : X.Element} (arrow : source ⟶ target) :
    normalizedObject object source ⟶ normalizedObject object target := by
  let collapse := (FolioData.ValidElement.elementsEquivalence X.pages).functor ⋙
    X.pages.toSemantics.collapseElements
  have sourceEq : object source.normalize =
      (FolioData.ValidElement.fromFinite Z.pages).obj (pages.obj (collapse.obj source)) :=
    (congrArg object (FolioData.ValidElement.fromFinite_collapse source).symm).trans (agrees _)
  have targetEq : object target.normalize =
      (FolioData.ValidElement.fromFinite Z.pages).obj (pages.obj (collapse.obj target)) :=
    (congrArg object (FolioData.ValidElement.fromFinite_collapse target).symm).trans (agrees _)
  have mapped : object source.normalize ⟶ object target.normalize := by
    rw [sourceEq, targetEq]
    exact (FolioData.ValidElement.fromFinite Z.pages).map (pages.map (collapse.map arrow))
  exact FolioData.ValidElement.normalizeArrow mapped

-- ALIGN: MERGE-LEFT-ARROW.
def leftArrow (X Y : Atlas) {source target : X.Element} (arrow : source ⟶ target) :
    normalizedObject (leftElement X Y) source ⟶ normalizedObject (leftElement X Y) target := by
  have result := arrowFromFinite (leftElement X Y)
    (Datra.Semantics.bouquetLeftElements X.toSemantics Y.toSemantics ⋙ finiteElementsInverse X Y)
    (leftElement_fromFinite X Y) arrow
  exact ⟨result.precedes, result.transported⟩

-- ALIGN: MERGE-RIGHT-ARROW.
def rightArrow (X Y : Atlas) {source target : Y.Element} (arrow : source ⟶ target) :
    normalizedObject (rightElement X Y) source ⟶ normalizedObject (rightElement X Y) target := by
  have result := arrowFromFinite (rightElement X Y)
    (Datra.Semantics.bouquetRightElements X.toSemantics Y.toSemantics ⋙ finiteElementsInverse X Y)
    (rightElement_fromFinite X Y) arrow
  exact ⟨result.precedes, result.transported⟩

end Datra.Executable.AtlasMerge
