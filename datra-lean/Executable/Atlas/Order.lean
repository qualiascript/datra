import Executable.Atlas.Elements

namespace Datra.Executable.Atlas.TransposalElement
open CategoryTheory Opposite

/-- Compare the two positions after transporting to their common earliest
page. Missing trace positions return false, as in the executable operation. -/
def lt {X : Atlas} (x y : X.TransposalElement) : Bool :=
  PageElement.elementLT x.val.val y.val.val

theorem lt_fromSemantics (X : Atlas) (x y : X.toSemantics.El) :
    lt (fromSemantics X x) (fromSemantics X y) = true ↔
      Datra.Semantics.elementLT X.toSemantics x y := by
  let m := X.toSemantics.Fo.commonBase x.1 y.1
  let a : X.toSemantics.El :=
    ⟨m, X.toSemantics.Fo.cellDiagram.map (X.toSemantics.Fo.toCommonLeft x.1 y.1) x.2⟩
  let b : X.toSemantics.El :=
    ⟨m, X.toSemantics.Fo.cellDiagram.map (X.toSemantics.Fo.toCommonRight x.1 y.1) y.2⟩
  let fx : x ⟶ a := CategoryOfElements.homMk _ _
    (X.toSemantics.Fo.toCommonLeft x.1 y.1) rfl
  let fy : y ⟶ b := CategoryOfElements.homMk _ _
    (X.toSemantics.Fo.toCommonRight x.1 y.1) rfl
  let F := FolioData.ValidElement.fromFinite X.pages
  have hx := FolioData.ValidElement.positionAtPage_arrow (F.map fx)
  have hy := FolioData.ValidElement.positionAtPage_arrow (F.map fy)
  have hm : m.unop.val = min x.1.unop.val y.1.unop.val := rfl
  change PageElement.positionAtPage m.unop.val (F.obj x).val = some (F.obj a).val.position at hx
  change PageElement.positionAtPage m.unop.val (F.obj y).val = some (F.obj b).val.position at hy
  simp only [lt, PageElement.elementLT, fromSemantics, FolioData.ValidElement.fromFinite_page]
  rw [← hm, hx, hy]
  change Ordinal.ordinalLT (F.obj a).val.position (F.obj b).val.position = true ↔ _
  have ha := FolioData.ValidElement.fromFinite_position X.pages m.unop a.2
  have hb := FolioData.ValidElement.fromFinite_position X.pages m.unop b.2
  simp only [op_unop] at ha hb
  change (F.obj a).val.position = _ at ha
  change (F.obj b).val.position = _ at hb
  rw [ha, hb]
  exact Ordinal.ordinalLT_correct _ _

-- ALIGN: ATLAS-ORDER-INTERPRETATION.
theorem lt_interpretation {X : Atlas} (x y : X.TransposalElement) :
    lt x y = true ↔ Datra.Semantics.elementLT X.toSemantics x.toSemantics y.toSemantics := by
  have h := lt_fromSemantics X x.toSemantics y.toSemantics
  have hx : fromSemantics X x.toSemantics = x := (semanticsEquiv X).left_inv x
  have hy : fromSemantics X y.toSemantics = y := (semanticsEquiv X).left_inv y
  rw [hx, hy] at h
  exact h

end Datra.Executable.Atlas.TransposalElement
