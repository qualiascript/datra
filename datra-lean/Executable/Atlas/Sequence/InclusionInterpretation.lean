import Executable.Atlas.Sequence.DataInterpretation

namespace Datra.Executable.AtlasSequence
open CategoryTheory

variable {count : Nat}

theorem finitePageEquiv_symm_succ_encode (positive : 0 < count) (members : Fin count → Atlas)
    (n : Fin (Datra.Semantics.sequenceDepth (fun i => (members i).toSemantics.Fo)))
    (value : PageValue members n.val) :
    (finitePageEquiv positive members n.succ).symm (toLex value) =
      cast (congrArg Page.Carrier (storedIndex_succ_page positive members n).symm)
        (encodedPageCell members n.val value) :=
  (Equiv.symm_apply_eq (finitePageEquiv positive members n.succ)).mpr
    (finitePageEquiv_succ_encode positive members n value).symm

theorem finitePageEquiv_member_position (positive : 0 < count) (members : Fin count → Atlas)
    (n : Fin (Datra.Semantics.sequenceDepth (fun i => (members i).toSemantics.Fo)))
    (index : Fin count) (value : (componentPage members n.val index).Carrier) :
    ((pagination positive members).pages.page (storedIndex positive members n.succ)).chain.position
      ((finitePageEquiv positive members n.succ).symm (toLex ⟨index, value⟩)) =
      Ordinal.addOrdinals (ChainSequence.prefixOrder (pageOrders members n.val) index.val)
        ((componentPage members n.val index).chain.position value) := by
  rw [finitePageEquiv_symm_succ_encode]
  refine (Page.cast_position (storedIndex_succ_page positive members n).symm
    (encodedPageCell members n.val ⟨index, value⟩)).trans ?_
  change (componentSum members n.val).position
    ((pageEncodingEquiv members n.val).symm (pageEncodingEquiv members n.val ⟨index, value⟩)) = _
  rw [Equiv.symm_apply_apply]
  rfl

-- ALIGN: SEQUENCE-MEMBER-OBJECT-INTERPRETATION.
theorem memberElement_fromFinite (positive : 0 < count) (members : Fin count → Atlas) (index : Fin count)
    (source : (members index).toSemantics.El) :
    memberElement positive members index ((FolioData.ValidElement.fromFinite (members index).pages).obj source) =
      (FolioData.ValidElement.fromFinite (atlasSequence positive members).pages).obj
        ((finiteElementsInverse positive members).obj
          (Datra.Semantics.sequenceMemberElement positive (fun i => (members i).toSemantics) index source)) := by
  apply FolioData.ValidElement.eq_of_page_position
  · rw [memberElement_page]
    rfl
  · rw [memberElement_position]
    let target := (finiteElementsInverse positive members).obj
      (Datra.Semantics.sequenceMemberElement positive (fun i => (members i).toSemantics) index source)
    have position := FolioData.ValidElement.fromFinite_position (atlasSequence positive members).pages target.1.unop target.2
    exact ((finitePageEquiv_member_position positive members
      (Datra.Semantics.sequenceMemberPred (fun i => (members i).toSemantics) index source.1.unop) index
      ((members index).pages.toSemantics.includeElements.obj source).2).symm).trans position.symm

theorem memberMorphism_finiteObject (positive : 0 < count) (members : Fin count → Atlas) (index : Fin count)
    (source : (members index).toSemantics.El) :
    (memberMorphism positive members index).toSemantics.Pa.obj source =
      (finiteElementsInverse positive members).obj
        (Datra.Semantics.sequenceMemberElement positive (fun i => (members i).toSemantics) index source) := by
  apply FolioData.ValidElement.fromFinite_injective (atlasSequence positive members).pages
  change (FolioData.ValidElement.fromFinite (atlasSequence positive members).pages).obj
    ((atlasSequence positive members).pages.toSemantics.collapseElements.obj
      ((FolioData.ValidElement.elementsEquivalence (atlasSequence positive members).pages).functor.obj
        ((memberMorphism positive members index).pageFunctor.obj
          ((FolioData.ValidElement.fromFinite (members index).pages).obj source)))) = _
  rw [FolioData.ValidElement.fromFinite_collapse]
  change ((memberElement positive members index
    ((FolioData.ValidElement.fromFinite (members index).pages).obj source).normalize).normalize).normalize = _
  rw [FolioData.ValidElement.normalize_fromFinite, FolioData.ValidElement.normalize_idempotent,
    memberElement_fromFinite, FolioData.ValidElement.normalize_fromFinite]

-- ALIGN: SEQUENCE-MEMBER-MORPHISM-RANK.
theorem memberMorphism_rank (positive : 0 < count) (members : Fin count → Atlas) (index : Fin count)
    (source : (members index).toSemantics.El) (datum : (members index).toSemantics.Da.obj source) :
    ((atlasSequence positive members).toSemantics.Da.obj
      ((memberMorphism positive members index).toSemantics.Pa.obj source)).toDom.rank
      ((memberMorphism positive members index).toSemantics.Da.app source datum) =
        count * (members index).originImageRank
          ((FolioData.ValidElement.fromFinite (members index).pages).obj source) datum + index.val := by
  change count * (members index).originImageRank
    ((FolioData.ValidElement.fromFinite (members index).pages).obj source).normalize datum + index.val = _
  rw [Atlas.originImageRank_normalize]

/-- Both the page action and the dependent data action of each canonical
member inclusion commute with the complete sequence comparison. -/
-- ALIGN: SEQUENCE-MEMBER-MORPHISM-INTERPRETATION.
theorem memberMorphism_interpretation (positive : 0 < count) (members : Fin count → Atlas) (index : Fin count) :
    (memberMorphism positive members index).toSemantics ≫ (interpretationIso positive members).hom =
      Datra.Semantics.sequenceMemberHom positive (fun i => (members i).toSemantics) index := by
  apply hom_eq_of_page_rank
  · refine CategoryTheory.Functor.ext (fun source => ?_)
    change finiteElementEquiv positive members ((memberMorphism positive members index).toSemantics.Pa.obj source) = _
    rw [memberMorphism_finiteObject]
    exact (finiteElementEquiv positive members).apply_symm_apply _
  · intro source datum
    change ((Datra.Semantics.sequenceAtlas positive (fun i => (members i).toSemantics)).Da.obj
      (finiteElementEquiv positive members ((memberMorphism positive members index).toSemantics.Pa.obj source))).toDom.rank
      (finiteDataEquiv positive members _ ((memberMorphism positive members index).toSemantics.Da.app source datum)) = _
    rw [finiteDataEquiv_rank, memberMorphism_rank, Atlas.originImageRank_interpretation]
    rfl

-- ALIGN: SEQUENCE-MEMBER-ORDERED-INTERPRETATION.
theorem memberOrderedTransposal_interpretation (positive : 0 < count) (members : Fin count → Atlas) (index : Fin count) :
    (memberOrderedTransposal positive members index).underlying.hom.finiteSemantics ≫ (interpretationIso positive members).hom =
      Datra.Semantics.sequenceMemberHom positive (fun i => (members i).toSemantics) index := by
  rw [Atlas.Hom.finiteSemantics_materialize]
  exact memberMorphism_interpretation positive members index

end Datra.Executable.AtlasSequence
