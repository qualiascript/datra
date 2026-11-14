import Executable.Atlas.Merge.Folio

namespace Datra.Executable.AtlasMerge

/-- Tag the two native trace carriers without changing their stored lists. -/
noncomputable def nativeCellEquiv (X Y : Atlas) (n : Nat) :
    Sum (X.pages.TraceCarrier n) (Y.pages.TraceCarrier n) ≃ ValidPageCell X Y n :=
  (Equiv.sumCongr (X.pages.traceEncodingEquiv X.pagination.folio.valid n).symm
    (Y.pages.traceEncodingEquiv Y.pagination.folio.valid n).symm).trans (pageEncodingEquiv X Y n)

theorem nativeCellEquiv_left (X Y : Atlas) (n : Nat) (trace : X.pages.TraceCarrier n) :
    (nativeCellEquiv X Y n (.inl trace)).val = .left trace.val := by
  change PageCell.left (X.pages.traceAt n ((X.pages.traceEncodingEquiv X.pagination.folio.valid n).symm trace)) = _
  exact congrArg PageCell.left (congrArg Subtype.val
    ((X.pages.traceEncodingEquiv X.pagination.folio.valid n).apply_symm_apply trace))

theorem nativeCellEquiv_right (X Y : Atlas) (n : Nat) (trace : Y.pages.TraceCarrier n) :
    (nativeCellEquiv X Y n (.inr trace)).val = .right trace.val := by
  change PageCell.right (Y.pages.traceAt n ((Y.pages.traceEncodingEquiv Y.pagination.folio.valid n).symm trace)) = _
  exact congrArg PageCell.right (congrArg Subtype.val
    ((Y.pages.traceEncodingEquiv Y.pagination.folio.valid n).apply_symm_apply trace))

-- ALIGN: MERGE-FIRST-CELL.
theorem nativeFirstPageCell (X Y : Atlas) :
    nativeCellEquiv X Y 0 (.inl (X.pages.traceOrigin X.pagination.folio.valid)) =
      firstPageCell X Y := by
  apply Subtype.ext
  rw [nativeCellEquiv_left]
  exact congrArg PageCell.left (congrArg Subtype.val
    (X.pages.encodeTrace_origin X.pagination.folio.valid (componentZeroValue X))).symm

/-- The Haskell constructor sums the two native trace chains, then retags them. -/
noncomputable def nativePageChain (X Y : Atlas) (n : Nat) : Chain (ValidPageCell X Y n) :=
  (Chain.sumChains (X.pages.traceChain X.pagination.folio.valid n)
    (Y.pages.traceChain Y.pagination.folio.valid n)).reindex (nativeCellEquiv X Y n)

theorem nativePageChain_order (X Y : Atlas) (n : Nat) :
    (nativePageChain X Y n).orderType = (pageChain X Y n).orderType := by
  change Ordinal.addOrdinals (X.pages.traceChain _ n).orderType (Y.pages.traceChain _ n).orderType = _
  rw [FolioData.traceChain_order, FolioData.traceChain_order]
  rfl

theorem nativePageChain_position (X Y : Atlas) (n : Nat) :
    (nativePageChain X Y n).position = (pageChain X Y n).position := by
  funext cell
  obtain ⟨parts, rfl⟩ := (nativeCellEquiv X Y n).surjective cell
  change (Chain.sumChains _ _).position
    ((nativeCellEquiv X Y n).symm ((nativeCellEquiv X Y n) parts)) = _
  rw [Equiv.symm_apply_apply]
  cases parts with
  | inl trace =>
      change FolioData.traceHead trace.val = pagePosition X Y n (nativeCellEquiv X Y n (.inl trace)).val
      rw [nativeCellEquiv_left]
      rfl
  | inr trace =>
      change Ordinal.addOrdinals (X.pages.traceChain _ n).orderType (FolioData.traceHead trace.val) =
        pagePosition X Y n (nativeCellEquiv X Y n (.inr trace)).val
      rw [nativeCellEquiv_right, FolioData.traceChain_order]
      rfl

-- ALIGN: MERGE-NATIVE-CHAIN-INTERPRETATION.
theorem nativePageChain_eq (X Y : Atlas) (n : Nat) : nativePageChain X Y n = pageChain X Y n := by
  apply Chain.ext_of_boundedLookup _ _ (nativePageChain_order X Y n) (nativePageChain_position X Y n)
  · intro position outside
    change Option.map _ ((Chain.sumChains _ _).lookup position) = none
    rw [Chain.sumChains_lookup_outside _ _ position outside]
    rfl
  · intro position outside
    change Option.map _ ((componentSum X Y n).chainIndex position) = none
    have absent := (componentSum X Y n).chainIndex_isSome position
    change Ordinal.ordinalLT position (componentSum X Y n).orderType = false at outside
    rw [outside] at absent
    cases found : (componentSum X Y n).chainIndex position <;> simp_all

-- ALIGN: MERGE-PAGE-PREVIOUS-VALID.
theorem nativePrevious_valid (X Y : Atlas) (n : Nat)
    (source : Sum (X.pages.TraceCarrier (n + 1)) (Y.pages.TraceCarrier (n + 1))) :
    previousValidCell X Y n (nativeCellEquiv X Y (n + 1) source) =
      nativeCellEquiv X Y n
        (Sum.map (fun trace => trace.previous X.pagination.folio.valid n)
          (fun trace => trace.previous Y.pagination.folio.valid n) source) := by
  apply Subtype.ext
  cases source with
  | inl trace =>
      change previousPageCell (nativeCellEquiv X Y (n + 1) (.inl trace)).val = _
      rw [nativeCellEquiv_left]
      exact (nativeCellEquiv_left X Y n (trace.previous X.pagination.folio.valid n)).symm
  | inr trace =>
      change previousPageCell (nativeCellEquiv X Y (n + 1) (.inr trace)).val = _
      rw [nativeCellEquiv_right]
      exact (nativeCellEquiv_right X Y n (trace.previous Y.pagination.folio.valid n)).symm

-- ALIGN: MERGE-PAGE-NEXT-VALID.
theorem nativeNext_valid (X Y : Atlas) (n : Nat)
    (source : Sum (X.pages.TraceCarrier n) (Y.pages.TraceCarrier n)) :
    nextValidCell X Y n (nativeCellEquiv X Y n source) =
      nativeCellEquiv X Y (n + 1)
        (Sum.map (fun trace => trace.next X.pagination.folio.valid n)
          (fun trace => trace.next Y.pagination.folio.valid n) source) := by
  apply Subtype.ext
  cases source with
  | inl trace =>
      obtain ⟨value, rfl⟩ := (X.pages.encodeTrace_bijective X.pagination.folio.valid n).2 trace
      change nextPageCell X Y n (nativeCellEquiv X Y n (.inl _)).val =
        (nativeCellEquiv X Y (n + 1) (.inl _)).val
      dsimp only
      rw [FolioData.next_encodeTrace, nativeCellEquiv_left, nativeCellEquiv_left]
      exact nextPageCell_encode X Y n (.inl value)
  | inr trace =>
      obtain ⟨value, rfl⟩ := (Y.pages.encodeTrace_bijective Y.pagination.folio.valid n).2 trace
      change nextPageCell X Y n (nativeCellEquiv X Y n (.inr _)).val =
        (nativeCellEquiv X Y (n + 1) (.inr _)).val
      dsimp only
      rw [FolioData.next_encodeTrace, nativeCellEquiv_right, nativeCellEquiv_right]
      exact nextPageCell_encode X Y n (.inr value)

/-- The native merge transition sums the component trace maps before retagging. -/
-- ALIGN: MERGE-NATIVE-TRANSITION.
noncomputable def nativePageTransition (X Y : Atlas) (n : Nat) :
    OrderedConsolidation (ValidPageCell X Y (n + 1)) (ValidPageCell X Y n) :=
  OrderedConsolidation.reindex
    (OrderedConsolidation.sum
      (X.pages.traceTransitionBetween X.pagination.folio.valid n
        (X.pages.traceChain X.pagination.folio.valid (n + 1))
        (X.pages.traceChain X.pagination.folio.valid n) rfl rfl)
      (Y.pages.traceTransitionBetween Y.pagination.folio.valid n
        (Y.pages.traceChain Y.pagination.folio.valid (n + 1))
        (Y.pages.traceChain Y.pagination.folio.valid n) rfl rfl))
    (nativeCellEquiv X Y (n + 1)) (nativeCellEquiv X Y n)

theorem nativePageTransition_source (X Y : Atlas) (n : Nat) :
    (nativePageTransition X Y n).source = pageChain X Y (n + 1) :=
  nativePageChain_eq X Y (n + 1)

theorem nativePageTransition_target (X Y : Atlas) (n : Nat) :
    (nativePageTransition X Y n).target = pageChain X Y n :=
  nativePageChain_eq X Y n

theorem nativePageTransition_map (X Y : Atlas) (n : Nat) (cell : ValidPageCell X Y (n + 1)) :
    (nativePageTransition X Y n).map.map cell = (pageTransition X Y n).map cell := by
  obtain ⟨parts, rfl⟩ := (nativeCellEquiv X Y (n + 1)).surjective cell
  change nativeCellEquiv X Y n
    (Sum.map (fun trace => trace.previous X.pagination.folio.valid n)
      (fun trace => trace.previous Y.pagination.folio.valid n)
      ((nativeCellEquiv X Y (n + 1)).symm (nativeCellEquiv X Y (n + 1) parts))) = _
  rw [Equiv.symm_apply_apply]
  exact (nativePrevious_valid X Y n parts).symm

theorem nativePageTransition_preimage (X Y : Atlas) (n : Nat) (cell : ValidPageCell X Y n) :
    (nativePageTransition X Y n).map.preimage cell = (pageTransition X Y n).preimage cell := by
  obtain ⟨parts, rfl⟩ := (nativeCellEquiv X Y n).surjective cell
  change nativeCellEquiv X Y (n + 1)
    (Sum.map (fun trace => trace.next X.pagination.folio.valid n)
      (fun trace => trace.next Y.pagination.folio.valid n)
      ((nativeCellEquiv X Y n).symm (nativeCellEquiv X Y n parts))) = _
  rw [Equiv.symm_apply_apply]
  exact (nativeNext_valid X Y n parts).symm

theorem nativePageTransition_interpretation (X Y : Atlas) (n : Nat)
    (value : Sum (componentPage X (n + 1)).Carrier (componentPage Y (n + 1)).Carrier) :
    pageSumOrderIso X Y n ((nativePageTransition X Y n).map.map (encodedPageCell X Y (n + 1) value)) =
      (Datra.Semantics.ConHom.sum
        (X.pages.transport (n + 1) n (Nat.le_succ n)).toSemantics
        (Y.pages.transport (n + 1) n (Nat.le_succ n)).toSemantics)
        (pageSumOrderIso X Y (n + 1) (encodedPageCell X Y (n + 1) value)) := by
  rw [nativePageTransition_map]
  exact pageTransition_interpretation X Y n value

-- ALIGN: MERGE-PAGE-TRANSITION.
noncomputable def nativePageTransitionTo (X Y : Atlas) (n : Nat)
    (target : Chain (ValidPageCell X Y n))
    (targetPosition : ∀ cell, target.position cell = pagePosition X Y n cell.val) :
    OrderedConsolidation (ValidPageCell X Y (n + 1)) (ValidPageCell X Y n) :=
  let mapping := nativePageTransition X Y n
  let sourcePosition : ∀ cell, pagePosition X Y (n + 1) cell.val = mapping.source.position cell := by
    intro cell
    rw [nativePageTransition_source]
    rfl
  let source := mapping.source.withPosition (fun cell => pagePosition X Y (n + 1) cell.val) sourcePosition
  mapping.withEndpoints source target sourcePosition (by
    intro cell
    rw [targetPosition, nativePageTransition_target]
    rfl)

theorem nativePageTransitionTo_source (X Y : Atlas) (n : Nat)
    (target : Chain (ValidPageCell X Y n))
    (targetPosition : ∀ cell, target.position cell = pagePosition X Y n cell.val) :
    (nativePageTransitionTo X Y n target targetPosition).source = pageChain X Y (n + 1) := by
  simp only [nativePageTransitionTo, OrderedConsolidation.withEndpoints,
    Chain.withPosition_eq, nativePageTransition_source]

theorem nativePageTransitionTo_target (X Y : Atlas) (n : Nat)
    (target : Chain (ValidPageCell X Y n))
    (targetPosition : ∀ cell, target.position cell = pagePosition X Y n cell.val) :
    (nativePageTransitionTo X Y n target targetPosition).target = target := rfl

-- ALIGN: MERGE-PAGE-TRANSITION-INTERPRETATION.
theorem nativePageTransitionTo_interpretation (X Y : Atlas) (n : Nat)
    (target : Chain (ValidPageCell X Y n))
    (targetPosition : ∀ cell, target.position cell = pagePosition X Y n cell.val)
    (value : Sum (componentPage X (n + 1)).Carrier (componentPage Y (n + 1)).Carrier) :
    pageSumOrderIso X Y n ((nativePageTransitionTo X Y n target targetPosition).map.map
        (encodedPageCell X Y (n + 1) value)) =
      (Datra.Semantics.ConHom.sum
        (X.pages.transport (n + 1) n (Nat.le_succ n)).toSemantics
        (Y.pages.transport (n + 1) n (Nat.le_succ n)).toSemantics)
        (pageSumOrderIso X Y (n + 1) (encodedPageCell X Y (n + 1) value)) :=
  nativePageTransition_interpretation X Y n value

theorem nativePageTransitionTo_preimage (X Y : Atlas) (n : Nat)
    (target : Chain (ValidPageCell X Y n))
    (targetPosition : ∀ cell, target.position cell = pagePosition X Y n cell.val)
    (cell : ValidPageCell X Y n) :
    (nativePageTransitionTo X Y n target targetPosition).map.preimage cell =
      (pageTransition X Y n).preimage cell :=
  nativePageTransition_preimage X Y n cell

end Datra.Executable.AtlasMerge
