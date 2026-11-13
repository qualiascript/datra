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

end Datra.Executable.AtlasMerge
