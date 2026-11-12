import Executable.Atlas.Merge.Data

namespace Datra.Executable.AtlasMerge
open CategoryTheory Opposite

-- ALIGN: MERGE-FINITE-INDEX-INTERPRETATION.
noncomputable def finiteIndexOrderIso (X Y : Atlas) :
    Fin (pagination X Y).pages.depth ≃o
      Fin (Datra.Semantics.bouquetLength X.toSemantics.Fo Y.toSemantics.Fo) :=
  Fin.castOrderIso (folio_length_interpretation X Y)

noncomputable def storedIndex (X Y : Atlas)
    (n : Fin (Datra.Semantics.bouquetLength X.toSemantics.Fo Y.toSemantics.Fo)) :
    (pagination X Y).pages.Index :=
  (pagination X Y).pages.indexEquivFin.symm ((finiteIndexOrderIso X Y).symm n)

theorem storedIndex_number (X Y : Atlas)
    (n : Fin (Datra.Semantics.bouquetLength X.toSemantics.Fo Y.toSemantics.Fo)) :
    (pagination X Y).pages.indexNumber (storedIndex X Y n) = n.val := by
  rw [storedIndex, FolioData.indexEquivFin_symm_number]
  rfl

theorem storedIndex_pageAt (X Y : Atlas)
    (n : Fin (Datra.Semantics.bouquetLength X.toSemantics.Fo Y.toSemantics.Fo)) :
    (pagination X Y).pages.page (storedIndex X Y n) = (pagination X Y).pages.pageAt n.val := by
  unfold storedIndex FolioData.pageAt
  congr 2
  apply Fin.ext
  change n.val = min n.val ((pagination X Y).pages.depth - 1)
  have bound := ((finiteIndexOrderIso X Y).symm n).isLt
  change n.val < (pagination X Y).pages.depth at bound
  omega

theorem storedIndex_zero_page (X Y : Atlas) :
    (pagination X Y).pages.page (storedIndex X Y 0) = DomanialInclusion.singletonPage :=
  (storedIndex_pageAt X Y 0).trans (prefixPageAt_zero X Y (mergeDepth X Y - 1))

theorem finiteComponent_bound (X Y : Atlas)
    (n : Fin (Datra.Semantics.bouquetDepth X.toSemantics.Fo Y.toSemantics.Fo)) :
    n.val ≤ mergeDepth X Y - 1 := by
  have hn := n.isLt
  change n.val < max X.pages.depth Y.pages.depth at hn
  unfold mergeDepth
  rw [X.pages.length_eq_depth X.pagination.folio.valid,
    Y.pages.length_eq_depth Y.pagination.folio.valid]
  omega

theorem storedIndex_succ_page (X Y : Atlas)
    (n : Fin (Datra.Semantics.bouquetDepth X.toSemantics.Fo Y.toSemantics.Fo)) :
    (pagination X Y).pages.page (storedIndex X Y n.succ) = mergePage X Y n.val := by
  exact (storedIndex_pageAt X Y n.succ).trans
    ((prefixPageAt_succ X Y (mergeDepth X Y - 1) n.val).trans
      (congrArg (mergePage X Y) (Nat.min_eq_left (finiteComponent_bound X Y n))))

/-- Identify every stored finite page with the corresponding written bouquet
page. The positive pages retain their left/right tags and ordinal positions. -/
-- ALIGN: MERGE-FINITE-PAGE-EQUIVALENCE.
noncomputable def finitePageEquiv (X Y : Atlas) :
    (n : Fin (Datra.Semantics.bouquetLength X.toSemantics.Fo Y.toSemantics.Fo)) →
      ((pagination X Y).pages.page (storedIndex X Y n)).Carrier ≃
        (Datra.Semantics.bouquetChain X.toSemantics.Fo Y.toSemantics.Fo n).Obj :=
  Fin.cases
    (Equiv.cast (congrArg Page.Carrier (storedIndex_zero_page X Y)))
    (fun n => (Equiv.cast (congrArg Page.Carrier (storedIndex_succ_page X Y n))).trans
      (bouquetPageOrderIso X Y n).toEquiv)

theorem finitePageEquiv_succ_encode (X Y : Atlas)
    (n : Fin (Datra.Semantics.bouquetDepth X.toSemantics.Fo Y.toSemantics.Fo))
    (value : Sum (componentPage X n.val).Carrier (componentPage Y n.val).Carrier) :
    finitePageEquiv X Y n.succ
      (cast (congrArg Page.Carrier (storedIndex_succ_page X Y n).symm)
        (encodedPageCell X Y n.val value)) = toLex value := by
  simp only [finitePageEquiv, Fin.cases_succ, Equiv.trans_apply, Equiv.cast_apply,
    cast_cast, cast_eq]
  exact congrArg (Chain.sumOrderIso _ _) (pageOrderIso_encode X Y n.val value)

theorem storedIndex_succ_component (X Y : Atlas)
    (n : Fin (Datra.Semantics.bouquetDepth X.toSemantics.Fo Y.toSemantics.Fo))
    (bound : n.val < (mergeDepth X Y - 1) + 1) :
    storedIndex X Y n.succ = componentIndex X Y (mergeDepth X Y - 1) ⟨n.val, bound⟩ := by
  apply index_eq_of_number (pagination X Y).pages
  exact (storedIndex_number X Y n.succ).trans
    (componentIndex_number X Y (mergeDepth X Y - 1) ⟨n.val, bound⟩).symm

theorem resolve_finitePage_succ (X Y : Atlas)
    (n : Fin (Datra.Semantics.bouquetDepth X.toSemantics.Fo Y.toSemantics.Fo))
    (value : ((pagination X Y).pages.page (storedIndex X Y n.succ)).Carrier) :
    sourceAtIndex X Y (mergeDepth X Y - 1) (storedIndex X Y n.succ) value =
      resolvePageCell X Y n.val (cast (congrArg Page.Carrier (storedIndex_succ_page X Y n)) value) := by
  have bound : n.val < (mergeDepth X Y - 1) + 1 := by
    exact Nat.lt_succ_of_le (finiteComponent_bound X Y n)
  let cell := cast (congrArg Page.Carrier (storedIndex_succ_page X Y n)) value
  have result := sourceAtIndex_component X Y (mergeDepth X Y - 1) ⟨n.val, bound⟩ cell
  refine (sourceAtIndex_heq X Y (mergeDepth X Y - 1)
    (storedIndex_succ_component X Y n bound) ?_).trans result
  exact (cast_heq _ value).symm.trans (cast_heq _ cell).symm

theorem decodedPageCell_transport (X Y : Atlas) {n m : Nat} (precedes : m ≤ n)
    (source : ValidPageCell X Y n) (target : ValidPageCell X Y m)
    (arrow : Transport (resolvePageCell X Y n source) (resolvePageCell X Y m target)) :
    decodedPageCell X Y m target =
      Sum.map (X.pages.transport n m precedes).map (Y.pages.transport n m precedes).map
        (decodedPageCell X Y n source) := by
  unfold resolvePageCell at arrow
  cases sourceDecoded : decodedPageCell X Y n source <;>
    cases targetDecoded : decodedPageCell X Y m target <;>
    rw [sourceDecoded, targetDecoded] at arrow
  · cases arrow with
    | left arrow =>
      exact congrArg Sum.inl ((X.pages.traceAt_suffix_iff n m precedes _ _).mp arrow.transported).symm
  · cases arrow
  · cases arrow
  · cases arrow with
    | right arrow =>
      exact congrArg Sum.inr ((Y.pages.traceAt_suffix_iff n m precedes _ _).mp arrow.transported).symm

theorem pageOrderIso_decode (X Y : Atlas) (n : Nat) (cell : ValidPageCell X Y n) :
    pageOrderIso X Y n cell = decodedPageCell X Y n cell := by
  have same : encodedPageCell X Y n (decodedPageCell X Y n cell) = cell :=
    Subtype.ext (encode_decodedPageCell X Y n cell)
  exact (congrArg (pageOrderIso X Y n) same).symm.trans (pageOrderIso_encode X Y n _)

theorem finitePageEquiv_succ_decode (X Y : Atlas)
    (n : Fin (Datra.Semantics.bouquetDepth X.toSemantics.Fo Y.toSemantics.Fo))
    (value : ((pagination X Y).pages.page (storedIndex X Y n.succ)).Carrier) :
    finitePageEquiv X Y n.succ value =
      toLex (decodedPageCell X Y n.val
        (cast (congrArg Page.Carrier (storedIndex_succ_page X Y n)) value)) :=
  congrArg (Chain.sumOrderIso _ _) (pageOrderIso_decode X Y n.val _)

/-- The page equivalences intertwine every generated finite interval, so
they compare the complete folio diagrams rather than isolated pages. -/
-- ALIGN: MERGE-FINITE-INTERVAL-INTERPRETATION.
theorem finitePageEquiv_interval (X Y : Atlas)
    {i j : Fin (Datra.Semantics.bouquetLength X.toSemantics.Fo Y.toSemantics.Fo)}
    (precedes : i ≤ j)
    (value : ((pagination X Y).pages.page (storedIndex X Y j)).Carrier) :
    finitePageEquiv X Y i
      (((pagination X Y).pages.interval (storedIndex X Y j) (storedIndex X Y i)
        (by simpa only [storedIndex_number] using precedes)).map value) =
      Datra.Semantics.bouquetConMap X.toSemantics.Fo Y.toSemantics.Fo precedes
        (finitePageEquiv X Y j value) := by
  induction i using Fin.cases with
  | zero => exact @Subsingleton.elim Unit _ _ _
  | succ i =>
    induction j using Fin.cases with
    | zero => have : i.val + 1 ≤ 0 := precedes; omega
    | succ j =>
      have ordered : (pagination X Y).pages.indexNumber (storedIndex X Y i.succ) ≤
          (pagination X Y).pages.indexNumber (storedIndex X Y j.succ) := by
        simpa only [storedIndex_number] using precedes
      have transported := resolve_interval X Y (mergeDepth X Y - 1)
        (storedIndex X Y j.succ) (storedIndex X Y i.succ) ordered value
      rw [resolve_finitePage_succ, resolve_finitePage_succ] at transported
      have decoded := decodedPageCell_transport X Y (Nat.succ_le_succ_iff.mp precedes) _ _ transported
      rw [finitePageEquiv_succ_decode, finitePageEquiv_succ_decode]
      exact congrArg toLex decoded

noncomputable def finiteElementEquiv (X Y : Atlas) :
    (atlasMerge X Y).toSemantics.El ≃
      (Datra.Semantics.bouquetPag X.toSemantics Y.toSemantics).El where
  toFun source :=
    ⟨op (finiteIndexOrderIso X Y source.1.unop),
      finitePageEquiv X Y (finiteIndexOrderIso X Y source.1.unop) source.2⟩
  invFun target :=
    ⟨op ((finiteIndexOrderIso X Y).symm target.1.unop),
      (finitePageEquiv X Y target.1.unop).symm target.2⟩
  left_inv source := by
    obtain ⟨⟨n⟩, value⟩ := source
    apply Sigma.ext
    · rfl
    · exact heq_of_eq ((finitePageEquiv X Y (finiteIndexOrderIso X Y n)).symm_apply_apply value)
  right_inv target := by
    obtain ⟨⟨n⟩, value⟩ := target
    apply Sigma.ext
    · rfl
    · exact heq_of_eq ((finitePageEquiv X Y n).apply_symm_apply value)

noncomputable def finiteElements (X Y : Atlas) :
    (atlasMerge X Y).toSemantics.El ⥤
      (Datra.Semantics.bouquetPag X.toSemantics Y.toSemantics).El where
  obj := finiteElementEquiv X Y
  map {source target} arrow := CategoryOfElements.homMk _ _
    (homOfLE ((finiteIndexOrderIso X Y).monotone (leOfHom arrow.val.unop))).op (by
      have natural := finitePageEquiv_interval X Y
        ((finiteIndexOrderIso X Y).monotone (leOfHom arrow.val.unop)) source.2
      have transported := arrow.property
      change ((pagination X Y).pages.interval _ _ _).map source.2 = target.2 at transported
      exact natural.symm.trans
        (congrArg (finitePageEquiv X Y (finiteIndexOrderIso X Y target.1.unop)) transported))
  map_id _ := Subsingleton.elim _ _
  map_comp _ _ := Subsingleton.elim _ _

noncomputable def finiteElementsInverse (X Y : Atlas) :
    (Datra.Semantics.bouquetPag X.toSemantics Y.toSemantics).El ⥤
      (atlasMerge X Y).toSemantics.El where
  obj := (finiteElementEquiv X Y).symm
  map {source target} arrow := CategoryOfElements.homMk _ _
    (homOfLE ((finiteIndexOrderIso X Y).symm.monotone (leOfHom arrow.val.unop))).op (by
      apply (finitePageEquiv X Y target.1.unop).injective
      have natural := finitePageEquiv_interval X Y (leOfHom arrow.val.unop)
        ((finitePageEquiv X Y source.1.unop).symm source.2)
      simp only [Equiv.apply_symm_apply] at natural
      exact (natural.trans arrow.property).trans
        ((finitePageEquiv X Y target.1.unop).apply_symm_apply target.2).symm)
  map_id _ := Subsingleton.elim _ _
  map_comp _ _ := Subsingleton.elim _ _

/-- The executable finite merge and the written bouquet have equivalent
element categories, with mutually inverse page and tagged-cell operations. -/
-- ALIGN: MERGE-FINITE-ELEMENTS-EQUIVALENCE.
noncomputable def finiteElementsEquivalence (X Y : Atlas) :
    (atlasMerge X Y).toSemantics.El ≌
      (Datra.Semantics.bouquetPag X.toSemantics Y.toSemantics).El where
  functor := finiteElements X Y
  inverse := finiteElementsInverse X Y
  unitIso := NatIso.ofComponents
    (fun source => eqToIso ((finiteElementEquiv X Y).symm_apply_apply source).symm)
    (fun _ => Subsingleton.elim _ _)
  counitIso := NatIso.ofComponents
    (fun target => eqToIso ((finiteElementEquiv X Y).apply_symm_apply target))
    (fun _ => Subsingleton.elim _ _)
  functor_unitIso_comp _ := Subsingleton.elim _ _

end Datra.Executable.AtlasMerge
