import Executable.Atlas.Sequence.InclusionOrder
import Executable.Folio.Comparison

namespace Datra.Executable.AtlasSequence
open CategoryTheory Opposite

variable {count : Nat}

/-- The executable member-prefix ordering is exactly the lexicographic
ordering of the semantic finite family. -/
noncomputable def componentSumOrderIso (members : Fin count → Atlas) (n : Nat) :
    (componentSum members n).toSemantics.Obj ≃o
      (Datra.Semantics.Chain.finiteSum (fun i => (members i).toSemantics.Fo.pageChain n)).Obj where
  toFun := toLex
  invFun := ofLex
  left_inv _ := rfl
  right_inv _ := rfl
  map_rel_iff' := by
    rintro ⟨i, a⟩ ⟨j, b⟩
    change Sigma.Lex (fun i j : Fin count => i < j)
      (fun index x y => ((componentPage members n index).chain.position x).toSemantics ≤
        ((componentPage members n index).chain.position y).toSemantics) ⟨i, a⟩ ⟨j, b⟩ ↔
      ((componentSum members n).position ⟨i, a⟩).toSemantics ≤
        ((componentSum members n).position ⟨j, b⟩).toSemantics
    rw [componentSum_position_le_iff]
    constructor
    · intro ordered
      cases ordered with
      | left _ _ earlier => exact Or.inl earlier
      | right _ _ ordered => exact Or.inr ⟨rfl, ordered⟩
    · rintro (earlier | ⟨same, ordered⟩)
      · exact Sigma.Lex.left _ _ earlier
      · have indices : i = j := Fin.ext same
        subst j
        exact Sigma.Lex.right _ _ ordered

noncomputable def pageOrderIso (members : Fin count → Atlas) (n : Nat) :
    (pageChain members n).toSemantics.Obj ≃o (componentSum members n).toSemantics.Obj where
  toEquiv := (pageEncodingEquiv members n).symm
  map_rel_iff' := Iff.rfl

-- ALIGN: SEQUENCE-PAGE-ORDER-INTERPRETATION.
noncomputable def pageSumOrderIso (members : Fin count → Atlas) (n : Nat) :
    (pageChain members n).toSemantics.Obj ≃o
      (Datra.Semantics.Chain.finiteSum (fun i => (members i).toSemantics.Fo.pageChain n)).Obj :=
  (pageOrderIso members n).trans (componentSumOrderIso members n)

@[simp] theorem pageSumOrderIso_encode (members : Fin count → Atlas) (n : Nat) (value : PageValue members n) :
    pageSumOrderIso members n (encodedPageCell members n value) = toLex value :=
  congrArg toLex ((pageEncodingEquiv members n).symm_apply_apply value)

-- ALIGN: SEQUENCE-PAGE-TRANSITION-INTERPRETATION.
theorem pageTransition_interpretation (members : Fin count → Atlas) (n : Nat) (value : PageValue members (n + 1)) :
    pageSumOrderIso members n ((pageTransition members n).map (encodedPageCell members (n + 1) value)) =
      (Datra.Semantics.ConHom.finiteSum (fun i =>
        ((members i).pages.transport (n + 1) n (Nat.le_succ n)).toSemantics))
        (pageSumOrderIso members (n + 1) (encodedPageCell members (n + 1) value)) := by
  rw [pageTransition_encode, pageSumOrderIso_encode, pageSumOrderIso_encode]
  rfl

theorem sequenceDepth_interpretation (members : Fin count → Atlas) :
    sequenceDepth members = Datra.Semantics.sequenceDepth (fun i => (members i).toSemantics.Fo) := by
  apply le_antisymm
  · have foldBound (values : List Nat) (initial bound : Nat) (initialBound : initial ≤ bound)
        (valuesBound : ∀ value ∈ values, value ≤ bound) : values.foldl max initial ≤ bound := by
      induction values generalizing initial with
      | nil => exact initialBound
      | cons first rest ih =>
        exact ih (max initial first) (max_le initialBound (valuesBound first (List.mem_cons_self ..)))
          (fun value member => valuesBound value (List.mem_cons_of_mem _ member))
    apply foldBound _ _ _ (Nat.zero_le _)
    intro value member
    obtain ⟨index, same⟩ := List.mem_ofFn.mp member
    rw [← same, (members index).pages.length_eq_depth (members index).pagination.folio.valid]
    exact Datra.Semantics.sequenceMember_depth (fun i => (members i).toSemantics.Fo) index
  · apply Finset.sup_le
    intro index _
    exact memberDepth_bound members index

-- ALIGN: SEQUENCE-FOLIO-LENGTH-INTERPRETATION.
theorem folio_length_interpretation (positive : 0 < count) (members : Fin count → Atlas) :
    (folio positive members).data.toSemantics.length =
      Datra.Semantics.sequenceLength (fun i => (members i).toSemantics.Fo) := by
  rw [(folio positive members).data.toSemantics_length (folio positive members).valid, folio_length]
  exact congrArg (· + 1) (sequenceDepth_interpretation members)

-- ALIGN: SEQUENCE-FINITE-INDEX-INTERPRETATION.
noncomputable def finiteIndexOrderIso (positive : 0 < count) (members : Fin count → Atlas) :
    Fin (pagination positive members).pages.depth ≃o
      Fin (Datra.Semantics.sequenceLength (fun i => (members i).toSemantics.Fo)) :=
  Fin.castOrderIso (folio_length_interpretation positive members)

noncomputable def storedIndex (positive : 0 < count) (members : Fin count → Atlas)
    (n : Fin (Datra.Semantics.sequenceLength (fun i => (members i).toSemantics.Fo))) :
    (pagination positive members).pages.Index :=
  (pagination positive members).pages.indexEquivFin.symm ((finiteIndexOrderIso positive members).symm n)

theorem storedIndex_number (positive : 0 < count) (members : Fin count → Atlas)
    (n : Fin (Datra.Semantics.sequenceLength (fun i => (members i).toSemantics.Fo))) :
    (pagination positive members).pages.indexNumber (storedIndex positive members n) = n.val := by
  rw [storedIndex, FolioData.indexEquivFin_symm_number]
  rfl

theorem storedIndex_pageAt (positive : 0 < count) (members : Fin count → Atlas)
    (n : Fin (Datra.Semantics.sequenceLength (fun i => (members i).toSemantics.Fo))) :
    (pagination positive members).pages.page (storedIndex positive members n) = (pagination positive members).pages.pageAt n.val := by
  unfold storedIndex FolioData.pageAt
  congr 2
  apply Fin.ext
  change n.val = min n.val ((pagination positive members).pages.depth - 1)
  have bound := ((finiteIndexOrderIso positive members).symm n).isLt
  change n.val < (pagination positive members).pages.depth at bound
  omega

theorem storedIndex_zero_page (positive : 0 < count) (members : Fin count → Atlas) :
    (pagination positive members).pages.page (storedIndex positive members 0) = DomanialInclusion.singletonPage :=
  (storedIndex_pageAt positive members 0).trans (prefixPageAt_zero positive members (sequenceDepth members - 1))

theorem finiteComponent_bound (members : Fin count → Atlas)
    (n : Fin (Datra.Semantics.sequenceDepth (fun i => (members i).toSemantics.Fo))) :
    n.val ≤ sequenceDepth members - 1 := by
  have hn := n.isLt
  have same := sequenceDepth_interpretation members
  omega

theorem storedIndex_succ_page (positive : 0 < count) (members : Fin count → Atlas)
    (n : Fin (Datra.Semantics.sequenceDepth (fun i => (members i).toSemantics.Fo))) :
    (pagination positive members).pages.page (storedIndex positive members n.succ) = sequencePage members n.val := by
  exact (storedIndex_pageAt positive members n.succ).trans
    ((prefixPageAt_succ positive members (sequenceDepth members - 1) n.val).trans
      (congrArg (sequencePage members) (Nat.min_eq_left (finiteComponent_bound members n))))

/-- Identify every stored finite page with the corresponding semantic finite sequence
page. The positive pages retain their member tags and ordinal positions. -/
-- ALIGN: SEQUENCE-FINITE-PAGE-EQUIVALENCE.
noncomputable def finitePageEquiv (positive : 0 < count) (members : Fin count → Atlas) :
    (n : Fin (Datra.Semantics.sequenceLength (fun i => (members i).toSemantics.Fo))) →
      ((pagination positive members).pages.page (storedIndex positive members n)).Carrier ≃
        (Datra.Semantics.sequenceChain (fun i => (members i).toSemantics.Fo) n).Obj :=
  Fin.cases
    (Equiv.cast (congrArg Page.Carrier (storedIndex_zero_page positive members)))
    (fun n => (Equiv.cast (congrArg Page.Carrier (storedIndex_succ_page positive members n))).trans
      (pageSumOrderIso members n.val).toEquiv)

theorem finitePageEquiv_succ_encode (positive : 0 < count) (members : Fin count → Atlas)
    (n : Fin (Datra.Semantics.sequenceDepth (fun i => (members i).toSemantics.Fo)))
    (value : PageValue members n.val) :
    finitePageEquiv positive members n.succ
      (cast (congrArg Page.Carrier (storedIndex_succ_page positive members n).symm)
        (encodedPageCell members n.val value)) = toLex value := by
  simp only [finitePageEquiv, Fin.cases_succ, Equiv.trans_apply, Equiv.cast_apply,
    cast_cast, cast_eq]
  exact pageSumOrderIso_encode members n.val value

theorem storedIndex_succ_component (positive : 0 < count) (members : Fin count → Atlas)
    (n : Fin (Datra.Semantics.sequenceDepth (fun i => (members i).toSemantics.Fo)))
    (bound : n.val < (sequenceDepth members - 1) + 1) :
    storedIndex positive members n.succ = componentIndex positive members (sequenceDepth members - 1) ⟨n.val, bound⟩ := by
  apply FolioData.index_eq_of_number (pagination positive members).pages
  exact (storedIndex_number positive members n.succ).trans
    (componentIndex_number positive members (sequenceDepth members - 1) ⟨n.val, bound⟩).symm

theorem resolve_finitePage_succ (positive : 0 < count) (members : Fin count → Atlas)
    (n : Fin (Datra.Semantics.sequenceDepth (fun i => (members i).toSemantics.Fo)))
    (value : ((pagination positive members).pages.page (storedIndex positive members n.succ)).Carrier) :
    sourceAtIndex positive members (sequenceDepth members - 1) (storedIndex positive members n.succ) value =
      resolvePageCell members n.val (cast (congrArg Page.Carrier (storedIndex_succ_page positive members n)) value) := by
  have bound : n.val < (sequenceDepth members - 1) + 1 := by
    exact Nat.lt_succ_of_le (finiteComponent_bound members n)
  let cell := cast (congrArg Page.Carrier (storedIndex_succ_page positive members n)) value
  have result := sourceAtIndex_component positive members (sequenceDepth members - 1) ⟨n.val, bound⟩ cell
  refine (sourceAtIndex_heq positive members (sequenceDepth members - 1)
    (storedIndex_succ_component positive members n bound) ?_).trans result
  exact (cast_heq _ value).symm.trans (cast_heq _ cell).symm

theorem decodedPageCell_transport (members : Fin count → Atlas) {n m : Nat} (precedes : m ≤ n)
    (source : ValidPageCell members n) (target : ValidPageCell members m)
    (arrow : Transport (resolvePageCell members n source) (resolvePageCell members m target)) :
    decodedPageCell members m target =
      ⟨(decodedPageCell members n source).1,
        ((members (decodedPageCell members n source).1).pages.transport n m precedes).map
          (decodedPageCell members n source).2⟩ := by
  obtain ⟨⟨i, a⟩, ha⟩ := source.property
  obtain ⟨⟨j, b⟩, hb⟩ := target.property
  have ea : encodedPageCell members n ⟨i, a⟩ = source := Subtype.ext ha
  have eb : encodedPageCell members m ⟨j, b⟩ = target := Subtype.ext hb
  rw [← ea, ← eb, resolvePageCell_encode, resolvePageCell_encode] at arrow
  rw [← ea, ← eb, decodedPageCell_encode, decodedPageCell_encode]
  cases arrow with
  | member _ arrow =>
    exact congrArg (Sigma.mk i)
      (((members i).pages.traceAt_suffix_iff n m precedes a b).mp arrow.transported).symm

theorem pageSumOrderIso_decode (members : Fin count → Atlas) (n : Nat) (cell : ValidPageCell members n) :
    pageSumOrderIso members n cell = toLex (decodedPageCell members n cell) := rfl

theorem finitePageEquiv_succ_decode (positive : 0 < count) (members : Fin count → Atlas)
    (n : Fin (Datra.Semantics.sequenceDepth (fun i => (members i).toSemantics.Fo)))
    (value : ((pagination positive members).pages.page (storedIndex positive members n.succ)).Carrier) :
    finitePageEquiv positive members n.succ value =
      toLex (decodedPageCell members n.val
        (cast (congrArg Page.Carrier (storedIndex_succ_page positive members n)) value)) :=
  pageSumOrderIso_decode members n.val _

/-- The page equivalences intertwine every generated finite interval, so
they compare the complete folio diagrams rather than isolated pages. -/
-- ALIGN: SEQUENCE-FINITE-INTERVAL-INTERPRETATION.
theorem finitePageEquiv_interval (positive : 0 < count) (members : Fin count → Atlas)
    {i j : Fin (Datra.Semantics.sequenceLength (fun i => (members i).toSemantics.Fo))}
    (precedes : i ≤ j)
    (value : ((pagination positive members).pages.page (storedIndex positive members j)).Carrier) :
    finitePageEquiv positive members i
      (((pagination positive members).pages.interval (storedIndex positive members j) (storedIndex positive members i)
        (by simpa only [storedIndex_number] using precedes)).map value) =
      Datra.Semantics.sequenceConMap positive (fun i => (members i).toSemantics.Fo) precedes
        (finitePageEquiv positive members j value) := by
  induction i using Fin.cases with
  | zero => exact @Subsingleton.elim Unit _ _ _
  | succ i =>
    induction j using Fin.cases with
    | zero => have : i.val + 1 ≤ 0 := precedes; omega
    | succ j =>
      have ordered : (pagination positive members).pages.indexNumber (storedIndex positive members i.succ) ≤
          (pagination positive members).pages.indexNumber (storedIndex positive members j.succ) := by
        simpa only [storedIndex_number] using precedes
      have transported := resolve_interval positive members (sequenceDepth members - 1)
        (storedIndex positive members j.succ) (storedIndex positive members i.succ) ordered value
      rw [resolve_finitePage_succ, resolve_finitePage_succ] at transported
      have decoded := decodedPageCell_transport members (Nat.succ_le_succ_iff.mp precedes) _ _ transported
      rw [finitePageEquiv_succ_decode, finitePageEquiv_succ_decode]
      exact congrArg toLex decoded

noncomputable def finiteComparison (positive : 0 < count) (members : Fin count → Atlas) :
    FolioData.Comparison (pagination positive members).pages
      (Datra.Semantics.sequenceFolio positive (fun i => (members i).toSemantics.Fo)) where
  length_eq := folio_length_interpretation positive members
  cell := finitePageEquiv positive members
  natural := finitePageEquiv_interval positive members

noncomputable def finiteElementEquiv (positive : 0 < count) (members : Fin count → Atlas) :
    (atlasSequence positive members).toSemantics.El ≃
      (Datra.Semantics.sequenceFolio positive (fun i => (members i).toSemantics.Fo)).El :=
  (finiteComparison positive members).elementEquiv

noncomputable def finiteElements (positive : 0 < count) (members : Fin count → Atlas) :
    (atlasSequence positive members).toSemantics.El ⥤
      (Datra.Semantics.sequenceFolio positive (fun i => (members i).toSemantics.Fo)).El :=
  (finiteComparison positive members).elements

noncomputable def finiteElementsInverse (positive : 0 < count) (members : Fin count → Atlas) :
    (Datra.Semantics.sequenceFolio positive (fun i => (members i).toSemantics.Fo)).El ⥤
      (atlasSequence positive members).toSemantics.El :=
  (finiteComparison positive members).elementsInverse

/-- The executable flattened sequence and its semantic finite family have
mutually inverse functors on page elements and their interval arrows. -/
-- ALIGN: SEQUENCE-FINITE-ELEMENTS-EQUIVALENCE.
noncomputable def finiteElementsEquivalence (positive : 0 < count) (members : Fin count → Atlas) :
    (atlasSequence positive members).toSemantics.El ≌
      (Datra.Semantics.sequenceFolio positive (fun i => (members i).toSemantics.Fo)).El :=
  (finiteComparison positive members).elementsEquivalence

end Datra.Executable.AtlasSequence
