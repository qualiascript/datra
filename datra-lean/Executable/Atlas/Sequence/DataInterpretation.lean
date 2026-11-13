import Executable.Atlas.Sequence.Interpretation
import Executable.Atlas.OriginInterpretation
import Executable.Atlas.Comparison

namespace Datra.Executable.AtlasSequence
open CategoryTheory Opposite

variable {count : Nat}

theorem resolve_fromFinite (positive : 0 < count) (members : Fin count → Atlas)
    (source : (atlasSequence positive members).toSemantics.El) :
    resolveStoredElement positive members
        ((FolioData.ValidElement.fromFinite (pagination positive members).pages).obj source) =
      sourceAtIndex positive members (sequenceDepth members - 1)
        ((pagination positive members).pages.indexEquivFin.symm source.1.unop) source.2 := by
  obtain ⟨⟨n⟩, value⟩ := source
  rw [← FolioData.ValidElement.ofFinite_interpretation]
  unfold resolveStoredElement FolioData.ValidElement.ofFinite
  rw [FolioData.ValidElement.occurrence_ofOccurrence]
  unfold resolveStoredOccurrence
  apply sourceAtIndex_heq
  · simp only [FolioData.paddedIndex_fin]
  · exact cast_heq _ value

theorem resolve_finitePage_zero (positive : 0 < count) (members : Fin count → Atlas)
    (value : ((pagination positive members).pages.page (storedIndex positive members 0)).Carrier) :
    sourceAtIndex positive members (sequenceDepth members - 1) (storedIndex positive members 0) value = .origin := by
  have index : storedIndex positive members 0 =
      (prefixFolio positive members (sequenceDepth members - 1)).data.firstIndex := by
    apply FolioData.index_eq_of_number (pagination positive members).pages
    exact (storedIndex_number positive members 0).trans
      ((prefixFolio positive members (sequenceDepth members - 1)).data.firstIndex_number).symm
  have result := sourceAtIndex_heq positive members (sequenceDepth members - 1) index
    (cast_heq (congrArg (fun i => ((pagination positive members).pages.page i).Carrier) index) value).symm
  exact result.trans (sourceAtIndex_first positive members _ _)

theorem radix_eq_iff {a b i j : Nat} (hi : i < count) (hj : j < count) :
    count * a + i = count * b + j ↔ a = b ∧ i = j := by
  constructor
  · intro same
    have tags := congrArg (fun n => n % count) same
    have ranks := congrArg (fun n => n / count) same
    exact ⟨by simpa [Nat.mul_add_div (Nat.zero_lt_of_lt hi), Nat.div_eq_of_lt hi,
      Nat.div_eq_of_lt hj] using ranks,
      by simpa [Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt hj] using tags⟩
  · rintro ⟨rfl, rfl⟩; rfl

theorem finiteSum_rank_exists (members : Fin count → Datra.Semantics.DomIns)
    (index : Fin count) (rank : Nat) :
    (∃ value : Datra.Semantics.domFiniteSum members,
      (Datra.Semantics.domFiniteSum members).toDom.rank value = count * rank + index.val) ↔
      ∃ value : members index, (members index).toDom.rank value = rank := by
  constructor
  · rintro ⟨⟨i, value⟩, same⟩
    have equations := (radix_eq_iff i.isLt index.isLt).mp same
    have indices : i = index := Fin.ext equations.2
    subst i
    exact ⟨value, equations.1⟩
  · rintro ⟨value, same⟩
    exact ⟨⟨index, value⟩, congrArg (fun n => count * n + index.val) same⟩

/-- With a bounded member tag, membership is exactly occurrence of the radix
rank in the semantic cell. The bound prevents aliases from malformed tags. -/
-- ALIGN: SEQUENCE-FINITE-MEMBERSHIP.
theorem contains_finite_interpretation (positive : 0 < count) (members : Fin count → Atlas)
    (n : Fin (Datra.Semantics.sequenceLength (fun i => (members i).toSemantics.Fo)))
    (value : ((pagination positive members).pages.page (storedIndex positive members n)).Carrier)
    {cell : PageElementCell} (datum : Datum cell) (bounded : datum.member < count) :
    contains (sourceAtIndex positive members (sequenceDepth members - 1)
      (storedIndex positive members n) value) datum = true ↔
      ∃ result : Datra.Semantics.sequenceDom positive (fun i => (members i).toSemantics)
          ⟨op n, finitePageEquiv positive members n value⟩,
        (Datra.Semantics.sequenceDom positive (fun i => (members i).toSemantics)
          ⟨op n, finitePageEquiv positive members n value⟩).toDom.rank result = datumRank count datum := by
  induction n using Fin.cases with
  | zero =>
    rw [resolve_finitePage_zero]
    change contains SourceCell.origin datum = true ↔
      ∃ result : Datra.Semantics.imageDom (𝟙 (Datra.Semantics.domFiniteSum
          (fun i => Datra.Semantics.extent (members i).toSemantics))),
        (Datra.Semantics.imageDom (𝟙 (Datra.Semantics.domFiniteSum
          (fun i => Datra.Semantics.extent (members i).toSemantics)))).toDom.rank result = datumRank count datum
    rw [imageDom_rank_exists]
    simp only [contains, dif_pos bounded]
    exact (extentContainsRank_interpretation (members ⟨datum.member, bounded⟩) datum.originRank).trans
      (finiteSum_rank_exists (fun i => Datra.Semantics.extent (members i).toSemantics)
        ⟨datum.member, bounded⟩ datum.originRank).symm
  | succ n =>
    rw [resolve_finitePage_succ, finitePageEquiv_succ_decode]
    let pageCell := cast (congrArg Page.Carrier (storedIndex_succ_page positive members n)) value
    obtain ⟨⟨index, source⟩, encoded⟩ := (pageEncodingEquiv members n.val).surjective pageCell
    change contains (resolvePageCell members n.val pageCell) datum = true ↔ _
    change encodedPageCell members n.val ⟨index, source⟩ = pageCell at encoded
    dsimp only [pageCell] at encoded ⊢
    rw [← encoded, resolvePageCell_encode, decodedPageCell_encode]
    rw [Datra.Semantics.sequenceDom, imageDom_rank_exists]
    change (datum.member == index.val &&
      (members index).cellContainsRank (FolioData.ValidElement.ofOccurrence ⟨n.val, source⟩) datum.originRank) = true ↔
        ∃ a, count * (Datra.Semantics.extent (members index).toSemantics).toDom.rank
          (Datra.Semantics.originImage (members index).toSemantics _ a) + index.val =
            count * datum.originRank + datum.member
    rw [Bool.and_eq_true_iff, beq_iff_eq, componentContainsRank_interpretation]
    constructor
    · rintro ⟨tag, a, same⟩
      exact ⟨a, (radix_eq_iff index.isLt bounded).mpr ⟨same, tag.symm⟩⟩
    · rintro ⟨a, same⟩
      have equations := (radix_eq_iff index.isLt bounded).mp same
      exact ⟨equations.2.symm, a, equations.1⟩

theorem finiteDatum_valid_iff (positive : 0 < count) (members : Fin count → Atlas)
    (source : (atlasSequence positive members).toSemantics.El)
    (datum : Datum ((FolioData.ValidElement.fromFinite (pagination positive members).pages).obj source).val.cell) :
    datum.Valid positive members ↔ datum.member < count ∧
      ∃ result : (Datra.Semantics.sequenceAtlas positive (fun i => (members i).toSemantics)).Da.obj
          (finiteElementEquiv positive members source),
        ((Datra.Semantics.sequenceAtlas positive (fun i => (members i).toSemantics)).Da.obj
          (finiteElementEquiv positive members source)).toDom.rank result = datumRank count datum := by
  rw [Datum.valid_iff, resolve_fromFinite]
  constructor
  · intro valid
    have bounded := contains_bounded _ datum valid
    exact ⟨bounded, (contains_finite_interpretation positive members
      (finiteIndexOrderIso positive members source.1.unop) source.2 datum bounded).mp valid⟩
  · rintro ⟨bounded, value⟩
    exact (contains_finite_interpretation positive members
      (finiteIndexOrderIso positive members source.1.unop) source.2 datum bounded).mpr value

/-- Decode semantic image data using the runtime quotient and remainder.
Membership follows from the exact cell comparison, including the member bound. -/
-- ALIGN: SEQUENCE-FINITE-DATA-DECODE.
noncomputable def finiteDataDecode (positive : 0 < count) (members : Fin count → Atlas)
    (source : (atlasSequence positive members).toSemantics.El)
    (datum : (Datra.Semantics.sequenceAtlas positive (fun i => (members i).toSemantics)).Da.obj
      (finiteElementEquiv positive members source)) : (atlasSequence positive members).toSemantics.Da.obj source :=
  ⟨decode _ count (((Datra.Semantics.sequenceAtlas positive (fun i => (members i).toSemantics)).Da.obj
      (finiteElementEquiv positive members source)).toDom.rank datum),
    (finiteDatum_valid_iff positive members source _).mpr
      ⟨(rank_decode _ _ _ positive).1, datum, (rank_decode _ _ _ positive).2.symm⟩⟩

theorem finiteDataDecode_rank (positive : 0 < count) (members : Fin count → Atlas)
    (source : (atlasSequence positive members).toSemantics.El)
    (datum : (Datra.Semantics.sequenceAtlas positive (fun i => (members i).toSemantics)).Da.obj
      (finiteElementEquiv positive members source)) :
    ((atlasSequence positive members).toSemantics.Da.obj source).toDom.rank
        (finiteDataDecode positive members source datum) =
      ((Datra.Semantics.sequenceAtlas positive (fun i => (members i).toSemantics)).Da.obj
        (finiteElementEquiv positive members source)).toDom.rank datum := (rank_decode _ _ _ positive).2

theorem finiteDataDecode_bijective (positive : 0 < count) (members : Fin count → Atlas)
    (source : (atlasSequence positive members).toSemantics.El) :
    Function.Bijective (finiteDataDecode positive members source) := by
  constructor
  · intro a b same
    apply ((Datra.Semantics.sequenceAtlas positive (fun i => (members i).toSemantics)).Da.obj
      (finiteElementEquiv positive members source)).toDom.rank.injective
    simpa only [finiteDataDecode_rank] using
      congrArg ((atlasSequence positive members).toSemantics.Da.obj source).toDom.rank same
  · intro datum
    obtain ⟨original, rank⟩ := ((finiteDatum_valid_iff positive members source datum.val).mp datum.property).2
    refine ⟨original, ?_⟩
    apply ((atlasSequence positive members).toSemantics.Da.obj source).toDom.rank.injective
    exact (finiteDataDecode_rank positive members source original).trans rank

-- ALIGN: SEQUENCE-FINITE-DATA-EQUIVALENCE.
noncomputable def finiteDataEquiv (positive : 0 < count) (members : Fin count → Atlas)
    (source : (atlasSequence positive members).toSemantics.El) :
    (atlasSequence positive members).toSemantics.Da.obj source ≃
      (Datra.Semantics.sequenceAtlas positive (fun i => (members i).toSemantics)).Da.obj
        (finiteElementEquiv positive members source) :=
  (Equiv.ofBijective (finiteDataDecode positive members source)
    (finiteDataDecode_bijective positive members source)).symm

-- ALIGN: SEQUENCE-FINITE-DATA-RANK.
theorem finiteDataEquiv_rank (positive : 0 < count) (members : Fin count → Atlas)
    (source : (atlasSequence positive members).toSemantics.El)
    (datum : (atlasSequence positive members).toSemantics.Da.obj source) :
    ((Datra.Semantics.sequenceAtlas positive (fun i => (members i).toSemantics)).Da.obj
      (finiteElementEquiv positive members source)).toDom.rank (finiteDataEquiv positive members source datum) =
      ((atlasSequence positive members).toSemantics.Da.obj source).toDom.rank datum := by
  have roundtrip := (finiteDataEquiv positive members source).symm_apply_apply datum
  exact (finiteDataDecode_rank positive members source (finiteDataEquiv positive members source datum)).symm.trans
    (congrArg ((atlasSequence positive members).toSemantics.Da.obj source).toDom.rank roundtrip)

noncomputable def rankComparison (positive : 0 < count) (members : Fin count → Atlas) :
    (atlasSequence positive members).RankComparison
      (Datra.Semantics.sequenceAtlas positive (fun i => (members i).toSemantics)) where
  folio := finiteComparison positive members
  dataEquiv := finiteDataEquiv positive members
  data_rank := finiteDataEquiv_rank positive members
  source_map_rank _ datum := retag_rank count datum.val
  target_map_rank _ _ := rfl

-- ALIGN: SEQUENCE-FINITE-DATA-NATURALITY.
theorem finiteDataEquiv_naturality (positive : 0 < count) (members : Fin count → Atlas)
    {source target : (atlasSequence positive members).toSemantics.El}
    (arrow : source ⟶ target) (datum : (atlasSequence positive members).toSemantics.Da.obj source) :
    finiteDataEquiv positive members target ((atlasSequence positive members).toSemantics.Da.map arrow datum) =
      (Datra.Semantics.sequenceAtlas positive (fun i => (members i).toSemantics)).Da.map
        ((finiteElements positive members).map arrow) (finiteDataEquiv positive members source datum) :=
  (rankComparison positive members).naturality arrow datum

/-- The complete executable sequence is isomorphic to the semantic finite
sequence, preserving both the page structure and the radix-ranked data action. -/
-- ALIGN: SEQUENCE-ATLAS-ISOMORPHISM.
noncomputable def interpretationIso (positive : 0 < count) (members : Fin count → Atlas) :
    (atlasSequence positive members).toSemantics ≅
      Datra.Semantics.sequenceAtlas positive (fun i => (members i).toSemantics) :=
  (rankComparison positive members).iso

end Datra.Executable.AtlasSequence
