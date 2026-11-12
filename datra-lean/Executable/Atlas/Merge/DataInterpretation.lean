import Executable.Atlas.Merge.Interpretation

namespace Datra.Executable.AtlasMerge
open CategoryTheory Opposite

theorem componentFinite_normalize (X : Atlas) (n : Nat) (value : (componentPage X n).Carrier) :
    (FolioData.ValidElement.fromFinite X.pages).obj
      (⟨op (X.toSemantics.Fo.paddedIndex n), value⟩ : X.toSemantics.El) =
      (FolioData.ValidElement.ofOccurrence (⟨n, value⟩ : X.pages.Occurrence)).normalize := by
  have result := FolioData.ValidElement.fromFinite_collapse
    (FolioData.ValidElement.ofOccurrence (⟨n, value⟩ : X.pages.Occurrence))
  change (FolioData.ValidElement.fromFinite X.pages).obj
    (X.pages.toSemantics.collapseElements.obj ((FolioData.Occurrence.toSemantics X.pages).obj
      (FolioData.ValidElement.ofOccurrence (⟨n, value⟩ : X.pages.Occurrence)).occurrence)) = _ at result
  rw [FolioData.ValidElement.occurrence_ofOccurrence] at result
  exact result

theorem componentContainsRank_interpretation (X : Atlas) (n : Nat)
    (value : (componentPage X n).Carrier) (valueRank : Nat) :
    X.cellContainsRank (FolioData.ValidElement.ofOccurrence ⟨n, value⟩) valueRank = true ↔
      ∃ datum : X.toSemantics.Da.obj ⟨op (X.toSemantics.Fo.paddedIndex n), value⟩,
        (Datra.Semantics.extent X.toSemantics).toDom.rank
          (Datra.Semantics.originImage X.toSemantics _ datum) = valueRank := by
  have normalized : ∀ source : X.Element,
      X.cellContainsRank source.normalize valueRank = true ↔ X.cellContainsRank source valueRank = true := by
    intro source
    simp only [X.cellContainsRank_iff, X.originImageRank_normalize]
    rfl
  rw [← normalized, ← componentFinite_normalize, X.cellContainsRank_iff]
  simp only [X.originImageRank_interpretation]
  rfl

theorem extentContainsRank_interpretation (X : Atlas) (valueRank : Nat) :
    X.extentContainsRank valueRank = true ↔
      ∃ datum : Datra.Semantics.extent X.toSemantics,
        (Datra.Semantics.extent X.toSemantics).toDom.rank datum = valueRank := by
  rw [← X.extent_interpretation]
  exact X.extentContainsRank_iff valueRank

theorem imageDom_rank_exists {A R : Datra.Semantics.DomIns} (map : A ⟶ R) (valueRank : Nat) :
    (∃ value : Datra.Semantics.imageDom map,
      (Datra.Semantics.imageDom map).toDom.rank value = valueRank) ↔
    ∃ value : A, R.toDom.rank (map value) = valueRank := by
  constructor
  · rintro ⟨⟨value, original, rfl⟩, same⟩
    exact ⟨original, same⟩
  · rintro ⟨value, same⟩
    exact ⟨⟨map value, value, rfl⟩, same⟩

theorem resolve_fromFinite (X Y : Atlas) (source : (atlasMerge X Y).toSemantics.El) :
    resolveStoredElement X Y ((FolioData.ValidElement.fromFinite (pagination X Y).pages).obj source) =
      sourceAtIndex X Y (mergeDepth X Y - 1)
        ((pagination X Y).pages.indexEquivFin.symm source.1.unop) source.2 := by
  obtain ⟨⟨n⟩, value⟩ := source
  rw [← FolioData.ValidElement.ofFinite_interpretation]
  unfold resolveStoredElement FolioData.ValidElement.ofFinite
  rw [FolioData.ValidElement.occurrence_ofOccurrence]
  unfold resolveStoredOccurrence
  apply sourceAtIndex_heq
  · simp only [FolioData.paddedIndex_fin]
  · exact cast_heq _ value

theorem resolve_finitePage_zero (X Y : Atlas)
    (value : ((pagination X Y).pages.page (storedIndex X Y 0)).Carrier) :
    sourceAtIndex X Y (mergeDepth X Y - 1) (storedIndex X Y 0) value = .origin := by
  have index : storedIndex X Y 0 = (prefixFolio X Y (mergeDepth X Y - 1)).data.firstIndex := by
    apply index_eq_of_number (pagination X Y).pages
    exact (storedIndex_number X Y 0).trans
      ((prefixFolio X Y (mergeDepth X Y - 1)).data.firstIndex_number).symm
  have result := sourceAtIndex_heq X Y (mergeDepth X Y - 1) index
    (cast_heq (congrArg (fun i => ((pagination X Y).pages.page i).Carrier) index) value).symm
  exact result.trans (sourceAtIndex_first X Y _ _)

theorem sum_rank_left_exists (A B : Datra.Semantics.DomIns) (n : Nat) :
    (∃ value : Datra.Semantics.domSum A B, (Datra.Semantics.domSum A B).toDom.rank value = 2 * n) ↔
      ∃ value : A, A.toDom.rank value = n := by
  constructor
  · rintro ⟨value, rank⟩
    cases value with
    | inl value => exact ⟨value, by change 2 * A.toDom.rank value = 2 * n at rank; omega⟩
    | inr value => change 2 * B.toDom.rank value + 1 = 2 * n at rank; omega
  · rintro ⟨value, rank⟩
    exact ⟨Sum.inl value, congrArg (2 * ·) rank⟩

theorem sum_rank_right_exists (A B : Datra.Semantics.DomIns) (n : Nat) :
    (∃ value : Datra.Semantics.domSum A B, (Datra.Semantics.domSum A B).toDom.rank value = 2 * n + 1) ↔
      ∃ value : B, B.toDom.rank value = n := by
  constructor
  · rintro ⟨value, rank⟩
    cases value with
    | inl value => change 2 * A.toDom.rank value = 2 * n + 1 at rank; omega
    | inr value => exact ⟨value, by change 2 * B.toDom.rank value + 1 = 2 * n + 1 at rank; omega⟩
  · rintro ⟨value, rank⟩
    exact ⟨Sum.inr value, congrArg (fun k => 2 * k + 1) rank⟩

/-- The runtime membership test accepts exactly the ranks occurring in the
written bouquet's image Dominion, at the matched finite cell. -/
-- ALIGN: MERGE-BOUQUET-MEMBERSHIP.
theorem contains_finite_interpretation (X Y : Atlas)
    (n : Fin (Datra.Semantics.bouquetLength X.toSemantics.Fo Y.toSemantics.Fo))
    (value : ((pagination X Y).pages.page (storedIndex X Y n)).Carrier)
    {cell : PageElementCell} (datum : Datum cell) :
    contains (sourceAtIndex X Y (mergeDepth X Y - 1) (storedIndex X Y n) value) datum = true ↔
      ∃ result : Datra.Semantics.bouquetDom X.toSemantics Y.toSemantics
          ⟨op n, finitePageEquiv X Y n value⟩,
        (Datra.Semantics.bouquetDom X.toSemantics Y.toSemantics
          ⟨op n, finitePageEquiv X Y n value⟩).toDom.rank result = datumRank datum := by
  induction n using Fin.cases with
  | zero =>
    rw [resolve_finitePage_zero]
    change contains SourceCell.origin datum = true ↔
      ∃ result : Datra.Semantics.imageDom (𝟙 (Datra.Semantics.domSum
          (Datra.Semantics.extent X.toSemantics) (Datra.Semantics.extent Y.toSemantics))),
        (Datra.Semantics.imageDom (𝟙 (Datra.Semantics.domSum
          (Datra.Semantics.extent X.toSemantics) (Datra.Semantics.extent Y.toSemantics)))).toDom.rank result =
            datumRank datum
    rw [imageDom_rank_exists]
    cases datum with
    | left n =>
      change X.extentContainsRank n = true ↔ ∃ result, _ = 2 * n
      exact (extentContainsRank_interpretation X n).trans
        (sum_rank_left_exists (Datra.Semantics.extent X.toSemantics)
          (Datra.Semantics.extent Y.toSemantics) n).symm
    | right n =>
      change Y.extentContainsRank n = true ↔ ∃ result, _ = 2 * n + 1
      exact (extentContainsRank_interpretation Y n).trans
        (sum_rank_right_exists (Datra.Semantics.extent X.toSemantics)
          (Datra.Semantics.extent Y.toSemantics) n).symm
  | succ n =>
    rw [resolve_finitePage_succ]
    rw [finitePageEquiv_succ_decode X Y n value]
    unfold resolvePageCell
    cases decoded : decodedPageCell X Y n.val
      (cast (congrArg Page.Carrier (storedIndex_succ_page X Y n)) value) with
    | inl source =>
      rw [Datra.Semantics.bouquetDom, imageDom_rank_exists]
      cases datum with
      | left k =>
        change X.cellContainsRank (FolioData.ValidElement.ofOccurrence ⟨n.val, source⟩) k = true ↔
          ∃ a, 2 * (Datra.Semantics.extent X.toSemantics).toDom.rank
            (Datra.Semantics.originImage X.toSemantics _ a) = 2 * k
        rw [componentContainsRank_interpretation]
        constructor <;> rintro ⟨a, ha⟩ <;>
          exact ⟨a, by dsimp only [Datra.Semantics.Pag.cell] at ha ⊢; omega⟩
      | right k =>
        change false = true ↔ ∃ a, 2 * (Datra.Semantics.extent X.toSemantics).toDom.rank
          (Datra.Semantics.originImage X.toSemantics _ a) = 2 * k + 1
        constructor
        · intro impossible; contradiction
        · rintro ⟨a, impossible⟩; omega
    | inr source =>
      rw [Datra.Semantics.bouquetDom, imageDom_rank_exists]
      cases datum with
      | left k =>
        change false = true ↔ ∃ a, 2 * (Datra.Semantics.extent Y.toSemantics).toDom.rank
          (Datra.Semantics.originImage Y.toSemantics _ a) + 1 = 2 * k
        constructor
        · intro impossible; contradiction
        · rintro ⟨a, impossible⟩; omega
      | right k =>
        change Y.cellContainsRank (FolioData.ValidElement.ofOccurrence ⟨n.val, source⟩) k = true ↔
          ∃ a, 2 * (Datra.Semantics.extent Y.toSemantics).toDom.rank
            (Datra.Semantics.originImage Y.toSemantics _ a) + 1 = 2 * k + 1
        rw [componentContainsRank_interpretation]
        constructor <;> rintro ⟨a, ha⟩ <;>
          exact ⟨a, by dsimp only [Datra.Semantics.Pag.cell] at ha ⊢; omega⟩

theorem finiteDatum_valid_iff (X Y : Atlas) (source : (atlasMerge X Y).toSemantics.El)
    (datum : Datum ((FolioData.ValidElement.fromFinite (pagination X Y).pages).obj source).val.cell) :
    datum.Valid X Y ↔
      ∃ result : (Datra.Semantics.bouquetAtlas X.toSemantics Y.toSemantics).Da.obj
          (finiteElementEquiv X Y source),
        ((Datra.Semantics.bouquetAtlas X.toSemantics Y.toSemantics).Da.obj
          (finiteElementEquiv X Y source)).toDom.rank result = datumRank datum := by
  rw [Datum.valid_iff, resolve_fromFinite]
  exact contains_finite_interpretation X Y (finiteIndexOrderIso X Y source.1.unop) source.2 datum

/-- Decode a written bouquet datum by its parity rank. The membership theorem
supplies exactly the executable cell invariant, without adding an assumption. -/
-- ALIGN: MERGE-BOUQUET-DATA-DECODE.
noncomputable def finiteDataDecode (X Y : Atlas) (source : (atlasMerge X Y).toSemantics.El)
    (datum : (Datra.Semantics.bouquetAtlas X.toSemantics Y.toSemantics).Da.obj
      (finiteElementEquiv X Y source)) : (atlasMerge X Y).toSemantics.Da.obj source :=
  ⟨decode _ (((Datra.Semantics.bouquetAtlas X.toSemantics Y.toSemantics).Da.obj
    (finiteElementEquiv X Y source)).toDom.rank datum),
    (finiteDatum_valid_iff X Y source _).mpr ⟨datum, (rank_decode _ _).symm⟩⟩

theorem finiteDataDecode_rank (X Y : Atlas) (source : (atlasMerge X Y).toSemantics.El)
    (datum : (Datra.Semantics.bouquetAtlas X.toSemantics Y.toSemantics).Da.obj
      (finiteElementEquiv X Y source)) :
    ((atlasMerge X Y).toSemantics.Da.obj source).toDom.rank (finiteDataDecode X Y source datum) =
      ((Datra.Semantics.bouquetAtlas X.toSemantics Y.toSemantics).Da.obj
        (finiteElementEquiv X Y source)).toDom.rank datum := rank_decode _ _

theorem finiteDataDecode_bijective (X Y : Atlas) (source : (atlasMerge X Y).toSemantics.El) :
    Function.Bijective (finiteDataDecode X Y source) := by
  constructor
  · intro a b same
    apply ((Datra.Semantics.bouquetAtlas X.toSemantics Y.toSemantics).Da.obj
      (finiteElementEquiv X Y source)).toDom.rank.injective
    simpa only [finiteDataDecode_rank] using
      congrArg ((atlasMerge X Y).toSemantics.Da.obj source).toDom.rank same
  · intro datum
    obtain ⟨original, rank⟩ := (finiteDatum_valid_iff X Y source datum.val).mp datum.property
    refine ⟨original, ?_⟩
    apply ((atlasMerge X Y).toSemantics.Da.obj source).toDom.rank.injective
    exact (finiteDataDecode_rank X Y source original).trans rank

-- ALIGN: MERGE-BOUQUET-DATA-EQUIVALENCE.
noncomputable def finiteDataEquiv (X Y : Atlas) (source : (atlasMerge X Y).toSemantics.El) :
    (atlasMerge X Y).toSemantics.Da.obj source ≃
      (Datra.Semantics.bouquetAtlas X.toSemantics Y.toSemantics).Da.obj
        (finiteElementEquiv X Y source) :=
  (Equiv.ofBijective (finiteDataDecode X Y source) (finiteDataDecode_bijective X Y source)).symm

-- ALIGN: MERGE-BOUQUET-DATA-RANK.
theorem finiteDataEquiv_rank (X Y : Atlas) (source : (atlasMerge X Y).toSemantics.El)
    (datum : (atlasMerge X Y).toSemantics.Da.obj source) :
    ((Datra.Semantics.bouquetAtlas X.toSemantics Y.toSemantics).Da.obj
      (finiteElementEquiv X Y source)).toDom.rank (finiteDataEquiv X Y source datum) =
      ((atlasMerge X Y).toSemantics.Da.obj source).toDom.rank datum := by
  have roundtrip := (finiteDataEquiv X Y source).symm_apply_apply datum
  exact (finiteDataDecode_rank X Y source (finiteDataEquiv X Y source datum)).symm.trans
    (congrArg ((atlasMerge X Y).toSemantics.Da.obj source).toDom.rank roundtrip)

-- ALIGN: MERGE-BOUQUET-DATA-NATURALITY.
theorem finiteDataEquiv_naturality (X Y : Atlas) {source target : (atlasMerge X Y).toSemantics.El}
    (arrow : source ⟶ target) (datum : (atlasMerge X Y).toSemantics.Da.obj source) :
    finiteDataEquiv X Y target ((atlasMerge X Y).toSemantics.Da.map arrow datum) =
      (Datra.Semantics.bouquetAtlas X.toSemantics Y.toSemantics).Da.map
        ((finiteElements X Y).map arrow) (finiteDataEquiv X Y source datum) := by
  apply ((Datra.Semantics.bouquetAtlas X.toSemantics Y.toSemantics).Da.obj
    (finiteElementEquiv X Y target)).toDom.rank.injective
  rw [finiteDataEquiv_rank]
  change datumRank (retag datum.val) =
    ((Datra.Semantics.bouquetAtlas X.toSemantics Y.toSemantics).Da.obj
      (finiteElementEquiv X Y source)).toDom.rank (finiteDataEquiv X Y source datum)
  exact (retag_rank datum.val).trans (finiteDataEquiv_rank X Y source datum).symm

/-- The page and data comparisons together give a morphism into the exact
written bouquet Atlas. -/
noncomputable def interpretationHom (X Y : Atlas) :
    (atlasMerge X Y).toSemantics ⟶ Datra.Semantics.bouquetAtlas X.toSemantics Y.toSemantics where
  Pa := finiteElements X Y
  Da :=
    { app := fun source => (finiteDataEquiv X Y source).toEmbedding
      naturality := by
        intro source target arrow
        apply Function.Embedding.ext
        intro datum
        exact finiteDataEquiv_naturality X Y arrow datum }

theorem finiteMap_rank (X Y : Atlas) {source target : (atlasMerge X Y).toSemantics.El}
    (arrow : source ⟶ target) (datum : (atlasMerge X Y).toSemantics.Da.obj source) :
    ((atlasMerge X Y).toSemantics.Da.obj target).toDom.rank
      ((atlasMerge X Y).toSemantics.Da.map arrow datum) =
      ((atlasMerge X Y).toSemantics.Da.obj source).toDom.rank datum := retag_rank datum.val

theorem bouquetMap_rank (X Y : Atlas)
    {source target : (Datra.Semantics.bouquetAtlas X.toSemantics Y.toSemantics).El}
    (arrow : source ⟶ target)
    (datum : (Datra.Semantics.bouquetAtlas X.toSemantics Y.toSemantics).Da.obj source) :
    ((Datra.Semantics.bouquetAtlas X.toSemantics Y.toSemantics).Da.obj target).toDom.rank
      ((Datra.Semantics.bouquetAtlas X.toSemantics Y.toSemantics).Da.map arrow datum) =
      ((Datra.Semantics.bouquetAtlas X.toSemantics Y.toSemantics).Da.obj source).toDom.rank datum := rfl

noncomputable def interpretationInvData (X Y : Atlas)
    (target : (Datra.Semantics.bouquetAtlas X.toSemantics Y.toSemantics).El) :
    (Datra.Semantics.bouquetAtlas X.toSemantics Y.toSemantics).Da.obj target ↪
      (atlasMerge X Y).toSemantics.Da.obj ((finiteElementEquiv X Y).symm target) :=
  ((Datra.Semantics.bouquetAtlas X.toSemantics Y.toSemantics).Da.map
    (eqToHom ((finiteElementEquiv X Y).apply_symm_apply target).symm)).trans
      (finiteDataEquiv X Y ((finiteElementEquiv X Y).symm target)).symm.toEmbedding

theorem interpretationInvData_rank (X Y : Atlas)
    (target : (Datra.Semantics.bouquetAtlas X.toSemantics Y.toSemantics).El)
    (datum : (Datra.Semantics.bouquetAtlas X.toSemantics Y.toSemantics).Da.obj target) :
    ((atlasMerge X Y).toSemantics.Da.obj ((finiteElementEquiv X Y).symm target)).toDom.rank
      (interpretationInvData X Y target datum) =
      ((Datra.Semantics.bouquetAtlas X.toSemantics Y.toSemantics).Da.obj target).toDom.rank datum :=
  (finiteDataDecode_rank X Y _ _).trans (bouquetMap_rank X Y _ datum)

noncomputable def interpretationInv (X Y : Atlas) :
    Datra.Semantics.bouquetAtlas X.toSemantics Y.toSemantics ⟶ (atlasMerge X Y).toSemantics where
  Pa := finiteElementsInverse X Y
  Da :=
    { app := interpretationInvData X Y
      naturality := by
        intro source target arrow
        apply Function.Embedding.ext
        intro datum
        apply ((atlasMerge X Y).toSemantics.Da.obj ((finiteElementEquiv X Y).symm target)).toDom.rank.injective
        change ((atlasMerge X Y).toSemantics.Da.obj ((finiteElementEquiv X Y).symm target)).toDom.rank
            (interpretationInvData X Y target
              ((Datra.Semantics.bouquetAtlas X.toSemantics Y.toSemantics).Da.map arrow datum)) =
          ((atlasMerge X Y).toSemantics.Da.obj ((finiteElementEquiv X Y).symm target)).toDom.rank
            ((atlasMerge X Y).toSemantics.Da.map ((finiteElementsInverse X Y).map arrow)
              (interpretationInvData X Y source datum))
        rw [interpretationInvData_rank, finiteMap_rank]
        exact (bouquetMap_rank X Y arrow datum).trans (interpretationInvData_rank X Y source datum).symm }

private theorem hom_eq_of_page_rank {A B : Datra.Semantics.Atl} (f g : Datra.Semantics.AtlHom A B)
    (pages : f.Pa = g.Pa)
    (ranks : ∀ source datum,
      (B.Da.obj (f.Pa.obj source)).toDom.rank (f.Da.app source datum) =
        (B.Da.obj (g.Pa.obj source)).toDom.rank (g.Da.app source datum)) : f = g := by
  cases f with
  | mk fp fd =>
    cases g with
    | mk gp gd =>
      dsimp only at pages
      subst gp
      apply Datra.Semantics.AtlHom.ext
      · rfl
      · apply heq_of_eq
        ext source datum
        exact (B.Da.obj (fp.obj source)).toDom.rank.injective (ranks source datum)

/-- The executable merge is isomorphic to the written bouquet Atlas, with
the finite page equivalence and parity-rank data equivalence as its actions. -/
-- ALIGN: MERGE-BOUQUET-ATLAS-ISOMORPHISM.
noncomputable def interpretationIso (X Y : Atlas) :
    (atlasMerge X Y).toSemantics ≅ Datra.Semantics.bouquetAtlas X.toSemantics Y.toSemantics where
  hom := interpretationHom X Y
  inv := interpretationInv X Y
  hom_inv_id := by
    apply hom_eq_of_page_rank
    · exact CategoryTheory.Functor.ext (fun source => (finiteElementEquiv X Y).symm_apply_apply source)
    · intro source datum
      exact (interpretationInvData_rank X Y _ _).trans (finiteDataEquiv_rank X Y source datum)
  inv_hom_id := by
    apply hom_eq_of_page_rank
    · exact CategoryTheory.Functor.ext (fun target => (finiteElementEquiv X Y).apply_symm_apply target)
    · intro target datum
      exact (finiteDataEquiv_rank X Y _ _).trans (interpretationInvData_rank X Y target datum)

end Datra.Executable.AtlasMerge
