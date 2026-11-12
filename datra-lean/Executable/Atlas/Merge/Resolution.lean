import Executable.Atlas.Merge

namespace Datra.Executable.AtlasMerge

/-- The structural index of component page k in the finite merge prefix.
Its page number is k+1 because page zero is the fresh origin. -/
def componentIndex (X Y : Atlas) : (n : Nat) → Fin (n + 1) → (prefixFolio X Y n).data.Index
  | 0, _ => none
  | n + 1, k =>
      if last : k.val = n + 1 then none
      else some (componentIndex X Y n ⟨k.val, by have := k.isLt; omega⟩)

theorem prefixFolio_depth (X Y : Atlas) (n : Nat) : (prefixFolio X Y n).data.depth = n + 2 := by
  rw [← (prefixFolio X Y n).data.length_eq_depth (prefixFolio X Y n).valid, prefixFolio_length]

-- ALIGN: MERGE-COMPONENT-PAGE-INDEX.
theorem componentIndex_number (X Y : Atlas) (n : Nat) (k : Fin (n + 1)) :
    (prefixFolio X Y n).data.indexNumber (componentIndex X Y n k) = k.val + 1 := by
  induction n with
  | zero => change 1 = k.val + 1; have := k.isLt; omega
  | succ n ih =>
    by_cases last : k.val = n + 1
    · simp only [componentIndex, dif_pos last]
      change (prefixFolio X Y n).data.depth = k.val + 1
      rw [prefixFolio_depth, last]
    · simp only [componentIndex, dif_neg last]
      exact ih ⟨k.val, by have := k.isLt; omega⟩

theorem componentIndex_page (X Y : Atlas) (n : Nat) (k : Fin (n + 1)) :
    (prefixFolio X Y n).data.page (componentIndex X Y n k) = mergePage X Y k.val := by
  induction n with
  | zero =>
    change mergePage X Y 0 = mergePage X Y k.val
    have zero : k.val = 0 := by have := k.isLt; omega
    rw [zero]
  | succ n ih =>
    by_cases last : k.val = n + 1
    · simp only [componentIndex, dif_pos last]
      change mergePage X Y (n + 1) = mergePage X Y k.val
      rw [last]
    · simp only [componentIndex, dif_neg last]
      exact ih ⟨k.val, by have := k.isLt; omega⟩

theorem index_eq_of_number {origin final : Page} (pages : FolioData origin final) {a b : pages.Index}
    (same : pages.indexNumber a = pages.indexNumber b) : a = b := by
  apply pages.indexEquivFin.injective
  apply Fin.ext
  simpa only [FolioData.indexEquivFin_val] using same

theorem prefixIndex_cases (X Y : Atlas) (n : Nat) (index : (prefixFolio X Y n).data.Index) :
    index = (prefixFolio X Y n).data.firstIndex ∨ ∃ k, index = componentIndex X Y n k := by
  by_cases origin : (prefixFolio X Y n).data.indexNumber index = 0
  · left
    apply index_eq_of_number
    simpa only [FolioData.firstIndex_number] using origin
  · right
    have bound := (prefixFolio X Y n).data.indexNumber_lt index
    rw [prefixFolio_depth] at bound
    let k : Fin (n + 1) := ⟨(prefixFolio X Y n).data.indexNumber index - 1, by omega⟩
    refine ⟨k, index_eq_of_number _ ?_⟩
    rw [componentIndex_number]
    dsimp only [k]
    omega

-- ALIGN: MERGE-PAGE-RESOLUTION.
theorem prefixIndex_page (X Y : Atlas) (n : Nat) (index : (prefixFolio X Y n).data.Index) :
    (prefixFolio X Y n).data.page index =
      if (prefixFolio X Y n).data.indexNumber index = 0 then DomanialInclusion.singletonPage
      else mergePage X Y ((prefixFolio X Y n).data.indexNumber index - 1) := by
  obtain origin | ⟨k, rfl⟩ := prefixIndex_cases X Y n index
  · rw [origin, FolioData.firstIndex_page, FolioData.firstIndex_number, if_pos rfl]
  · rw [componentIndex_page, componentIndex_number]
    simp

theorem prefixPageAt_zero (X Y : Atlas) (n : Nat) :
    (prefixFolio X Y n).data.pageAt 0 = DomanialInclusion.singletonPage := by
  unfold FolioData.pageAt
  rw [prefixIndex_page, FolioData.indexEquivFin_symm_number]
  simp [FolioData.paddedIndex]

-- ALIGN: MERGE-PADDED-PAGE-RESOLUTION.
theorem prefixPageAt_succ (X Y : Atlas) (n k : Nat) :
    (prefixFolio X Y n).data.pageAt (k + 1) = mergePage X Y (min k n) := by
  unfold FolioData.pageAt
  rw [prefixIndex_page, FolioData.indexEquivFin_symm_number]
  simp only [FolioData.paddedIndex, prefixFolio_depth]
  have h : min (k + 1) (n + 2 - 1) ≠ 0 := by omega
  rw [if_neg h]
  congr 1
  omega


def pageDecode (X Y : Atlas) (n : Nat) (cell : PageCell) :
    Option (Sum (componentPage X n).Carrier (componentPage Y n).Carrier) :=
  ((componentSum X Y n).chainIndex (pagePosition X Y n cell)).map ChainIndex.object

-- ALIGN: MERGE-COMPONENT-DECODER.
theorem pageDecode_encode (X Y : Atlas) (n : Nat)
    (value : Sum (componentPage X n).Carrier (componentPage Y n).Carrier) :
    pageDecode X Y n (pageEncode X Y n value) = some value := by
  simp [pageDecode, pagePosition_encode, Chain.chainIndex_position, Chain.chainIndexOf]

theorem pageDecode_isSome (X Y : Atlas) (n : Nat) (cell : ValidPageCell X Y n) :
    (pageDecode X Y n cell.val).isSome = true := by
  obtain ⟨value, same⟩ := cell.property
  rw [← same, pageDecode_encode]
  rfl

/-- Recover the component by checked lookup of the combined ordinal
position, using the same sum-chain decoder as the runtime page resolver. -/
def decodedPageCell (X Y : Atlas) (n : Nat) (cell : ValidPageCell X Y n) :
    Sum (componentPage X n).Carrier (componentPage Y n).Carrier :=
  (pageDecode X Y n cell.val).get (pageDecode_isSome X Y n cell)

theorem decodedPageCell_encode (X Y : Atlas) (n : Nat)
    (value : Sum (componentPage X n).Carrier (componentPage Y n).Carrier) :
    decodedPageCell X Y n (encodedPageCell X Y n value) = value := by
  apply Option.some.inj
  exact (Option.some_get (pageDecode_isSome X Y n (encodedPageCell X Y n value))).trans
    (pageDecode_encode X Y n value)

theorem encode_decodedPageCell (X Y : Atlas) (n : Nat) (cell : ValidPageCell X Y n) :
    pageEncode X Y n (decodedPageCell X Y n cell) = cell.val := by
  obtain ⟨value, same⟩ := cell.property
  have hc : encodedPageCell X Y n value = cell := Subtype.ext same
  rw [← hc, decodedPageCell_encode]
  rfl

def resolvePageCell (X Y : Atlas) (n : Nat) (cell : ValidPageCell X Y n) : SourceCell X Y :=
  match decodedPageCell X Y n cell with
  | .inl value => .left (FolioData.ValidElement.ofOccurrence ⟨n, value⟩)
  | .inr value => .right (FolioData.ValidElement.ofOccurrence ⟨n, value⟩)

theorem resolvePageCell_left (X Y : Atlas) (n : Nat) (value : (componentPage X n).Carrier) :
    resolvePageCell X Y n (encodedPageCell X Y n (.inl value)) =
      .left (FolioData.ValidElement.ofOccurrence ⟨n, value⟩) := by
  simp only [resolvePageCell, decodedPageCell_encode]

theorem resolvePageCell_right (X Y : Atlas) (n : Nat) (value : (componentPage Y n).Carrier) :
    resolvePageCell X Y n (encodedPageCell X Y n (.inr value)) =
      .right (FolioData.ValidElement.ofOccurrence ⟨n, value⟩) := by
  simp only [resolvePageCell, decodedPageCell_encode]

theorem componentPage_clamp (X : Atlas) (limit n : Nat) (bound : X.pages.depth - 1 ≤ limit) :
    componentPage X (min n limit) = componentPage X n := by
  unfold componentPage FolioData.pageAt
  congr 1
  congr 1
  apply Fin.ext
  simp only [FolioData.paddedIndex]
  omega

theorem leftDepth_bound (X Y : Atlas) : X.pages.depth - 1 ≤ mergeDepth X Y - 1 := by
  have hl := X.pages.length_eq_depth X.pagination.folio.valid
  have h := Nat.le_max_left X.pages.length Y.pages.length
  unfold mergeDepth
  omega

theorem rightDepth_bound (X Y : Atlas) : Y.pages.depth - 1 ≤ mergeDepth X Y - 1 := by
  have hl := Y.pages.length_eq_depth Y.pagination.folio.valid
  have h := Nat.le_max_right X.pages.length Y.pages.length
  unfold mergeDepth
  omega

/-- Resolve full-spine occurrences, retaining the requested component page
number even beyond the finite merge. Only its carrier is padding-clamped. -/
-- ALIGN: MERGE-SOURCE-RESOLUTION.
def resolveOccurrence (X Y : Atlas) (occurrence : (pagination X Y).pages.Occurrence) : SourceCell X Y :=
  match occurrence with
  | ⟨0, _⟩ => .origin
  | ⟨n + 1, value⟩ =>
      let cell : ValidPageCell X Y (min n (mergeDepth X Y - 1)) :=
        cast (congrArg Page.Carrier (prefixPageAt_succ X Y (mergeDepth X Y - 1) n)) value
      match decodedPageCell X Y _ cell with
      | .inl source =>
          .left (FolioData.ValidElement.ofOccurrence ⟨n,
            cast (congrArg Page.Carrier (componentPage_clamp X _ n (leftDepth_bound X Y))) source⟩)
      | .inr source =>
          .right (FolioData.ValidElement.ofOccurrence ⟨n,
            cast (congrArg Page.Carrier (componentPage_clamp Y _ n (rightDepth_bound X Y))) source⟩)


-- ALIGN: MERGE-LEFT-OBJECT.
def leftOccurrence (X Y : Atlas) (source : X.pages.Occurrence) : (pagination X Y).pages.Occurrence :=
  let n := source.page
  let value := cast (congrArg Page.Carrier (componentPage_clamp X _ n (leftDepth_bound X Y)).symm) source.value
  let cell := encodedPageCell X Y (min n (mergeDepth X Y - 1)) (.inl value)
  ⟨n + 1, cast (congrArg Page.Carrier (prefixPageAt_succ X Y (mergeDepth X Y - 1) n).symm) cell⟩

-- ALIGN: MERGE-RIGHT-OBJECT.
def rightOccurrence (X Y : Atlas) (source : Y.pages.Occurrence) : (pagination X Y).pages.Occurrence :=
  let n := source.page
  let value := cast (congrArg Page.Carrier (componentPage_clamp Y _ n (rightDepth_bound X Y)).symm) source.value
  let cell := encodedPageCell X Y (min n (mergeDepth X Y - 1)) (.inr value)
  ⟨n + 1, cast (congrArg Page.Carrier (prefixPageAt_succ X Y (mergeDepth X Y - 1) n).symm) cell⟩

-- ALIGN: MERGE-LEFT-RESOLVED.
theorem resolveOccurrence_left (X Y : Atlas) (source : X.pages.Occurrence) :
    resolveOccurrence X Y (leftOccurrence X Y source) = .left (FolioData.ValidElement.ofOccurrence source) := by
  cases source with
  | mk n value =>
    simp only [leftOccurrence, resolveOccurrence, cast_cast, cast_eq, decodedPageCell_encode]

-- ALIGN: MERGE-RIGHT-RESOLVED.
theorem resolveOccurrence_right (X Y : Atlas) (source : Y.pages.Occurrence) :
    resolveOccurrence X Y (rightOccurrence X Y source) = .right (FolioData.ValidElement.ofOccurrence source) := by
  cases source with
  | mk n value =>
    simp only [rightOccurrence, resolveOccurrence, cast_cast, cast_eq, decodedPageCell_encode]

theorem pagePosition_cast {source target : Page} (same : source = target) (value : source.Carrier) :
    target.chain.position (cast (congrArg Page.Carrier same) value) = source.chain.position value := by
  cases same
  rfl

-- ALIGN: MERGE-LEFT-PAGE.
theorem leftOccurrence_page (X Y : Atlas) (source : X.pages.Occurrence) :
    (leftOccurrence X Y source).page = source.page + 1 := rfl

-- ALIGN: MERGE-RIGHT-PAGE.
theorem rightOccurrence_page (X Y : Atlas) (source : Y.pages.Occurrence) :
    (rightOccurrence X Y source).page = source.page + 1 := rfl

-- ALIGN: MERGE-LEFT-POSITION.
theorem leftOccurrence_position (X Y : Atlas) (source : X.pages.Occurrence) :
    (leftOccurrence X Y source).toRaw.position = source.toRaw.position := by
  let n := source.page
  let limit := mergeDepth X Y - 1
  let hpage := prefixPageAt_succ X Y limit n
  let hsource := componentPage_clamp X limit n (leftDepth_bound X Y)
  let value := cast (congrArg Page.Carrier hsource.symm) source.value
  exact (pagePosition_cast hpage.symm (encodedPageCell X Y (min n limit) (.inl value))).trans
    ((pagePosition_encode X Y (min n limit) (.inl value)).trans
      (pagePosition_cast hsource.symm source.value))

-- ALIGN: MERGE-RIGHT-POSITION.
theorem rightOccurrence_position (X Y : Atlas) (source : Y.pages.Occurrence) :
    (rightOccurrence X Y source).toRaw.position =
      Ordinal.addOrdinals (componentPage X source.page).chain.orderType source.toRaw.position := by
  let n := source.page
  let limit := mergeDepth X Y - 1
  let hpage := prefixPageAt_succ X Y limit n
  let hsource := componentPage_clamp Y limit n (rightDepth_bound X Y)
  let value := cast (congrArg Page.Carrier hsource.symm) source.value
  have first := (pagePosition_cast hpage.symm (encodedPageCell X Y (min n limit) (.inr value))).trans
    (pagePosition_encode X Y (min n limit) (.inr value))
  have second := congrArg (Ordinal.addOrdinals (componentPage X (min n limit)).chain.orderType)
    (pagePosition_cast hsource.symm source.value)
  have third := congrArg (fun page : Page => Ordinal.addOrdinals page.chain.orderType source.toRaw.position)
    (componentPage_clamp X limit n (leftDepth_bound X Y))
  exact first.trans (second.trans third)


def originOccurrence (X Y : Atlas) : (pagination X Y).pages.Occurrence :=
  ⟨0, cast (congrArg Page.Carrier (prefixPageAt_zero X Y (mergeDepth X Y - 1)).symm) ()⟩

def sourceOccurrence (X Y : Atlas) : SourceCell X Y → (pagination X Y).pages.Occurrence
  | .origin => originOccurrence X Y
  | .left source => leftOccurrence X Y source.occurrence
  | .right source => rightOccurrence X Y source.occurrence

theorem resolve_sourceOccurrence (X Y : Atlas) (source : SourceCell X Y) :
    resolveOccurrence X Y (sourceOccurrence X Y source) = source := by
  cases source with
  | origin => rfl
  | left source => simp only [sourceOccurrence, resolveOccurrence_left, FolioData.ValidElement.ofOccurrence_occurrence]
  | right source => simp only [sourceOccurrence, resolveOccurrence_right, FolioData.ValidElement.ofOccurrence_occurrence]

theorem singletonPage_cast_unique {page : Page} (same : page = DomanialInclusion.singletonPage)
    (value : page.Carrier) : cast (congrArg Page.Carrier same.symm) () = value := by
  cases same
  cases value
  rfl

theorem sourceOccurrence_resolve (X Y : Atlas) (occurrence : (pagination X Y).pages.Occurrence) :
    sourceOccurrence X Y (resolveOccurrence X Y occurrence) = occurrence := by
  cases occurrence with
  | mk page value =>
    cases page with
    | zero =>
      apply FolioData.Occurrence.ext
      · rfl
      exact heq_of_eq (singletonPage_cast_unique (prefixPageAt_zero X Y (mergeDepth X Y - 1)) value)
    | succ n =>
      let limit := mergeDepth X Y - 1
      let hpage := prefixPageAt_succ X Y limit n
      let cell : ValidPageCell X Y (min n limit) := cast (congrArg Page.Carrier hpage) value
      have encoded := encode_decodedPageCell X Y (min n limit) cell
      dsimp only [resolveOccurrence]
      cases decoded : decodedPageCell X Y (min n limit) cell with
      | inl source =>
        have same : encodedPageCell X Y (min n limit) (.inl source) = cell :=
          Subtype.ext (by simpa only [decoded] using encoded)
        simp only [sourceOccurrence]
        rw [FolioData.ValidElement.occurrence_ofOccurrence (pages := X.pages)]
        simp only [leftOccurrence, cast_cast, cast_eq]
        apply FolioData.Occurrence.ext
        · rfl
        apply heq_of_eq
        simpa only [cell, cast_cast, cast_eq] using congrArg (cast (congrArg Page.Carrier hpage.symm)) same
      | inr source =>
        have same : encodedPageCell X Y (min n limit) (.inr source) = cell :=
          Subtype.ext (by simpa only [decoded] using encoded)
        simp only [sourceOccurrence]
        rw [FolioData.ValidElement.occurrence_ofOccurrence (pages := Y.pages)]
        simp only [rightOccurrence, cast_cast, cast_eq]
        apply FolioData.Occurrence.ext
        · rfl
        apply heq_of_eq
        simpa only [cell, cast_cast, cast_eq] using congrArg (cast (congrArg Page.Carrier hpage.symm)) same

/-- The full-spine merge has exactly one new origin and all left and right
component occurrences. The resolver is the forward executable operation. -/
-- ALIGN: MERGE-SOURCE-RESOLUTION-EQUIV.
def occurrenceEquiv (X Y : Atlas) : (pagination X Y).pages.Occurrence ≃ SourceCell X Y where
  toFun := resolveOccurrence X Y
  invFun := sourceOccurrence X Y
  left_inv := sourceOccurrence_resolve X Y
  right_inv := resolve_sourceOccurrence X Y

end Datra.Executable.AtlasMerge
