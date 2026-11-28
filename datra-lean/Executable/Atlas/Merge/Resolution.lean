import Executable.Atlas.Merge

namespace Datra.Executable.AtlasMerge

theorem leftTrace_accepted (X Y : Atlas) (page : Nat) (positions : List Ordinal)
    (accepted : PageCell.left positions ∈ Set.range (pageEncode X Y page)) :
    X.pages.traceLookup page (FolioData.traceHead positions) = some positions := by
  obtain ⟨value, same⟩ := accepted
  cases value with
  | inl value =>
      have traces := PageCell.left.inj same
      rw [← traces]
      exact (X.pages.encodeTrace X.pagination.folio.valid page value).property
  | inr value => cases same

theorem rightTrace_accepted (X Y : Atlas) (page : Nat) (positions : List Ordinal)
    (accepted : PageCell.right positions ∈ Set.range (pageEncode X Y page)) :
    Y.pages.traceLookup page (FolioData.traceHead positions) = some positions := by
  obtain ⟨value, same⟩ := accepted
  cases value with
  | inl value => cases same
  | inr value =>
      have traces := PageCell.right.inj same
      rw [← traces]
      exact (Y.pages.encodeTrace Y.pagination.folio.valid page value).property

-- ALIGN: MERGE-NATIVE-CELL-RESOLUTION.
def withNativeCell {result : Type*} (X Y : Atlas) (page : Nat) (cell : ValidPageCell X Y page)
    (useLeft : (source : X.Element) → source.val.page = page → cell.val = .left source.val.trace → result)
    (useRight : (source : Y.Element) → source.val.page = page → cell.val = .right source.val.trace → result) : Option result :=
  match found : cell.val with
  | .left positions =>
      X.withCellTrace page ⟨positions, leftTrace_accepted X Y page positions (found ▸ cell.property)⟩
        (fun source location _ same => useLeft source location (by rw [same]; exact found))
  | .right positions =>
      Y.withCellTrace page ⟨positions, rightTrace_accepted X Y page positions (found ▸ cell.property)⟩
        (fun source location _ same => useRight source location (by rw [same]; exact found))

theorem withNativeCell_isSome {result : Type*} (X Y : Atlas) (page : Nat) (cell : ValidPageCell X Y page)
    (useLeft : (source : X.Element) → source.val.page = page → cell.val = .left source.val.trace → result)
    (useRight : (source : Y.Element) → source.val.page = page → cell.val = .right source.val.trace → result) :
    (withNativeCell X Y page cell useLeft useRight).isSome = true := by
  unfold withNativeCell
  split
  · apply Atlas.withCellTrace_isSome
  · apply Atlas.withCellTrace_isSome

/-- The structural index of component page k in the finite merge prefix.
Its page number is k+1 because page zero is the fresh origin. -/
def componentIndex (X Y : Atlas) : (n : Nat) → Fin (n + 1) → (prefixFolio X Y n).data.Index
  := Folio.prefixIndex _ _ _ _ _ _

theorem prefixFolio_depth (X Y : Atlas) (n : Nat) : (prefixFolio X Y n).data.depth = n + 2 := by
  rw [← (prefixFolio X Y n).data.length_eq_depth (prefixFolio X Y n).valid, prefixFolio_length]

-- ALIGN: MERGE-COMPONENT-PAGE-INDEX.
theorem componentIndex_number (X Y : Atlas) (n : Nat) (k : Fin (n + 1)) :
    (prefixFolio X Y n).data.indexNumber (componentIndex X Y n k) = k.val + 1 :=
  Folio.prefixIndex_number _ _ _ _ _ _ n k

theorem componentIndex_page (X Y : Atlas) (n : Nat) (k : Fin (n + 1)) :
    (prefixFolio X Y n).data.page (componentIndex X Y n k) = mergePage X Y k.val :=
  Folio.prefixIndex_page _ _ _ _ _ _ n k

theorem index_eq_of_number {origin final : Page} (pages : FolioData origin final) {a b : pages.Index}
    (same : pages.indexNumber a = pages.indexNumber b) : a = b :=
  pages.index_eq_of_number same

-- ALIGN: MERGE-PAGE-RESOLUTION.
theorem prefixIndex_page (X Y : Atlas) (n : Nat) (index : (prefixFolio X Y n).data.Index) :
    (prefixFolio X Y n).data.page index =
      if (prefixFolio X Y n).data.indexNumber index = 0 then DomanialInclusion.singletonPage
      else mergePage X Y ((prefixFolio X Y n).data.indexNumber index - 1) :=
  Folio.buildPrefix_page _ _ _ _ _ _ n index

theorem prefixPageAt_zero (X Y : Atlas) (n : Nat) :
    (prefixFolio X Y n).data.pageAt 0 = DomanialInclusion.singletonPage :=
  Folio.buildPrefix_pageAt_zero _ _ _ _ _ _ n

-- ALIGN: MERGE-PADDED-PAGE-RESOLUTION.
theorem prefixPageAt_succ (X Y : Atlas) (n k : Nat) :
    (prefixFolio X Y n).data.pageAt (k + 1) = mergePage X Y (min k n) :=
  Folio.buildPrefix_pageAt_succ _ _ _ _ _ _ n k


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

/-- Recover the component in the sum presentation. `withNativeCell_resolve`
identifies this with the runtime's accepted-trace lookup. -/
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

-- ALIGN: MERGE-NATIVE-CELL-RESOLUTION-INTERPRETATION.
theorem withNativeCell_resolve (X Y : Atlas) (page : Nat) (cell : ValidPageCell X Y page) :
    withNativeCell X Y page cell (fun source _ _ => SourceCell.left source)
      (fun source _ _ => SourceCell.right source) = some (resolvePageCell X Y page cell) := by
  obtain ⟨value, same⟩ := cell.property
  have encoded : encodedPageCell X Y page value = cell := Subtype.ext same
  rw [← encoded]
  cases value with
  | inl value =>
      rw [resolvePageCell_left]
      change X.withCellTrace page ⟨X.pages.traceAt page value, _⟩
        (fun source _ _ _ => SourceCell.left source) = _
      rw [Atlas.withCellTrace_forget]
      change (X.pages.elementAt page (FolioData.traceHead (X.pages.traceAt page value))).map SourceCell.left = _
      rw [FolioData.traceHead_of_head (X.pages.traceAt_head page value)]
      exact congrArg (fun resolved : Option X.Element => resolved.map (SourceCell.left : X.Element → SourceCell X Y)) (X.pages.elementAt_occurrence ⟨page, value⟩)
  | inr value =>
      rw [resolvePageCell_right]
      change Y.withCellTrace page ⟨Y.pages.traceAt page value, _⟩
        (fun source _ _ _ => SourceCell.right source) = _
      rw [Atlas.withCellTrace_forget]
      change (Y.pages.elementAt page (FolioData.traceHead (Y.pages.traceAt page value))).map SourceCell.right = _
      rw [FolioData.traceHead_of_head (Y.pages.traceAt_head page value)]
      exact congrArg (fun resolved : Option Y.Element => resolved.map (SourceCell.right : Y.Element → SourceCell X Y)) (Y.pages.elementAt_occurrence ⟨page, value⟩)

-- ALIGN: MERGE-RAW-POSITION-RESOLVABLE.
def positionResolvable (X Y : Atlas) : Nat → Ordinal → Bool
  | 0, _ => true
  | page + 1, position => ((pageChain X Y page).chainIndex position).isSome

/-- The executable resolver keeps failure separate from the fresh origin. -/
-- ALIGN: MERGE-RESOLVED-LOOKUP-VALUE.
def resolveCellAt (X Y : Atlas) : Nat → Ordinal → Option (SourceCell X Y)
  | 0, _ => some .origin
  | page + 1, position =>
      ((pageChain X Y page).chainIndex position).bind fun index =>
        withNativeCell X Y page index.object (fun source _ _ => SourceCell.left source)
          (fun source _ _ => SourceCell.right source)

-- ALIGN: MERGE-RESOLVER-NATIVE-SUCCESS.
theorem resolveCellAt_isSome (X Y : Atlas) (page : Nat) (position : Ordinal) :
    (resolveCellAt X Y page position).isSome = positionResolvable X Y page position := by
  cases page with
  | zero => rfl
  | succ page =>
      cases found : (pageChain X Y page).chainIndex position with
      | none => simp [resolveCellAt, positionResolvable, found]
      | some index =>
          simpa only [resolveCellAt, positionResolvable, found, Option.bind_some,
            Option.isSome_some] using
            withNativeCell_isSome X Y page index.object
              (fun source _ _ => SourceCell.left source) (fun source _ _ => SourceCell.right source)

theorem resolveCellAt_position (X Y : Atlas) (page : Nat) (cell : ValidPageCell X Y page) :
    resolveCellAt X Y (page + 1) ((pageChain X Y page).position cell) =
      some (resolvePageCell X Y page cell) := by
  simp only [resolveCellAt, Chain.chainIndex_position, Option.bind_some, Chain.chainIndexOf]
  exact withNativeCell_resolve X Y page cell

theorem componentPage_clamp (X : Atlas) (limit n : Nat) (bound : X.pages.depth - 1 ≤ limit) :
    componentPage X (min n limit) = componentPage X n := by
  exact X.pages.pageAt_clamp limit n bound

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
  exact (Page.cast_position hpage.symm (encodedPageCell X Y (min n limit) (.inl value))).trans
    ((pagePosition_encode X Y (min n limit) (.inl value)).trans
      (Page.cast_position hsource.symm source.value))

-- ALIGN: MERGE-RIGHT-POSITION.
theorem rightOccurrence_position (X Y : Atlas) (source : Y.pages.Occurrence) :
    (rightOccurrence X Y source).toRaw.position =
      Ordinal.addOrdinals (componentPage X source.page).chain.orderType source.toRaw.position := by
  let n := source.page
  let limit := mergeDepth X Y - 1
  let hpage := prefixPageAt_succ X Y limit n
  let hsource := componentPage_clamp Y limit n (rightDepth_bound X Y)
  let value := cast (congrArg Page.Carrier hsource.symm) source.value
  have first := (Page.cast_position hpage.symm (encodedPageCell X Y (min n limit) (.inr value))).trans
    (pagePosition_encode X Y (min n limit) (.inr value))
  have second := congrArg (Ordinal.addOrdinals (componentPage X (min n limit)).chain.orderType)
    (Page.cast_position hsource.symm source.value)
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

theorem sourceOccurrence_resolve (X Y : Atlas) (occurrence : (pagination X Y).pages.Occurrence) :
    sourceOccurrence X Y (resolveOccurrence X Y occurrence) = occurrence := by
  cases occurrence with
  | mk page value =>
    cases page with
    | zero =>
      apply FolioData.Occurrence.ext
      · rfl
      exact heq_of_eq (Page.cast_from_unique (prefixPageAt_zero X Y (mergeDepth X Y - 1)).symm () (fun x => by cases x; rfl) value)
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
