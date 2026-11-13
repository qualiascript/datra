import Executable.Atlas.Merge.Resolution
import Executable.Folio.PrefixResolution

namespace Datra.Executable.AtlasMerge
open CategoryTheory

def Transport.toOrigin {X Y : Atlas} (source : SourceCell X Y) : Transport source .origin :=
  match source with
  | .origin => .origin
  | .left source => .leftOrigin source
  | .right source => .rightOrigin source

/-- Decoding one stored page transition yields the component's own interval
arrow. The proof uses the raw trace-dropping implementation. -/
theorem resolve_pageTransition (X Y : Atlas) (n : Nat) (cell : ValidPageCell X Y (n + 1)) :
    Transport (resolvePageCell X Y (n + 1) cell)
      (resolvePageCell X Y n ((pageTransition X Y n).map cell)) := by
  obtain ⟨value, same⟩ := cell.property
  have hc : encodedPageCell X Y (n + 1) value = cell := Subtype.ext same
  rw [← hc, pageTransition_encode]
  cases value with
  | inl value =>
    simp only [componentTransition, Consolidation.sum, Sum.map_inl,
      resolvePageCell_left]
    exact .left (X.pages.transportArrow (n + 1) n (Nat.le_succ n) value)
  | inr value =>
    simp only [componentTransition, Consolidation.sum, Sum.map_inr,
      resolvePageCell_right]
    exact .right (Y.pages.transportArrow (n + 1) n (Nat.le_succ n) value)

/-- Resolve a stored finite page structurally, before presenting its index as
a natural page number. This avoids any choice of an inverse page lookup. -/
def sourceAtIndex (X Y : Atlas) : (n : Nat) →
    (index : (prefixFolio X Y n).data.Index) →
    ((prefixFolio X Y n).data.page index).Carrier → SourceCell X Y
  := Folio.PrefixResolution.atIndex DomanialInclusion.singletonPage () (fun x => by cases x; rfl)
    (mergePage X Y) (collapseToOrigin X Y) (pageTransition X Y)
    (SourceCell.origin : SourceCell X Y) (resolvePageCell X Y)

/-- Every generated interval in the finite folio resolves to a component
transport, including its composite through all intervening stored pages. -/
theorem resolve_interval (X Y : Atlas) (n : Nat)
    (source target : (prefixFolio X Y n).data.Index)
    (precedes : (prefixFolio X Y n).data.indexNumber target ≤ (prefixFolio X Y n).data.indexNumber source)
    (value : ((prefixFolio X Y n).data.page source).Carrier) :
    Transport (sourceAtIndex X Y n source value)
      (sourceAtIndex X Y n target ((prefixFolio X Y n).data.interval source target precedes |>.map value)) :=
  Folio.PrefixResolution.interval DomanialInclusion.singletonPage () (fun x => by cases x; rfl)
    (mergePage X Y) (collapseToOrigin X Y) (pageTransition X Y)
    (SourceCell.origin : SourceCell X Y) (resolvePageCell X Y)
    Transport Transport.identity (fun first second => first.comp second)
    (fun _ _ => Transport.toOrigin _) (resolve_pageTransition X Y) n source target precedes value


/-- The stored-page form of resolution forgets only the repeated padding
page number. Its selected genuine cell remains unchanged. -/
def resolveStoredOccurrence (X Y : Atlas) (occurrence : (pagination X Y).pages.Occurrence) : SourceCell X Y :=
  sourceAtIndex X Y (mergeDepth X Y - 1)
    ((pagination X Y).pages.indexEquivFin.symm ((pagination X Y).pages.paddedIndex occurrence.page)) occurrence.value

theorem sourceAtIndex_first (X Y : Atlas) (n : Nat)
    (value : ((prefixFolio X Y n).data.page (prefixFolio X Y n).data.firstIndex).Carrier) :
    sourceAtIndex X Y n (prefixFolio X Y n).data.firstIndex value = .origin :=
  Folio.PrefixResolution.atIndex_first DomanialInclusion.singletonPage () (fun x => by cases x; rfl)
    (mergePage X Y) (collapseToOrigin X Y) (pageTransition X Y)
    (SourceCell.origin : SourceCell X Y) (resolvePageCell X Y) n value

theorem sourceAtIndex_heq (X Y : Atlas) (n : Nat)
    {i j : (prefixFolio X Y n).data.Index} (same : i = j)
    {a : ((prefixFolio X Y n).data.page i).Carrier}
    {b : ((prefixFolio X Y n).data.page j).Carrier} (values : HEq a b) :
    sourceAtIndex X Y n i a = sourceAtIndex X Y n j b :=
  Folio.PrefixResolution.atIndex_heq DomanialInclusion.singletonPage () (fun x => by cases x; rfl)
    (mergePage X Y) (collapseToOrigin X Y) (pageTransition X Y)
    (SourceCell.origin : SourceCell X Y) (resolvePageCell X Y) n same values

theorem sourceAtIndex_component (X Y : Atlas) (n : Nat) (k : Fin (n + 1))
    (value : ValidPageCell X Y k.val) :
    sourceAtIndex X Y n (componentIndex X Y n k)
      (cast (congrArg Page.Carrier (componentIndex_page X Y n k).symm) value) =
      resolvePageCell X Y k.val value :=
  Folio.PrefixResolution.atIndex_component DomanialInclusion.singletonPage () (fun x => by cases x; rfl)
    (mergePage X Y) (collapseToOrigin X Y) (pageTransition X Y)
    (SourceCell.origin : SourceCell X Y) (resolvePageCell X Y) n k value

theorem resolveStored_arrow (X Y : Atlas) {source target : (pagination X Y).pages.Occurrence}
    (arrow : source ⟶ target) :
    Transport (resolveStoredOccurrence X Y source) (resolveStoredOccurrence X Y target) := by
  let pages := (pagination X Y).pages
  have precedes : target.page ≤ source.page := arrow.precedes
  have transported : (pages.transport source.page target.page precedes).map source.value = target.value :=
    (pages.traceAt_suffix_iff source.page target.page precedes source.value target.value).mp arrow.transported
  have ordered : pages.indexNumber (pages.indexEquivFin.symm (pages.paddedIndex target.page)) ≤
      pages.indexNumber (pages.indexEquivFin.symm (pages.paddedIndex source.page)) := by
    simpa only [FolioData.indexEquivFin_symm_number, FolioData.paddedIndex] using
      min_le_min_right (pages.depth - 1) precedes
  have result := resolve_interval X Y (mergeDepth X Y - 1)
    (pages.indexEquivFin.symm (pages.paddedIndex source.page))
    (pages.indexEquivFin.symm (pages.paddedIndex target.page)) ordered source.value
  change Transport (resolveStoredOccurrence X Y source)
    (sourceAtIndex X Y (mergeDepth X Y - 1)
      (pages.indexEquivFin.symm (pages.paddedIndex target.page))
      ((pages.transport source.page target.page precedes).map source.value)) at result
  rw [transported] at result
  exact result

theorem sourceAtIndex_transport_same (X Y : Atlas) (n : Nat)
    (source target : (prefixFolio X Y n).data.Index)
    (precedes : (prefixFolio X Y n).data.indexNumber target ≤ (prefixFolio X Y n).data.indexNumber source)
    (same : source = target) (value : ((prefixFolio X Y n).data.page source).Carrier) :
    sourceAtIndex X Y n target ((prefixFolio X Y n).data.interval source target precedes |>.map value) =
      sourceAtIndex X Y n source value := by
  subst target
  rw [FolioData.interval_identity]
  rfl

theorem resolveStored_normalize (X Y : Atlas) (source : (pagination X Y).pages.Occurrence) :
    resolveStoredOccurrence X Y source.normalize = resolveStoredOccurrence X Y source := by
  unfold resolveStoredOccurrence FolioData.Occurrence.normalize FolioData.transport
  apply sourceAtIndex_transport_same
  simp [FolioData.paddedIndex]

theorem resolvePageCell_cast (X Y : Atlas) {n m : Nat} (same : n = m) (cell : ValidPageCell X Y n) :
    resolvePageCell X Y m (cast (congrArg (ValidPageCell X Y) same) cell) =
      match decodedPageCell X Y n cell with
      | .inl value => .left (FolioData.ValidElement.ofOccurrence
          ⟨m, cast (congrArg (fun k => (componentPage X k).Carrier) same) value⟩)
      | .inr value => .right (FolioData.ValidElement.ofOccurrence
          ⟨m, cast (congrArg (fun k => (componentPage Y k).Carrier) same) value⟩) := by
  subst m
  rfl

theorem resolveStored_bounded (X Y : Atlas) (source : (pagination X Y).pages.Occurrence)
    (bounded : source.page ≤ (pagination X Y).pages.depth - 1) :
    resolveStoredOccurrence X Y source = resolveOccurrence X Y source := by
  let limit := mergeDepth X Y - 1
  cases source with
  | mk page value =>
    cases page with
    | zero =>
      have index : (pagination X Y).pages.indexEquivFin.symm ((pagination X Y).pages.paddedIndex 0) =
          (prefixFolio X Y limit).data.firstIndex := by
        change (prefixFolio X Y limit).data.indexEquivFin.symm
          ((prefixFolio X Y limit).data.paddedIndex 0) = _
        apply index_eq_of_number (prefixFolio X Y limit).data
        simp [FolioData.paddedIndex]
      have result := sourceAtIndex_heq X Y limit index
        (cast_heq (congrArg (fun i => ((prefixFolio X Y limit).data.page i).Carrier) index) value).symm
      exact result.trans (sourceAtIndex_first X Y limit _)
    | succ n =>
      have hn : n ≤ limit := by
        change n + 1 ≤ (prefixFolio X Y limit).data.depth - 1 at bounded
        rw [prefixFolio_depth] at bounded
        omega
      let k : Fin (limit + 1) := ⟨n, by omega⟩
      have index : (pagination X Y).pages.indexEquivFin.symm ((pagination X Y).pages.paddedIndex (n + 1)) =
          componentIndex X Y limit k := by
        change (prefixFolio X Y limit).data.indexEquivFin.symm
          ((prefixFolio X Y limit).data.paddedIndex (n + 1)) = _
        apply index_eq_of_number (prefixFolio X Y limit).data
        rw [FolioData.indexEquivFin_symm_number, componentIndex_number]
        simp only [FolioData.paddedIndex, k]
        rw [prefixFolio_depth]
        omega
      have page : (pagination X Y).pages.pageAt (n + 1) = mergePage X Y n :=
        (prefixPageAt_succ X Y limit n).trans (congrArg (mergePage X Y) (Nat.min_eq_left hn))
      let cell := cast (congrArg Page.Carrier page) value
      have result := (sourceAtIndex_heq X Y limit index
        ((cast_heq (congrArg Page.Carrier page) value).symm.trans
          (cast_heq (congrArg Page.Carrier (componentIndex_page X Y limit k).symm) cell).symm)).trans
        (sourceAtIndex_component X Y limit k cell)
      refine result.trans ?_
      have runtime := resolvePageCell_cast X Y (Nat.min_eq_left hn)
        (cast (congrArg Page.Carrier (prefixPageAt_succ X Y limit n)) value)
      dsimp only [resolveOccurrence, k, cell]
      convert runtime using 1 <;> simp only [cast_cast]
      cases decodedPageCell X Y (min n limit)
        (cast (congrArg Page.Carrier (prefixPageAt_succ X Y limit n)) value) <;> rfl

theorem resolveStored_normalized_runtime (X Y : Atlas) (source : (pagination X Y).pages.Occurrence) :
    resolveStoredOccurrence X Y source = resolveOccurrence X Y source.normalize := by
  rw [← resolveStored_normalize X Y source]
  exact resolveStored_bounded X Y source.normalize (min_le_right _ _)

def resolveStoredElement (X Y : Atlas) (source : (pagination X Y).Element) : SourceCell X Y :=
  resolveStoredOccurrence X Y source.occurrence

-- ALIGN: MERGE-RESOLVED-ARROW.
theorem resolveStoredElement_arrow (X Y : Atlas) {source target : (pagination X Y).Element}
    (arrow : source ⟶ target) : Transport (resolveStoredElement X Y source) (resolveStoredElement X Y target) := by
  apply resolveStored_arrow
  change PageElement.Arrow source.occurrence.toRaw target.occurrence.toRaw
  simpa only [FolioData.ValidElement.occurrence_toRaw] using arrow

theorem resolveStoredElement_normalize (X Y : Atlas) (source : (pagination X Y).Element) :
    resolveStoredElement X Y source.normalize = resolveStoredElement X Y source := by
  have same : source.normalize.occurrence = source.occurrence.normalize := by
    apply FolioData.Occurrence.toRaw_injective
    rw [FolioData.ValidElement.occurrence_toRaw, FolioData.Occurrence.normalize_toRaw,
      FolioData.ValidElement.occurrence_toRaw]
    rfl
  unfold resolveStoredElement
  rw [same, resolveStored_normalize]

-- ALIGN: MERGE-NORMALIZED-RESOLUTION.
theorem resolveStoredElement_runtime (X Y : Atlas) (source : (pagination X Y).Element) :
    resolveStoredElement X Y source = resolveOccurrence X Y source.normalize.occurrence := by
  rw [← resolveStoredElement_normalize X Y source]
  apply resolveStored_bounded
  change source.normalize.occurrence.toRaw.page ≤ _
  rw [FolioData.ValidElement.occurrence_toRaw]
  exact min_le_right _ _

-- ALIGN: MERGE-RESOLVED-CELL.
theorem resolveStoredElement_cell_eq (X Y : Atlas) {source target : (pagination X Y).Element}
    (same : source.val.cell = target.val.cell) :
    resolveStoredElement X Y source = resolveStoredElement X Y target := by
  rw [← resolveStoredElement_normalize X Y source, ← resolveStoredElement_normalize X Y target]
  congr 1
  exact (FolioData.ValidElement.cell_eq_iff_normalize_eq source target).mp same

end Datra.Executable.AtlasMerge
