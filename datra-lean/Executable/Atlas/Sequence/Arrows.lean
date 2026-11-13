import Executable.Atlas.Sequence.Resolution
import Executable.Folio.PrefixResolution

namespace Datra.Executable.AtlasSequence
open CategoryTheory

variable {count : Nat}

def resolvePageValue (members : Fin count → Atlas) (n : Nat) (source : PageValue members n) :
    SourceCell members :=
  .member source.1 (FolioData.ValidElement.ofOccurrence ⟨n, source.2⟩)

def resolvePageCell (members : Fin count → Atlas) (n : Nat) (cell : ValidPageCell members n) :
    SourceCell members := resolvePageValue members n (decodedPageCell members n cell)

theorem resolvePageCell_encode (members : Fin count → Atlas) (n : Nat) (source : PageValue members n) :
    resolvePageCell members n (encodedPageCell members n source) =
      .member source.1 (FolioData.ValidElement.ofOccurrence ⟨n, source.2⟩) := by
  unfold resolvePageCell
  rw [decodedPageCell_encode]
  rfl

theorem pageTransition_encode (members : Fin count → Atlas) (n : Nat) (source : PageValue members (n + 1)) :
    (pageTransition members n).map (encodedPageCell members (n + 1) source) =
      encodedPageCell members n ((componentTransition members n).map source) :=
  Subtype.ext (previousPageCell_encode members n source)

def Transport.intoOrigin {members : Fin count → Atlas} (source : SourceCell members) :
    Transport source .origin :=
  match source with
  | .origin => .origin
  | .member index source => .toOrigin index source

/-- Dropping a sequence trace preserves its member and applies that member's
checked page transport. -/
theorem resolve_pageTransition (members : Fin count → Atlas) (n : Nat)
    (cell : ValidPageCell members (n + 1)) :
    Transport (resolvePageCell members (n + 1) cell)
      (resolvePageCell members n ((pageTransition members n).map cell)) := by
  obtain ⟨value, same⟩ := cell.property
  have cellEq : encodedPageCell members (n + 1) value = cell := Subtype.ext same
  rw [← cellEq, pageTransition_encode, resolvePageCell_encode, resolvePageCell_encode]
  exact .member value.1 ((members value.1).pages.transportArrow (n + 1) n (Nat.le_succ n) value.2)

def sourceAtIndex (positive : 0 < count) (members : Fin count → Atlas) : (n : Nat) →
    (index : (prefixFolio positive members n).data.Index) →
    ((prefixFolio positive members n).data.page index).Carrier → SourceCell members :=
  Folio.PrefixResolution.atIndex DomanialInclusion.singletonPage () (fun x => by cases x; rfl)
    (sequencePage members) (collapseToOrigin positive members) (pageTransition members)
    (SourceCell.origin : SourceCell members) (resolvePageCell members)

/-- Every interval in the finite sequence folio resolves to a transport in
one member, or to the fresh sequence origin. -/
theorem resolve_interval (positive : 0 < count) (members : Fin count → Atlas) (n : Nat)
    (source target : (prefixFolio positive members n).data.Index)
    (precedes : (prefixFolio positive members n).data.indexNumber target ≤
      (prefixFolio positive members n).data.indexNumber source)
    (value : ((prefixFolio positive members n).data.page source).Carrier) :
    Transport (sourceAtIndex positive members n source value)
      (sourceAtIndex positive members n target
        ((prefixFolio positive members n).data.interval source target precedes |>.map value)) :=
  Folio.PrefixResolution.interval DomanialInclusion.singletonPage () (fun x => by cases x; rfl)
    (sequencePage members) (collapseToOrigin positive members) (pageTransition members)
    (SourceCell.origin : SourceCell members) (resolvePageCell members)
    Transport Transport.identity (fun first second => first.comp second)
    (fun _ _ => Transport.intoOrigin _) (resolve_pageTransition members) n source target precedes value

def resolveStoredOccurrence (positive : 0 < count) (members : Fin count → Atlas)
    (occurrence : (pagination positive members).pages.Occurrence) : SourceCell members :=
  sourceAtIndex positive members (sequenceDepth members - 1)
    ((pagination positive members).pages.indexEquivFin.symm
      ((pagination positive members).pages.paddedIndex occurrence.page)) occurrence.value


def componentIndex (positive : 0 < count) (members : Fin count → Atlas) :
    (n : Nat) → Fin (n + 1) → (prefixFolio positive members n).data.Index :=
  Folio.prefixIndex _ _ _ _ _ _

theorem componentIndex_number (positive : 0 < count) (members : Fin count → Atlas) (n : Nat) (k : Fin (n + 1)) :
    (prefixFolio positive members n).data.indexNumber (componentIndex positive members n k) = k.val + 1 :=
  Folio.prefixIndex_number _ _ _ _ _ _ n k

theorem componentIndex_page (positive : 0 < count) (members : Fin count → Atlas) (n : Nat) (k : Fin (n + 1)) :
    (prefixFolio positive members n).data.page (componentIndex positive members n k) = sequencePage members k.val :=
  Folio.prefixIndex_page _ _ _ _ _ _ n k
theorem sourceAtIndex_first (positive : 0 < count) (members : Fin count → Atlas) (n : Nat)
    (value : ((prefixFolio positive members n).data.page (prefixFolio positive members n).data.firstIndex).Carrier) :
    sourceAtIndex positive members n (prefixFolio positive members n).data.firstIndex value = .origin :=
  Folio.PrefixResolution.atIndex_first DomanialInclusion.singletonPage () (fun x => by cases x; rfl)
    (sequencePage members) (collapseToOrigin positive members) (pageTransition members)
    (SourceCell.origin : SourceCell members) (resolvePageCell members) n value

theorem sourceAtIndex_heq (positive : 0 < count) (members : Fin count → Atlas) (n : Nat)
    {i j : (prefixFolio positive members n).data.Index} (same : i = j)
    {a : ((prefixFolio positive members n).data.page i).Carrier}
    {b : ((prefixFolio positive members n).data.page j).Carrier} (values : HEq a b) :
    sourceAtIndex positive members n i a = sourceAtIndex positive members n j b :=
  Folio.PrefixResolution.atIndex_heq DomanialInclusion.singletonPage () (fun x => by cases x; rfl)
    (sequencePage members) (collapseToOrigin positive members) (pageTransition members)
    (SourceCell.origin : SourceCell members) (resolvePageCell members) n same values

theorem sourceAtIndex_component (positive : 0 < count) (members : Fin count → Atlas) (n : Nat) (k : Fin (n + 1))
    (value : ValidPageCell members k.val) :
    sourceAtIndex positive members n (componentIndex positive members n k)
      (cast (congrArg Page.Carrier (componentIndex_page positive members n k).symm) value) =
      resolvePageCell members k.val value :=
  Folio.PrefixResolution.atIndex_component DomanialInclusion.singletonPage () (fun x => by cases x; rfl)
    (sequencePage members) (collapseToOrigin positive members) (pageTransition members)
    (SourceCell.origin : SourceCell members) (resolvePageCell members) n k value

theorem resolveStored_arrow (positive : 0 < count) (members : Fin count → Atlas)
    {source target : (pagination positive members).pages.Occurrence} (arrow : source ⟶ target) :
    Transport (resolveStoredOccurrence positive members source) (resolveStoredOccurrence positive members target) := by
  let pages := (pagination positive members).pages
  have precedes : target.page ≤ source.page := arrow.precedes
  have transported : (pages.transport source.page target.page precedes).map source.value = target.value :=
    (pages.traceAt_suffix_iff source.page target.page precedes source.value target.value).mp arrow.transported
  have ordered : pages.indexNumber (pages.indexEquivFin.symm (pages.paddedIndex target.page)) ≤
      pages.indexNumber (pages.indexEquivFin.symm (pages.paddedIndex source.page)) := by
    simpa only [FolioData.indexEquivFin_symm_number, FolioData.paddedIndex] using
      min_le_min_right (pages.depth - 1) precedes
  have result := resolve_interval positive members (sequenceDepth members - 1)
    (pages.indexEquivFin.symm (pages.paddedIndex source.page))
    (pages.indexEquivFin.symm (pages.paddedIndex target.page)) ordered source.value
  change Transport (resolveStoredOccurrence positive members source)
    (sourceAtIndex positive members (sequenceDepth members - 1)
      (pages.indexEquivFin.symm (pages.paddedIndex target.page))
      ((pages.transport source.page target.page precedes).map source.value)) at result
  rw [transported] at result
  exact result

theorem sourceAtIndex_transport_same (positive : 0 < count) (members : Fin count → Atlas) (n : Nat)
    (source target : (prefixFolio positive members n).data.Index)
    (precedes : (prefixFolio positive members n).data.indexNumber target ≤
      (prefixFolio positive members n).data.indexNumber source)
    (same : source = target) (value : ((prefixFolio positive members n).data.page source).Carrier) :
    sourceAtIndex positive members n target
      ((prefixFolio positive members n).data.interval source target precedes |>.map value) =
      sourceAtIndex positive members n source value := by
  subst target
  rw [FolioData.interval_identity]
  rfl

theorem resolveStored_normalize (positive : 0 < count) (members : Fin count → Atlas)
    (source : (pagination positive members).pages.Occurrence) :
    resolveStoredOccurrence positive members source.normalize = resolveStoredOccurrence positive members source := by
  unfold resolveStoredOccurrence FolioData.Occurrence.normalize FolioData.transport
  apply sourceAtIndex_transport_same
  simp [FolioData.paddedIndex]


theorem resolvePageCell_cast (members : Fin count → Atlas) {n m : Nat} (same : n = m)
    (cell : ValidPageCell members n) :
    resolvePageCell members m (cast (congrArg (ValidPageCell members) same) cell) =
      .member (decodedPageCell members n cell).1 (FolioData.ValidElement.ofOccurrence
        ⟨m, cast (congrArg (fun k => (componentPage members k (decodedPageCell members n cell).1).Carrier) same)
          (decodedPageCell members n cell).2⟩) := by
  subst m
  rfl
theorem resolveStored_bounded (positive : 0 < count) (members : Fin count → Atlas) (source : (pagination positive members).pages.Occurrence)
    (bounded : source.page ≤ (pagination positive members).pages.depth - 1) :
    resolveStoredOccurrence positive members source = resolveOccurrence positive members source := by
  let limit := sequenceDepth members - 1
  cases source with
  | mk page value =>
    cases page with
    | zero =>
      have index : (pagination positive members).pages.indexEquivFin.symm ((pagination positive members).pages.paddedIndex 0) =
          (prefixFolio positive members limit).data.firstIndex := by
        change (prefixFolio positive members limit).data.indexEquivFin.symm
          ((prefixFolio positive members limit).data.paddedIndex 0) = _
        apply FolioData.index_eq_of_number (prefixFolio positive members limit).data
        simp [FolioData.paddedIndex]
      have result := sourceAtIndex_heq positive members limit index
        (cast_heq (congrArg (fun i => ((prefixFolio positive members limit).data.page i).Carrier) index) value).symm
      exact result.trans (sourceAtIndex_first positive members limit _)
    | succ n =>
      have hn : n ≤ limit := by
        change n + 1 ≤ (prefixFolio positive members limit).data.depth - 1 at bounded
        rw [prefixFolio_depth] at bounded
        omega
      let k : Fin (limit + 1) := ⟨n, by omega⟩
      have index : (pagination positive members).pages.indexEquivFin.symm ((pagination positive members).pages.paddedIndex (n + 1)) =
          componentIndex positive members limit k := by
        change (prefixFolio positive members limit).data.indexEquivFin.symm
          ((prefixFolio positive members limit).data.paddedIndex (n + 1)) = _
        apply FolioData.index_eq_of_number (prefixFolio positive members limit).data
        rw [FolioData.indexEquivFin_symm_number, componentIndex_number]
        simp only [FolioData.paddedIndex, k]
        rw [prefixFolio_depth]
        omega
      have page : (pagination positive members).pages.pageAt (n + 1) = sequencePage members n :=
        (prefixPageAt_succ positive members limit n).trans (congrArg (sequencePage members) (Nat.min_eq_left hn))
      let cell := cast (congrArg Page.Carrier page) value
      have result := (sourceAtIndex_heq positive members limit index
        ((cast_heq (congrArg Page.Carrier page) value).symm.trans
          (cast_heq (congrArg Page.Carrier (componentIndex_page positive members limit k).symm) cell).symm)).trans
        (sourceAtIndex_component positive members limit k cell)
      refine result.trans ?_
      have runtime := resolvePageCell_cast members (Nat.min_eq_left hn)
        (cast (congrArg Page.Carrier (prefixPageAt_succ positive members limit n)) value)
      dsimp only [resolveOccurrence, sourceAtPage, k, cell]
      convert runtime using 1
      simp only [cast_cast]

theorem resolveStored_normalized_runtime (positive : 0 < count) (members : Fin count → Atlas) (source : (pagination positive members).pages.Occurrence) :
    resolveStoredOccurrence positive members source = resolveOccurrence positive members source.normalize := by
  rw [← resolveStored_normalize positive members source]
  exact resolveStored_bounded positive members source.normalize (min_le_right _ _)

def resolveStoredElement (positive : 0 < count) (members : Fin count → Atlas)
    (source : (pagination positive members).Element) : SourceCell members :=
  resolveStoredOccurrence positive members source.occurrence

-- ALIGN: SEQUENCE-RESOLVED-ARROW.
theorem resolveStoredElement_arrow (positive : 0 < count) (members : Fin count → Atlas)
    {source target : (pagination positive members).Element} (arrow : source ⟶ target) :
    Transport (resolveStoredElement positive members source) (resolveStoredElement positive members target) := by
  apply resolveStored_arrow
  change PageElement.Arrow source.occurrence.toRaw target.occurrence.toRaw
  simpa only [FolioData.ValidElement.occurrence_toRaw] using arrow

theorem resolveStoredElement_normalize (positive : 0 < count) (members : Fin count → Atlas)
    (source : (pagination positive members).Element) :
    resolveStoredElement positive members source.normalize = resolveStoredElement positive members source := by
  have same : source.normalize.occurrence = source.occurrence.normalize := by
    apply FolioData.Occurrence.toRaw_injective
    rw [FolioData.ValidElement.occurrence_toRaw, FolioData.Occurrence.normalize_toRaw,
      FolioData.ValidElement.occurrence_toRaw]
    rfl
  unfold resolveStoredElement
  rw [same, resolveStored_normalize]

-- ALIGN: SEQUENCE-NORMALIZED-RESOLUTION.
theorem resolveStoredElement_runtime (positive : 0 < count) (members : Fin count → Atlas) (source : (pagination positive members).Element) :
    resolveStoredElement positive members source = resolveOccurrence positive members source.normalize.occurrence := by
  rw [← resolveStoredElement_normalize positive members source]
  apply resolveStored_bounded
  change source.normalize.occurrence.toRaw.page ≤ _
  rw [FolioData.ValidElement.occurrence_toRaw]
  exact min_le_right _ _


-- ALIGN: SEQUENCE-RESOLVED-CELL.
theorem resolveStoredElement_cell_eq (positive : 0 < count) (members : Fin count → Atlas)
    {source target : (pagination positive members).Element} (same : source.val.cell = target.val.cell) :
    resolveStoredElement positive members source = resolveStoredElement positive members target := by
  rw [← resolveStoredElement_normalize positive members source, ← resolveStoredElement_normalize positive members target]
  congr 1
  exact (FolioData.ValidElement.cell_eq_iff_normalize_eq source target).mp same

end Datra.Executable.AtlasSequence
