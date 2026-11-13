import Executable.Atlas.Merge.Arrows

namespace Datra.Executable.AtlasMerge
open CategoryTheory

/-- Membership depends on the genuine cell. An occurrence is only a
presentation used to compute the component membership test. -/
def Datum.Valid (X Y : Atlas) {cell : PageElementCell} (datum : Datum cell) : Prop :=
  ∃ source : (pagination X Y).Element, source.val.cell = cell ∧
    contains (resolveStoredElement X Y source) datum = true

theorem Datum.valid_iff (X Y : Atlas) (source : (pagination X Y).Element)
    (datum : Datum source.val.cell) :
    datum.Valid X Y ↔ contains (resolveStoredElement X Y source) datum = true := by
  constructor
  · rintro ⟨target, same, valid⟩
    rwa [resolveStoredElement_cell_eq X Y same] at valid
  · intro valid
    exact ⟨source, rfl, valid⟩

abbrev IndexedDatum (X Y : Atlas) (cell : PageElementCell) :=
  {datum : Datum cell // datum.Valid X Y}

def indexedDatumEquiv (X Y : Atlas) (source : (pagination X Y).Element) :
    IndexedDatum X Y source.val.cell ≃
      CertifiedDatum (resolveStoredElement X Y source) source.val.cell where
  toFun datum := ⟨datum.val, (Datum.valid_iff X Y source datum.val).mp datum.property⟩
  invFun datum := ⟨datum.val, (Datum.valid_iff X Y source datum.val).mpr datum.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

-- ALIGN: MERGE-INDEXED-DOMINION.
def indexedDominion (X Y : Atlas) (source : (pagination X Y).Element) :
    Dominion (IndexedDatum X Y source.val.cell) where
  rank datum := datumRank datum.val
  unrank candidate := ((dominionAt (resolveStoredElement X Y source) source.val.cell).unrank candidate).map
    (indexedDatumEquiv X Y source).symm
  coherence datum := by
    change Option.map _ ((dominionAt (resolveStoredElement X Y source) source.val.cell).unrank
      ((dominionAt (resolveStoredElement X Y source) source.val.cell).rank
        (indexedDatumEquiv X Y source datum))) = _
    simp only [Dominion.coherence, Option.map_some, Equiv.symm_apply_apply]

def indexedDataMap {X Y : Atlas} {source target : (pagination X Y).Element} (arrow : source ⟶ target) :
    DomanialInsertion (IndexedDatum X Y source.val.cell) (IndexedDatum X Y target.val.cell) where
  map datum := (indexedDatumEquiv X Y target).symm
    ((dataMap (resolveStoredElement_arrow X Y arrow) source.val.cell target.val.cell).map
      (indexedDatumEquiv X Y source datum))
  preimage datum := ((dataMap (resolveStoredElement_arrow X Y arrow) source.val.cell target.val.cell).preimage
    (indexedDatumEquiv X Y target datum)).map (indexedDatumEquiv X Y source).symm
  leftInverse datum := by
    simp only [Equiv.apply_symm_apply, DomanialInsertion.leftInverse, Option.map_some,
      Equiv.symm_apply_apply]

def action (X Y : Atlas) : AtlasAction (pagination X Y).pages (IndexedDatum X Y) where
  dataAt := indexedDominion X Y
  mapData := indexedDataMap

theorem action_map_value {X Y : Atlas} {source target : (pagination X Y).Element}
    (arrow : source ⟶ target) (datum : IndexedDatum X Y source.val.cell) :
    ((action X Y).normalizedMap arrow |>.map datum).val = retag datum.val := rfl

-- ALIGN: MERGE-ATLAS-IDENTITY.
theorem action_identity (X Y : Atlas) (source : (pagination X Y).Element)
    (datum : IndexedDatum X Y source.val.cell) :
    ((action X Y).normalizedMap (𝟙 source)).map datum = datum := by
  apply Subtype.ext
  exact retag_self datum.val

-- ALIGN: MERGE-ATLAS-COMPOSITION.
theorem action_composition {X Y : Atlas} {source middle target : (pagination X Y).Element}
    (first : source ⟶ middle) (second : middle ⟶ target) (datum : IndexedDatum X Y source.val.cell) :
    ((action X Y).normalizedMap (first ≫ second)).map datum =
      ((action X Y).normalizedMap second).map (((action X Y).normalizedMap first).map datum) := by
  apply Subtype.ext
  exact (retag_retag datum.val).symm

-- ALIGN: MERGE-ATLAS-COHERENCE.
theorem action_coherence (X Y : Atlas) (source : (pagination X Y).Element)
    (datum : IndexedDatum X Y source.val.cell) :
    ((action X Y).normalizedMap source.toNormalized).map datum = datum := by
  apply Subtype.ext
  exact retag_self datum.val

theorem resolvePageCell_separates (X Y : Atlas) (n : Nat) (left right : ValidPageCell X Y n)
    {cell : PageElementCell} (datum : Datum cell)
    (inLeft : contains (resolvePageCell X Y n left) datum = true)
    (inRight : contains (resolvePageCell X Y n right) datum = true) : left = right := by
  obtain ⟨a, ha⟩ := left.property
  obtain ⟨b, hb⟩ := right.property
  have ea : encodedPageCell X Y n a = left := Subtype.ext ha
  have eb : encodedPageCell X Y n b = right := Subtype.ext hb
  rw [← ea] at inLeft
  rw [← eb] at inRight
  rw [← ea, ← eb]
  cases a <;> cases b <;> cases datum <;>
    simp only [resolvePageCell_left, resolvePageCell_right, contains] at inLeft inRight
  all_goals try contradiction
  all_goals rename_i a b valueRank
  · have same := X.cellContainsRank_samePage
      (FolioData.ValidElement.ofOccurrence ⟨n, a⟩)
      (FolioData.ValidElement.ofOccurrence ⟨n, b⟩) rfl valueRank inLeft inRight
    have positions := congrArg (fun source : X.Element => source.val.position) same
    have values : a = b := (componentPage X n).chain.positionInjective positions
    rw [values]
  · have same := Y.cellContainsRank_samePage
      (FolioData.ValidElement.ofOccurrence ⟨n, a⟩)
      (FolioData.ValidElement.ofOccurrence ⟨n, b⟩) rfl valueRank inLeft inRight
    have positions := congrArg (fun source : Y.Element => source.val.position) same
    have values : a = b := (componentPage Y n).chain.positionInjective positions
    rw [values]

theorem sourceAtIndex_separates (X Y : Atlas) (n : Nat) (index : (prefixFolio X Y n).data.Index)
    (left right : ((prefixFolio X Y n).data.page index).Carrier) {cell : PageElementCell}
    (datum : Datum cell)
    (inLeft : contains (sourceAtIndex X Y n index left) datum = true)
    (inRight : contains (sourceAtIndex X Y n index right) datum = true) : left = right :=
  Folio.PrefixResolution.atIndex_separates DomanialInclusion.singletonPage () (fun x => by cases x; rfl)
    (mergePage X Y) (collapseToOrigin X Y) (pageTransition X Y)
    (SourceCell.origin : SourceCell X Y) (resolvePageCell X Y)
    (fun source => contains source datum = true)
    (fun n a b => resolvePageCell_separates X Y n a b datum) n index left right inLeft inRight

theorem resolveStoredOccurrence_separates (X Y : Atlas)
    (left right : (pagination X Y).pages.Occurrence) (samePage : left.page = right.page)
    {cell : PageElementCell} (datum : Datum cell)
    (inLeft : contains (resolveStoredOccurrence X Y left) datum = true)
    (inRight : contains (resolveStoredOccurrence X Y right) datum = true) : left = right := by
  cases left with
  | mk n left =>
    cases right with
    | mk m right =>
      change n = m at samePage
      subst m
      have values := sourceAtIndex_separates X Y (mergeDepth X Y - 1) _ left right datum inLeft inRight
      cases values
      rfl

theorem resolveStoredElement_separates (X Y : Atlas)
    (left right : (pagination X Y).Element) (samePage : left.val.page = right.val.page)
    {cell : PageElementCell} (datum : Datum cell)
    (inLeft : contains (resolveStoredElement X Y left) datum = true)
    (inRight : contains (resolveStoredElement X Y right) datum = true) : left = right := by
  have same : left.occurrence.page = right.occurrence.page := by
    simpa only [← FolioData.ValidElement.occurrence_toRaw] using samePage
  have occurrences := resolveStoredOccurrence_separates X Y left.occurrence right.occurrence same datum inLeft inRight
  simpa only [FolioData.ValidElement.ofOccurrence_occurrence] using
    congrArg FolioData.ValidElement.ofOccurrence occurrences

-- ALIGN: MERGE-ATLAS-DISJOINT.
theorem action_disjoint (X Y : Atlas) {left right origin : (pagination X Y).Element}
    (samePage : left.val.page = right.val.page) (different : left.val.position ≠ right.val.position)
    (leftArrow : left ⟶ origin) (rightArrow : right ⟶ origin)
    (a : IndexedDatum X Y left.val.cell) (b : IndexedDatum X Y right.val.cell) :
    ((action X Y).normalizedMap leftArrow).map a ≠ ((action X Y).normalizedMap rightArrow).map b := by
  intro equal
  have ranks := congrArg (fun datum => datumRank datum.val) equal
  simp only [action_map_value, retag_rank] at ranks
  have sameDatum : retag a.val = b.val := datumRank_injective _ ((retag_rank a.val).trans ranks)
  have inLeft := (Datum.valid_iff X Y left a.val).mp a.property
  have inRight := (Datum.valid_iff X Y right b.val).mp b.property
  rw [← sameDatum, contains_retag] at inRight
  have cells := resolveStoredElement_separates X Y left right samePage a.val inLeft inRight
  exact different (congrArg (fun source => source.val.position) cells)

/-- The finite merge with its computable genuine-cell data family. All four
Atlas constructor obligations follow from the component Atlas laws. -/
-- ALIGN: MERGE-ATLAS-CONSTRUCTION.
def atlasMerge (X Y : Atlas) : Atlas where
  pagination := pagination X Y
  cellData := IndexedDatum X Y
  data :=
    { action := action X Y
      identity := action_identity X Y
      composition := action_composition
      coherence := action_coherence X Y
      disjoint := fun samePage different _ _ => action_disjoint X Y samePage different }

/-- The genuine-cell data family has the image-Dominion interpretation of
the written merge, with exactly the executable parity ranking. -/
-- ALIGN: MERGE-INDEXED-INTERPRETATION.
noncomputable def indexedInterpretationEquiv (X Y : Atlas) (source : (pagination X Y).Element) :
    IndexedDatum X Y source.val.cell ≃
      Datra.Semantics.imageDom (rootMap (resolveStoredElement X Y source)) :=
  (indexedDatumEquiv X Y source).trans (interpretationEquiv _ source.val.cell)

theorem indexedInterpretation_rank (X Y : Atlas) (source : (pagination X Y).Element)
    (datum : IndexedDatum X Y source.val.cell) :
    (Datra.Semantics.imageDom (rootMap (resolveStoredElement X Y source))).toDom.rank
      (indexedInterpretationEquiv X Y source datum) = (indexedDominion X Y source).rank datum :=
  interpretation_rank _ _ (indexedDatumEquiv X Y source datum)

theorem indexedDataMap_interpretation {X Y : Atlas} {source target : (pagination X Y).Element}
    (arrow : source ⟶ target) (datum : IndexedDatum X Y source.val.cell) :
    indexedInterpretationEquiv X Y target ((indexedDataMap arrow).map datum) =
      semanticMap (resolveStoredElement_arrow X Y arrow) (indexedInterpretationEquiv X Y source datum) :=
  dataMap_interpretation (resolveStoredElement_arrow X Y arrow) _ _ (indexedDatumEquiv X Y source datum)

-- ALIGN: MERGE-ATLAS-DATA-INTERPRETATION.
theorem atlasMerge_data_interpretation {X Y : Atlas} {source target : (atlasMerge X Y).Element}
    (arrow : source ⟶ target) (datum : (atlasMerge X Y).cellData source.val.cell) :
    indexedInterpretationEquiv X Y target.normalize
      (((atlasMerge X Y).data.action.normalizedMap arrow).map datum) =
      semanticMap (resolveStoredElement_arrow X Y (FolioData.ValidElement.normalizeArrow arrow))
        (indexedInterpretationEquiv X Y source.normalize datum) :=
  indexedDataMap_interpretation (FolioData.ValidElement.normalizeArrow arrow) datum

-- ALIGN: MERGE-ATLAS-RANK-INTERPRETATION.
theorem atlasMerge_rank_interpretation (X Y : Atlas) (source : (atlasMerge X Y).Element)
    (datum : (atlasMerge X Y).cellData source.val.cell) :
    (Datra.Semantics.imageDom (rootMap (resolveStoredElement X Y source.normalize))).toDom.rank
      (indexedInterpretationEquiv X Y source.normalize datum) =
      ((atlasMerge X Y).dataAt source).rank datum :=
  indexedInterpretation_rank X Y source.normalize datum

end Datra.Executable.AtlasMerge
