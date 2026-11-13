import Executable.Atlas.Sequence.Arrows

namespace Datra.Executable.AtlasSequence
open CategoryTheory

variable {count : Nat}

/-- Membership depends on the genuine cell. An occurrence is only a
presentation used to compute the component membership test. -/
def Datum.Valid (positive : 0 < count) (members : Fin count → Atlas) {cell : PageElementCell} (datum : Datum cell) : Prop :=
  ∃ source : (pagination positive members).Element, source.val.cell = cell ∧
    contains (resolveStoredElement positive members source) datum = true

theorem Datum.valid_iff (positive : 0 < count) (members : Fin count → Atlas) (source : (pagination positive members).Element)
    (datum : Datum source.val.cell) :
    datum.Valid positive members ↔ contains (resolveStoredElement positive members source) datum = true := by
  constructor
  · rintro ⟨target, same, valid⟩
    rwa [resolveStoredElement_cell_eq positive members same] at valid
  · intro valid
    exact ⟨source, rfl, valid⟩

abbrev IndexedDatum (positive : 0 < count) (members : Fin count → Atlas) (cell : PageElementCell) :=
  {datum : Datum cell // datum.Valid positive members}

def indexedDatumEquiv (positive : 0 < count) (members : Fin count → Atlas) (source : (pagination positive members).Element) :
    IndexedDatum positive members source.val.cell ≃
      CertifiedDatum (resolveStoredElement positive members source) source.val.cell where
  toFun datum := ⟨datum.val, (Datum.valid_iff positive members source datum.val).mp datum.property⟩
  invFun datum := ⟨datum.val, (Datum.valid_iff positive members source datum.val).mpr datum.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

-- ALIGN: SEQUENCE-INDEXED-DOMINION.
def indexedDominion (positive : 0 < count) (members : Fin count → Atlas) (source : (pagination positive members).Element) :
    Dominion (IndexedDatum positive members source.val.cell) :=
  (dominionAt positive (resolveStoredElement positive members source) source.val.cell).reindex
    (indexedDatumEquiv positive members source).symm

def indexedDataMap {positive : 0 < count} {members : Fin count → Atlas} {source target : (pagination positive members).Element} (arrow : source ⟶ target) :
    DomanialInsertion (IndexedDatum positive members source.val.cell) (IndexedDatum positive members target.val.cell) :=
  (dataMap (resolveStoredElement_arrow positive members arrow) source.val.cell target.val.cell).reindex
    (indexedDatumEquiv positive members source).symm (indexedDatumEquiv positive members target).symm

def action (positive : 0 < count) (members : Fin count → Atlas) : AtlasAction (pagination positive members).pages (IndexedDatum positive members) where
  dataAt := indexedDominion positive members
  mapData := indexedDataMap

theorem action_map_value {positive : 0 < count} {members : Fin count → Atlas} {source target : (pagination positive members).Element}
    (arrow : source ⟶ target) (datum : IndexedDatum positive members source.val.cell) :
    ((action positive members).normalizedMap arrow |>.map datum).val = retag datum.val := rfl

-- ALIGN: SEQUENCE-ATLAS-IDENTITY.
theorem action_identity (positive : 0 < count) (members : Fin count → Atlas) (source : (pagination positive members).Element)
    (datum : IndexedDatum positive members source.val.cell) :
    ((action positive members).normalizedMap (𝟙 source)).map datum = datum := by
  apply Subtype.ext
  exact retag_self datum.val

-- ALIGN: SEQUENCE-ATLAS-COMPOSITION.
theorem action_composition {positive : 0 < count} {members : Fin count → Atlas} {source middle target : (pagination positive members).Element}
    (first : source ⟶ middle) (second : middle ⟶ target) (datum : IndexedDatum positive members source.val.cell) :
    ((action positive members).normalizedMap (first ≫ second)).map datum =
      ((action positive members).normalizedMap second).map (((action positive members).normalizedMap first).map datum) := by
  apply Subtype.ext
  exact (retag_retag datum.val).symm

-- ALIGN: SEQUENCE-ATLAS-COHERENCE.
theorem action_coherence (positive : 0 < count) (members : Fin count → Atlas) (source : (pagination positive members).Element)
    (datum : IndexedDatum positive members source.val.cell) :
    ((action positive members).normalizedMap source.toNormalized).map datum = datum := by
  apply Subtype.ext
  exact retag_self datum.val

theorem resolvePageCell_separates (members : Fin count → Atlas) (n : Nat)
    (left right : ValidPageCell members n) {cell : PageElementCell} (datum : Datum cell)
    (inLeft : contains (resolvePageCell members n left) datum = true)
    (inRight : contains (resolvePageCell members n right) datum = true) : left = right := by
  obtain ⟨⟨i, a⟩, ha⟩ := left.property
  obtain ⟨⟨j, b⟩, hb⟩ := right.property
  have ea : encodedPageCell members n ⟨i, a⟩ = left := Subtype.ext ha
  have eb : encodedPageCell members n ⟨j, b⟩ = right := Subtype.ext hb
  rw [← ea, resolvePageCell_encode] at inLeft
  rw [← eb, resolvePageCell_encode] at inRight
  obtain ⟨tagA, inLeft⟩ := Bool.and_eq_true_iff.mp inLeft
  obtain ⟨tagB, inRight⟩ := Bool.and_eq_true_iff.mp inRight
  have indices : i = j := Fin.ext ((beq_iff_eq.mp tagA).symm.trans (beq_iff_eq.mp tagB))
  subst j
  have same := (members i).cellContainsRank_samePage
    (FolioData.ValidElement.ofOccurrence ⟨n, a⟩)
    (FolioData.ValidElement.ofOccurrence ⟨n, b⟩) rfl datum.originRank inLeft inRight
  have positions := congrArg (fun source : (members i).Element => source.val.position) same
  have values : a = b := (componentPage members n i).chain.positionInjective positions
  rw [← ea, ← eb, values]

theorem sourceAtIndex_separates (positive : 0 < count) (members : Fin count → Atlas) (n : Nat) (index : (prefixFolio positive members n).data.Index)
    (left right : ((prefixFolio positive members n).data.page index).Carrier) {cell : PageElementCell}
    (datum : Datum cell)
    (inLeft : contains (sourceAtIndex positive members n index left) datum = true)
    (inRight : contains (sourceAtIndex positive members n index right) datum = true) : left = right :=
  Folio.PrefixResolution.atIndex_separates DomanialInclusion.singletonPage () (fun x => by cases x; rfl)
    (sequencePage members) (collapseToOrigin positive members) (pageTransition members)
    (SourceCell.origin : SourceCell members) (resolvePageCell members)
    (fun source => contains source datum = true)
    (fun n a b => resolvePageCell_separates members n a b datum) n index left right inLeft inRight

theorem resolveStoredOccurrence_separates (positive : 0 < count) (members : Fin count → Atlas)
    (left right : (pagination positive members).pages.Occurrence) (samePage : left.page = right.page)
    {cell : PageElementCell} (datum : Datum cell)
    (inLeft : contains (resolveStoredOccurrence positive members left) datum = true)
    (inRight : contains (resolveStoredOccurrence positive members right) datum = true) : left = right := by
  cases left with
  | mk n left =>
    cases right with
    | mk m right =>
      change n = m at samePage
      subst m
      have values := sourceAtIndex_separates positive members (sequenceDepth members - 1) _ left right datum inLeft inRight
      cases values
      rfl

theorem resolveStoredElement_separates (positive : 0 < count) (members : Fin count → Atlas)
    (left right : (pagination positive members).Element) (samePage : left.val.page = right.val.page)
    {cell : PageElementCell} (datum : Datum cell)
    (inLeft : contains (resolveStoredElement positive members left) datum = true)
    (inRight : contains (resolveStoredElement positive members right) datum = true) : left = right := by
  have same : left.occurrence.page = right.occurrence.page := by
    simpa only [← FolioData.ValidElement.occurrence_toRaw] using samePage
  have occurrences := resolveStoredOccurrence_separates positive members left.occurrence right.occurrence same datum inLeft inRight
  simpa only [FolioData.ValidElement.ofOccurrence_occurrence] using
    congrArg FolioData.ValidElement.ofOccurrence occurrences

-- ALIGN: SEQUENCE-ATLAS-DISJOINT.
theorem action_disjoint (positive : 0 < count) (members : Fin count → Atlas) {left right origin : (pagination positive members).Element}
    (samePage : left.val.page = right.val.page) (different : left.val.position ≠ right.val.position)
    (leftArrow : left ⟶ origin) (rightArrow : right ⟶ origin)
    (a : IndexedDatum positive members left.val.cell) (b : IndexedDatum positive members right.val.cell) :
    ((action positive members).normalizedMap leftArrow).map a ≠ ((action positive members).normalizedMap rightArrow).map b := by
  intro equal
  have sameDatum : retag a.val = b.val := by
    apply Datum.ext
    · exact congrArg (fun datum => datum.val.member) equal
    · exact congrArg (fun datum => datum.val.originRank) equal
  have inLeft := (Datum.valid_iff positive members left a.val).mp a.property
  have inRight := (Datum.valid_iff positive members right b.val).mp b.property
  rw [← sameDatum, contains_retag] at inRight
  have cells := resolveStoredElement_separates positive members left right samePage a.val inLeft inRight
  exact different (congrArg (fun source => source.val.position) cells)

/-- The finite sequence with its computable genuine-cell data family. All four
Atlas constructor obligations follow from the component Atlas laws. -/
-- ALIGN: SEQUENCE-ATLAS-CONSTRUCTION.
def atlasSequence (positive : 0 < count) (members : Fin count → Atlas) : Atlas where
  pagination := pagination positive members
  cellData := IndexedDatum positive members
  data :=
    { action := action positive members
      identity := action_identity positive members
      composition := action_composition
      coherence := action_coherence positive members
      disjoint := fun samePage different _ _ => action_disjoint positive members samePage different }

/-- The genuine-cell data family has the image-Dominion interpretation of
the tagged member extents, with exactly the executable radix ranking. -/
-- ALIGN: SEQUENCE-INDEXED-INTERPRETATION.
noncomputable def indexedInterpretationEquiv (positive : 0 < count) (members : Fin count → Atlas) (source : (pagination positive members).Element) :
    IndexedDatum positive members source.val.cell ≃
      Datra.Semantics.imageDom (rootMap (resolveStoredElement positive members source)) :=
  (indexedDatumEquiv positive members source).trans (interpretationEquiv _ source.val.cell)

theorem indexedInterpretation_rank (positive : 0 < count) (members : Fin count → Atlas) (source : (pagination positive members).Element)
    (datum : IndexedDatum positive members source.val.cell) :
    (Datra.Semantics.imageDom (rootMap (resolveStoredElement positive members source))).toDom.rank
      (indexedInterpretationEquiv positive members source datum) = (indexedDominion positive members source).rank datum :=
  interpretation_rank positive _ _ (indexedDatumEquiv positive members source datum)

theorem indexedDataMap_interpretation {positive : 0 < count} {members : Fin count → Atlas} {source target : (pagination positive members).Element}
    (arrow : source ⟶ target) (datum : IndexedDatum positive members source.val.cell) :
    indexedInterpretationEquiv positive members target ((indexedDataMap arrow).map datum) =
      semanticMap (resolveStoredElement_arrow positive members arrow) (indexedInterpretationEquiv positive members source datum) :=
  dataMap_interpretation (resolveStoredElement_arrow positive members arrow) _ _ (indexedDatumEquiv positive members source datum)

-- ALIGN: SEQUENCE-ATLAS-DATA-INTERPRETATION.
theorem atlasSequence_data_interpretation {positive : 0 < count} {members : Fin count → Atlas} {source target : (atlasSequence positive members).Element}
    (arrow : source ⟶ target) (datum : (atlasSequence positive members).cellData source.val.cell) :
    indexedInterpretationEquiv positive members target.normalize
      (((atlasSequence positive members).data.action.normalizedMap arrow).map datum) =
      semanticMap (resolveStoredElement_arrow positive members (FolioData.ValidElement.normalizeArrow arrow))
        (indexedInterpretationEquiv positive members source.normalize datum) :=
  indexedDataMap_interpretation (FolioData.ValidElement.normalizeArrow arrow) datum

-- ALIGN: SEQUENCE-ATLAS-RANK-INTERPRETATION.
theorem atlasSequence_rank_interpretation (positive : 0 < count) (members : Fin count → Atlas) (source : (atlasSequence positive members).Element)
    (datum : (atlasSequence positive members).cellData source.val.cell) :
    (Datra.Semantics.imageDom (rootMap (resolveStoredElement positive members source.normalize))).toDom.rank
      (indexedInterpretationEquiv positive members source.normalize datum) =
      ((atlasSequence positive members).dataAt source).rank datum :=
  indexedInterpretation_rank positive members source.normalize datum

end Datra.Executable.AtlasSequence
