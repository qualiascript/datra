import Executable.Atlas.ChainedDominionAction

namespace Datra.Executable

/-- Ranked and chained presentations have the same two datum tags. Their
region selection and decoding operations are different. -/
abbrev RankedDominionCellData := ChainedDominionCellData
abbrev RankedDominionCell := ChainedDominionCell Nat

namespace RankedDominionAtlas
variable {A Object Source Middle Target : Type}

-- ALIGN: RANKED-DATUM-VALUE.
def cellValue : RankedDominionCellData A Object → A := ChainedDominionAtlas.cellValue

-- ALIGN: RANKED-SPINE-RANK.
def spineRank (position : Ordinal) : Nat :=
  (Ordinal.naturalAtOrdinal position).getD 0

theorem spineRank_finite (index : Nat) : spineRank (Ordinal.finiteOrdinal index) = index := by
  simp [spineRank]

def cellAt {Scope : Type*} {scope : Scope} (occurrence : PageElement scope) : RankedDominionCell :=
  if occurrence.page = 0 then .extent else .region (spineRank occurrence.position)

theorem cellAt_normalize {Scope : Type*} {scope : Scope} (occurrence : PageElement scope) :
    cellAt (PageElement.normalize 1 2 occurrence) = cellAt occurrence := by
  by_cases origin : occurrence.page = 0
  · simp [cellAt, PageElement.normalize, origin]
  · have positive : min occurrence.page 1 ≠ 0 := by omega
    simp [cellAt, PageElement.normalize, origin, positive]

def cellAccepts (owner : Dominion A) : RankedDominionCell → RankedDominionCellData A Object → Bool
  | .extent, datum => ChainedDominionAtlas.extentAccepts datum
  | .region _, .extent _ => false
  | .region index, .region value => decide (owner.rank value = index)

-- ALIGN: RANKED-PRESENTATION-MEMBERSHIP.
def rankedDominionAccepts {Scope : Type*} {scope : Scope} (owner : Dominion A)
    (occurrence : PageElement scope) (datum : RankedDominionCellData A Object) : Bool :=
  cellAccepts owner (cellAt occurrence) datum

abbrev CellCarrier (owner : Dominion A) (cell : RankedDominionCell) (Object : Type) :=
  {datum : RankedDominionCellData A Object // cellAccepts owner cell datum = true}

-- ALIGN: RANKED-CELL-RANK.
def cellRank (owner : Dominion A) : RankedDominionCell → RankedDominionCellData A Object → Nat
  | .extent, datum => owner.rank (cellValue datum)
  | .region _, _ => 0

/-- Preserve the original extent decoder. A region accepts only a decoder
result whose forward rank matches that region's position. -/
-- ALIGN: RANKED-CELL-DECODE.
def cellUnrank (owner : Dominion A) : RankedDominionCell → Nat → Option (RankedDominionCellData A Object)
  | .extent, index => (owner.unrank index).map ChainedDominionCellData.extent
  | .region position, index =>
      if index = 0 then (owner.lookupRank position).map ChainedDominionCellData.region else none

theorem cellUnrank_accepted (owner : Dominion A) (cell : RankedDominionCell) (index : Nat)
    (datum : RankedDominionCellData A Object) (found : cellUnrank owner cell index = some datum) :
    cellAccepts owner cell datum = true := by
  cases cell with
  | extent =>
      obtain ⟨value, _, rfl⟩ := Option.map_eq_some_iff.mp found
      rfl
  | region position =>
      simp only [cellUnrank] at found
      split_ifs at found with zero
      · obtain ⟨value, decoded, rfl⟩ := Option.map_eq_some_iff.mp found
        simp [cellAccepts, owner.lookupRank_sound position value decoded]

theorem cellRoundTrip (owner : Dominion A) (cell : RankedDominionCell)
    (datum : CellCarrier owner cell Object) :
    cellUnrank owner cell (cellRank owner cell datum.val) = some datum.val := by
  obtain ⟨datum, accepted⟩ := datum
  change cellUnrank owner cell (cellRank owner cell datum) = some datum
  cases cell <;> cases datum <;> simp_all [cellAccepts, ChainedDominionAtlas.extentAccepts, cellRank, cellUnrank, cellValue,
    ChainedDominionAtlas.cellValue, owner.coherence]
  rw [← accepted]
  exact owner.lookupRank_roundTrip _

def cellDominion (owner : Dominion A) (cell : RankedDominionCell) :
    Dominion (CellCarrier owner cell Object) where
  rank datum := cellRank owner cell datum.val
  unrank index := match found : cellUnrank owner cell index with
    | none => none
    | some datum => some ⟨datum, cellUnrank_accepted owner cell index datum found⟩
  coherence datum := by
    split <;> rename_i found
    · simp [cellRoundTrip] at found
    · simp only [cellRoundTrip, Option.some.injEq] at found
      subst found
      rfl

theorem cellDominion_unrank (owner : Dominion A) (cell : RankedDominionCell) (index : Nat) :
    ((cellDominion owner cell).unrank index).map Subtype.val =
      (cellUnrank owner cell index : Option (RankedDominionCellData A Object)) := by
  simp only [cellDominion]
  split <;> rename_i found <;> simp [found]

-- ALIGN: RANKED-REGION-MEMBERSHIP.
def regionAccepts (owner : Dominion A) (selected : Nat) (datum : RankedDominionCellData A Object) : Bool :=
  cellAccepts owner (.region selected) datum

-- ALIGN: RANKED-REGION-DECODE.
def regionUnrank (owner : Dominion A) (selected index : Nat) : Option (RankedDominionCellData A Object) :=
  cellUnrank owner (.region selected) index

-- ALIGN: RANKED-REGION-ROUNDTRIP.
theorem regionRoundTrip (owner : Dominion A) (selected : Nat)
    (datum : CellCarrier owner (.region selected) Object) :
    regionUnrank owner selected (ChainedDominionAtlas.regionRank datum.val) = some datum.val :=
  cellRoundTrip owner (.region selected) datum

-- ALIGN: RANKED-REGION-DOMINION.
def regionDominion (owner : Dominion A) (selected : Nat) :
    Dominion (CellCarrier owner (.region selected) Object) := cellDominion owner (.region selected)

-- ALIGN: RANKED-REGION-DOMINION-DECODE.
theorem regionDominion_unrank (owner : Dominion A) (selected index : Nat) :
    ((regionDominion owner selected).unrank index).map Subtype.val =
      (regionUnrank owner selected index : Option (RankedDominionCellData A Object)) :=
  cellDominion_unrank owner (.region selected) index

def extentEquiv (owner : Dominion A) : CellCarrier owner .extent Object ≃ A :=
  ChainedDominionAtlas.extentEquiv

theorem extent_rank (owner : Dominion A) (datum : CellCarrier owner .extent Object) :
    (cellDominion owner .extent).rank datum = owner.rank (extentEquiv owner datum) := rfl

/-- A region is exactly the fiber of the original Dominion's rank embedding. -/
def regionEquiv (owner : Dominion A) (index : Nat) :
    CellCarrier owner (.region index) Object ≃ {value : A // owner.rank value = index} where
  toFun datum := ⟨cellValue datum.val, by
    obtain ⟨datum, accepted⟩ := datum
    cases datum with
    | extent _ => simp [cellAccepts] at accepted
    | region value => exact of_decide_eq_true accepted⟩
  invFun value := ⟨.region value.val, by simp [cellAccepts, value.property]⟩
  left_inv datum := by
    obtain ⟨datum, accepted⟩ := datum
    apply Subtype.ext
    change ChainedDominionCellData.region (cellValue datum) = datum
    cases datum with
    | extent _ => simp [cellAccepts] at accepted
    | region _ => rfl
  right_inv _ := rfl

theorem region_subsingleton (owner : Dominion A) (index : Nat) :
    Subsingleton (CellCarrier owner (.region index) Object) := by
  constructor
  rintro ⟨left, hl⟩ ⟨right, hr⟩
  apply Subtype.ext
  change left = right
  cases left <;> cases right <;> simp_all [cellAccepts]
  exact owner.rank_injective (hl.trans hr.symm)

/-- Empty rank slots stay empty even if the ambient decoder returns a value
at a different rank. -/
theorem region_inhabited_iff (owner : Dominion A) (index : Nat) :
    Nonempty (CellCarrier owner (.region index) Object) ↔ ∃ value, owner.rank value = index := by
  constructor
  · rintro ⟨⟨datum, accepted⟩⟩
    cases datum with
    | extent _ => simp [cellAccepts] at accepted
    | region value => exact ⟨value, of_decide_eq_true accepted⟩
  · rintro ⟨value, same⟩
    exact ⟨⟨.region value, by simp [cellAccepts, same]⟩⟩

def cellPrecedes : RankedDominionCell → RankedDominionCell → Bool
  | .extent, .extent => true
  | .extent, .region _ => false
  | .region _, .extent => true
  | .region source, .region target => decide (source = target)

-- ALIGN: RANKED-CELL-FORWARD.
def cellMap : RankedDominionCell → RankedDominionCell →
    RankedDominionCellData A Source → RankedDominionCellData A Target
  | .extent, _, datum => ChainedDominionAtlas.retagCell datum
  | .region _, .extent, datum => .extent (cellValue datum)
  | .region _, .region _, datum => ChainedDominionAtlas.retagCell datum

/-- The raw inverse checks the rank of either datum tag, exactly as the
runtime region-to-extent component does. -/
-- ALIGN: RANKED-CELL-INVERSE.
def cellPreimage (owner : Dominion A) : RankedDominionCell → RankedDominionCell →
    RankedDominionCellData A Target → Option (RankedDominionCellData A Source)
  | .extent, _, datum => some (ChainedDominionAtlas.retagCell datum)
  | .region index, .extent, datum =>
      if owner.rank (cellValue datum) = index then some (.region (cellValue datum)) else none
  | .region _, .region _, datum => some (ChainedDominionAtlas.retagCell datum)

theorem cellMap_accepted (owner : Dominion A) (source target : RankedDominionCell)
    (arrow : cellPrecedes source target = true) (datum : CellCarrier owner source Source) :
    cellAccepts owner target (cellMap source target datum.val : RankedDominionCellData A Target) = true := by
  obtain ⟨datum, accepted⟩ := datum
  change cellAccepts owner target (cellMap source target datum : RankedDominionCellData A Target) = true
  cases source <;> cases target <;> cases datum <;>
    simp_all [cellPrecedes, cellAccepts, ChainedDominionAtlas.extentAccepts, cellMap, cellValue, ChainedDominionAtlas.cellValue,
      ChainedDominionAtlas.retagCell]

theorem cellLeftInverse (owner : Dominion A) (source target : RankedDominionCell)
    (arrow : cellPrecedes source target = true) (datum : CellCarrier owner source Source) :
    cellPreimage owner source target (cellMap source target datum.val : RankedDominionCellData A Target) =
      some datum.val := by
  obtain ⟨datum, accepted⟩ := datum
  change cellPreimage owner source target (cellMap source target datum : RankedDominionCellData A Target) =
    some datum
  cases source <;> cases target <;> cases datum <;>
    simp_all [cellPrecedes, cellAccepts, ChainedDominionAtlas.extentAccepts, cellMap, cellPreimage, cellValue,
      ChainedDominionAtlas.cellValue, ChainedDominionAtlas.retagCell]

theorem cellPreimage_accepted (owner : Dominion A) (source target : RankedDominionCell)
    (arrow : cellPrecedes source target = true) (datum : RankedDominionCellData A Target)
    (accepted : cellAccepts owner target datum = true) (result : RankedDominionCellData A Source)
    (found : cellPreimage owner source target datum = some result) :
    cellAccepts owner source result = true := by
  cases source <;> cases target <;> cases datum <;>
    simp_all [cellPrecedes, cellAccepts, ChainedDominionAtlas.extentAccepts, cellPreimage,
      cellValue, ChainedDominionAtlas.cellValue, ChainedDominionAtlas.retagCell]
  all_goals first | subst result | obtain ⟨same, rfl⟩ := found
  all_goals simp_all

def certifiedCellPreimage (owner : Dominion A) (source target : RankedDominionCell)
    (arrow : cellPrecedes source target = true) (datum : CellCarrier owner target Target) :
    Option (CellCarrier owner source Source) :=
  match found : cellPreimage owner source target datum.val with
  | none => none
  | some value => some ⟨value, cellPreimage_accepted owner source target arrow
      datum.val datum.property value found⟩

def cellInsertion (owner : Dominion A) (source target : RankedDominionCell)
    (arrow : cellPrecedes source target = true) :
    DomanialInsertion (CellCarrier owner source Source) (CellCarrier owner target Target) where
  map datum := ⟨cellMap source target datum.val, cellMap_accepted owner source target arrow datum⟩
  preimage := certifiedCellPreimage owner source target arrow
  leftInverse datum := by
    have roundTrip := cellLeftInverse (Target := Target) owner source target arrow datum
    unfold certifiedCellPreimage
    split
    · rename_i missing
      rw [missing] at roundTrip
      cases roundTrip
    · rename_i value found
      exact congrArg some (Subtype.ext (Option.some.inj (found.symm.trans roundTrip)))

theorem cellInsertion_map (owner : Dominion A) (source target : RankedDominionCell)
    (arrow : cellPrecedes source target = true) (datum : CellCarrier owner source Source) :
    ((cellInsertion owner source target arrow).map datum : CellCarrier owner target Target).val =
      cellMap source target datum.val := rfl

theorem cellInsertion_preimage (owner : Dominion A) (source target : RankedDominionCell)
    (arrow : cellPrecedes source target = true) (datum : CellCarrier owner target Target) :
    ((cellInsertion owner source target arrow).preimage datum).map
        (fun value : CellCarrier owner source Source => value.val) = cellPreimage owner source target datum.val := by
  change (certifiedCellPreimage owner source target arrow datum).map _ = _
  unfold certifiedCellPreimage
  split <;> simp_all

theorem cellComposition (source middle target : RankedDominionCell)
    (first : cellPrecedes source middle = true) (second : cellPrecedes middle target = true)
    (datum : RankedDominionCellData A Source) :
    cellMap middle target (cellMap source middle datum : RankedDominionCellData A Middle) =
      (cellMap source target datum : RankedDominionCellData A Target) := by
  cases source <;> cases middle <;> cases target <;> cases datum <;>
    simp_all [cellPrecedes, cellMap, cellValue, ChainedDominionAtlas.cellValue,
      ChainedDominionAtlas.retagCell]

theorem cellIdentity (cell : RankedDominionCell) (datum : RankedDominionCellData A Object) :
    cellMap cell cell datum = datum := by
  cases cell <;> cases datum <;> rfl

theorem cellDisjoint (owner : Dominion A) (left right : Nat)
    (leftDatum : RankedDominionCellData A Source) (rightDatum : RankedDominionCellData A Target)
    (leftAccepted : cellAccepts owner (.region left) leftDatum = true)
    (rightAccepted : cellAccepts owner (.region right) rightDatum = true)
    (same : (cellMap (.region left) .extent leftDatum : RankedDominionCellData A Object) =
      cellMap (.region right) .extent rightDatum) : left = right := by
  cases leftDatum <;> cases rightDatum <;>
    simp_all [cellAccepts, cellMap, cellValue, ChainedDominionAtlas.cellValue]

theorem cellInverseComposition (owner : Dominion A) (source middle target : RankedDominionCell)
    (first : cellPrecedes source middle = true) (second : cellPrecedes middle target = true)
    (datum : RankedDominionCellData A Target) :
    (cellPreimage owner middle target datum : Option (RankedDominionCellData A Middle)).bind
        (cellPreimage owner source middle) =
      (cellPreimage owner source target datum : Option (RankedDominionCellData A Source)) := by
  cases source <;> cases middle <;> cases target <;> cases datum <;>
    simp_all [cellPrecedes, cellPreimage, cellValue, ChainedDominionAtlas.cellValue,
      ChainedDominionAtlas.retagCell]
  all_goals split_ifs <;> simp_all

end RankedDominionAtlas
end Datra.Executable
