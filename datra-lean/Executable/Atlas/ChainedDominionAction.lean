import Executable.Atlas.ChainedDominion

namespace Datra.Executable

inductive ChainedDominionCell (A : Type) where
  | extent
  | region : A → ChainedDominionCell A

namespace ChainedDominionAtlas
variable {A Object Source Middle Target : Type}

-- ALIGN: CHAINED-PAGE-SELECTION.
def chainValueAt {Scope : Type*} {scope : Scope} (first : A) (owner : Chain A)
    (occurrence : PageElement scope) : A :=
  match owner.chainIndex occurrence.position with
  | none => first
  | some index => index.object

-- ALIGN: CHAINED-PAGE-CELL.
def chainedDominionCell {Scope : Type*} {scope : Scope} (first : A) (owner : Chain A)
    (occurrence : PageElement scope) : ChainedDominionCell A :=
  if occurrence.page = 0 then .extent else .region (chainValueAt first owner occurrence)

-- ALIGN: CHAINED-PAGE-NORMALIZATION.
theorem cellNormalization {Scope : Type*} {scope : Scope} (first : A) (owner : Chain A)
    (occurrence : PageElement scope) :
    chainedDominionCell first owner (PageElement.normalize 1 2 occurrence) =
      chainedDominionCell first owner occurrence := by
  by_cases origin : occurrence.page = 0
  · simp [chainedDominionCell, PageElement.normalize, origin]
  · have positive : min occurrence.page 1 ≠ 0 := by omega
    simp [chainedDominionCell, PageElement.normalize, origin, positive, chainValueAt]

-- ALIGN: CHAINED-CELL-MEMBERSHIP.
def cellAccepts (owner : Chain A) : ChainedDominionCell A → ChainedDominionCellData A Object → Bool
  | .extent, datum => extentAccepts datum
  | .region selected, datum => regionAccepts owner selected datum

-- ALIGN: CHAINED-CELL-ORDER.
def cellPrecedes (owner : Chain A) : ChainedDominionCell A → ChainedDominionCell A → Bool
  | .extent, .extent => true
  | .extent, .region _ => false
  | .region _, .extent => true
  | .region source, .region target => decide (owner.position source = owner.position target)

-- ALIGN: CHAINED-CELL-RETAG.
-- ALIGN: RANKED-CELL-RETAG.
def retagCell : ChainedDominionCellData A Source → ChainedDominionCellData A Target
  | .extent value => .extent value
  | .region value => .region value

-- ALIGN: CHAINED-CELL-RETAG-MEMBERSHIP.
theorem retagAccepts (owner : Chain A) (cell : ChainedDominionCell A)
    (datum : ChainedDominionCellData A Source) :
    cellAccepts owner cell (retagCell datum : ChainedDominionCellData A Target) =
      cellAccepts owner cell datum := by
  cases cell <;> cases datum <;> rfl

-- ALIGN: CHAINED-CELL-FORWARD.
def cellMap (owner : Chain A) : ChainedDominionCell A → ChainedDominionCell A →
    ChainedDominionCellData A Source → ChainedDominionCellData A Target
  | .extent, _, datum => retagCell datum
  | .region selected, .extent, datum => regionToExtent owner selected datum
  | .region _, .region _, datum => retagCell datum

-- ALIGN: CHAINED-CELL-INVERSE.
def cellPreimage (owner : Chain A) : ChainedDominionCell A → ChainedDominionCell A →
    ChainedDominionCellData A Target → Option (ChainedDominionCellData A Source)
  | .extent, _, datum => some (retagCell datum)
  | .region selected, .extent, datum => extentToRegion owner selected datum
  | .region _, .region _, datum => some (retagCell datum)

theorem cellMap_accepted (owner : Chain A) (source target : ChainedDominionCell A)
    (arrow : cellPrecedes owner source target = true) (datum : ChainedDominionCellData A Source)
    (accepted : cellAccepts owner source datum = true) :
    cellAccepts owner target (cellMap owner source target datum : ChainedDominionCellData A Target) = true := by
  cases source <;> cases target <;> cases datum <;>
    simp_all [cellPrecedes, cellAccepts, extentAccepts, regionAccepts, cellMap,
      retagCell, regionToExtent, cellValue]

theorem cellPreimage_accepted (owner : Chain A) (source target : ChainedDominionCell A)
    (arrow : cellPrecedes owner source target = true) (datum : ChainedDominionCellData A Target)
    (accepted : cellAccepts owner target datum = true) (result : ChainedDominionCellData A Source)
    (found : cellPreimage owner source target datum = some result) :
    cellAccepts owner source result = true := by
  cases source <;> cases target <;> cases datum <;>
    simp_all [cellPrecedes, cellAccepts, extentAccepts, regionAccepts, cellPreimage,
      retagCell, extentToRegion]
  all_goals first | subst result | obtain ⟨same, rfl⟩ := found
  all_goals simp_all

-- ALIGN: CHAINED-CELL-ROUNDTRIP.
theorem cellRoundTrip (owner : Chain A) (source target : ChainedDominionCell A)
    (arrow : cellPrecedes owner source target = true) (datum : ChainedDominionCellData A Source)
    (accepted : cellAccepts owner source datum = true) :
    cellPreimage owner source target
      (cellMap owner source target datum : ChainedDominionCellData A Target) = some datum := by
  cases source <;> cases target <;> cases datum <;>
    simp_all [cellPrecedes, cellAccepts, extentAccepts, regionAccepts, cellMap,
      cellPreimage, retagCell, regionToExtent, cellValue, extentToRegion]

-- ALIGN: CHAINED-CELL-IDENTITY.
theorem cellIdentity (owner : Chain A) (cell : ChainedDominionCell A)
    (datum : ChainedDominionCellData A Object) :
    cellMap owner cell cell datum = datum ∧ cellPreimage owner cell cell datum = some datum := by
  cases cell <;> cases datum <;> simp [cellMap, cellPreimage, retagCell]

theorem cellPrecedes_trans (owner : Chain A) (source middle target : ChainedDominionCell A)
    (first : cellPrecedes owner source middle = true)
    (second : cellPrecedes owner middle target = true) : cellPrecedes owner source target = true := by
  cases source <;> cases middle <;> cases target <;> simp_all [cellPrecedes]

-- ALIGN: CHAINED-CELL-COMPOSITION.
theorem cellComposition (owner : Chain A) (source middle target : ChainedDominionCell A)
    (first : cellPrecedes owner source middle = true)
    (second : cellPrecedes owner middle target = true) (datum : ChainedDominionCellData A Source) :
    cellMap owner middle target (cellMap owner source middle datum : ChainedDominionCellData A Middle) =
      (cellMap owner source target datum : ChainedDominionCellData A Target) := by
  cases source <;> cases middle <;> cases target <;> cases datum <;>
    simp_all [cellPrecedes, cellMap, retagCell, regionToExtent, cellValue]

-- ALIGN: CHAINED-CELL-COMPOSE-INVERSE.
def composedCellPreimage (owner : Chain A) (source middle target : ChainedDominionCell A)
    (datum : ChainedDominionCellData A Target) : Option (ChainedDominionCellData A Source) :=
  (cellPreimage owner middle target datum : Option (ChainedDominionCellData A Middle)).bind
    (cellPreimage owner source middle)

-- ALIGN: CHAINED-CELL-INVERSE-COMPOSITION.
theorem cellInverseComposition (owner : Chain A) (source middle target : ChainedDominionCell A)
    (first : cellPrecedes owner source middle = true)
    (second : cellPrecedes owner middle target = true) (datum : ChainedDominionCellData A Target) :
    composedCellPreimage (Middle := Middle) owner source middle target datum =
      (cellPreimage owner source target datum : Option (ChainedDominionCellData A Source)) := by
  cases source <;> cases middle <;> cases target <;> cases datum <;>
    simp_all [cellPrecedes, composedCellPreimage, cellPreimage, retagCell, extentToRegion]
  all_goals split_ifs <;> simp_all

-- ALIGN: CHAINED-CELL-DISJOINT.
theorem cellDisjoint (owner : Chain A) (left right : A)
    (leftDatum : ChainedDominionCellData A Source) (rightDatum : ChainedDominionCellData A Target)
    (leftAccepted : cellAccepts owner (.region left) leftDatum = true)
    (rightAccepted : cellAccepts owner (.region right) rightDatum = true)
    (same : (cellMap owner (.region left) .extent leftDatum : ChainedDominionCellData A Object) =
      cellMap owner (.region right) .extent rightDatum) : owner.position left = owner.position right := by
  cases leftDatum <;> cases rightDatum <;>
    simp_all [cellAccepts, regionAccepts, cellMap, regionToExtent, cellValue]

abbrev CellCarrier (owner : Chain A) (cell : ChainedDominionCell A) (Object : Type) :=
  {datum : ChainedDominionCellData A Object // cellAccepts owner cell datum = true}

def certifiedCellPreimage (owner : Chain A) (source target : ChainedDominionCell A)
    (arrow : cellPrecedes owner source target = true) (datum : CellCarrier owner target Target) :
    Option (CellCarrier owner source Source) :=
  match found : cellPreimage owner source target datum.val with
  | none => none
  | some value => some ⟨value, cellPreimage_accepted owner source target arrow datum.val datum.property value found⟩

theorem certifiedCellPreimage_val (owner : Chain A) (source target : ChainedDominionCell A)
    (arrow : cellPrecedes owner source target = true) (datum : CellCarrier owner target Target) :
    (certifiedCellPreimage owner source target arrow datum).map
        (fun value : CellCarrier owner source Source => value.val) = cellPreimage owner source target datum.val := by
  unfold certifiedCellPreimage
  split <;> simp_all

-- ALIGN: CHAINED-CELL-INSERTION.
def cellInsertion (owner : Chain A) (source target : ChainedDominionCell A)
    (arrow : cellPrecedes owner source target = true) :
    DomanialInsertion (CellCarrier owner source Source) (CellCarrier owner target Target) where
  map datum := ⟨cellMap owner source target datum.val,
    cellMap_accepted owner source target arrow datum.val datum.property⟩
  preimage := certifiedCellPreimage owner source target arrow
  leftInverse datum := by
    have roundTrip := cellRoundTrip (Target := Target) owner source target arrow datum.val datum.property
    unfold certifiedCellPreimage
    split
    · rename_i missing
      rw [missing] at roundTrip
      cases roundTrip
    · rename_i value found
      exact congrArg some (Subtype.ext (Option.some.inj (found.symm.trans roundTrip)))

-- ALIGN: CHAINED-CELL-INSERTION-FORWARD.
theorem cellInsertion_map (owner : Chain A) (source target : ChainedDominionCell A)
    (arrow : cellPrecedes owner source target = true) (datum : CellCarrier owner source Source) :
    ((cellInsertion owner source target arrow).map datum : CellCarrier owner target Target).val =
      cellMap owner source target datum.val := rfl

-- ALIGN: CHAINED-CELL-INSERTION-INVERSE.
theorem cellInsertion_preimage (owner : Chain A) (source target : ChainedDominionCell A)
    (arrow : cellPrecedes owner source target = true) (datum : CellCarrier owner target Target) :
    ((cellInsertion owner source target arrow).preimage datum).map
        (fun value : CellCarrier owner source Source => value.val) = cellPreimage owner source target datum.val :=
  certifiedCellPreimage_val owner source target arrow datum

end ChainedDominionAtlas
end Datra.Executable
