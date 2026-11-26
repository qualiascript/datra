import Executable.Chain
import Executable.Atlas.TotalMap

namespace Datra.Executable

/-- The ambient datum type retains the distinction between extent and region
values. Membership, rather than the ambient type, selects each cell's carrier. -/
inductive ChainedDominionCellData (A : Type) (Object : Type) where
  | extent : A → ChainedDominionCellData A Object
  | region : A → ChainedDominionCellData A Object

namespace ChainedDominionAtlas
variable {A Object Source Target : Type}

-- ALIGN: CHAINED-DATUM-VALUE.
def cellValue : ChainedDominionCellData A Object → A
  | .extent value => value
  | .region value => value

-- ALIGN: CHAINED-EXTENT-MEMBERSHIP.
-- ALIGN: RANKED-EXTENT-MEMBERSHIP.
def extentAccepts : ChainedDominionCellData A Object → Bool
  | .extent _ => true
  | .region _ => false

-- ALIGN: CHAINED-REGION-MEMBERSHIP.
def regionAccepts (owner : Chain A) (selected : A) : ChainedDominionCellData A Object → Bool
  | .extent _ => false
  | .region value => decide (owner.position value = owner.position selected)

abbrev Extent (A Object : Type) :=
  {datum : ChainedDominionCellData A Object // extentAccepts datum = true}

abbrev Region (owner : Chain A) (selected : A) (Object : Type) :=
  {datum : ChainedDominionCellData A Object // regionAccepts owner selected datum = true}

theorem region_unique (owner : Chain A) (selected : A)
    (datum : Region owner selected Object) : datum.val = .region selected := by
  obtain ⟨datum, accepted⟩ := datum
  cases datum with
  | extent value => simp [regionAccepts] at accepted
  | region value =>
      have equal := owner.positionInjective (of_decide_eq_true accepted)
      exact congrArg ChainedDominionCellData.region equal

/-- The accepted extent has precisely the original Dominion's carrier. -/
def extentEquiv : Extent A Object ≃ A where
  toFun datum := cellValue datum.val
  invFun value := ⟨.extent value, rfl⟩
  left_inv datum := by
    obtain ⟨datum, accepted⟩ := datum
    cases datum with
    | extent value => rfl
    | region value => simp [extentAccepts] at accepted
  right_inv _ := rfl

-- ALIGN: CHAINED-EXTENT-RANK.
-- ALIGN: RANKED-EXTENT-RANK.
def extentRank (owner : Dominion A) (datum : ChainedDominionCellData A Object) : Nat :=
  owner.rank (cellValue datum)

-- ALIGN: CHAINED-EXTENT-DECODE.
-- ALIGN: RANKED-EXTENT-DECODE.
def extentUnrank (owner : Dominion A) (index : Nat) : Option (ChainedDominionCellData A Object) :=
  (owner.unrank index).map ChainedDominionCellData.extent

-- ALIGN: CHAINED-EXTENT-ROUNDTRIP.
-- ALIGN: RANKED-EXTENT-ROUNDTRIP.
theorem extentRoundTrip (owner : Dominion A) (datum : Extent A Object) :
    extentUnrank owner (extentRank owner datum.val) = some datum.val := by
  obtain ⟨datum, accepted⟩ := datum
  cases datum with
  | extent value => simp [extentUnrank, extentRank, cellValue, owner.coherence]
  | region value => simp [extentAccepts] at accepted

-- ALIGN: CHAINED-EXTENT-DOMINION.
-- ALIGN: RANKED-EXTENT-DOMINION.
def extentDominion (owner : Dominion A) : Dominion (Extent A Object) :=
  owner.reindex extentEquiv.symm

-- ALIGN: CHAINED-EXTENT-DOMINION-DECODE.
-- ALIGN: RANKED-EXTENT-DOMINION-DECODE.
theorem extentDominion_unrank (owner : Dominion A) (index : Nat) :
    ((extentDominion owner).unrank index).map (fun datum : Extent A Object => datum.val) =
      extentUnrank owner index := by
  simp [extentDominion, Dominion.reindex, extentUnrank, extentEquiv, Function.comp_def]

-- ALIGN: CHAINED-REGION-RANK.
-- ALIGN: RANKED-REGION-RANK.
def regionRank (_datum : ChainedDominionCellData A Object) : Nat := 0

-- ALIGN: CHAINED-REGION-DECODE.
def regionUnrank (_owner : Chain A) (selected : A) (index : Nat) :
    Option (ChainedDominionCellData A Object) :=
  if index = 0 then some (.region selected) else none

-- ALIGN: CHAINED-REGION-ROUNDTRIP.
theorem regionRoundTrip (owner : Chain A) (selected : A) (datum : Region owner selected Object) :
    regionUnrank owner selected (regionRank datum.val) = some datum.val := by
  simp [regionUnrank, regionRank, region_unique owner selected datum]

def regionSingleton (owner : Chain A) (selected : A) : SingletonDominion (Region owner selected Object) :=
  ⟨⟨.region selected, by simp [regionAccepts]⟩,
    fun datum => Subtype.ext (region_unique owner selected datum)⟩

-- ALIGN: CHAINED-REGION-DOMINION.
def regionDominion (owner : Chain A) (selected : A) : Dominion (Region owner selected Object) where
  rank _ := 0
  unrank index := if index = 0 then some (regionSingleton owner selected).value else none
  coherence datum := by simp [← (regionSingleton owner selected).unique datum]

-- ALIGN: CHAINED-REGION-DOMINION-DECODE.
theorem regionDominion_unrank (owner : Chain A) (selected : A) (index : Nat) :
    ((regionDominion owner selected).unrank index).map
        (fun datum : Region owner selected Object => datum.val) = regionUnrank owner selected index := by
  by_cases zero : index = 0 <;> simp [regionDominion, regionUnrank, zero, regionSingleton]

-- ALIGN: CHAINED-REGION-TO-EXTENT.
def regionToExtent (_owner : Chain A) (_selected : A) (datum : ChainedDominionCellData A Source) :
    ChainedDominionCellData A Target := .extent (cellValue datum)

-- ALIGN: CHAINED-EXTENT-TO-REGION.
def extentToRegion (owner : Chain A) (selected : A) :
    ChainedDominionCellData A Target → Option (ChainedDominionCellData A Source)
  | .extent value =>
      if owner.position value = owner.position selected then some (.region value) else none
  | .region _ => none

theorem extentToRegion_accepted (owner : Chain A) (selected : A)
    (datum : ChainedDominionCellData A Target) (result : ChainedDominionCellData A Source)
    (found : extentToRegion owner selected datum = some result) :
    regionAccepts owner selected result = true := by
  cases datum with
  | region value => simp [extentToRegion] at found
  | extent value =>
      simp only [extentToRegion] at found
      split_ifs at found with same
      · cases found
        simp [regionAccepts, same]

end ChainedDominionAtlas
end Datra.Executable
