import Executable.Atlas.Derived

namespace Datra.Executable.AtlasSequence
open CategoryTheory

/-- A raw member tag and origin rank. Validity bounds the member index and
restricts the rank to the selected cell's image in its member's extent. -/
@[ext] structure Datum (_cell : PageElementCell) where
  member : Nat
  originRank : Nat
  deriving DecidableEq

-- ALIGN: SEQUENCE-DATUM-MEMBER.
def datumMember {cell : PageElementCell} (datum : Datum cell) : Nat := datum.member

-- ALIGN: SEQUENCE-DATUM-ORIGIN-RANK.
def datumOriginRank {cell : PageElementCell} (datum : Datum cell) : Nat := datum.originRank

-- ALIGN: SEQUENCE-DATUM-RANK.
def datumRank {cell : PageElementCell} (count : Nat) (datum : Datum cell) : Nat :=
  count * datum.originRank + datum.member

def decode (cell : PageElementCell) (count n : Nat) : Datum cell := ⟨n % count, n / count⟩

-- ALIGN: SEQUENCE-DATUM-ENCODE.
theorem rank_decode (cell : PageElementCell) (count n : Nat) (positive : 0 < count) :
    (decode cell count n).member < count ∧ datumRank count (decode cell count n) = n := by
  exact ⟨Nat.mod_lt _ positive, Nat.div_add_mod n count⟩

-- ALIGN: SEQUENCE-DATUM-DECODE.
@[simp] theorem decode_rank {cell : PageElementCell} (count : Nat) (datum : Datum cell)
    (bounded : datum.member < count) : decode cell count (datumRank count datum) = datum := by
  have positive : 0 < count := Nat.zero_lt_of_lt bounded
  cases datum
  simp_all [decode, datumRank, Nat.mul_add_div, Nat.div_eq_of_lt, Nat.mod_eq_of_lt]

-- ALIGN: SEQUENCE-DATUM-LOOKUP.
def lookupDatum {cell : PageElementCell} (count : Nat) (accepts : Datum cell → Bool)
    (n : Nat) : Option (Datum cell) :=
  if accepts (decode cell count n) then some (decode cell count n) else none

-- ALIGN: SEQUENCE-DATUM-LOOKUP-ROUNDTRIP.
theorem lookupDatum_roundtrip {cell : PageElementCell} (count : Nat) (accepts : Datum cell → Bool)
    (datum : Datum cell) (bounded : datum.member < count) (valid : accepts datum = true) :
    lookupDatum count accepts (datumRank count datum) = some datum := by
  simp [lookupDatum, decode_rank count datum bounded, valid]

-- ALIGN: SEQUENCE-DATUM-LOOKUP-SOUND.
theorem lookupDatum_sound {cell : PageElementCell} (count : Nat) (positive : 0 < count)
    (accepts : Datum cell → Bool) (n : Nat) (datum : Datum cell)
    (found : lookupDatum count accepts n = some datum) :
    accepts datum = true ∧ datum.member < count ∧ datumRank count datum = n := by
  unfold lookupDatum at found
  split at found
  · rename_i valid
    cases Option.some.inj found
    exact ⟨valid, rank_decode cell count n positive⟩
  · contradiction

abbrev AcceptedDatum {cell : PageElementCell} (count : Nat) (accepts : Datum cell → Bool) :=
  {datum : Datum cell // datum.member < count ∧ accepts datum = true}

-- ALIGN: SEQUENCE-ACCEPTED-DOMINION.
def lookupDominion {cell : PageElementCell} (count : Nat) (positive : 0 < count)
    (accepts : Datum cell → Bool) : Dominion (AcceptedDatum count accepts) where
  rank datum := datumRank count datum.val
  unrank n := (lookupDatum count accepts n).attach.map (fun datum =>
    let sound := lookupDatum_sound count positive accepts n datum.val datum.property
    ⟨datum.val, sound.2.1, sound.1⟩)
  coherence datum := by
    rw [Option.attach_eq_some _ ⟨datum.val,
      lookupDatum_roundtrip count accepts datum.val datum.property.1 datum.property.2⟩]
    rfl

-- ALIGN: SEQUENCE-DATUM-RETAG.
def retag {source target : PageElementCell} (datum : Datum source) : Datum target :=
  ⟨datum.member, datum.originRank⟩

@[simp] theorem retag_member {source target : PageElementCell} (datum : Datum source) :
    (retag (target := target) datum).member = datum.member := rfl

@[simp] theorem retag_rank {source target : PageElementCell} (count : Nat) (datum : Datum source) :
    datumRank count (retag (target := target) datum) = datumRank count datum := rfl

@[simp] theorem retag_retag {a b c : PageElementCell} (datum : Datum a) :
    retag (source := b) (target := c) (retag datum) = retag datum := rfl

@[simp] theorem retag_self {cell : PageElementCell} (datum : Datum cell) : retag datum = datum := rfl

-- ALIGN: SEQUENCE-DATUM-RETAG-ROUNDTRIP.
theorem retag_roundtrip {source middle : PageElementCell} (datum : Datum source) :
    retag (retag (target := middle) datum) = datum := rfl

/-- Retagging is independent of the number of members. Its insertion law
requires cell membership; the radix bound is needed separately for unranking. -/
abbrev CellDatum {cell : PageElementCell} (accepts : Datum cell → Bool) :=
  {datum : Datum cell // accepts datum = true}

-- ALIGN: SEQUENCE-DATA-PREIMAGE.
def preimageDatum {source target : PageElementCell} (accepts : Datum source → Bool)
    (datum : Datum target) : Option (Datum source) :=
  if accepts (retag datum) then some (retag datum) else none

-- ALIGN: SEQUENCE-DATA-PREIMAGE-ROUNDTRIP.
theorem preimageDatum_roundtrip {source target : PageElementCell} (accepts : Datum source → Bool)
    (datum : Datum source) (valid : accepts datum = true) :
    preimageDatum accepts (retag (target := target) datum) = some datum := by
  simp [preimageDatum, valid]

-- ALIGN: SEQUENCE-DATA-MEMBERSHIP-MAP.
def mapDatum {source target : PageElementCell}
    (sourceContains : Datum source → Bool) (targetContains : Datum target → Bool)
    (preserves : ∀ datum, sourceContains datum = true → targetContains (retag datum) = true)
    (datum : CellDatum sourceContains) : CellDatum targetContains :=
  ⟨retag datum.val, preserves datum.val datum.property⟩

-- ALIGN: SEQUENCE-ACCEPTED-INSERTION.
def acceptedInsertion {source target : PageElementCell}
    (sourceContains : Datum source → Bool) (targetContains : Datum target → Bool)
    (preserves : ∀ datum, sourceContains datum = true → targetContains (retag datum) = true) :
    DomanialInsertion (CellDatum sourceContains) (CellDatum targetContains) where
  map := mapDatum sourceContains targetContains preserves
  preimage datum :=
    if valid : sourceContains (retag (target := source) datum.val) = true then
      some ⟨retag datum.val, valid⟩
    else none
  leftInverse datum := by simp [mapDatum, datum.property]

/-- Successful branches of the runtime source-cell resolver. An actual
sequence page resolver must produce these from its full-spine occurrence. -/
inductive SourceCell {count : Nat} (members : Fin count → Atlas) where
  | origin
  | member (index : Fin count) (source : (members index).Element)

-- ALIGN: SEQUENCE-CELL-MEMBERSHIP.
def contains {count : Nat} {members : Fin count → Atlas} (source : SourceCell members)
    {cell : PageElementCell} (datum : Datum cell) : Bool :=
  match source with
  | .origin =>
    if bounded : datum.member < count then
      (members ⟨datum.member, bounded⟩).extentContainsRank datum.originRank
    else false
  | .member index occurrence =>
    datum.member == index.val && (members index).cellContainsRank occurrence datum.originRank

@[simp] theorem contains_retag {count : Nat} {members : Fin count → Atlas}
    (source : SourceCell members) {a b : PageElementCell} (datum : Datum a) :
    contains source (retag (target := b) datum) = contains source datum := rfl

theorem contains_bounded {count : Nat} {members : Fin count → Atlas}
    (source : SourceCell members) {cell : PageElementCell} (datum : Datum cell)
    (valid : contains source datum = true) : datum.member < count := by
  cases source with
  | origin =>
    simp only [contains] at valid
    split at valid
    · assumption
    · contradiction
  | member index occurrence =>
    have same : datum.member = index.val := (Bool.and_eq_true_iff.mp valid).1 |> beq_iff_eq.mp
    exact same ▸ index.isLt

abbrev CertifiedDatum {count : Nat} {members : Fin count → Atlas}
    (source : SourceCell members) (cell : PageElementCell) := CellDatum (contains source : Datum cell → Bool)

-- ALIGN: SEQUENCE-DOMINION-ROUNDTRIP.
def dominionAt {count : Nat} (positive : 0 < count) {members : Fin count → Atlas}
    (source : SourceCell members) (cell : PageElementCell) : Dominion (CertifiedDatum source cell) where
  rank datum := datumRank count datum.val
  unrank n := (lookupDatum count (contains source) n).attach.map (fun datum =>
    ⟨datum.val, (lookupDatum_sound count positive (contains source) n datum.val datum.property).1⟩)
  coherence datum := by
    rw [Option.attach_eq_some _ ⟨datum.val, lookupDatum_roundtrip count (contains source) datum.val
      (contains_bounded source datum.val datum.property) datum.property⟩]
    rfl

inductive Transport {count : Nat} {members : Fin count → Atlas} :
    SourceCell members → SourceCell members → Prop
  | origin : Transport .origin .origin
  | toOrigin (index : Fin count) (source : (members index).Element) :
      Transport (.member index source) .origin
  | member (index : Fin count) {source target : (members index).Element} (arrow : source ⟶ target) :
      Transport (.member index source) (.member index target)

theorem contains_transport {count : Nat} {members : Fin count → Atlas}
    {source target : SourceCell members} (arrow : Transport source target)
    {cell : PageElementCell} (datum : Datum cell) (valid : contains source datum = true) :
    contains target datum = true := by
  cases arrow with
  | origin => exact valid
  | toOrigin index occurrence =>
    obtain ⟨same, valid⟩ := Bool.and_eq_true_iff.mp valid
    have same : datum.member = index.val := beq_iff_eq.mp same
    have bounded : datum.member < count := same ▸ index.isLt
    have eqIndex : (⟨datum.member, bounded⟩ : Fin count) = index := Fin.ext same
    simp only [contains, dif_pos bounded, eqIndex]
    exact (members index).cellContainsRank_inExtent occurrence datum.originRank valid
  | member index f =>
    obtain ⟨same, valid⟩ := Bool.and_eq_true_iff.mp valid
    apply Bool.and_eq_true_iff.mpr
    refine ⟨same, ?_⟩
    exact (members index).cellContainsRank_preserved f datum.originRank valid

-- ALIGN: SEQUENCE-DATA-INSERTION.
def dataMap {count : Nat} {members : Fin count → Atlas} {source target : SourceCell members}
    (arrow : Transport source target) (sourceCell targetCell : PageElementCell) :
    DomanialInsertion (CertifiedDatum source sourceCell) (CertifiedDatum target targetCell) :=
  acceptedInsertion (contains source) (contains target)
    (fun datum valid => by simpa using contains_transport arrow datum valid)

-- ALIGN: SEQUENCE-MEMBER-COMPONENT.
def memberComponent {count : Nat} (members : Fin count → Atlas) (index : Fin count)
    (source : (members index).Element) (cell : PageElementCell) :
    DomanialInsertion ((members index).cellData source.val.cell)
      (CertifiedDatum (SourceCell.member index source) cell) where
  map value := ⟨⟨index.val, (members index).originImageRank source value⟩,
    Bool.and_eq_true_iff.mpr ⟨beq_self_eq_true _, ((members index).cellContainsRank_iff _ _).mpr ⟨value, rfl⟩⟩⟩
  preimage datum :=
    if datum.val.member == index.val then
      ((members index).cellOriginRankInsertion source).preimage datum.val.originRank
    else none
  leftInverse value := by
    simp only [beq_self_eq_true, ↓reduceIte]
    exact ((members index).cellOriginRankInsertion source).leftInverse value

-- ALIGN: SEQUENCE-MEMBER-NATURALITY.
theorem memberComponent_naturality {count : Nat} (members : Fin count → Atlas) (index : Fin count)
    {source target : (members index).Element} (arrow : source ⟶ target)
    (a b : PageElementCell) (value : (members index).cellData source.val.cell) :
    (dataMap (Transport.member index arrow) a b).map ((memberComponent members index source a).map value) =
      (memberComponent members index target b).map (((members index).data.action.normalizedMap arrow).map value) := by
  apply Subtype.ext
  apply congrArg (Datum.mk index.val)
  exact (congrArg ((members index).dataAt (FolioData.ValidElement.originElement (members index).pages)).rank
    ((members index).originImage_map arrow value)).symm

def Transport.identity {count : Nat} {members : Fin count → Atlas} (source : SourceCell members) :
    Transport source source :=
  match source with
  | .origin => .origin
  | .member index source => .member index (𝟙 source)

def Transport.comp {count : Nat} {members : Fin count → Atlas} {a b c : SourceCell members}
    (first : Transport a b) (second : Transport b c) : Transport a c := by
  cases first with
  | origin => exact second
  | toOrigin index source => cases second; exact .toOrigin index source
  | member index first =>
    cases second with
    | toOrigin => exact .toOrigin index _
    | member _ second => exact .member index (first ≫ second)

-- ALIGN: SEQUENCE-DATA-IDENTITY.
theorem dataMap_identity {count : Nat} {members : Fin count → Atlas}
    (source : SourceCell members) (cell : PageElementCell) :
    dataMap (Transport.identity source) cell cell = DomanialInsertion.identity _ := by
  apply DomanialInsertion.ext
  · rfl
  · funext datum
    simp [dataMap, acceptedInsertion, DomanialInsertion.identity, datum.property]

-- ALIGN: SEQUENCE-DATA-COMPOSITION.
theorem dataMap_comp {count : Nat} {members : Fin count → Atlas} {source middle target : SourceCell members}
    (first : Transport source middle) (second : Transport middle target) (a b c : PageElementCell) :
    dataMap (first.comp second) a c = DomanialInsertion.comp (dataMap first a b) (dataMap second b c) := by
  apply DomanialInsertion.ext
  · rfl
  · funext datum
    by_cases hs : contains source datum.val = true
    · have hm := contains_transport first datum.val hs
      simp [dataMap, acceptedInsertion, DomanialInsertion.comp, hs, hm]
    · by_cases hm : contains middle datum.val = true <;>
        simp [dataMap, acceptedInsertion, DomanialInsertion.comp, hs, hm]

/-- The finite tagged sum of the member extents. Its rank is the exact
runtime radix encoding, rather than a nested binary merge's parity encoding. -/
def rootDomain {count : Nat} (members : Fin count → Atlas) : Datra.Semantics.DomIns :=
  Datra.Semantics.domFiniteSum (fun i => members i |>.extent.toSemantics)

def sourceDomain {count : Nat} {members : Fin count → Atlas} : SourceCell members → Datra.Semantics.DomIns
  | .origin => rootDomain members
  | .member index source => ⟨((members index).dataAt source).toSemantics⟩

def rootMap {count : Nat} {members : Fin count → Atlas} (source : SourceCell members) :
    sourceDomain source ⟶ rootDomain members :=
  match source with
  | .origin => Function.Embedding.refl _
  | .member index source =>
    { toFun := fun datum => ⟨index, (members index).originImage source datum⟩
      inj' := fun _ _ same => ((members index).data.action.normalizedMap source.toOrigin).injective
        (eq_of_heq (Sigma.mk.inj same).2) }

def rootEncode {count : Nat} {members : Fin count → Atlas} (cell : PageElementCell)
    (value : rootDomain members) : Datum cell :=
  ⟨value.1.val, (members value.1).extent.dominion.rank value.2⟩

theorem rootEncode_rank {count : Nat} {members : Fin count → Atlas} (cell : PageElementCell)
    (value : rootDomain members) :
    datumRank count (rootEncode cell value) = (rootDomain members).toDom.rank value := rfl

theorem rootEncode_injective {count : Nat} (members : Fin count → Atlas) (cell : PageElementCell) :
    Function.Injective (@rootEncode count members cell) := by
  intro a b same
  apply (rootDomain members).toDom.rank.injective
  exact congrArg (datumRank count) same

-- ALIGN: SEQUENCE-CELL-ROOT-IMAGE.
theorem contains_iff_root_image {count : Nat} {members : Fin count → Atlas}
    (source : SourceCell members) {cell : PageElementCell} (datum : Datum cell) :
    contains source datum = true ↔
      ∃ value : sourceDomain source, rootEncode cell (rootMap source value) = datum := by
  cases source with
  | origin =>
    constructor
    · intro valid
      have bounded := contains_bounded (SourceCell.origin (members := members)) datum valid
      simp only [contains, dif_pos bounded] at valid
      obtain ⟨value, rank⟩ := ((members ⟨datum.member, bounded⟩).extentContainsRank_iff _).mp valid
      refine ⟨⟨⟨datum.member, bounded⟩, value⟩, ?_⟩
      exact Datum.ext rfl rank
    · rintro ⟨⟨index, value⟩, rfl⟩
      change (if h : index.val < count then (members ⟨index.val, h⟩).extentContainsRank
        ((members index).extent.dominion.rank value) else false) = true
      rw [dif_pos index.isLt]
      exact ((members index).extentContainsRank_iff _).mpr ⟨value, rfl⟩
  | member index source =>
    constructor
    · intro valid
      obtain ⟨same, valid⟩ := Bool.and_eq_true_iff.mp valid
      obtain ⟨value, rank⟩ := ((members index).cellContainsRank_iff _ _).mp valid
      exact ⟨value, Datum.ext (beq_iff_eq.mp same).symm rank⟩
    · rintro ⟨value, rfl⟩
      exact Bool.and_eq_true_iff.mpr ⟨beq_self_eq_true _,
        ((members index).cellContainsRank_iff _ _).mpr ⟨value, rfl⟩⟩

def imageToDatum {count : Nat} {members : Fin count → Atlas}
    (source : SourceCell members) (cell : PageElementCell) :
    Datra.Semantics.imageDom (rootMap source) → CertifiedDatum source cell := fun value =>
  ⟨rootEncode cell value.val, (contains_iff_root_image source _).mpr (by
    obtain ⟨datum, same⟩ := value.property
    exact ⟨datum, congrArg (rootEncode cell) same⟩)⟩

theorem imageToDatum_bijective {count : Nat} {members : Fin count → Atlas}
    (source : SourceCell members) (cell : PageElementCell) : Function.Bijective (imageToDatum source cell) := by
  constructor
  · intro a b same
    exact Subtype.ext (rootEncode_injective members cell (congrArg Subtype.val same))
  · intro datum
    obtain ⟨value, same⟩ := (contains_iff_root_image source datum.val).mp datum.property
    exact ⟨⟨rootMap source value, ⟨value, rfl⟩⟩, Subtype.ext same⟩

noncomputable def encodingEquiv {count : Nat} {members : Fin count → Atlas}
    (source : SourceCell members) (cell : PageElementCell) :
    Datra.Semantics.imageDom (rootMap source) ≃ CertifiedDatum source cell :=
  Equiv.ofBijective (imageToDatum source cell) (imageToDatum_bijective source cell)

-- ALIGN: SEQUENCE-DOMINION-INTERPRETATION.
noncomputable def interpretationEquiv {count : Nat} {members : Fin count → Atlas}
    (source : SourceCell members) (cell : PageElementCell) :
    CertifiedDatum source cell ≃ Datra.Semantics.imageDom (rootMap source) :=
  (encodingEquiv source cell).symm

theorem interpretation_encode {count : Nat} {members : Fin count → Atlas}
    (source : SourceCell members) (cell : PageElementCell) (datum : CertifiedDatum source cell) :
    rootEncode cell (interpretationEquiv source cell datum).val = datum.val :=
  congrArg Subtype.val ((encodingEquiv source cell).apply_symm_apply datum)

-- ALIGN: SEQUENCE-DOMINION-RANK.
theorem interpretation_rank {count : Nat} (positive : 0 < count) {members : Fin count → Atlas}
    (source : SourceCell members) (cell : PageElementCell) (datum : CertifiedDatum source cell) :
    (Datra.Semantics.imageDom (rootMap source)).toDom.rank (interpretationEquiv source cell datum) =
      (dominionAt positive source cell).rank datum := by
  change (rootDomain members).toDom.rank (interpretationEquiv source cell datum).val = datumRank count datum.val
  rw [← rootEncode_rank cell, interpretation_encode]

theorem rootRange_mono {count : Nat} {members : Fin count → Atlas}
    {source target : SourceCell members} (arrow : Transport source target) :
    Set.range (rootMap source) ⊆ Set.range (rootMap target) := by
  intro value found
  let cell := (members value.1).extent.element.val.cell
  have valid := (imageToDatum source cell ⟨value, found⟩).property
  have mapped := contains_transport arrow (rootEncode cell value) valid
  obtain ⟨datum, same⟩ := (contains_iff_root_image target _).mp mapped
  exact ⟨datum, rootEncode_injective members cell same⟩

def semanticMap {count : Nat} {members : Fin count → Atlas}
    {source target : SourceCell members} (arrow : Transport source target) :
    Datra.Semantics.imageDom (rootMap source) ⟶ Datra.Semantics.imageDom (rootMap target) :=
  Datra.Semantics.imageDom.map _ _ (rootRange_mono arrow)

-- ALIGN: SEQUENCE-DATA-INTERPRETATION.
theorem dataMap_interpretation {count : Nat} {members : Fin count → Atlas}
    {source target : SourceCell members} (arrow : Transport source target)
    (a b : PageElementCell) (datum : CertifiedDatum source a) :
    interpretationEquiv target b ((dataMap arrow a b).map datum) =
      semanticMap arrow (interpretationEquiv source a datum) := by
  apply Subtype.ext
  apply rootEncode_injective members b
  have same := interpretation_encode source a datum
  have mapped := interpretation_encode target b ((dataMap arrow a b).map datum)
  change rootEncode b (interpretationEquiv target b ((dataMap arrow a b).map datum)).val =
    rootEncode b (interpretationEquiv source a datum).val
  rw [mapped]
  exact (congrArg (retag (target := b)) same).symm

end Datra.Executable.AtlasSequence
