import Executable.Atlas.Merge.Folio

namespace Datra.Executable.AtlasMerge
open CategoryTheory

inductive Side where
  | left
  | right
  deriving DecidableEq

/-- The runtime tags retain the member's origin rank and the phantom merge
cell. Membership is an additional invariant, not a property of arbitrary tags. -/
inductive Datum (_cell : PageElementCell) where
  | left (valueRank : Nat)
  | right (valueRank : Nat)
  deriving DecidableEq

-- ALIGN: MERGE-DATUM-SIDE.
def datumSide {cell : PageElementCell} : Datum cell → Side
  | .left _ => .left
  | .right _ => .right

-- ALIGN: MERGE-DATUM-RANK.
def datumRank {cell : PageElementCell} : Datum cell → Nat
  | .left n => 2 * n
  | .right n => 2 * n + 1

def retag {source target : PageElementCell} : Datum source → Datum target
  | .left n => .left n
  | .right n => .right n

def decode (cell : PageElementCell) (n : Nat) : Datum cell :=
  if n % 2 = 0 then .left (n / 2) else .right (n / 2)

-- ALIGN: MERGE-DATUM-DECODE.
@[simp] theorem decode_rank {cell : PageElementCell} (datum : Datum cell) :
    decode cell (datumRank datum) = datum := by
  cases datum <;> simp [decode, datumRank, Nat.add_div]

-- ALIGN: MERGE-DATUM-ENCODE.
@[simp] theorem rank_decode (cell : PageElementCell) (n : Nat) :
    datumRank (decode cell n) = n := by
  unfold decode
  split <;> simp only [datumRank] <;> omega

theorem datumRank_injective (cell : PageElementCell) : Function.Injective (@datumRank cell) := by
  intro a b same
  have := congrArg (decode cell) same
  simpa using this

-- ALIGN: MERGE-DATUM-RETAG-RANK.
@[simp] theorem retag_rank {source target : PageElementCell} (datum : Datum source) :
    datumRank (retag (target := target) datum) = datumRank datum := by cases datum <;> rfl

@[simp] theorem retag_retag {a b c : PageElementCell} (datum : Datum a) :
    retag (source := b) (target := c) (retag datum) = retag datum := by cases datum <;> rfl

@[simp] theorem retag_self {cell : PageElementCell} (datum : Datum cell) : retag datum = datum := by
  cases datum <;> rfl

-- ALIGN: MERGE-DATUM-RETAG-ROUNDTRIP.
theorem retag_roundtrip {source middle : PageElementCell} (datum : Datum source) :
    retag (retag (target := middle) datum) = datum := by
  rw [retag_retag, retag_self]

/-- The three successful branches of the runtime merge cell resolver. The
folio bridge must establish which branch a valid merge occurrence selects. -/
inductive SourceCell (X Y : Atlas) where
  | origin
  | left (source : X.Element)
  | right (source : Y.Element)

def contains {X Y : Atlas} (source : SourceCell X Y) {cell : PageElementCell} : Datum cell → Bool :=
  match source with
  | .origin => fun
      | .left n => X.extentContainsRank n
      | .right n => Y.extentContainsRank n
  | .left x => fun
      | .left n => X.cellContainsRank x n
      | .right _ => false
  | .right y => fun
      | .left _ => false
      | .right n => Y.cellContainsRank y n

@[simp] theorem contains_retag {X Y : Atlas} (source : SourceCell X Y) {a b : PageElementCell}
    (datum : Datum a) : contains source (retag (target := b) datum) = contains source datum := by
  cases source <;> cases datum <;> rfl

/-- Decode the parity rank and retain it exactly when the supplied cell
membership predicate accepts it. -/
-- ALIGN: MERGE-DATUM-LOOKUP.
def lookupDatum {cell : PageElementCell} (accepts : Datum cell → Bool) (n : Nat) : Option (Datum cell) :=
  if accepts (decode cell n) then some (decode cell n) else none

-- ALIGN: MERGE-DATUM-LOOKUP-ROUNDTRIP.
theorem lookupDatum_roundtrip {cell : PageElementCell} (accepts : Datum cell → Bool)
    (datum : Datum cell) (valid : accepts datum = true) :
    lookupDatum accepts (datumRank datum) = some datum := by
  simp [lookupDatum, valid]

-- ALIGN: MERGE-DATUM-LOOKUP-SOUND.
theorem lookupDatum_sound {cell : PageElementCell} (accepts : Datum cell → Bool)
    (n : Nat) (datum : Datum cell) (found : lookupDatum accepts n = some datum) :
    accepts datum = true ∧ datumRank datum = n := by
  unfold lookupDatum at found
  split at found
  · rename_i valid
    cases Option.some.inj found
    exact ⟨valid, rank_decode cell n⟩
  · contradiction

/-- Invalid resolved occurrences have no data; valid occurrences use exactly
the selected component's membership test. -/
def datumAt {X Y : Atlas} (source : Option (SourceCell X Y)) (cell : PageElementCell)
    (n : Nat) : Option (Datum cell) :=
  match source with
  | none => none
  | some source => lookupDatum (contains source) n

-- ALIGN: MERGE-DOMINION-ROUNDTRIP.
theorem datumAt_roundtrip {X Y : Atlas} (source : SourceCell X Y) {cell : PageElementCell}
    (datum : Datum cell) (valid : contains source datum = true) :
    datumAt (some source) cell (datumRank datum) = some datum := by
  exact lookupDatum_roundtrip (contains source) datum valid

-- ALIGN: MERGE-UNRANK-SOUND.
theorem datumAt_sound {X Y : Atlas} (source : SourceCell X Y) (cell : PageElementCell)
    (n : Nat) (datum : Datum cell) (found : datumAt (some source) cell n = some datum) :
    contains source datum = true ∧ datumRank datum = n := by
  exact lookupDatum_sound (contains source) n datum found

abbrev CertifiedDatum {X Y : Atlas} (source : SourceCell X Y) (cell : PageElementCell) :=
  {datum : Datum cell // contains source datum = true}

def dominionAt {X Y : Atlas} (source : SourceCell X Y) (cell : PageElementCell) :
    Dominion (CertifiedDatum source cell) where
  rank datum := datumRank datum.val
  unrank n := (datumAt (some source) cell n).attach.map
    (fun datum => ⟨datum.val, (datumAt_sound source cell n datum.val datum.property).1⟩)
  coherence datum := by
    rw [Option.attach_eq_some _ ⟨datum.val, datumAt_roundtrip source datum.val datum.property⟩]
    rfl

/-- Component arrows either remain in that component or enter the fresh
origin. This relation records the data action's required transport evidence. -/
inductive Transport {X Y : Atlas} : SourceCell X Y → SourceCell X Y → Prop
  | origin : Transport .origin .origin
  | leftOrigin (source : X.Element) : Transport (.left source) .origin
  | rightOrigin (source : Y.Element) : Transport (.right source) .origin
  | left {source target : X.Element} (arrow : source ⟶ target) : Transport (.left source) (.left target)
  | right {source target : Y.Element} (arrow : source ⟶ target) : Transport (.right source) (.right target)

theorem contains_transport {X Y : Atlas} {source target : SourceCell X Y}
    (arrow : Transport source target) {cell : PageElementCell} (datum : Datum cell)
    (valid : contains source datum = true) : contains target datum = true := by
  cases arrow with
  | origin => exact valid
  | leftOrigin x =>
    cases datum with
    | left n =>
      obtain ⟨value, same⟩ := (X.cellContainsRank_iff x n).mp valid
      exact (X.extentContainsRank_iff n).mpr ⟨X.originImage x value, same⟩
    | right n => contradiction
  | rightOrigin y =>
    cases datum with
    | left n => contradiction
    | right n =>
      obtain ⟨value, same⟩ := (Y.cellContainsRank_iff y n).mp valid
      exact (Y.extentContainsRank_iff n).mpr ⟨Y.originImage y value, same⟩
  | left f =>
    cases datum with
    | left n =>
      obtain ⟨value, same⟩ := (X.cellContainsRank_iff _ n).mp valid
      apply (X.cellContainsRank_iff _ n).mpr
      exact ⟨(X.data.action.normalizedMap f).map value,
        (congrArg (X.dataAt (FolioData.ValidElement.originElement X.pages)).rank
          (X.originImage_map f value)).trans same⟩
    | right n => contradiction
  | right f =>
    cases datum with
    | left n => contradiction
    | right n =>
      obtain ⟨value, same⟩ := (Y.cellContainsRank_iff _ n).mp valid
      apply (Y.cellContainsRank_iff _ n).mpr
      exact ⟨(Y.data.action.normalizedMap f).map value,
        (congrArg (Y.dataAt (FolioData.ValidElement.originElement Y.pages)).rank
          (Y.originImage_map f value)).trans same⟩

-- ALIGN: MERGE-DATA-INSERTION.
def dataMap {X Y : Atlas} {source target : SourceCell X Y} (arrow : Transport source target)
    (sourceCell targetCell : PageElementCell) :
    DomanialInsertion (CertifiedDatum source sourceCell) (CertifiedDatum target targetCell) where
  map datum := ⟨retag datum.val, by simpa using contains_transport arrow datum.val datum.property⟩
  preimage datum :=
    if valid : contains source (retag (target := sourceCell) datum.val) = true then
      some ⟨retag datum.val, valid⟩
    else none
  leftInverse datum := by simp [datum.property]


abbrev ExtentData (X : Atlas) := X.cellData (FolioData.ValidElement.originElement X.pages).val.cell

def extentDominion (X : Atlas) : Dominion (ExtentData X) :=
  X.dataAt (FolioData.ValidElement.originElement X.pages)

def rootDomain (X Y : Atlas) : Datra.Semantics.DomIns :=
  Datra.Semantics.domSum ⟨(extentDominion X).toSemantics⟩ ⟨(extentDominion Y).toSemantics⟩

def sourceDomain {X Y : Atlas} : SourceCell X Y → Datra.Semantics.DomIns
  | .origin => rootDomain X Y
  | .left x => ⟨(X.dataAt x).toSemantics⟩
  | .right y => ⟨(Y.dataAt y).toSemantics⟩

/-- The three root maps in the written merge construction: identity at the
fresh origin, or transport into a tagged component of its extent. -/
def rootMap {X Y : Atlas} (source : SourceCell X Y) : sourceDomain source ⟶ rootDomain X Y :=
  match source with
  | .origin => Function.Embedding.refl _
  | .left x =>
      { toFun := fun value => Sum.inl (X.originImage x value)
        inj' := fun _ _ same => (X.data.action.normalizedMap x.toOrigin).injective (Sum.inl.inj same) }
  | .right y =>
      { toFun := fun value => Sum.inr (Y.originImage y value)
        inj' := fun _ _ same => (Y.data.action.normalizedMap y.toOrigin).injective (Sum.inr.inj same) }

def rootEncode {X Y : Atlas} (cell : PageElementCell) : rootDomain X Y → Datum cell
  | .inl value => .left ((extentDominion X).rank value)
  | .inr value => .right ((extentDominion Y).rank value)

theorem rootEncode_injective (X Y : Atlas) (cell : PageElementCell) :
    Function.Injective (@rootEncode X Y cell) := by
  intro a b same
  cases a with
  | inl a =>
    cases b with
    | inl b => exact congrArg Sum.inl ((extentDominion X).rank_injective (Datum.left.inj same))
    | inr b => contradiction
  | inr a =>
    cases b with
    | inl b => contradiction
    | inr b => exact congrArg Sum.inr ((extentDominion Y).rank_injective (Datum.right.inj same))

theorem rootEncode_rank {X Y : Atlas} (cell : PageElementCell) (value : rootDomain X Y) :
    datumRank (rootEncode cell value) = (rootDomain X Y).toDom.rank value := by cases value <;> rfl

/-- Membership of a tagged rank is precisely membership in the root map's
image. This uses the checked rank test, not mere success of a partial inverse. -/
-- ALIGN: MERGE-CELL-MEMBERSHIP.
theorem contains_iff_root_image {X Y : Atlas} (source : SourceCell X Y) {cell : PageElementCell}
    (datum : Datum cell) :
    contains source datum = true ↔ ∃ value : sourceDomain source, rootEncode cell (rootMap source value) = datum := by
  cases source <;> cases datum <;>
    simp [contains, sourceDomain, rootMap, rootDomain, rootEncode, extentDominion,
      Datra.Semantics.domSum, Atlas.extentContainsRank_iff, Atlas.cellContainsRank_iff,
      Atlas.originImageRank] <;> rfl

def imageToDatum {X Y : Atlas} (source : SourceCell X Y) (cell : PageElementCell) :
    Datra.Semantics.imageDom (rootMap source) → CertifiedDatum source cell := fun value =>
  ⟨rootEncode cell value.val, (contains_iff_root_image source _).mpr (by
    obtain ⟨datum, same⟩ := value.property
    exact ⟨datum, congrArg (rootEncode cell) same⟩)⟩

theorem imageToDatum_bijective {X Y : Atlas} (source : SourceCell X Y) (cell : PageElementCell) :
    Function.Bijective (imageToDatum source cell) := by
  constructor
  · intro a b same
    apply Subtype.ext
    exact rootEncode_injective X Y cell (congrArg Subtype.val same)
  · intro datum
    obtain ⟨value, same⟩ := (contains_iff_root_image source datum.val).mp datum.property
    exact ⟨⟨rootMap source value, ⟨value, rfl⟩⟩, Subtype.ext same⟩

noncomputable def encodingEquiv {X Y : Atlas} (source : SourceCell X Y) (cell : PageElementCell) :
    Datra.Semantics.imageDom (rootMap source) ≃ CertifiedDatum source cell :=
  Equiv.ofBijective (imageToDatum source cell) (imageToDatum_bijective source cell)

/-- The proof-only semantic equivalence forgets the raw phantom tag and
identifies the accepted ranks with the image Dominion in the written merge. -/
-- ALIGN: MERGE-DOMINION-INTERPRETATION.
noncomputable def interpretationEquiv {X Y : Atlas} (source : SourceCell X Y) (cell : PageElementCell) :
    CertifiedDatum source cell ≃ Datra.Semantics.imageDom (rootMap source) :=
  (encodingEquiv source cell).symm

theorem interpretation_encode {X Y : Atlas} (source : SourceCell X Y) (cell : PageElementCell)
    (datum : CertifiedDatum source cell) :
    rootEncode cell (interpretationEquiv source cell datum).val = datum.val :=
  congrArg Subtype.val ((encodingEquiv source cell).apply_symm_apply datum)

-- ALIGN: MERGE-DOMINION-RANK.
theorem interpretation_rank {X Y : Atlas} (source : SourceCell X Y) (cell : PageElementCell)
    (datum : CertifiedDatum source cell) :
    (Datra.Semantics.imageDom (rootMap source)).toDom.rank (interpretationEquiv source cell datum) =
      (dominionAt source cell).rank datum := by
  change (rootDomain X Y).toDom.rank (interpretationEquiv source cell datum).val = datumRank datum.val
  rw [← rootEncode_rank cell, interpretation_encode]

theorem rootRange_mono {X Y : Atlas} {source target : SourceCell X Y}
    (arrow : Transport source target) : Set.range (rootMap source) ⊆ Set.range (rootMap target) := by
  intro value found
  let cell := (FolioData.ValidElement.originElement X.pages).val.cell
  have valid := (imageToDatum source cell ⟨value, found⟩).property
  have mapped := contains_transport arrow (rootEncode cell value) valid
  obtain ⟨datum, same⟩ := (contains_iff_root_image target _).mp mapped
  exact ⟨datum, rootEncode_injective X Y cell same⟩

def semanticMap {X Y : Atlas} {source target : SourceCell X Y} (arrow : Transport source target) :
    Datra.Semantics.imageDom (rootMap source) ⟶ Datra.Semantics.imageDom (rootMap target) :=
  Datra.Semantics.imageDom.map _ _ (rootRange_mono arrow)

-- ALIGN: MERGE-DATA-INTERPRETATION.
theorem dataMap_interpretation {X Y : Atlas} {source target : SourceCell X Y}
    (arrow : Transport source target) (sourceCell targetCell : PageElementCell)
    (datum : CertifiedDatum source sourceCell) :
    interpretationEquiv target targetCell ((dataMap arrow sourceCell targetCell).map datum) =
      semanticMap arrow (interpretationEquiv source sourceCell datum) := by
  apply Subtype.ext
  apply (rootDomain X Y).toDom.rank.injective
  change (Datra.Semantics.imageDom (rootMap target)).toDom.rank
      (interpretationEquiv target targetCell ((dataMap arrow sourceCell targetCell).map datum)) =
    (Datra.Semantics.imageDom (rootMap source)).toDom.rank
      (interpretationEquiv source sourceCell datum)
  rw [interpretation_rank, interpretation_rank]
  exact retag_rank datum.val


def Transport.identity {X Y : Atlas} (source : SourceCell X Y) : Transport source source :=
  match source with
  | .origin => .origin
  | .left x => .left (𝟙 x)
  | .right y => .right (𝟙 y)

def Transport.comp {X Y : Atlas} {source middle target : SourceCell X Y}
    (first : Transport source middle) (second : Transport middle target) : Transport source target := by
  cases first with
  | origin => exact second
  | leftOrigin source => cases second; exact .leftOrigin source
  | rightOrigin source => cases second; exact .rightOrigin source
  | left first =>
    cases second with
    | leftOrigin => exact .leftOrigin _
    | left second => exact .left (first ≫ second)
  | right first =>
    cases second with
    | rightOrigin => exact .rightOrigin _
    | right second => exact .right (first ≫ second)

-- ALIGN: MERGE-DATA-IDENTITY.
theorem dataMap_identity {X Y : Atlas} (source : SourceCell X Y) (cell : PageElementCell) :
    dataMap (Transport.identity source) cell cell = DomanialInsertion.identity _ := by
  apply DomanialInsertion.ext
  · funext datum; apply Subtype.ext; exact retag_self datum.val
  · funext datum
    simp [dataMap, DomanialInsertion.identity, datum.property]

-- ALIGN: MERGE-DATA-COMPOSITION.
theorem dataMap_comp {X Y : Atlas} {source middle target : SourceCell X Y}
    (first : Transport source middle) (second : Transport middle target) (a b c : PageElementCell) :
    dataMap (first.comp second) a c = DomanialInsertion.comp (dataMap first a b) (dataMap second b c) := by
  apply DomanialInsertion.ext
  · funext datum; apply Subtype.ext; exact (retag_retag datum.val).symm
  · funext datum
    by_cases hs : contains source datum.val = true
    · have hm := contains_transport first datum.val hs
      simp [dataMap, DomanialInsertion.comp, hs, hm]
    · by_cases hm : contains middle datum.val = true <;>
        simp [dataMap, DomanialInsertion.comp, hs, hm]

-- ALIGN: MERGE-LEFT-COMPONENT.
def leftComponent (X Y : Atlas) (source : X.Element) (cell : PageElementCell) :
    DomanialInsertion (X.cellData source.val.cell) (CertifiedDatum (SourceCell.left (Y := Y) source) cell) where
  map value := ⟨.left (X.originImageRank source value), (X.cellContainsRank_iff _ _).mpr ⟨value, rfl⟩⟩
  preimage datum := match datum.val with
    | .left n => (X.cellOriginRankInsertion source).preimage n
    | .right _ => none
  leftInverse value := (X.cellOriginRankInsertion source).leftInverse value

-- ALIGN: MERGE-RIGHT-COMPONENT.
def rightComponent (X Y : Atlas) (source : Y.Element) (cell : PageElementCell) :
    DomanialInsertion (Y.cellData source.val.cell) (CertifiedDatum (SourceCell.right (X := X) source) cell) where
  map value := ⟨.right (Y.originImageRank source value), (Y.cellContainsRank_iff _ _).mpr ⟨value, rfl⟩⟩
  preimage datum := match datum.val with
    | .left _ => none
    | .right n => (Y.cellOriginRankInsertion source).preimage n
  leftInverse value := (Y.cellOriginRankInsertion source).leftInverse value

-- ALIGN: MERGE-LEFT-NATURALITY.
theorem leftComponent_naturality (X Y : Atlas) {source target : X.Element} (arrow : source ⟶ target)
    (a b : PageElementCell) (value : X.cellData source.val.cell) :
    (dataMap (Transport.left (Y := Y) arrow) a b).map ((leftComponent X Y source a).map value) =
      (leftComponent X Y target b).map ((X.data.action.normalizedMap arrow).map value) := by
  apply Subtype.ext
  apply congrArg Datum.left
  exact (congrArg (extentDominion X).rank (X.originImage_map arrow value)).symm

-- ALIGN: MERGE-RIGHT-NATURALITY.
theorem rightComponent_naturality (X Y : Atlas) {source target : Y.Element} (arrow : source ⟶ target)
    (a b : PageElementCell) (value : Y.cellData source.val.cell) :
    (dataMap (Transport.right (X := X) arrow) a b).map ((rightComponent X Y source a).map value) =
      (rightComponent X Y target b).map ((Y.data.action.normalizedMap arrow).map value) := by
  apply Subtype.ext
  apply congrArg Datum.right
  exact (congrArg (extentDominion Y).rank (Y.originImage_map arrow value)).symm

theorem rootDomain_interpretation (X Y : Atlas) :
    rootDomain X Y = Datra.Semantics.domSum (Datra.Semantics.extent X.toSemantics)
      (Datra.Semantics.extent Y.toSemantics) := by
  change Datra.Semantics.domSum X.extent.toSemantics Y.extent.toSemantics = _
  rw [X.extent_interpretation, Y.extent_interpretation]

end Datra.Executable.AtlasMerge
