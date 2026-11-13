import Executable.Atlas.Sequence.Folio

namespace Datra.Executable.AtlasSequence

variable {count : Nat}

theorem prefixFolio_depth (positive : 0 < count) (members : Fin count → Atlas) (n : Nat) :
    (prefixFolio positive members n).data.depth = n + 2 :=
  Folio.buildPrefix_depth _ _ _ _ _ _ n

theorem prefixPageAt_zero (positive : 0 < count) (members : Fin count → Atlas) (n : Nat) :
    (prefixFolio positive members n).data.pageAt 0 = DomanialInclusion.singletonPage :=
  Folio.buildPrefix_pageAt_zero _ _ _ _ _ _ n

-- ALIGN: SEQUENCE-PADDED-PAGE-RESOLUTION.
theorem prefixPageAt_succ (positive : 0 < count) (members : Fin count → Atlas) (n k : Nat) :
    (prefixFolio positive members n).data.pageAt (k + 1) = sequencePage members (min k n) :=
  Folio.buildPrefix_pageAt_succ _ _ _ _ _ _ n k

/-- Locate the member, then decode its local position with checked lookup.
This is the successful callback of withMemberAtPosition. -/
def resolvePosition (members : Fin count → Atlas) (n : Nat) (position : Ordinal) :
    Option (PageValue members n) :=
  (ChainSequence.locate (pageOrders members n) position).attach.map (fun found =>
    valueAtPosition members n ⟨found.val, (ChainSequence.locate_sound _ _ _ found.property).1⟩)

theorem resolvePosition_position (members : Fin count → Atlas) (n : Nat) (value : PageValue members n) :
    resolvePosition members n ((componentSum members n).position value) = some value := by
  have found := ChainSequence.locate_position (pageOrders members n)
    (componentPosition members n value).val (componentPosition members n value).property
  change ChainSequence.locate (pageOrders members n) ((componentSum members n).position value) =
    some (componentPosition members n value).val at found
  unfold resolvePosition
  rw [Option.attach_eq_some _ ⟨_, found⟩]
  change some (valueAtPosition members n (componentPosition members n value)) = _
  rw [valueAtPosition_componentPosition]

def pageLookup (members : Fin count → Atlas) (n : Nat) (position : Ordinal) :
    Option (ValidPageCell members n) :=
  (resolvePosition members n position).map (encodedPageCell members n)

-- ALIGN: SEQUENCE-PAGE-LOOKUP.
theorem pageChain_lookup (members : Fin count → Atlas) (n : Nat) (position : Ordinal) :
    (pageChain members n).lookup position = pageLookup members n position := by
  simp [pageChain, componentSum, Chain.reindex, ChainSequence.chain, pageLookup, resolvePosition,
    Option.map_map, Function.comp_def, componentPositionEquiv, pageEncodingEquiv]

-- ALIGN: SEQUENCE-PAGE-LOOKUP-BOUNDS.
theorem pageLookup_isSome (members : Fin count → Atlas) (n : Nat) (position : Ordinal) :
    (pageLookup members n position).isSome = Ordinal.ordinalLT position (ChainSequence.orderSum (pageOrders members n)) := by
  simp [pageLookup, resolvePosition, ChainSequence.locate_isSome]

def decodedPageCell (members : Fin count → Atlas) (n : Nat) : ValidPageCell members n → PageValue members n :=
  (pageEncodingEquiv members n).symm

@[simp] theorem decodedPageCell_encode (members : Fin count → Atlas) (n : Nat) (value : PageValue members n) :
    decodedPageCell members n (encodedPageCell members n value) = value :=
  (pageEncodingEquiv members n).symm_apply_apply value

theorem encode_decodedPageCell (members : Fin count → Atlas) (n : Nat) (cell : ValidPageCell members n) :
    pageEncode members n (decodedPageCell members n cell) = cell.val :=
  congrArg Subtype.val ((pageEncodingEquiv members n).apply_symm_apply cell)

-- ALIGN: SEQUENCE-COMPONENT-DECODER.
theorem resolvePosition_pagePosition (members : Fin count → Atlas) (n : Nat) (cell : ValidPageCell members n) :
    resolvePosition members n (pagePosition members n cell.val) = some (decodedPageCell members n cell) := by
  obtain ⟨value, same⟩ := cell.property
  have cellEq : encodedPageCell members n value = cell := Subtype.ext same
  rw [← cellEq, decodedPageCell_encode]
  exact (congrArg (resolvePosition members n) (pagePosition_encode members n value)).trans
    (resolvePosition_position members n value)

theorem componentPage_clamp (members : Fin count → Atlas) (index : Fin count) (limit n : Nat)
    (bound : (members index).pages.depth - 1 ≤ limit) :
    componentPage members (min n limit) index = componentPage members n index := by
  exact (members index).pages.pageAt_clamp limit n bound

theorem memberClamp_bound (members : Fin count → Atlas) (index : Fin count) :
    (members index).pages.depth - 1 ≤ sequenceDepth members - 1 :=
  Nat.sub_le_sub_right (memberDepth_bound members index) 1

def sourceAtPage (members : Fin count → Atlas) (n : Nat)
    (source : PageValue members (min n (sequenceDepth members - 1))) : SourceCell members :=
  .member source.1 (FolioData.ValidElement.ofOccurrence ⟨n,
    cast (congrArg Page.Carrier (componentPage_clamp members source.1 _ n (memberClamp_bound members source.1))) source.2⟩)

-- ALIGN: SEQUENCE-SOURCE-RESOLUTION.
def resolveOccurrence (positive : 0 < count) (members : Fin count → Atlas)
    (occurrence : (pagination positive members).pages.Occurrence) : SourceCell members :=
  match occurrence with
  | ⟨0, _⟩ => .origin
  | ⟨n + 1, value⟩ =>
    let cell : ValidPageCell members (min n (sequenceDepth members - 1)) :=
      cast (congrArg Page.Carrier (prefixPageAt_succ positive members (sequenceDepth members - 1) n)) value
    sourceAtPage members n (decodedPageCell members _ cell)

-- ALIGN: SEQUENCE-MEMBER-OBJECT.
def memberOccurrence (positive : 0 < count) (members : Fin count → Atlas) (index : Fin count)
    (source : (members index).pages.Occurrence) : (pagination positive members).pages.Occurrence :=
  let n := source.page
  let value := cast (congrArg Page.Carrier (componentPage_clamp members index _ n (memberClamp_bound members index)).symm) source.value
  let cell := encodedPageCell members (min n (sequenceDepth members - 1)) ⟨index, value⟩
  ⟨n + 1, cast (congrArg Page.Carrier (prefixPageAt_succ positive members (sequenceDepth members - 1) n).symm) cell⟩

-- ALIGN: SEQUENCE-MEMBER-RESOLVED.
theorem resolveOccurrence_member (positive : 0 < count) (members : Fin count → Atlas) (index : Fin count)
    (source : (members index).pages.Occurrence) :
    resolveOccurrence positive members (memberOccurrence positive members index source) =
      .member index (FolioData.ValidElement.ofOccurrence source) := by
  cases source with
  | mk n value =>
    simp only [memberOccurrence, resolveOccurrence, cast_cast, cast_eq, decodedPageCell_encode]
    simp only [sourceAtPage, cast_cast, cast_eq]

-- ALIGN: SEQUENCE-MEMBER-PAGE.
theorem memberOccurrence_page (positive : 0 < count) (members : Fin count → Atlas) (index : Fin count)
    (source : (members index).pages.Occurrence) :
    (memberOccurrence positive members index source).page = source.page + 1 := rfl

theorem pageOrders_clamp (members : Fin count → Atlas) (n : Nat) :
    pageOrders members (min n (sequenceDepth members - 1)) = pageOrders members n := by
  unfold pageOrders
  congr 1
  funext index
  exact congrArg (fun page : Page => page.chain.orderType)
    (componentPage_clamp members index _ n (memberClamp_bound members index))

-- ALIGN: SEQUENCE-MEMBER-POSITION.
theorem memberOccurrence_position (positive : 0 < count) (members : Fin count → Atlas) (index : Fin count)
    (source : (members index).pages.Occurrence) :
    (memberOccurrence positive members index source).toRaw.position =
      Ordinal.addOrdinals (ChainSequence.prefixOrder (pageOrders members source.page) index.val) source.toRaw.position := by
  let n := source.page
  let limit := sequenceDepth members - 1
  let hpage := prefixPageAt_succ positive members limit n
  let hsource := componentPage_clamp members index limit n (memberClamp_bound members index)
  let value := cast (congrArg Page.Carrier hsource.symm) source.value
  have first := (Page.cast_position hpage.symm (encodedPageCell members (min n limit) ⟨index, value⟩)).trans
    (pageChain_position members (min n limit) (encodedPageCell members (min n limit) ⟨index, value⟩))
  have first := first.trans (pagePosition_encode members (min n limit) ⟨index, value⟩)
  change (memberOccurrence positive members index source).toRaw.position =
    Ordinal.addOrdinals (ChainSequence.prefixOrder (pageOrders members n) index.val) source.toRaw.position
  change (memberOccurrence positive members index source).toRaw.position =
    Ordinal.addOrdinals (ChainSequence.prefixOrder (pageOrders members (min n limit)) index.val)
      ((componentPage members (min n limit) index).chain.position value) at first
  rw [Page.cast_position hsource.symm, pageOrders_clamp] at first
  exact first

def originOccurrence (positive : 0 < count) (members : Fin count → Atlas) :
    (pagination positive members).pages.Occurrence :=
  ⟨0, cast (congrArg Page.Carrier (prefixPageAt_zero positive members (sequenceDepth members - 1)).symm) ()⟩

def sourceOccurrence (positive : 0 < count) (members : Fin count → Atlas) :
    SourceCell members → (pagination positive members).pages.Occurrence
  | .origin => originOccurrence positive members
  | .member index source => memberOccurrence positive members index source.occurrence

theorem resolve_sourceOccurrence (positive : 0 < count) (members : Fin count → Atlas) (source : SourceCell members) :
    resolveOccurrence positive members (sourceOccurrence positive members source) = source := by
  cases source with
  | origin => rfl
  | member index source =>
    simp only [sourceOccurrence, resolveOccurrence_member, FolioData.ValidElement.ofOccurrence_occurrence]

theorem sourceOccurrence_resolve (positive : 0 < count) (members : Fin count → Atlas)
    (occurrence : (pagination positive members).pages.Occurrence) :
    sourceOccurrence positive members (resolveOccurrence positive members occurrence) = occurrence := by
  cases occurrence with
  | mk page value =>
    cases page with
    | zero =>
      apply FolioData.Occurrence.ext
      · rfl
      exact heq_of_eq (Page.cast_from_unique (prefixPageAt_zero positive members (sequenceDepth members - 1)).symm () (fun x => by cases x; rfl) value)
    | succ n =>
      let limit := sequenceDepth members - 1
      let hpage := prefixPageAt_succ positive members limit n
      let cell : ValidPageCell members (min n limit) := cast (congrArg Page.Carrier hpage) value
      let source := decodedPageCell members (min n limit) cell
      have same : encodedPageCell members (min n limit) source = cell :=
        Subtype.ext (encode_decodedPageCell members (min n limit) cell)
      dsimp only [resolveOccurrence, sourceAtPage, sourceOccurrence]
      rw [FolioData.ValidElement.occurrence_ofOccurrence]
      simp only [memberOccurrence, cast_cast, cast_eq]
      apply FolioData.Occurrence.ext
      · rfl
      apply heq_of_eq
      simpa only [cell, source, cast_cast, cast_eq] using congrArg (cast (congrArg Page.Carrier hpage.symm)) same

-- ALIGN: SEQUENCE-SOURCE-RESOLUTION-EQUIV.
def occurrenceEquiv (positive : 0 < count) (members : Fin count → Atlas) :
    (pagination positive members).pages.Occurrence ≃ SourceCell members where
  toFun := resolveOccurrence positive members
  invFun := sourceOccurrence positive members
  left_inv := sourceOccurrence_resolve positive members
  right_inv := resolve_sourceOccurrence positive members

end Datra.Executable.AtlasSequence
