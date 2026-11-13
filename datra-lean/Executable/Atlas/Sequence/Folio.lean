import Executable.Atlas.Sequence
import Executable.Chain.Sequence
import Executable.Atlas.DomanialInclusion
import Executable.Folio.Prefix

namespace Datra.Executable.AtlasSequence

variable {count : Nat}

def componentPage (members : Fin count → Atlas) (n : Nat) (index : Fin count) : Page :=
  (members index).pages.pageAt n

def pageOrders (members : Fin count → Atlas) (n : Nat) : List Ordinal :=
  List.ofFn (fun index => (componentPage members n index).chain.orderType)

abbrev PageValue (members : Fin count → Atlas) (n : Nat) :=
  (index : Fin count) × (componentPage members n index).Carrier

def componentPosition (members : Fin count → Atlas) (n : Nat) (value : PageValue members n) :
    ChainSequence.Position (pageOrders members n) :=
  ⟨(value.1.val, (componentPage members n value.1).chain.position value.2), by
    simpa [ChainSequence.validPosition, pageOrders, value.1.isLt] using
      (componentPage members n value.1).chain.positionBelow value.2⟩

def positionMember (members : Fin count → Atlas) (n : Nat)
    (position : ChainSequence.Position (pageOrders members n)) : Fin count :=
  ⟨position.val.1, by
    simpa [pageOrders] using ChainSequence.validPosition_index_lt position.property⟩

theorem componentPosition_below (members : Fin count → Atlas) (n : Nat)
    (position : ChainSequence.Position (pageOrders members n)) :
    Ordinal.ordinalLT position.val.2 (componentPage members n (positionMember members n position)).chain.orderType = true := by
  have bounded : position.val.1 < count := (positionMember members n position).isLt
  simpa [ChainSequence.validPosition, pageOrders, bounded, positionMember] using position.property

/-- Recover a source value with the component chain's checked lookup. -/
def valueAtPosition (members : Fin count → Atlas) (n : Nat)
    (position : ChainSequence.Position (pageOrders members n)) : PageValue members n :=
  let index := positionMember members n position
  let found := (componentPage members n index).chain.chainIndex position.val.2
  ⟨index, (found.get (by
    rw [Chain.chainIndex_isSome]
    exact componentPosition_below members n position)).object⟩

theorem valueAtPosition_componentPosition (members : Fin count → Atlas) (n : Nat)
    (value : PageValue members n) : valueAtPosition members n (componentPosition members n value) = value := by
  rcases value with ⟨index, value⟩
  simp [valueAtPosition, componentPosition, positionMember, Chain.chainIndex_position, Chain.chainIndexOf]

theorem componentPosition_valueAtPosition (members : Fin count → Atlas) (n : Nat)
    (position : ChainSequence.Position (pageOrders members n)) :
    componentPosition members n (valueAtPosition members n position) = position := by
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · let source := (componentPage members n (positionMember members n position)).chain
    have found : (source.chainIndex position.val.2).isSome = true := by
      rw [Chain.chainIndex_isSome]; exact componentPosition_below members n position
    change source.position ((source.chainIndex position.val.2).get found).object = position.val.2
    obtain ⟨value, _, same⟩ := source.positionSurjective position.val.2 (componentPosition_below members n position)
    have decoded : source.chainIndex position.val.2 = some (source.chainIndexOf value) := by
      rw [← same, Chain.chainIndex_position]
    simpa only [decoded, Option.get_some, Chain.chainIndexOf] using same

def componentPositionEquiv (members : Fin count → Atlas) (n : Nat) :
    PageValue members n ≃ ChainSequence.Position (pageOrders members n) where
  toFun := componentPosition members n
  invFun := valueAtPosition members n
  left_inv := valueAtPosition_componentPosition members n
  right_inv := componentPosition_valueAtPosition members n

def componentSum (members : Fin count → Atlas) (n : Nat) : Chain (PageValue members n) :=
  (ChainSequence.chain (pageOrders members n)).reindex (componentPositionEquiv members n)

/-- A flattened member tag and its source transport trace, exactly the
runtime page payload. -/
@[ext] structure PageCell where
  member : Nat
  trace : List Ordinal
  deriving DecidableEq

def pageEncode (members : Fin count → Atlas) (n : Nat) (value : PageValue members n) : PageCell :=
  ⟨value.1.val, (members value.1).pages.traceAt n value.2⟩

def cellCoordinates (cell : PageCell) : Nat × Ordinal :=
  (cell.member, cell.trace.headD (Ordinal.finiteOrdinal 0))

theorem cellCoordinates_encode (members : Fin count → Atlas) (n : Nat) (value : PageValue members n) :
    cellCoordinates (pageEncode members n value) = (componentPosition members n value).val := by
  cases n <;> rfl

theorem pageEncode_injective (members : Fin count → Atlas) (n : Nat) :
    Function.Injective (pageEncode members n) := by
  intro a b same
  apply (componentPositionEquiv members n).injective
  apply Subtype.ext
  simpa only [cellCoordinates_encode] using congrArg cellCoordinates same

abbrev ValidPageCell (members : Fin count → Atlas) (n : Nat) :=
  {cell : PageCell // cell ∈ Set.range (pageEncode members n)}

def encodedPageCell (members : Fin count → Atlas) (n : Nat) (value : PageValue members n) :
    ValidPageCell members n := ⟨pageEncode members n value, ⟨value, rfl⟩⟩

def pageCellPosition (members : Fin count → Atlas) (n : Nat) (cell : ValidPageCell members n) :
    ChainSequence.Position (pageOrders members n) :=
  ⟨cellCoordinates cell.val, by
    obtain ⟨value, same⟩ := cell.property
    rw [← same, cellCoordinates_encode]
    exact (componentPosition members n value).property⟩

def pageEncodingEquiv (members : Fin count → Atlas) (n : Nat) :
    PageValue members n ≃ ValidPageCell members n where
  toFun := encodedPageCell members n
  invFun cell := valueAtPosition members n (pageCellPosition members n cell)
  left_inv value := by
    dsimp only
    have same : pageCellPosition members n (encodedPageCell members n value) = componentPosition members n value :=
      Subtype.ext (cellCoordinates_encode members n value)
    rw [same, valueAtPosition_componentPosition]
  right_inv cell := by
    dsimp only
    obtain ⟨value, same⟩ := cell.property
    have cellEq : encodedPageCell members n value = cell := Subtype.ext same
    rw [← cellEq]
    have samePosition : pageCellPosition members n (encodedPageCell members n value) = componentPosition members n value :=
      Subtype.ext (cellCoordinates_encode members n value)
    rw [samePosition, valueAtPosition_componentPosition]

-- ALIGN: SEQUENCE-PAGE-CHAIN.
def pageChain (members : Fin count → Atlas) (n : Nat) : Chain (ValidPageCell members n) :=
  (componentSum members n).reindex (pageEncodingEquiv members n).symm

-- ALIGN: SEQUENCE-PAGE-CELL-POSITION.
def pagePosition (members : Fin count → Atlas) (n : Nat) (cell : PageCell) : Ordinal :=
  match cell.trace with
  | [] => Ordinal.finiteOrdinal 0
  | first :: _ => Ordinal.addOrdinals (ChainSequence.prefixOrder (pageOrders members n) cell.member) first

-- ALIGN: SEQUENCE-PAGE-TRACE-ENCODING.
theorem pagePosition_encode (members : Fin count → Atlas) (n : Nat) (value : PageValue members n) :
    pagePosition members n (pageEncode members n value) = (componentSum members n).position value := by
  cases n <;> rfl

theorem pageChain_position (members : Fin count → Atlas) (n : Nat) (cell : ValidPageCell members n) :
    (pageChain members n).position cell = pagePosition members n cell.val := by
  obtain ⟨value, same⟩ := cell.property
  have cellEq : encodedPageCell members n value = cell := Subtype.ext same
  rw [← cellEq]
  change (componentSum members n).position ((pageEncodingEquiv members n).symm
    ((pageEncodingEquiv members n) value)) = _
  rw [Equiv.symm_apply_apply]
  exact (pagePosition_encode members n value).symm

theorem componentSum_position_le_iff (members : Fin count → Atlas) (n : Nat) (a b : PageValue members n) :
    ((componentSum members n).position a).toSemantics ≤ ((componentSum members n).position b).toSemantics ↔
      a.1.val < b.1.val ∨ (a.1.val = b.1.val ∧
        ((componentPage members n a.1).chain.position a.2).toSemantics ≤
          ((componentPage members n b.1).chain.position b.2).toSemantics) :=
  ChainSequence.position_le_iff _ _ _ (componentPosition members n a).property (componentPosition members n b).property

def componentTransition (members : Fin count → Atlas) (n : Nat) :
    Consolidation (componentSum members (n + 1)) (componentSum members n) where
  map value := ⟨value.1, ((members value.1).pages.transport (n + 1) n (Nat.le_succ n)).map value.2⟩
  preimage value := ⟨value.1, ((members value.1).pages.transport (n + 1) n (Nat.le_succ n)).preimage value.2⟩
  monotone := by
    rintro ⟨i, a⟩ ⟨j, b⟩ ordered
    rw [componentSum_position_le_iff] at ordered ⊢
    rcases ordered with different | ⟨same, ordered⟩
    · exact Or.inl different
    · have equal : i = j := Fin.ext same
      subst j
      exact Or.inr ⟨rfl, ((members i).pages.transport (n + 1) n (Nat.le_succ n)).monotone a b ordered⟩
  rightInverse value := by
    rcases value with ⟨index, value⟩
    simp only [Consolidation.rightInverse]

def previousPageCell : PageCell → PageCell
  | ⟨index, _ :: next :: rest⟩ => ⟨index, next :: rest⟩
  | cell => cell

-- ALIGN: SEQUENCE-PAGE-PREVIOUS.
theorem previousPageCell_encode (members : Fin count → Atlas) (n : Nat) (value : PageValue members (n + 1)) :
    previousPageCell (pageEncode members (n + 1) value) =
      pageEncode members n ((componentTransition members n).map value) := by
  cases n <;> rfl

def nextPageCell (members : Fin count → Atlas) (n : Nat) (previous : PageCell) : PageCell :=
  match previous.trace with
  | [] => previous
  | sourcePosition :: _ =>
    if bounded : previous.member < count then
      let index : Fin count := ⟨previous.member, bounded⟩
      (((componentPage members n index).chain.chainIndex sourcePosition).map (fun source =>
        pageEncode members (n + 1) ⟨index,
          ((members index).pages.transport (n + 1) n (Nat.le_succ n)).preimage source.object⟩)).getD previous
    else previous

-- ALIGN: SEQUENCE-PAGE-NEXT.
theorem nextPageCell_encode (members : Fin count → Atlas) (n : Nat) (value : PageValue members n) :
    nextPageCell members n (pageEncode members n value) =
      pageEncode members (n + 1) ((componentTransition members n).preimage value) := by
  rcases value with ⟨index, value⟩
  cases n <;>
    simp [nextPageCell, pageEncode, FolioData.traceAt, index.isLt, componentPage,
      Chain.chainIndex_position, Chain.chainIndexOf, componentTransition]

def previousValidCell (members : Fin count → Atlas) (n : Nat) (cell : ValidPageCell members (n + 1)) :
    ValidPageCell members n :=
  ⟨previousPageCell cell.val, by
    obtain ⟨value, same⟩ := cell.property
    rw [← same, previousPageCell_encode]
    exact ⟨_, rfl⟩⟩

def nextValidCell (members : Fin count → Atlas) (n : Nat) (cell : ValidPageCell members n) :
    ValidPageCell members (n + 1) :=
  ⟨nextPageCell members n cell.val, by
    obtain ⟨value, same⟩ := cell.property
    rw [← same, nextPageCell_encode]
    exact ⟨_, rfl⟩⟩

-- ALIGN: SEQUENCE-PAGE-TRANSITION.
def pageTransition (members : Fin count → Atlas) (n : Nat) :
    Consolidation (pageChain members (n + 1)) (pageChain members n) where
  map := previousValidCell members n
  preimage := nextValidCell members n
  monotone := by
    rintro ⟨a, x, rfl⟩ ⟨b, y, rfl⟩ ordered
    rw [pageChain_position, pageChain_position] at ordered ⊢
    change (pagePosition members n (previousPageCell (pageEncode members (n + 1) x))).toSemantics ≤
      (pagePosition members n (previousPageCell (pageEncode members (n + 1) y))).toSemantics
    rw [previousPageCell_encode, previousPageCell_encode, pagePosition_encode, pagePosition_encode]
    apply (componentTransition members n).monotone
    simpa only [pagePosition_encode] using ordered
  rightInverse := by
    rintro ⟨cell, value, rfl⟩
    apply Subtype.ext
    change previousPageCell (nextPageCell members n (pageEncode members n value)) = pageEncode members n value
    rw [nextPageCell_encode, previousPageCell_encode, Consolidation.rightInverse]

def componentZeroValue (X : Atlas) : (X.pages.pageAt 0).Carrier :=
  cast (congrArg Page.Carrier (X.pages.pageAt_fin ⟨0, X.pages.depth_positive⟩).symm)
    (FolioData.ValidElement.originFiniteValue X.pages)

def firstPageCell (positive : 0 < count) (members : Fin count → Atlas) : ValidPageCell members 0 :=
  encodedPageCell members 0 ⟨⟨0, positive⟩, componentZeroValue (members ⟨0, positive⟩)⟩

-- ALIGN: SEQUENCE-COLLAPSE-ORIGIN.
def collapseToOrigin (positive : 0 < count) (members : Fin count → Atlas) :
    Consolidation (pageChain members 0) DomanialInclusion.singletonChain where
  map _ := ()
  preimage _ := firstPageCell positive members
  monotone _ _ _ := le_rfl
  rightInverse value := by cases value; rfl

def sequencePage (members : Fin count → Atlas) (n : Nat) : Page := ⟨ValidPageCell members n, pageChain members n⟩

-- ALIGN: SEQUENCE-FOLIO-PREFIX.
def prefixFolio (positive : 0 < count) (members : Fin count → Atlas) (n : Nat) :
    Folio DomanialInclusion.singletonPage (sequencePage members n) :=
  Folio.buildPrefix DomanialInclusion.singletonPage () (fun value => by cases value; rfl)
    (sequencePage members) (collapseToOrigin positive members) (pageTransition members) n

theorem prefixFolio_length (positive : 0 < count) (members : Fin count → Atlas) (n : Nat) :
    (prefixFolio positive members n).data.length = n + 2 :=
  Folio.buildPrefix_length _ _ _ _ _ _ n

def sequenceDepth (members : Fin count → Atlas) : Nat :=
  (List.ofFn (fun index => (members index).pages.length)).foldl max 0

theorem le_foldl_max (values : List Nat) (initial : Nat) (value : Nat) (member : value ∈ values) :
    value ≤ values.foldl max initial := by
  have le_initial (values : List Nat) (initial : Nat) : initial ≤ values.foldl max initial := by
    induction values generalizing initial with
    | nil => exact Nat.le_refl _
    | cons first rest ih => exact (Nat.le_max_left initial first).trans (ih _)
  induction values generalizing initial with
  | nil => simp at member
  | cons first rest ih =>
    rcases List.mem_cons.mp member with rfl | member
    · exact (Nat.le_max_right initial value).trans (le_initial _ _)
    · exact ih _ member

theorem memberDepth_bound (members : Fin count → Atlas) (index : Fin count) :
    (members index).pages.depth ≤ sequenceDepth members := by
  rw [← (members index).pages.length_eq_depth (members index).pagination.folio.valid]
  exact le_foldl_max _ _ _ (List.mem_ofFn.mpr ⟨index, rfl⟩)

theorem sequenceDepth_positive (positive : 0 < count) (members : Fin count → Atlas) :
    0 < sequenceDepth members :=
  ((members ⟨0, positive⟩).pages.depth_positive).trans_le (memberDepth_bound members ⟨0, positive⟩)

-- ALIGN: SEQUENCE-FOLIO.
def folio (positive : 0 < count) (members : Fin count → Atlas) :
    Folio DomanialInclusion.singletonPage (sequencePage members (sequenceDepth members - 1)) :=
  prefixFolio positive members (sequenceDepth members - 1)

-- ALIGN: SEQUENCE-FOLIO-LENGTH.
theorem folio_length (positive : 0 < count) (members : Fin count → Atlas) :
    (folio positive members).data.length = sequenceDepth members + 1 := by
  rw [folio, prefixFolio_length]
  have := sequenceDepth_positive positive members
  omega

def pagination (positive : 0 < count) (members : Fin count → Atlas) : Pagination :=
  ⟨DomanialInclusion.singletonPage, sequencePage members (sequenceDepth members - 1), folio positive members⟩

end Datra.Executable.AtlasSequence
