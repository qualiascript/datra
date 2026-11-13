import Executable.Atlas.Derived
import Executable.Atlas.DomanialInclusion
import Executable.Folio.Prefix

namespace Datra.Executable.AtlasMerge

/-- The stored merge page payload is a tagged full transport trace. -/
inductive PageCell where
  | left (trace : List Ordinal)
  | right (trace : List Ordinal)
  deriving DecidableEq

def componentPage (X : Atlas) (n : Nat) : Page := X.pages.pageAt n

def pageEncode (X Y : Atlas) (n : Nat) :
    Sum (componentPage X n).Carrier (componentPage Y n).Carrier → PageCell
  | .inl value => .left (X.pages.traceAt n value)
  | .inr value => .right (Y.pages.traceAt n value)

def cellPosition : PageCell → Ordinal
  | .left trace => trace.headD (Ordinal.finiteOrdinal 0)
  | .right trace => trace.headD (Ordinal.finiteOrdinal 0)

def pagePosition (X _Y : Atlas) (n : Nat) : PageCell → Ordinal
  | .left trace => cellPosition (.left trace)
  | .right trace => Ordinal.addOrdinals (componentPage X n).chain.orderType (cellPosition (.right trace))

theorem cellPosition_encode_left (X : Atlas) (n : Nat) (value : (componentPage X n).Carrier) :
    cellPosition (.left (X.pages.traceAt n value)) = (componentPage X n).chain.position value := by
  cases n <;> rfl

theorem cellPosition_encode_right (Y : Atlas) (n : Nat) (value : (componentPage Y n).Carrier) :
    cellPosition (.right (Y.pages.traceAt n value)) = (componentPage Y n).chain.position value := by
  cases n <;> rfl

def componentSum (X Y : Atlas) (n : Nat) :=
  Chain.sumChains (componentPage X n).chain (componentPage Y n).chain

-- ALIGN: MERGE-PAGE-TRACE-ENCODING.
theorem pagePosition_encode (X Y : Atlas) (n : Nat)
    (value : Sum (componentPage X n).Carrier (componentPage Y n).Carrier) :
    pagePosition X Y n (pageEncode X Y n value) = (componentSum X Y n).position value := by
  cases value with
  | inl value => exact cellPosition_encode_left X n value
  | inr value =>
      exact congrArg (Ordinal.addOrdinals (componentPage X n).chain.orderType)
        (cellPosition_encode_right Y n value)

theorem pageEncode_injective (X Y : Atlas) (n : Nat) : Function.Injective (pageEncode X Y n) := by
  intro a b same
  apply (componentSum X Y n).positionInjective
  simpa only [pagePosition_encode] using congrArg (pagePosition X Y n) same

abbrev ValidPageCell (X Y : Atlas) (n : Nat) := {cell : PageCell // cell ∈ Set.range (pageEncode X Y n)}

def encodedPageCell (X Y : Atlas) (n : Nat)
    (value : Sum (componentPage X n).Carrier (componentPage Y n).Carrier) : ValidPageCell X Y n :=
  ⟨pageEncode X Y n value, ⟨value, rfl⟩⟩

def pageLookup (X Y : Atlas) (n : Nat) (position : Ordinal) : Option (ValidPageCell X Y n) :=
  ((componentSum X Y n).chainIndex position).map
    (fun index => encodedPageCell X Y n index.object)

/-- The executable page keeps the runtime trace payload and the invariant
that it arose from lookup in one of the two component pages. -/
-- ALIGN: MERGE-PAGE-CHAIN.
def pageChain (X Y : Atlas) (n : Nat) : Chain (ValidPageCell X Y n) where
  orderType := (componentSum X Y n).orderType
  position cell := pagePosition X Y n cell.val
  lookup := pageLookup X Y n
  positionBelow cell := by
    obtain ⟨value, same⟩ := cell.property
    rw [← same, pagePosition_encode]
    exact (componentSum X Y n).positionBelow value
  positionInjective := by
    rintro ⟨a, x, rfl⟩ ⟨b, y, rfl⟩ same
    apply Subtype.ext
    apply congrArg (pageEncode X Y n)
    apply (componentSum X Y n).positionInjective
    simpa only [pagePosition_encode] using same
  positionSurjective position below := by
    obtain ⟨value, _, same⟩ := (componentSum X Y n).positionSurjective position below
    refine ⟨encodedPageCell X Y n value, ?_, (pagePosition_encode X Y n value).trans same⟩
    rw [← same]
    simp [pageLookup, Chain.chainIndex_position, Chain.chainIndexOf]

noncomputable def pageEncodingEquiv (X Y : Atlas) (n : Nat) :
    Sum (componentPage X n).Carrier (componentPage Y n).Carrier ≃ ValidPageCell X Y n :=
  Equiv.ofBijective (encodedPageCell X Y n) ⟨
    fun _ _ same => pageEncode_injective X Y n (congrArg Subtype.val same),
    fun cell => by obtain ⟨value, same⟩ := cell.property; exact ⟨value, Subtype.ext same⟩⟩

noncomputable def pageOrderIso (X Y : Atlas) (n : Nat) :
    (pageChain X Y n).toSemantics.Obj ≃o (componentSum X Y n).toSemantics.Obj where
  toEquiv := (pageEncodingEquiv X Y n).symm
  map_rel_iff' := by
    intro a b
    have h (cell : ValidPageCell X Y n) :
        (componentSum X Y n).position ((pageEncodingEquiv X Y n).symm cell) =
          pagePosition X Y n cell.val := by
      rw [← pagePosition_encode]
      exact congrArg (pagePosition X Y n)
        (congrArg Subtype.val ((pageEncodingEquiv X Y n).apply_symm_apply cell))
    change ((componentSum X Y n).position _).toSemantics ≤
        ((componentSum X Y n).position _).toSemantics ↔
      (pagePosition X Y n a.val).toSemantics ≤ (pagePosition X Y n b.val).toSemantics
    exact iff_of_eq (congrArg₂ (fun x y : Ordinal => x.toSemantics ≤ y.toSemantics) (h a) (h b))


def previousPageCell : PageCell → PageCell
  | .left (_ :: next :: rest) => .left (next :: rest)
  | .right (_ :: next :: rest) => .right (next :: rest)
  | cell => cell

def componentTransition (X Y : Atlas) (n : Nat) :
    Consolidation (componentSum X Y (n + 1)) (componentSum X Y n) :=
  Consolidation.sum (X.pages.transport (n + 1) n (Nat.le_succ n))
    (Y.pages.transport (n + 1) n (Nat.le_succ n))

-- ALIGN: MERGE-PAGE-PREVIOUS.
theorem previousPageCell_encode (X Y : Atlas) (n : Nat)
    (value : Sum (componentPage X (n + 1)).Carrier (componentPage Y (n + 1)).Carrier) :
    previousPageCell (pageEncode X Y (n + 1) value) =
      pageEncode X Y n ((componentTransition X Y n).map value) := by
  cases value <;> cases n <;> rfl

def componentPreimageTrace (X : Atlas) (n : Nat) (position : Ordinal) : Option (List Ordinal) :=
  ((componentPage X n).chain.chainIndex position).map (fun index =>
    X.pages.traceAt (n + 1) ((X.pages.transport (n + 1) n (Nat.le_succ n)).preimage index.object))

def nextPageCell (X Y : Atlas) (n : Nat) (previous : PageCell) : PageCell :=
  match previous with
  | .left (position :: _) => ((componentPreimageTrace X n position).map PageCell.left).getD previous
  | .right (position :: _) => ((componentPreimageTrace Y n position).map PageCell.right).getD previous
  | _ => previous

-- ALIGN: MERGE-PAGE-NEXT.
theorem nextPageCell_encode (X Y : Atlas) (n : Nat)
    (value : Sum (componentPage X n).Carrier (componentPage Y n).Carrier) :
    nextPageCell X Y n (pageEncode X Y n value) =
      pageEncode X Y (n + 1) ((componentTransition X Y n).preimage value) := by
  cases value <;> cases n <;>
    simp [pageEncode, FolioData.traceAt, nextPageCell, componentPreimageTrace,
      componentPage, Chain.chainIndex_position, Chain.chainIndexOf,
      componentTransition, Consolidation.sum]

def previousValidCell (X Y : Atlas) (n : Nat) (cell : ValidPageCell X Y (n + 1)) : ValidPageCell X Y n :=
  ⟨previousPageCell cell.val, by
    obtain ⟨value, same⟩ := cell.property
    rw [← same, previousPageCell_encode]
    exact ⟨_, rfl⟩⟩

def nextValidCell (X Y : Atlas) (n : Nat) (cell : ValidPageCell X Y n) : ValidPageCell X Y (n + 1) :=
  ⟨nextPageCell X Y n cell.val, by
    obtain ⟨value, same⟩ := cell.property
    rw [← same, nextPageCell_encode]
    exact ⟨_, rfl⟩⟩

-- ALIGN: MERGE-PAGE-TRANSITION.
def pageTransition (X Y : Atlas) (n : Nat) :
    Consolidation (pageChain X Y (n + 1)) (pageChain X Y n) where
  map := previousValidCell X Y n
  preimage := nextValidCell X Y n
  monotone := by
    rintro ⟨a, x, rfl⟩ ⟨b, y, rfl⟩ ordered
    change (pagePosition X Y n (previousPageCell (pageEncode X Y (n + 1) x))).toSemantics ≤
      (pagePosition X Y n (previousPageCell (pageEncode X Y (n + 1) y))).toSemantics
    rw [previousPageCell_encode, previousPageCell_encode, pagePosition_encode, pagePosition_encode]
    apply (componentTransition X Y n).monotone
    simpa only [pageChain, pagePosition_encode] using ordered
  rightInverse := by
    rintro ⟨cell, value, rfl⟩
    apply Subtype.ext
    change previousPageCell (nextPageCell X Y n (pageEncode X Y n value)) = pageEncode X Y n value
    rw [nextPageCell_encode, previousPageCell_encode, Consolidation.rightInverse]


def componentZeroValue (X : Atlas) : (componentPage X 0).Carrier :=
  cast (congrArg Page.Carrier (X.pages.pageAt_fin ⟨0, X.pages.depth_positive⟩).symm)
    (FolioData.ValidElement.originFiniteValue X.pages)

def firstPageCell (X Y : Atlas) : ValidPageCell X Y 0 :=
  encodedPageCell X Y 0 (.inl (componentZeroValue X))

-- ALIGN: MERGE-COLLAPSE-ORIGIN.
def collapseToOrigin (X Y : Atlas) : Consolidation (pageChain X Y 0) DomanialInclusion.singletonChain where
  map _ := ()
  preimage _ := firstPageCell X Y
  monotone _ _ _ := le_rfl
  rightInverse value := by cases value; rfl

def mergePage (X Y : Atlas) (n : Nat) : Page := ⟨ValidPageCell X Y n, pageChain X Y n⟩

/-- Append the component pages in increasing full-spine order, retaining the
fresh singleton origin. This is the structural form of appendRemainingPages. -/
-- ALIGN: MERGE-FOLIO-PREFIX.
def prefixFolio (X Y : Atlas) (n : Nat) : Folio DomanialInclusion.singletonPage (mergePage X Y n) :=
  Folio.buildPrefix DomanialInclusion.singletonPage () (fun value => by cases value; rfl)
    (mergePage X Y) (collapseToOrigin X Y) (pageTransition X Y) n

theorem prefixFolio_length (X Y : Atlas) (n : Nat) : (prefixFolio X Y n).data.length = n + 2 := by
  exact Folio.buildPrefix_length _ _ _ _ _ _ n

def mergeDepth (X Y : Atlas) : Nat := max X.pages.length Y.pages.length

-- ALIGN: MERGE-FOLIO.
def folio (X Y : Atlas) :
    Folio DomanialInclusion.singletonPage (mergePage X Y (mergeDepth X Y - 1)) :=
  prefixFolio X Y (mergeDepth X Y - 1)

-- ALIGN: MERGE-FOLIO-LENGTH.
theorem folio_length (X Y : Atlas) : (folio X Y).data.length = max X.pages.length Y.pages.length + 1 := by
  rw [folio, prefixFolio_length]
  have positive : 0 < X.pages.length := by
    rw [X.pages.length_eq_depth X.pagination.folio.valid]
    exact X.pages.depth_positive
  unfold mergeDepth
  omega

def pagination (X Y : Atlas) : Pagination :=
  ⟨DomanialInclusion.singletonPage, mergePage X Y (mergeDepth X Y - 1), folio X Y⟩


-- ALIGN: MERGE-PAGE-LOOKUP-BOUNDS.
theorem pageLookup_isSome (X Y : Atlas) (n : Nat) (position : Ordinal) :
    (pageLookup X Y n position).isSome = Ordinal.ordinalLT position (componentSum X Y n).orderType := by
  simp [pageLookup, Chain.chainIndex_isSome]

theorem pageTransition_encode (X Y : Atlas) (n : Nat)
    (value : Sum (componentPage X (n + 1)).Carrier (componentPage Y (n + 1)).Carrier) :
    (pageTransition X Y n).map (encodedPageCell X Y (n + 1) value) =
      encodedPageCell X Y n ((componentTransition X Y n).map value) :=
  Subtype.ext (previousPageCell_encode X Y n value)

-- ALIGN: MERGE-PAGE-PREIMAGE.
theorem pageTransition_preimage_encode (X Y : Atlas) (n : Nat)
    (value : Sum (componentPage X n).Carrier (componentPage Y n).Carrier) :
    (pageTransition X Y n).preimage (encodedPageCell X Y n value) =
      encodedPageCell X Y (n + 1) ((componentTransition X Y n).preimage value) :=
  Subtype.ext (nextPageCell_encode X Y n value)

@[simp] theorem pageOrderIso_encode (X Y : Atlas) (n : Nat)
    (value : Sum (componentPage X n).Carrier (componentPage Y n).Carrier) :
    pageOrderIso X Y n (encodedPageCell X Y n value) = value :=
  (pageEncodingEquiv X Y n).symm_apply_apply value

noncomputable def pageSumOrderIso (X Y : Atlas) (n : Nat) :
    (pageChain X Y n).toSemantics.Obj ≃o
      (Datra.Semantics.Chain.sum (componentPage X n).chain.toSemantics
        (componentPage Y n).chain.toSemantics).Obj :=
  (pageOrderIso X Y n).trans (Chain.sumOrderIso (componentPage X n).chain (componentPage Y n).chain)

-- ALIGN: MERGE-PAGE-TRANSITION-INTERPRETATION.
theorem pageTransition_interpretation (X Y : Atlas) (n : Nat)
    (value : Sum (componentPage X (n + 1)).Carrier (componentPage Y (n + 1)).Carrier) :
    pageSumOrderIso X Y n ((pageTransition X Y n).map (encodedPageCell X Y (n + 1) value)) =
      (Datra.Semantics.ConHom.sum
        (X.pages.transport (n + 1) n (Nat.le_succ n)).toSemantics
        (Y.pages.transport (n + 1) n (Nat.le_succ n)).toSemantics)
        (pageSumOrderIso X Y (n + 1) (encodedPageCell X Y (n + 1) value)) := by
  rw [pageTransition_encode]
  change Chain.sumOrderIso _ _ (pageOrderIso X Y n (encodedPageCell X Y n _)) =
    Datra.Semantics.ConHom.sum _ _ (Chain.sumOrderIso _ _
      (pageOrderIso X Y (n + 1) (encodedPageCell X Y (n + 1) value)))
  rw [pageOrderIso_encode, pageOrderIso_encode]
  exact Consolidation.sum_interpretation _ _ value


theorem componentPage_interpretation (X : Atlas) (n : Nat) :
    (componentPage X n).chain.toSemantics =
      (X.toSemantics.Fo.core.obj (X.toSemantics.Fo.paddedIndex n)).unop := rfl

-- ALIGN: MERGE-PAGE-ORDER-INTERPRETATION.
noncomputable def bouquetPageOrderIso (X Y : Atlas)
    (n : Fin (Datra.Semantics.bouquetDepth X.toSemantics.Fo Y.toSemantics.Fo)) :
    (pageChain X Y n.val).toSemantics.Obj ≃o
      (Datra.Semantics.bouquetChain X.toSemantics.Fo Y.toSemantics.Fo n.succ).Obj :=
  pageSumOrderIso X Y n.val

-- ALIGN: MERGE-FOLIO-LENGTH-INTERPRETATION.
theorem folio_length_interpretation (X Y : Atlas) :
    (folio X Y).data.toSemantics.length = Datra.Semantics.bouquetLength X.toSemantics.Fo Y.toSemantics.Fo := by
  rw [(folio X Y).data.toSemantics_length (folio X Y).valid, folio_length]
  change max X.pages.length Y.pages.length + 1 = max X.pages.depth Y.pages.depth + 1
  rw [X.pages.length_eq_depth X.pagination.folio.valid, Y.pages.length_eq_depth Y.pagination.folio.valid]

end Datra.Executable.AtlasMerge
