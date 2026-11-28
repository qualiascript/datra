import Executable.Atlas.ChainedDominionPresentation

namespace Datra.Executable.ChainedDominionAtlas
open CategoryTheory

universe u
variable {A Owner : Type}

/-- The four runtime fields, with a predicate relating the retained inputs to
the actual allocation. The occurrence scope is the stored folio's value index. -/
structure ChainedDominionAtlasData (A : Type) (Raw : Type u)
    (owns : A → Chain A → Dominion A → Raw → Prop) where
  storedFirst : A
  storedChain : Chain A
  storedDominion : Dominion A
  storedAtlas : Raw
  owned : owns storedFirst storedChain storedDominion storedAtlas

/-- The presentation's owning folio and entire action are retained. Equality
also retains membership, the cell Dominions, and both insertion callbacks;
the stored law proofs are propositionally irrelevant. -/
def OwnsChainedAllocation (first : A) (chain : Chain A) (dominion : Dominion A)
    (allocation : AtlasAllocation Owner) : Prop :=
  ∃ (root : Chain Unit) (pages : Folio ⟨Unit, root⟩ ⟨A, chain⟩)
    (twoPages : pages.data.length = 2),
    allocation.atlasDescription =
      chainedDominionPresentation (Pagination.fromPageElements pages) twoPages first chain rfl dominion

abbrev RetainedAtlas (Owner A : Type) :=
  ChainedDominionAtlasData A (AtlasAllocation Owner) OwnsChainedAllocation

-- ALIGN: CHAINED-OWNER-FIRST.
def chainedDominionFirst (owner : RetainedAtlas Owner A) : A := owner.storedFirst

-- ALIGN: CHAINED-OWNER-CHAIN.
def chainedDominionChain (owner : RetainedAtlas Owner A) : Chain A := owner.storedChain

-- ALIGN: CHAINED-OWNER-DOMINION.
def chainedDominionValueDominion (owner : RetainedAtlas Owner A) : Dominion A := owner.storedDominion

-- ALIGN: CHAINED-OWNER-ATLAS.
def chainedDominionAtlas (owner : RetainedAtlas Owner A) : AtlasAllocation Owner := owner.storedAtlas

-- ALIGN: CHAINED-OWNER-CONTRACT.
theorem chainedDominionAtlas_contract (owner : RetainedAtlas Owner A) :
    OwnsChainedAllocation (chainedDominionFirst owner) (chainedDominionChain owner)
      (chainedDominionValueDominion owner) (chainedDominionAtlas owner) := owner.owned

theorem chainedDominionAtlas_length (owner : RetainedAtlas Owner A) :
    (chainedDominionAtlas owner).atlasDescription.pagination.pages.length = 2 := by
  obtain ⟨root, pages, twoPages, same⟩ := owner.owned
  change owner.storedAtlas.atlasDescription.pagination.pages.length = 2
  rw [same]
  exact twoPages

theorem chainedDominionAtlas_final (owner : RetainedAtlas Owner A) :
    (chainedDominionAtlas owner).atlasDescription.pagination.final = ⟨A, chainedDominionChain owner⟩ := by
  obtain ⟨root, pages, twoPages, same⟩ := owner.owned
  change owner.storedAtlas.atlasDescription.pagination.final = _
  rw [same]
  rfl

/-- Allocation erases the static datum-family index into its presentation.
The owning certificate recovers that exact family for public observations. -/
theorem chainedDominionAtlas_cellData (owner : RetainedAtlas Owner A) :
    (chainedDominionAtlas owner).atlasDescription.cellData =
      (fun cell => ChainedDominionCellData A cell.Carrier) := by
  obtain ⟨root, pages, twoPages, same⟩ := owner.owned
  change owner.storedAtlas.atlasDescription.cellData = _
  rw [same]
  rfl

-- ALIGN: CHAINED-OWNER-MEMBERSHIP.
theorem chainedDominionMembership (owner : RetainedAtlas Owner A)
    (occurrence : PageElement (chainedDominionAtlas owner).atlasDescription.pagination.pages)
    (datum : (chainedDominionAtlas owner).atlasDescription.cellData occurrence.cell) :
    (chainedDominionAtlas owner).acceptsDatum occurrence datum =
      chainedDominionAccepts (chainedDominionFirst owner) (chainedDominionChain owner) occurrence
        (cast (congrFun (chainedDominionAtlas_cellData owner) occurrence.cell) datum) := by
  rcases owner with ⟨first, chain, dominion, ⟨presentation⟩, owned⟩
  obtain ⟨root, pages, twoPages, same⟩ := owned
  change presentation = _ at same
  subst presentation
  change chainedDominionAccepts first chain
      (occurrence.normalize (pages.data.depth - 1) pages.data.depth) datum =
    chainedDominionAccepts first chain occurrence datum
  exact congrArg (fun cell => cellAccepts chain cell datum)
    (ownedCellNormalization pages.data pages.valid twoPages first chain occurrence)

/-- The allocated action is the checked cell map on the original endpoints.
Normalization changes neither endpoint's selected extent or region. -/
-- ALIGN: CHAINED-OWNER-TRANSPORT.
theorem chainedDominionTransport (owner : RetainedAtlas Owner A) :
    let allocation := chainedDominionAtlas owner
    letI := allocation.atlasDescription.ownership
    ∀ {source target : allocation.atlasDescription.pagination.pages.ValidElement}
      (arrow : source ⟶ target)
      (datum : allocation.atlasDescription.action.membership.Carrier source.normalize.val),
      cast (congrFun (chainedDominionAtlas_cellData owner) target.val.cell)
        ((allocation.atlasDescription.action.normalizedMap arrow).map datum).val =
      cellMap (chainedDominionChain owner)
        (chainedDominionCell (chainedDominionFirst owner) (chainedDominionChain owner) source.val)
        (chainedDominionCell (chainedDominionFirst owner) (chainedDominionChain owner) target.val)
        (cast (congrFun (chainedDominionAtlas_cellData owner) source.val.cell) datum.val) := by
  rcases owner with ⟨first, chain, dominion, ⟨presentation⟩, owned⟩
  obtain ⟨root, pages, twoPages, same⟩ := owned
  change presentation = _ at same
  subst presentation
  dsimp only
  intro source target arrow datum
  change cellMap chain
    (chainedDominionCell first chain (source.val.normalize (pages.data.depth - 1) pages.data.depth))
    (chainedDominionCell first chain (target.val.normalize (pages.data.depth - 1) pages.data.depth)) datum.val =
    cellMap chain (chainedDominionCell first chain source.val)
      (chainedDominionCell first chain target.val) datum.val
  rw [ownedCellNormalization pages.data pages.valid twoPages first chain source.val,
    ownedCellNormalization pages.data pages.valid twoPages first chain target.val]

-- ALIGN: CHAINED-OWNER-RETAIN.
def retainChainedDominionAtlas (first : A) (chain : Chain A) (dominion : Dominion A)
    (allocation : AtlasAllocation Owner) (checked : OwnsChainedAllocation first chain dominion allocation) :
    RetainedAtlas Owner A := ⟨first, chain, dominion, allocation, checked⟩

theorem retainChainedDominionAtlas_fields (first : A) (chain : Chain A) (dominion : Dominion A)
    (allocation : AtlasAllocation Owner) (checked : OwnsChainedAllocation first chain dominion allocation) :
    let retained := retainChainedDominionAtlas first chain dominion allocation checked
    chainedDominionFirst retained = first ∧ chainedDominionChain retained = chain ∧
      chainedDominionValueDominion retained = dominion ∧ chainedDominionAtlas retained = allocation :=
  ⟨rfl, rfl, rfl, rfl⟩

-- ALIGN: CHAINED-OWNER-RETAIN-PRESENTATION.
def retainChainedPresentation (first : A) (chain : Chain A) (dominion : Dominion A)
    (root : Chain Unit) (pages : Folio ⟨Unit, root⟩ ⟨A, chain⟩) (twoPages : pages.data.length = 2)
    (allocation : AtlasAllocation Owner)
    (same : allocation.atlasDescription =
      chainedDominionPresentation (Pagination.fromPageElements pages) twoPages first chain rfl dominion) :
    RetainedAtlas Owner A :=
  retainChainedDominionAtlas first chain dominion allocation ⟨root, pages, twoPages, same⟩

-- ALIGN: CHAINED-OWNER-PAGINATION-ALLOCATION.
def withChainedPagination {Result : Type u} (first : A) (chain : Chain A) (dominion : Dominion A)
    (root : Chain Unit) (pages : Folio ⟨Unit, root⟩ ⟨A, chain⟩) (twoPages : pages.data.length = 2)
    (useOwner : ∀ Owner : Type, RetainedAtlas Owner A → Result) : Result :=
  let presentation := chainedDominionPresentation (Pagination.fromPageElements pages) twoPages first chain rfl dominion
  useOwner Unit (retainChainedPresentation first chain dominion root pages twoPages
    presentation.allocateStored rfl)

-- ALIGN: CHAINED-OWNER-ALLOCATION.
def withChainedDominionAtlas {Result : Type u} (first : A) (chain : Chain A) (dominion : Dominion A)
    (useOwner : ∀ Owner : Type, RetainedAtlas Owner A → Result) : Result :=
  withChainedPagination first chain dominion Chain.singletonChain (chainedDominionFolio first chain)
    (chainedDominionFolio_length first chain) useOwner

theorem withChainedDominionAtlas_inputs (first : A) (chain : Chain A) (dominion : Dominion A) :
    withChainedDominionAtlas first chain dominion (fun _ owner =>
      (chainedDominionFirst owner, chainedDominionChain owner, chainedDominionValueDominion owner)) =
      (first, chain, dominion) := rfl

end Datra.Executable.ChainedDominionAtlas
