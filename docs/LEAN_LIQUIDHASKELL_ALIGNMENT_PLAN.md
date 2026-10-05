# Lean/LiquidHaskell alignment plan for `DatraCore`

## Purpose

This document proposes a staged rewrite of the Lean formalization so that it
models the **current executable representation** in `datra-haskell/src/DatraCore`,
then uses that model to remove the remaining LiquidHaskell assumptions.

The governing rule is:

> Haskell defines the executable representation; Lean proves that representation
> correct and relates it to the abstract mathematics in the preprint.

This is deliberately stronger than renaming Lean declarations to resemble the
Haskell API. In particular, the new Lean layer must model Haskell's finite folio
GADT, full-spine page-element traces, normalization idempotent, dependent Atlas
data action, and symbolic `AtlasHom` syntax. The existing Mathlib-based model
should remain as the denotational specification.

There is no expectation that Lean proof terms can be pasted into
LiquidHaskell. Proof transfer means aligning definitions and theorem statements,
proving the result in Lean, and then porting the same structural argument to a
LiquidHaskell-friendly first-order proof function. Lean is the reference model
and regression oracle; LiquidHaskell remains the checker for the Haskell code.

## Current state

### Lean

`datra.lean` is a 4,000-plus-line monolithic formalization. Its foundational
model is mostly extensional:

- `Dominion` stores a carrier and an embedding into `Nat`.
- `Chain` stores a linearly and well-founded ordered carrier with order type
  below `omega0 ^ omega0`.
- `Folio` stores a positive finite diagram `Fin length -> CoCon` and obtains the
  infinite spine by padding with the final page.
- `Folio.El` is Mathlib's category of elements of the page diagram.
- `Pag` wraps a folio; pagination morphisms are arbitrary functors between the
  stored element categories.
- `Atl` stores a pagination, a functor `Pa.El -> DomIns`, and pagewise
  disjointness.
- `AtlHom` stores a page functor and a natural transformation.
- `TallAtlas` and `Atl.coherence` expose the padded-spine presentation and prove
  that its coherence map is idempotent and not generally the raw identity.
- `DaTra` is then the ordinary Mathlib presheaf category `Atl^op -> Type`.

This is a good denotational account, but it does not yet capture several
implementation choices on which the Haskell proofs depend.

### Haskell and LiquidHaskell

The current `DatraCore` representation is executable and intensional:

- `Dominion` has `rank`, executable `unrank`, and a checked round-trip law.
- `Ordinal` is a canonical Cantor-normal-form value below `omega^omega`.
- `Chain` has an explicit order type, position function, lookup function, bounds,
  injectivity, and surjectivity witnesses.
- `FolioData` is a nonempty, type-aligned GADT built from an origin and `SnocPage`
  steps, each carrying an adjacent coconsolidation.
- `PageElement` stores a page number, ordinal position, full transport trace,
  and existential cell. Arrows are characterized by reverse page order plus the
  trace-suffix transport relation.
- Pages beyond the finite presentation are real full-spine occurrences. They
  normalize to their last genuine representatives by clamping the page and
  trimming repeated trace entries.
- `Pagination` gives a folio a generative phantom scope. Its morphisms are
  object maps plus an arrow-preservation witness.
- `Atlas` has a second generative identity and a dependent `cellData` family.
  `AtlasData` stores the object/action operations plus identity, composition,
  full-spine coherence, and pagewise-disjointness witnesses.
- Primitive Atlas morphisms normalize at source and target and carry page-arrow
  preservation and data-naturality witnesses.
- `AtlasMorphism` and `AtlasHom` explicitly represent identity and composition.
  A materialized identity is the Atlas normalization/coherence idempotent, and
  composite evaluation inserts the middle Atlas coherence.
- Presheaves use a defunctionalized value-family symbol
  `DataTransformationValue` because the needed higher-kinded/rank-N encoding is
  difficult for LiquidHaskell on the current GHC.

### Remaining explicit trust boundary

A repository-wide scan of `DatraCore` currently finds four explicit
LiquidHaskell `assume` declarations, all in
`DataTransformations/DataTransformations/DataTransformation/LiquidInternal.hs`:

| Assumption | Intended fact | Nature of the gap |
| --- | --- | --- |
| `presheafRightIdentity` | `presheafCompose arrow presheafIdentity == arrow` | Structural equality of the indexed `AtlasHom` syntax |
| `presheafAssociativity` | Associativity of `presheafCompose` | Structural induction over the indexed syntax |
| `yoneda` | The representable action packages as a lawful `DataTransformation` | LiquidHaskell loses verified laws at a rank-N/defunctionalized constructor boundary |
| `yonedaNatural` | An Atlas arrow packages as the corresponding Yoneda natural transformation | The pointwise naturality lemma is checked, but its rank-N component cannot be stored without an assumption |

`yoneda` and `yonedaNatural` also have `ignore` directives. These are packaging
limitations rather than missing mathematical arguments, but they are still part
of the trusted code base and must be removed.

## Architectural decision: two Lean layers

The rewrite should not discard the existing abstract development. It should
separate it into two connected layers.

### 1. Executable layer

Create a `Datra.Executable` namespace whose definitions mirror the Haskell data
constructors, eliminators, and recursive functions closely enough that every
LiquidHaskell theorem has a Lean counterpart over the same cases.

Suggested modules:

```text
Datra/Executable/Ordinal.lean
Datra/Executable/Dominion.lean
Datra/Executable/Chain.lean
Datra/Executable/Consolidation.lean
Datra/Executable/Folio.lean
Datra/Executable/PageElements.lean
Datra/Executable/Pagination.lean
Datra/Executable/Atlas/Data.lean
Datra/Executable/Atlas/Morphism.lean
Datra/Executable/DataTransformation.lean
```

Initially, `datra.lean` can import these modules while retaining the literate
preprint material and compatibility aliases. Splitting the file is part of the
work, not a prerequisite for changing the mathematics.

### 2. Semantic layer

Move or retain the existing Mathlib definitions under `Datra.Semantics`. This
layer contains the ordinary categories, functors, presheaves, adjunctions, and
monoidal results.

The bridge from the executable layer should provide:

- an interpretation of executable ordinals and chains into the Mathlib order
  model;
- an interpretation of a GADT-style folio as the current finite diagram;
- an equivalence between trace-based page elements and the appropriate category
  of elements;
- an interpretation of normalized executable Atlases into stored finite
  semantic Atlases;
- preservation of identity and composition; and
- compatibility of the derived constructions that the Haskell implementation
  exposes.

The target is not necessarily definitional equality. Named equivalences and
commuting theorems are preferable to pervasive casts.

## The Atlas alignment in detail

Atlas is the critical boundary because every remaining assumption concerns the
Atlas category or presheaves over it.

### A. Reproduce the executable foundations

1. Define an executable dominion with `rank`, `unrank`, and
   `unrank (rank x) = some x`. Prove that `rank` is injective and provide a
   forgetful map to the current `Dominion`.
2. Define the executable ordinal representation used by Haskell, including
   canonical coefficients and comparison. Prove its interpretation is below
   `omega0 ^ omega0`, and prove correctness of comparison and the operations
   needed by chains and sums.
3. Define an executable chain using `orderType`, `position`, and `lookup` plus
   the three Haskell laws. Derive `LinearOrder`, `WellFoundedLT`, and the current
   semantic `Chain`. Conversely, identify exactly which semantic chains admit
   an executable lookup; do not claim an equivalence for noncomputable chains.
4. Mirror `Consolidation` as a monotone map with chosen executable preimages and
   the corresponding right-inverse proof. Prove identity and composition both
   extensionally and at the stored representation level.

### B. Make the finite folio representation explicit

Introduce a dependent nonempty sequence corresponding to Haskell's
`OriginFolio`/`SnocPage`:

- the origin page includes a selected value and uniqueness proof;
- each snoc step includes the next chain and the adjacent coconsolidation;
- `length`, `origin`, `last`, interval transport, and padded lookup are recursive
  functions with the same equations as Haskell; and
- interval identity/composition theorems are proved independently of the
  Mathlib functor laws.

Then construct the current finite `Folio.core` functor and prove that its map on
an interval is the composite generated by the GADT. If useful in the opposite
direction, add a noncomputable conversion from a finite semantic folio to an
executable folio, clearly marking its use of choice.

### C. Formalize traced page elements

Mirror the implementation-level objects:

- a dependent/existential cell carrying its chain and value;
- `PageElement` with page, position, trace, and cell;
- existential `SomePageElement` for dynamic lookup;
- `pageElementPrecedes` and the trace-suffix relation;
- `PageElementArrow` as evidence of both predicates;
- identity and composition of arrows;
- `trimTrace`, page clamping, and element/arrow normalization; and
- reachability, preservation of arrows, and idempotence of normalization.

The Haskell phantom `scope` should correspond in Lean to ownership by a
particular folio/pagination value, preferably through dependent indices. Lean
does not need to simulate `runST`-style generativity; it needs a type-level
invariant strong enough to prove that elements from different paginations
cannot be mixed.

Prove a representation theorem:

> Valid traced page elements and arrows are equivalent to objects and arrows in
> the category of elements of the padded folio diagram.

This theorem is the bridge between executable predicates and the existing
categorical formulation.

### D. Define the executable Atlas data action

The new Lean Atlas should expose the same obligations as the Haskell smart
constructor:

- dependent data carrier at each page element;
- a `Dominion` for each carrier;
- a `DomanialInsertion` for each page-element arrow;
- identity action;
- composition action;
- normalization/coherence action is the identity insertion pointwise; and
- pagewise disjointness after transport to the common origin.

The existing semantic `Atl` stores only a functor and disjointness because its
finite presentation makes stability implicit. The executable Atlas must store
or derive the explicit coherence law because Haskell exposes the full padded
spine. Prove that the identity and composition witnesses construct a semantic
functor, and that executable disjointness implies `IsPagewiseDisjoint`.

### E. Model the correct category of Atlas morphisms

The finite semantic category and the Haskell runtime category must not be
silently identified:

- In the finite `Atl` category, identity is an ordinary functor identity.
- On the padded spine, Haskell's identity is normalization/coherence, which is
  idempotent but is not generally the raw identity.
- Haskell primitive maps are normalized at both boundaries, and composite
  evaluation inserts the middle coherence.

Formalize this as a category of split idempotents (or an equivalent explicit
`NormalizedAtlas`/Karoubi construction):

- an object carries its tall Atlas and normalization idempotent `e`;
- a morphism `f : X -> Y` satisfies `f = e_X ≫ f ≫ e_Y` in Lean's
  source-to-target `≫` convention (equivalently `e_Y . f . e_X` in Haskell's
  right-to-left `(.)` notation);
- object identity is `e`; and
- composition is coherence-sandwiched and associative.

Then mirror Haskell's two syntactic types:

- `AtlasMorphism`: primitive, identity, or composite materialized operations;
- `AtlasHom`: typed symbolic primitive, identity, or composite nodes with the
  same identity simplifications as `composeAtlasHoms`/`presheafCompose`.

Prove:

1. page-object mapping preserves both arrow predicates;
2. dependent data components satisfy the normalized naturality equation;
3. materialization respects symbolic composition;
4. symbolic identity materializes to the object's coherence;
5. `presheafCompose` has right identity and is associative by structural
   induction; and
6. the normalized full-spine category is equivalent to the finite stored Atlas
   category, or at minimum connected by full/faithful functors with an explicit
   essential-image theorem.

The existing `Folio.collapse_include`, `Folio.include_collapse_ne_id`,
`Atl.coherence_idempotent`, and `AtlHom.coherence_left/right` results are the
starting lemmas for this step.

## Phased implementation plan

### Phase 0: freeze the correspondence surface

- Record the Haskell constructors, reflected functions, and refinement theorems
  in a checked manifest, grouped by module.
- Give every cross-language theorem a stable identifier, for example
  `PE-NORMALIZE-IDEMPOTENT` or `ATLASHOM-ASSOC`.
- Add a short comment containing that identifier at both the Lean theorem and
  LiquidHaskell proof function.
- Capture the current four-assumption inventory in CI so new assumptions cannot
  be introduced unnoticed.

Exit criterion: every core Haskell representation and every trusted assumption
has an assigned Lean target.

### Phase 1: executable ordinal, dominion, chain, and consolidation

- Implement the representations and interpretation functions.
- Port the Haskell property names and recursive equations.
- Prove identity, composition, bounds, lookup/position round trips, and chain
  sum behavior.
- Add small cross-language golden vectors for ordinal encoding, comparison,
  addition, chain lookup, and chain sum. These test computation; the Lean proofs
  establish the general facts.

Exit criterion: no Atlas-level proof depends on an unmodeled primitive or on an
unexplained semantic/executable mismatch.

### Phase 2: folios, page elements, and pagination

- Implement the GADT-equivalent folio and padded page lookup.
- Implement traces and trace-derived arrows.
- Prove page-element category laws and all normalization lemmas.
- Build the equivalence with the semantic category of elements.
- Model pagination ownership and morphisms as object maps with an arrow witness.

Exit criterion: Lean can state and prove the same contracts as
`Folio.LiquidInternal`, `PageElements.LiquidInternal`, and
`Pagination.LiquidInternal` without appealing to the old `Pag` morphism type.

### Phase 3: Atlas objects and morphisms

- Implement `AtlasDataAction`, its four laws, and the executable Atlas smart
  constructor.
- Implement primitive normalized Atlas morphisms and data naturality.
- Formalize the normalized/Karoubi category.
- Implement symbolic `AtlasHom`, `presheafIdentity`, and `presheafCompose` with
  the Haskell equations.
- Prove interpretation into the existing finite `Atl` category.

Exit criterion: `presheafRightIdentity` and `presheafAssociativity` are theorems
over a faithful model of the actual Haskell syntax and evaluation, not merely
consequences of Mathlib's unrelated category instance.

### Phase 4: remove the structural LiquidHaskell assumptions

Port the Lean proofs for the two structural facts back to Haskell:

1. Make `presheafRightIdentity` a reflected/PLE proof by the exact constructor
   cases used in Lean.
2. Make `presheafAssociativity` recurse on the same `AtlasHom` argument as the
   definition of `presheafCompose`.
3. If LiquidHaskell cannot reason directly through the GADT equality witnesses,
   factor out a first-order spine for the symbolic composition shape and prove:
   - erasure commutes with `presheafCompose`;
   - the first-order spine has identity and associativity; and
   - reconstruction/materialization preserves the erased shape.

Do not replace these assumptions with a differently named assumed lemma or an
unchecked `unsafeCoerce` boundary.

Exit criterion: the first two `assume` declarations are gone and
`make verify-liquid` passes.

### Phase 5: align presheaves and Yoneda packaging

Define in Lean the same defunctionalized interface used in Haskell:

- a symbol `values` and interpretation `DataTransformationValue values atlas`;
- a rank-polymorphic contravariant action;
- stored identity and composition eliminators;
- natural-transformation components and naturality eliminators;
- `YonedaPresheaf`, `Yoneda`, `mapYoneda`, and `mapYonedaNatural`.

Prove the representable laws from the symbolic Atlas composition theorems. Keep
these separate:

- pointwise Yoneda identity/composition/naturality; and
- safe storage of those pointwise results in the rank-N packages.

The first group is mathematics; the second is an encoding theorem specific to
GHC and LiquidHaskell.

Exit criterion: Lean models both the mathematical law and the exact packaging
boundary at which LiquidHaskell currently fails.

### Phase 6: remove `yoneda` and `yonedaNatural` assumptions

Try the following Haskell refactors in order, keeping the smallest one that
LiquidHaskell can verify:

1. Construct both values through the existing checked smart constructors
   `dataTransformation` and `dataTransformationNatural`, rather than directly
   through data constructors.
2. Replace anonymous rank-N function fields with named wrapper types and named
   reflected eliminators, following the already successful pattern used by
   `AtlasAction` and `DataTransformationAction`.
3. Store law dictionaries separately from executable actions so that each law
   is recovered through a monomorphic reflected accessor.
4. Specialize representable presheaves with a dedicated checked constructor
   whose refinements mention `mapYoneda` directly, avoiding a coercion through
   the open type family at the critical equality.
5. Only if the above fail, introduce a defunctionalized component symbol and an
   explicit interpretation family for Yoneda components, with Lean proving that
   this refactor denotes the same natural transformation.

For each attempt, keep the already checked pointwise functions
`yonedaIdentity`, `yonedaComposition`, and `yonedaNaturality` as the leaf proofs.
The goal is to make their refinements survive packaging, not to re-prove them
axiomatically.

Exit criterion: `assume yoneda`, `assume yonedaNatural`, and their two `ignore`
directives are removed; all public callers continue to typecheck.

### Phase 7: migrate derived constructions in dependency order

Once core Atlas and presheaf parity is established, align the remaining Lean
and Haskell modules in this order:

1. Atlas extent, territory, and covered page elements.
2. Atlas transposals, ordered transposals, transversals, and stable transversals.
3. Dominion inclusion, charter, coalition, and cartography.
4. Empty Atlas, merge, sequence, confederation, federation, and horizontal sum.
5. Data transversals, stable data transversals, navigation, expedition, and
   Data Transformation Maps.
6. Stable confederal data, Day convolution, monoidal structure, and Kleisli
   structure.

At each step, prove that the executable operation interprets to the existing
semantic operation before changing downstream definitions.

Exit criterion: the public Haskell `DatraCore` API has a named Lean model and
the major categorical results are recovered through the bridge.

## Proof-transfer workflow

For every assumption or difficult LiquidHaskell theorem:

1. **Normalize the statement.** Write a first-order equation or predicate over
   named executable functions. Avoid relying on an implicit Mathlib instance.
2. **Prove it in Lean over the executable datatype.** The induction variable
   and recursive calls should match the Haskell function's recursion.
3. **Record a proof recipe.** In a comment beside the Lean theorem, list the
   constructor cases, rewrite lemmas, and induction hypothesis used.
4. **Port the recipe.** Implement a total Haskell function returning `()` with
   the corresponding refinement, using `seq` only to expose recursive proof
   calls when required by PLE.
5. **Check the leaf theorem and the package theorem separately.** This prevents
   a rank-N packaging failure from being mistaken for a mathematical hole.
6. **Run both checkers.** A theorem is closed only when Lean builds and the
   LiquidHaskell-enabled Haskell library builds.
7. **Delete the assumption and ignore directives in the same change.** The CI
   gate should reject reintroduction.

Lean should not be used as an external oracle that emits `True` certificates;
that would leave the executable/refinement connection trusted. The Haskell
proof must still be checked against the Haskell definition.

## Validation and CI

The final workflow should provide one top-level target, for example
`make verify-formal`, that performs:

```sh
lake build
cd datra-haskell && make verify-liquid
cd datra-haskell && make check
```

Add an assumption gate equivalent to:

```sh
if rg -n '(^|[[:space:]])assume[[:space:]]|\{-@[[:space:]]+ignore' \
  datra-haskell/src/DatraCore; then
  echo "Unexpected LiquidHaskell trust escape in DatraCore" >&2
  exit 1
fi
```

Maintain three kinds of tests:

- **Lean theorem tests:** compilation of every executable and bridge theorem.
- **LiquidHaskell verification:** refinements for the implementation itself.
- **Cross-language computation fixtures:** shared inputs and expected outputs
  for ordinal, chain, trace, normalization, and composition functions. These
  catch definition drift but do not replace proofs.

Pin Lean/Mathlib, GHC, LiquidHaskell, and Z3 versions in CI. The Yoneda gaps are
compiler/elaborator-sensitive, so version changes must rerun the assumption-free
verification rather than relying on cached results.

## Deliverables

1. A modular executable Lean layer mirroring `DatraCore` foundations.
2. A preserved semantic layer containing the abstract category theory.
3. Interpretation/equivalence theorems connecting both layers.
4. A formal normalized/Karoubi Atlas category matching Haskell identity and
   composition.
5. Lean proofs of symbolic Atlas identity and associativity.
6. LiquidHaskell implementations of those proofs with no `assume`.
7. A refactored Yoneda packaging boundary with no `assume` or `ignore`.
8. An assumption gate and a combined formal-verification target.
9. A theorem correspondence manifest and cross-language fixtures.

## Definition of done

The alignment is complete when all of the following hold:

- Lean definitions cover the actual executable representations, including
  traces, normalization, generative ownership, and symbolic Atlas arrows.
- The executable Atlas category's identity and composition agree with Haskell's
  coherence-sandwiched behavior.
- The executable model is related by proved interpretation theorems to the
  existing finite semantic Atlas model.
- `presheafRightIdentity`, `presheafAssociativity`, `yoneda`, and
  `yonedaNatural` are checked rather than assumed.
- No `assume`, relevant `ignore`, `unsafeCoerce`, or equivalent trust escape is
  present in `DatraCore`.
- `lake build`, `make verify-liquid`, and `make check` pass in the pinned toolchain.
- Derived constructions use the aligned core or have explicit, documented
  bridge theorems showing why the old semantic definition is equivalent.

## Main risks and mitigations

- **Mistaking semantic category laws for implementation proofs.** Prove the
  laws over the reified Haskell syntax first, then interpret them.
- **Dependent casts overwhelming the Lean development.** Isolate sigma/GADT
  transport in constructors and extensionality lemmas; expose typed eliminators
  analogous to the Haskell rank-N callbacks.
- **Treating normalization as raw identity.** Use the explicit split-idempotent
  category and keep `include_collapse_ne_id` as a regression theorem.
- **LiquidHaskell rank-N/type-family limitations.** Separate pointwise proofs
  from storage, prefer named reflected accessors, and introduce specialized
  smart constructors before changing the public representation.
- **Claiming computability for every semantic chain.** The executable-to-semantic
  direction is canonical; any reverse construction using choice must be marked
  noncomputable and must not be used to justify runtime behavior.
- **A long-lived duplicate formalization.** Require every executable definition
  to gain its semantic bridge before downstream migration, and retire obsolete
  compatibility aliases after their callers move.

## Recommended first vertical slice

The first implementation change should be deliberately narrow:

1. Add executable `AtlasHom` syntax in Lean with exactly the Haskell constructors.
2. Port `presheafIdentity` and `presheafCompose` verbatim at the equation level.
3. Prove right identity and associativity by structural induction.
4. Connect syntax evaluation to the existing `AtlHom` composition where possible,
   using the current coherence lemmas for the padded presentation.
5. Port the two proof recipes to LiquidHaskell and remove the first two
   assumptions.

This slice tests the proof-transfer method against real trust holes before the
larger representation migration. The full Atlas rewrite should follow once it
has confirmed which indexed/GADT proof patterns both Lean and LiquidHaskell can
support cleanly.
