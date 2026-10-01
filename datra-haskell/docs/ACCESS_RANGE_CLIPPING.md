# Range selectors on the right hand side of access

Status: implementation plan.

## Purpose

Access should treat `..` expressions as clipping selectors rather than exact
insertions when they occur on the right hand side of `@` or inside access
brackets. A selector keeps the positions that exist in the source, in its
original traversal order, and produces the empty map when none of its positions
exist. This makes ordinary head-and-tail decomposition possible with
`value[0; 1..]` while leaving the meaning of `..` unchanged outside access.

Comma-concatenated `range` selectors must also use their component access
semantics. Each component is clipped independently before its results are
flattened. The implementation must not collapse a concatenated range to one
exact insertion and thereby bypass clipping.

`from` remains the exact, valued-range form. Access through `from` fails when
any requested position is outside the source.

## Required behavior

The three range forms have the following access behavior.

| Selector form | Bounds | Out-of-bounds behavior | Result role |
| --- | --- | --- | --- |
| `a..b`, `a..`, `a..-` | Directed; an explicit target is excluded, while `..-` includes zero | Clip to the positions present in the source | Concrete selector |
| `range a to b`, `range a up`, `range a down` | Inclusive | Select the largest member of the range federation that fits | Range-federation selector |
| `from a to b`, `from a up`, `from a down` | Inclusive | Reject access if any selected position is absent | Exact valued-range selector |

Clipping applies only in the selector position of access. A `..` expression
used as a value, specification source, function argument, or subfederation
member continues to denote the same concrete half-open range.

### Single selectors

For a source with finite order type `n`, a `..` selector retains exactly the
selected positions below `n`. It preserves direction and order:

- `3..10` over a five-position source selects `3, 4`;
- `10..2` over a five-position source selects `4, 3`;
- `10..` over a five-position source selects the empty map;
- every `..` selector over an empty source selects the empty map.

Open and transfinite selectors use the same rule against the source order type.
If the evaluator cannot decide the intersection for a non-total source, access
remains undecidable rather than assuming a representative map is universal.

Numerical singleton selectors, `Infinity`, `from`, and other exact insertions do
not acquire clipping behavior.

### Sequence selectors

A semicolon sequence applies each selector independently and preserves one
outer position per selector result. A clipped empty result remains the empty
coalition in its sequence position; it does not remove or renumber surrounding
positions.

For every nonempty ordinary source:

```datra
value[0; 1..] = value[0; range 1 up]
```

Both expressions preserve the head-and-tail boundary. If a strict component,
such as `0` or `from 1 up`, fails, the complete sequence access fails.

### Concatenated selectors

A comma concatenation retains the semantics of its leaves:

1. validate the selector concatenation independently of the accessed source;
2. reject overlapping components before clipping;
3. access the source with each component independently;
4. concatenate the component results in selector order; and
5. flatten the result, without introducing sequence coalitions.

Consequently, both of these forms select and flatten the available head and
tail of an ordinary source:

```datra
value[0..1, 1..]
value[range 0 to 0, range 1 up]
```

Adjacent components may still canonicalize as values, but canonicalization
must not erase whether a leaf clips (`..` and `range`) or is exact (`from`). A
mixed concatenation applies the policy of each original leaf. Computed range
results that no longer retain a surface-syntax tree must carry enough semantic
information to make the same decision when reused as selectors.

For a nonempty ordinary source, flattened head-and-tail access satisfies:

```datra
value[0, 1..] = value[range 0 up]
```

### Federation sources

A clippable selector is total on an empty concrete source and can therefore be
applied pointwise to a source federation whose members have different order
types. The access decision must describe the results for all source members;
it must not validate only the representative map.

This changes the existing empty-map counterexample for concrete `..`
selectors. For example, accessing a `NaturalRange` source with `0..1` can
produce an empty member for the empty source member and a singleton member for
source members with a first position. An exact `from` or numerical selector
continues to be refuted when the source federation contains an empty map.

The implementation should reuse the existing range-federation access model
rather than add a second, unrelated clipping path.

## Standard library syntax updates

Once `..` clips in access, ordinary access sites should use `..`; `range`
should remain visible where its first-class federation meaning is required.

The recursive numeric helpers become:

```datra
candidate >= (next : this remaining[0; 1..])
candidate <= (next : this remaining[0; 1..])
```

The variadic argument family becomes:

```datra
Args := (for T? of Any) -> Any do
  slots := with i in Nat do "arg%(i)"? : T
yield with n in Nat do slots[0..n]
```

This is equivalent to the current definition. Because `0..n` is half-open,
`n = 0` supplies the empty argument map, and each `n > 0` supplies exactly the
first `n` slots. The separate `()` alternative is no longer needed. The
current inclusive `range 0 to n` instead supplies `n + 1` slots, with the empty
case added separately.

Update the matching example in the repository README. Search all maintained
`.datra` sources for `range` in an access-selector position and replace it only
when the expression is being used for clipping. Preserve `range` in type,
specification, subfederation, signed-range, and other first-class federation
positions. Generated output files are regenerated by their owning workflow
rather than edited by hand.

## Implementation structure

### Preserve selector intent

Represent access policy explicitly at the evaluated selector level:

- clippable concrete range;
- clippable range federation; or
- exact insertion.

Do not infer this policy solely from a normalized `EvaluatedRange`. Range
canonicalization currently combines `..`, `range`, and `from` operands into
shared range forms, which can erase the distinction needed by access. Preserve
leaf policy through concatenation and through computed range results.

### Centralize clipping

Add one direction-aware operation that restricts a described range to a source
order type. Use it for both concrete `..` selectors and members chosen from a
`range` federation. The operation must handle:

- ascending, descending, open, empty, and singleton ranges;
- finite and transfinite boundaries;
- a selector wholly before, wholly after, or crossing the source boundary;
- preservation of range level and symbolic semantics; and
- an empty result without manufacturing an invalid insertion.

Keep source-federation decisions separate from range arithmetic. The decision
layer establishes that pointwise access is valid; the clipping operation then
constructs each selected range.

### Compose sequences and concatenations

Continue to map semicolon sequences through access and coalize each result.
Change range concatenation handling so it traverses semantic selector leaves,
clips the clippable leaves, accesses exact leaves strictly, and concatenates
the results. This should cover `RangeConcatenationForm` both with and without a
retained syntax pair.

Reuse the same composition path for `..` and `range` leaves. Avoid separate
special cases whose behavior can diverge again.

### Expected implementation areas

The main implementation work belongs in:

- `src/DatraTypes/Evaluation/Access.hs`, for selector dispatch and result
  construction;
- `src/DatraTypes/Evaluation/Access/Federation.hs`, for total pointwise access
  over source federations;
- `src/DatraTypes/Evaluation/Access/Composition.hs`, for lifted access through
  concatenated and expanded sources;
- `src/DatraTypes/Evaluation/Access/RangeSelection.hs`, for direction-aware
  clipping and symbolic range reconstruction;
- `src/DatraTypes/Evaluation/Map.hs` and
  `src/DatraTypes/Evaluation/Value.hs`, if normalized range values need to
  retain leaf access policy; and
- the parsing, interpreting, type, and CLI test suites for regression
  coverage.

No grammar change is required. The parser should continue to produce the same
range expressions; evaluation changes only when those expressions occupy an
access-selector position.

### Preserve type interactions

Clipping is an access behavior, not a new subtyping rule. Preserve these
properties:

- a concrete `..` value can still specify into a compatible `range` target;
- `range` subfederation checks continue to use bounds and direction;
- `from` and `range` remain distinct federation families;
- optional names remain distinct from optional values; and
- named access, specification access, and access through federation branches
  apply clipping without discarding identifiers or annotations.

Add explicit regression coverage for optional identifiers, `~>` and `<~`
specifications, and `of` subfederation checks. In particular, verify that using
a clipped access result in these constructs preserves its canonical range or
map semantics and that repeated specification composition terminates.

## Test plan

### Direct access

Cover `..` selectors against empty, shorter, exact-length, longer, infinite,
and transfinite sources. Include ascending, descending, open, empty, singleton,
partially fitting, and wholly out-of-bounds selectors. Confirm that `from` and
numerical singleton selectors remain strict.

### Sequence access

Cover:

- `value[0; 1..]` against one-element and longer sources;
- multiple independently clipped `..` selectors;
- multiple independently clipped `range` selectors;
- empty clipped components retaining their sequence positions;
- overlapping selectors being allowed because sequence positions are
  independent; and
- a strict failing component rejecting the entire sequence.

### Concatenated access

Cover:

- finite and open `..` concatenations;
- finite and open `range` concatenations;
- mixed `..`, `range`, and `from` leaves;
- flattening in selector order;
- adjacent ranges and canonicalization;
- overlap rejection before clipping;
- a component clipping to empty;
- out-of-bounds `from` components remaining errors; and
- computed concatenated range results reused as selectors.

### Federation and type interactions

Cover access over `NaturalRange`, valued-range, concatenated, expanded,
specified, assigned, argument-map, and dependent-identifier sources. Add
focused tests for optional names, forward and reverse specification,
subfederation membership, and the empty member of `NaturalRange`.

### Library integration

Update and exercise `std.datra`, `numbers.datra`, and the README example. Verify
zero, one, and several variadic arguments and numeric reductions over one and
several values. Run the focused parsing and interpreting tests first, then the
complete test suite once with LiquidHaskell disabled, following the repository
test guidance.

## Completion criteria

The update is complete when:

- every `..` selector clips without changing `..` as a non-selector value;
- semicolon sequences preserve independently clipped results;
- comma concatenations clip `..` and `range` leaves independently and flatten
  them, while `from` leaves remain exact;
- overlap, direction, symbolic range, and federation decisions remain sound;
- optional-name, specification, and subfederation interactions are covered;
- maintained library access sites use the equivalent `..` spelling;
- `Args` derives its empty case from `0..0`; and
- focused and full regression tests pass.

## Non-goals

This update does not make scalar indices clip, make `from` tolerant, relax
range-overlap checks, replace the first-class `range` federation, or change the
meaning of `..` in specifications and subfederation checks.
