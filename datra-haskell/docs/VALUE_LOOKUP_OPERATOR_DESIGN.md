# Foliage-ordered lookup operator

## Summary

Change `~` from name-oriented parser sugar into a first-class prefix operator
over string expressions. It returns a lazy map of key-value pairs for the
matching bindings which exist in the current lexical scope:

```datra
(
  (key : "arg0"; value : 123);
  (key : "arg4"; value : 456);
  ...
)
```

Missing bindings do not produce rows. There is no `Maybe` wrapper in the
result. If `arg1`, `arg2`, and `arg3` are absent, the row after `arg0` can be
the row for `arg4`.

For a concrete string, including a total string template, the result is either
an empty map or a singleton map. For a non-total string template, every
existing scope key admitted by the template appears exactly once. Rows follow
the `FoliageMap` traversal order of their capture tuples, not declaration order
or the template family's raw ordinal order.

A template capture is admissible exactly when it can participate in the
ordinal-indexed map projection used by a `^` generic. A capture such as `Any`,
which has no such projection, is a compilation error.

String-template matching is also changed to validate captures with ordinary
function-domain preparation rather than generic `of` membership. Captured text
must be canonical. Thus `"arg%(_x : Nat)"` generates and matches `"arg4"`, not
`"arg(_x := 4)"`.

## Terminology

The language-level name of `~` is the **lookup operator**. Documentation,
diagnostics, test descriptions, and user-facing messages must use that name.
Do not call it the “value lookup operator,” “value-of operator,” or “tilde
operator.” Existing implementation names such as `ValueOfOperator` may be
renamed to `LookupOperator` as part of this change; the new AST constructor
should likewise be named `Lookup` unless a more specific internal name is
needed to avoid a collision.

## Goals

1. Make the right operand of `~` an evaluated string expression.
2. Return a map of existing key-value pairs, with no absence rows and no
   optional value wrapper.
3. Return an empty map for a concrete key which is not bound.
4. Order template matches by the canonical `FoliageMap` traversal of the
   capture family.
5. Build the result lazily so binding values are evaluated only when their rows
   are demanded.
6. Reuse exactly the ordinal-indexed-family rules used to give `^` generic
   functions a map-access view.
7. Reject non-enumerable captures, such as `Any`, while compiling the lookup.
8. Use function-domain preparation for canonical string capture and inversion.
9. Preserve a distinct, strict representation for compiler-generated lexical
   references and ordinary identifier evaluation.

## Non-goals

- `~` does not return a function. `~"arg%Nat" 4` is not the lookup interface;
  callers inspect the returned map.
- `~` does not search an arbitrary value. It searches the lexical scope in
  which the operator is evaluated.
- This change does not alter ordinary identifier references or `value.name`
  scope access.
- This change does not alter declarative syntax matching introduced by the
  syntax `%` operator. Syntax holes capture ASTs; they are not canonical string
  captures.
- Foliage traversal determines result order only. It does not change the
  ordinal order of the capture family itself.
- An existing binding which fails to evaluate is still an error. Its row is
  not omitted as though the binding were absent.

## Current behavior

`Parsing.valueOfExpression` currently parses one or more names and expands each
name into:

```haskell
ScopeAccess
  (contextualAccess (IdentifierString "_this"))
  (IdentifierReference name)
```

Consequently:

- `~a` treats `a` as the literal name `"a"`;
- `~(a, b)` is a special list of two strict accesses;
- a missing name raises `UnknownIdentifier` or a named-access error;
- only the selected payload is returned; and
- no `~` node survives in the AST.

`DatraLanguage.AST.Source` recognizes the expanded shape and renders it as `~`.
`FunctionClosure` and canonical dependency rendering also rely on that shape
for strict generated references. That coupling must be removed because the new
operator returns a map and cannot represent a strict closure dependency.

String templates currently become string federations. Reverse matching splits
input at literal boundaries and uses the general federation-selection logic
behind `of` for each interpolation. That path can retain an identifier
assignment spelling where lookup needs the canonical spelling of the prepared
capture payload.

## Result semantics

### Lookup row

Every result member is a two-member named map:

```datra
(key : <concrete string>; value : <resolved value>)
```

The `key` member contains the exact query string. The `value` member contains
the value produced by ordinary resolution of that key. There is no tag around
the value.

The row is a regular map, not an argument-map permutation. Preserve its
two-member boundary with `makeAtlasMapPreservingSingleton` or an equivalent
constructor. The outer lookup result is also a preserved map in the zero- and
one-row cases, so callers can uniformly use map access:

```datra
(~"arg%Nat")[0].key
(~"arg%Nat")[0].value
```

Construct both members with the ordinary identifier-value machinery. Do not
coerce the key to a less precise `Str` value or the payload to `Any` merely to
make rows homogeneous. Each row retains its exact key and value.

### Concrete strings and total templates

For a concrete string:

```datra
~"abc"
```

return:

- `((key : "abc"; value : <resolved abc>))` when `abc` is bound; or
- `()` when `abc` is not bound.

`~a` evaluates `a`. If `a` evaluates to `"abc"`, it has the same result as
`~"abc"`; it never treats the spelling `a` as the key.

A string template whose interpolations all evaluate to total values is also a
concrete string. It performs one existence check and does not require a foliage
capability:

```datra
~"arg%(2 + 2)"
```

returns the singleton row for `"arg4"` when that binding exists, and the empty
map otherwise.

### Non-total templates

A template with at least one non-total capture describes a family of possible
keys. Lookup intersects that family with the names visible in the current
scope. Only the intersection becomes rows.

For example, if the scope contains `arg0` and `arg4` but no other `argN`
bindings, then:

```datra
~"arg%Nat"
```

contains exactly the `arg0` and `arg4` rows. Their positions are determined by
the foliage ranks of captures `0` and `4`, regardless of declaration order.

The output is finite whenever the visible scope-key index is finite, even when
the template family is infinite. Its order type is the natural number of
matching keys. The row values remain lazy.

The scope used for both name discovery and later value resolution is captured
when the `~` expression is evaluated. Accessing a row after leaving that block
does not switch to the caller's scope.

## Capture compilation

### Retained template plan

A string-template value must retain its ordinary string federation and a
capture plan:

```haskell
data EvaluatedStringTemplate = EvaluatedStringTemplate
  { stringTemplateSegments :: [EvaluatedStringTemplateSegment]
  , stringTemplateCaptureSchema :: InterpretedValue
  }

data EvaluatedStringTemplateSegment
  = EvaluatedStringLiteral String
  | EvaluatedStringCapture CaptureIndex InterpretedValue
```

The exact fields are provisional. The plan must retain:

- literal text and capture order;
- each capture's function-domain schema;
- the underlying bound used to enumerate that capture;
- the converted string federation used by specification and projection; and
- enough provenance to survive aliases and wrappers which preserve a
  `TemplateForm`.

`interpretStringTemplateWith` already evaluates interpolation expressions
before calling `toStringValue`. It should build the plan at that boundary.
Total interpolations are folded into adjacent literal text. Only non-total
interpolations become capture slots.

For `%(_x : Nat)`, `_x` is slot metadata and `Nat` is the enumerated bound.
Domain preparation still sees the named slot, but generated key text comes
from the prepared payload. This distinction produces `"arg4"` rather than
`"arg(_x := 4)"`.

### The `^`-generic map-access rule

Capture admissibility is defined by the following equivalence:

> A lookup capture plan is admissible if and only if the equivalent leading
> `^`-generic telescope can expose its ordinary map-access view.

Compilation should share `genericFunctionMapView` and
`ordinalIndexedValueFamily`, or extract their common family builder. Lookup
must not reimplement the predicate.

The existing rule admits:

- an atomic value with an `orderedAtlasMapView` whose order type is at most
  `omega`; and
- a sequential product of admitted values, using the existing lexicographic
  product construction.

It preserves the coordinate order, dependency preparation, and ordinal
multiplication observed through map access on generic functions. Finite
products may have transfinite order below `omega ^ omega`; foliage traversal
fairly reindexes those positions.

The rule rejects values without that semantic capability, including:

- `Any`;
- arbitrary functions or unions without an ordered family;
- coalized limit-endpoint ranges such as `from 0 to Infinity`; and
- wrappers which erase the ordered-map capability.

Ordinary generic functions remain callable when their `^` bound lacks a map
view; they simply do not expose that projection. Lookup has no callable
fallback, so the same failure is a compilation error:

```datra
~"value%Any"    # compilation error
```

Add a diagnostic such as:

```haskell
LookupCaptureHasNoGenericMapView CaptureIndex String
```

Report it while compiling `Lookup`, before scope matching or result-map
construction. It must not be represented as an empty result.

This check applies only when non-total captures remain. A total template is a
single concrete key.

### Preparing capture tuples

Capture matching and key rendering must use the same argument-schema
preparation as an ordinary function domain. In the current implementation this
means sharing the logic behind `argumentSchemaFromValue`,
`argumentSchemaValuesComplete`, and `overloadArgumentSchemaComplete` rather
than checking witnesses with `of`.

Preparation provides the canonical payload for every slot and applies named
and positional rules consistently. Each payload must have one canonical
concrete string conversion. Failure is a compilation error in the capture
plan, not a skipped scope key.

## Scope-key discovery

Filtering an infinite foliage traversal directly is insufficient. If only
finitely many keys exist, searching for a row after the last hit would never
prove that the result is exhausted. The implementation must derive the result
cardinality from the scope side.

Introduce a name-only view of the current lexical scope:

```haskell
scopeLookupKeys
  :: Scope
  -> Either InterpretingError [String]
```

This view applies the same visibility, alias, privacy, and shadowing rules as
ordinary lookup, but it does not evaluate bindings. It returns each queryable
key once. Canonical aliases which are independently queryable are included
under their query spelling.

For a non-total template:

1. Compile the capture family using the `^`-generic map-view rule.
2. Obtain the finite set of queryable scope keys.
3. Run canonical reverse template matching against each key.
4. Discard keys which do not match.
5. Retain the matching key, its prepared capture tuple, and a binding handle.
6. Expose the retained entries in foliage-rank order.

This computes the result's finite cardinality without evaluating any binding
value and without attempting to exhaust an infinite template family.

The current `ScopeBindings` representation is finite, so this design has a
conclusive name set. A future symbolic or transfinite namespace must expose an
equivalent searchable key-index capability before it can participate. It must
not be converted to a list by unbounded traversal.

## Foliage ordering

Let the compiled capture family have order type `alpha`. Each matching scope
key has a prepared capture tuple. Its result order is the order in which that
tuple appears under:

```haskell
foliageMap alpha
```

There are two valid implementation strategies.

### Structural inverse

Extend the shared ordinal-indexed-family construction with a structural inverse
which maps a prepared witness tuple to its source ordinal. Then use
`foliageMapRankOf` to obtain its natural rank and sort matching scope keys by
that rank.

This is preferred when the primitive ordered-family adapters can provide
inverse lookup without enumeration. The inverse is derived from the same
family structure as `^` map access; it is not a new admissibility requirement.

### Lazy foliage merge

If no structural inverse is available, retain the finite set of matching key
strings and scan foliage ranks lazily. Generate the key at each rank and emit a
row only when it belongs to that retained set. Stop after all retained keys
have been emitted.

This scan terminates for every valid result position because canonical reverse
matching proved that every retained key has a capture tuple in the family. The
known retained-key count supplies the exact output order type, so access after
the final row is rejected by bounds checking rather than searching forever.

In both strategies:

- declaration order has no effect;
- missing candidate keys never become rows;
- every retained key appears once;
- finite and transfinite capture-family lanes use the existing `FoliageMap`
  ordering; and
- string-template injectivity is required so two tuples cannot produce the
  same key.

If two distinct prepared tuples render the same key, compilation fails with
`NonInjectiveStringInterpolation` or a more specific equivalent.

## Lazy values and error propagation

Name discovery determines membership and order, but it must not evaluate every
matching binding. Each retained entry stores a binding handle. Demanding row
`n` resolves only that handle and constructs:

```datra
(key : <retained key>; value : <resolved binding>)
```

The current `makeLazyMapValue` accessor cannot report an evaluation error
separately from an unavailable ordinal. Add a checked lazy-map boundary, for
example:

```haskell
data CheckedOrdinalValues value = CheckedOrdinalValues
  { checkedOrderType :: Ordinal
  , checkedValueAt
      :: Ordinal -> Either InterpretingError value
  }
```

Bounds are checked against `checkedOrderType` before calling `checkedValueAt`.
`accessValues` propagates an error produced by a demanded binding. Finite and
range access propagate the first demanded failure under their existing
evaluation order.

The pure `OrdinalOrderedValues` capability remains appropriate for the capture
family. Only output rows need checked access because binding evaluation can
fail. Do not globally weaken pure ordered-map laws.

## Binding resolution

Refactor ordinary identifier resolution so name discovery can retain a stable
binding handle and value evaluation can happen later:

```haskell
data ResolvedScopeKey = ResolvedScopeKey
  { resolvedScopeKeyText :: String
  , evaluateResolvedScopeKey
      :: ReductionContext -> Either InterpretingError InterpretedValue
  }
```

The exact representation is provisional. It must share canonical alias
selection, privacy, shadowing, cycle detection, and scope-protection behavior
with `resolveIdentifierAccess`.

Once a key has been included, failure while evaluating its binding remains an
error from that row. It cannot cause the row to disappear. The row's `key`
member retains the query spelling even when resolution follows an internal
canonical alias.

## Canonical reverse matching

String-template matching needs a dedicated operation shared by string
specification, `of` checks, template projections, and scope-key filtering:

```haskell
matchCanonicalTemplate
  :: CanonicalStringCodec
  -> EvaluatedStringTemplate
  -> String
  -> Decision PreparedTemplateCaptures
```

Keep the existing finite split search over literal delimiters, but replace the
leaf call to general federation membership. For each possible split:

1. Decode captured substrings with `decodeCanonicalString`.
2. Require each candidate to re-render to exactly the same substring.
3. Submit the candidate tuple to ordinary function-domain preparation.
4. Extract the prepared capture payloads.
5. Reconstruct the complete string from those payloads.
6. Accept only if reconstruction equals the input byte for byte.

Distinct splits which prepare to the same tuple are one match. Distinct
prepared tuples retain the existing ambiguity error.

The reconstruction check excludes identifier-assignment syntax from generated
or matched keys:

```datra
"arg4" of "arg%(_x : Nat)"             # true
"arg(_x := 4)" of "arg%(_x : Nat)"     # false
```

The successful witness retains the prepared tuple. Lookup uses it for foliage
ordering, while `Evaluation.Specification.Projection` continues to expose the
whole string at position zero and captures at subsequent positions.

This rule is specific to canonical string templates. Declarative `%` syntax
patterns continue to match source AST structure.

## Syntax and AST

### Parsing

Add a real expression constructor:

```haskell
Lookup Expression
```

and the corresponding `OperatorExpression` constructor. `~` remains a tight
prefix operator:

```text
~a                 == Lookup (IdentifierReference "a")
~"a"               == Lookup (AsciiStringLiteral "a")
~"arg%Nat"         == Lookup <template>
~(a + b)           == Lookup (Addition a b)
```

Postfix access applies to the result map, so `~"arg%Nat"[0]` selects its first
existing pair. Parentheses are required when the string expression contains a
looser infix or map operator.

Remove `namedAccessNames` and `expandedNamedAccess` from the `~` parser path.
`~(a, b)` is one lookup expression, not two strict name lookups. The lone token
`~` remains a parse error, and token guards continue to distinguish `~`, `~>`,
and `<~`.

### Rendering and traversal

Update normalization, child traversal, source rendering, canonical AST
rendering, syntax rewriting, closure analysis, and serialized-AST parsing for
the new node.

Source rendering prints `~` followed by its operand at prefix precedence. It
must round-trip to `Lookup`; it must not infer `~` from a `ScopeAccess`
shape.

### Strict generated references

Compiler-generated closure and canonical-dependency references remain strict.
Represent them as `IdentifierReference` or explicit `ScopeAccess` nodes, and
render explicit current-scope access when a quoted name is required:

```datra
this."value with spaces"
```

Remove the `scopeNames` renderer shortcut. Generated code must never use
`Lookup`, because doing so would change a strict dependency into a map.

## Interpreter structure

A suggested top-level decomposition is:

```haskell
evaluateLookup
  :: ReductionContext
  -> Scope
  -> [String]
  -> InterpretedValue
  -> Either InterpretingError InterpretedValue

compileLookupCaptureFamily
  :: EvaluatedStringTemplate
  -> Either InterpretingError OrdinalIndexedFamily

matchingScopeKeys
  :: Scope
  -> EvaluatedStringTemplate
  -> Either InterpretingError [RankedScopeKey]
```

`evaluateLookup` distinguishes:

1. a concrete string, producing an empty or checked singleton map; and
2. a retained non-total template plan, compiling its `^`-generic map view,
   discovering matching scope keys, and producing a checked lazy result map.

Any other operand produces `LookupRequiresString`.

`compileLookupCaptureFamily` should be a thin adapter over generic map-view
machinery. Future changes to generic projection rules must automatically apply
to lookup capture admissibility.

## Diagnostics

Add or reuse diagnostics for:

- `LookupRequiresString` when the operand is neither a concrete string nor
  a retained string template;
- `LookupCaptureHasNoGenericMapView` when a non-total capture fails the
  same map-view rule as a `^` generic bound;
- `LookupCaptureNotCanonical` when a capture has no unique canonical
  concrete string conversion;
- a scope-key-index error when a namespace cannot conclusively expose its
  queryable keys; and
- existing `NonInjectiveStringInterpolation` and `AmbiguousStringTemplate`
  cases.

Capture-family failures are compilation errors for the whole lookup. A missing
key is not a diagnostic and has no row.

## Compatibility

This change is intentionally source- and result-incompatible with old `~`:

| Source | Old meaning | New meaning | Strict replacement |
| --- | --- | --- | --- |
| `~a` | value at literal name `a` | matching-pair map for the string value of `a` | `a` |
| `~"a"` | value at name `a` | empty or singleton pair map | `a`, or `this."a"` when quoting is required |
| `~(a, b)` | concatenation of two strict lookups | one lookup over evaluated `(a, b)` | `(a, b)` |
| `~"arg%Nat"` | unsupported by the old operator | lazy map of existing `argN` pairs | not applicable |

Canonical rendering, retained begin-block rendering, and serialized closures
must be migrated in the same change so generated strict references never
acquire the new map semantics.

## Test plan

### Parser and rendering regressions

Update `DatraParsingTests` to cover:

- `~a`, `~"a"`, `~"arg%Nat"`, and `~(a + b)` as `Lookup` nodes;
- postfix selection from a lookup result;
- rejection of a lone `~`;
- `~(a, b)` no longer expanding into two scope accesses;
- source and canonical AST round trips; and
- explicit rendering of generated strict references as `this.name` or
  `this."quoted name"`.

### Concrete and total-template regressions

Add cases proving that:

- a bound literal key produces one raw key-value row;
- an absent literal key produces an empty map;
- `~a` uses the string value of `a`;
- no lookup result contains `Just`, `nothing`, or another optional wrapper;
- a private quoted key follows ordinary lexical resolution rules;
- aliases and shadowing agree with strict identifier resolution;
- `~"arg%(2 + 2)"` produces the `arg4` row when bound and otherwise produces
  an empty map; and
- an existing binding failure propagates when its row is demanded.

### Filtering and foliage-order regressions

Add cases for:

- a scope containing only `arg0` and `arg4`, producing exactly those rows;
- declarations written as `arg4` then `arg0`, still producing foliage order;
- no matching scope names, producing an empty map without scanning an infinite
  family;
- a finite valued range filtering scope names and exposing the exact result
  cardinality;
- a two-capture finite product using the same coordinate order as `^` generic
  map access;
- `Nat; Nat`, `omega + omega`, and another transfinite product demonstrating
  `FoliageMap` interleaving;
- every retained capture tuple agreeing with its `foliageMapRankOf` rank;
- duplicate aliases not duplicating the same query spelling;
- map and range access over the lazy result; and
- lexical scope capture for rows demanded after the producing block exits.

### Capture admissibility regressions

Use the existing generic-family projection matrix as the oracle. Add paired
tests showing that each bound accepted for `^` map access is accepted as a
lookup capture and each unsupported bound is rejected during lookup
compilation.

At minimum cover:

- finite and infinite valued ranges;
- named ordered Atlas maps;
- sequential products;
- `Any` rejection;
- limit-endpoint range rejection; and
- wrappers which preserve or erase the ordered-map view.

### Canonical string regressions

Add membership, specification, projection, and lookup-filtering cases proving
that:

- `"arg4"` matches `"arg%(_x : Nat)"` and selects an existing `arg4` binding;
- `"arg(_x := 4)"` neither matches nor becomes a lookup row;
- noncanonical spellings such as padded naturals do not match;
- projections return prepared capture payloads;
- multiple holes use ordinary function-domain ordering and naming rules;
- ambiguous splits are rejected; and
- declarative `%` syntax matching remains unchanged.

### Cross-feature regressions

Update `FunctionClosureTests`, retained-block rendering tests, CLI golden
fixtures, and source snapshots containing old `~` sugar. Add a closure
round-trip proving that a strict generated dependency is not converted into a
lookup map.

## Implementation sequence

1. Add `Lookup` AST constructors and update traversal, parsing, rendering,
   and strict generated-reference rendering.
2. Retain evaluated string-template capture plans and fold total
   interpolations to concrete strings.
3. Extract or reuse the exact `^`-generic map-view builder as the capture-family
   admissibility boundary.
4. Add canonical reverse matching based on function-domain preparation.
5. Add the finite, name-only scope-key index and stable binding handles.
6. Add checked lazy-map access for deferred binding evaluation.
7. Implement concrete empty/singleton lookup and foliage-ranked template
   filtering.
8. Update existing regressions and add parser, filtering, foliage,
   admissibility, canonical matching, closure, and golden tests.

## Acceptance criteria

The change is complete when all of the following hold:

1. `~a` evaluates `a` as a string expression and never treats its spelling as
   the key.
2. Every result member is a raw `(key; value)` pair with no optional wrapper.
3. Missing keys produce no row; a missing concrete key produces an empty map.
4. Every existing scope key admitted by a template appears exactly once.
5. Template rows follow `FoliageMap` traversal order, independent of
   declaration order.
6. Result cardinality is known from scope-key filtering, so an empty or
   exhausted result never requires an unbounded scan of the template family.
7. Capture admissibility is exactly the map-access rule for `^` generics;
   `Any` is rejected during lookup compilation.
8. Total templates bypass capture enumeration and perform one concrete-key
   lookup.
9. `"arg%(_x : Nat)"` matches `"arg4"`, never `"arg(_x := 4)"`.
10. Demanding a row propagates failure from its existing binding instead of
    omitting that row.
11. Compiler-generated strict references round-trip without using `~`.
