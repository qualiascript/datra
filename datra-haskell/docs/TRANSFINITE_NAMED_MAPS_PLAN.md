# Transfinite named maps

## Goal

Allow named maps with transfinite final order types to participate in
`public`, canonical-value declarations, module exports, and named scope lookup without converting
their order type to a `Natural`, enumerating the entire map, or hanging while
trying to prove that an infinite traversal is complete.

This is deliberately separate from the removal of the `~~` operator. The
current `'datra` work should retain its finite module-export boundary until the
changes below are implemented together.

## Current finite boundary

`DatraHost.namedMembers` currently obtains the final order type of an
`InterpretedMap`, converts it with `naturalAtOrdinal`, indexes every finite
position, and returns a completed list:

```haskell
namedMembers
  :: InterpretedValue
  -> Either InterpretingError [(String, InterpretedValue)]
```

That type commits the operation to all of the following:

1. Every member is visited before the outer `Right` can be returned.
2. Every member is validated as a simple identifier value up front.
3. The complete set of names is materialized as a Haskell list.
4. A transfinite map is rejected because its order type cannot be converted to
   a `Natural`.

The main consumers inherit that finite assumption:

- `publicValue` filters the completed list and constructs a new finite map.
- declaration-map construction attaches canonical-value metadata to the
  individually marked members while constructing a new finite map.
- module syntax discovery enumerates every exported member.
- scope construction turns every exported member into a finite binding list.
- module export-name reporting returns a complete list of names.

`argumentMapMembers` avoids reconstructing the written members of an argument
map from its erased Atlas-map projection, but it still returns a finite list.
It is therefore not the transfinite abstraction.

## Why `FoliageMap` is not a direct replacement

`FoliageMap` gives a fair natural-number traversal of positions below an
arbitrary ordinal. It is useful when an operation needs to observe a finite
frontier of an infinite family, as overload selection does.

Replacing the current range with:

```haskell
mapMaybe (foliageMapPositionAt traversal) [0 ..]
```

would not make `namedMembers` lazy in a useful sense. `traverse` over the
result still has to reach the end before it can return `Right members`; an
infinite successful traversal never reaches that point.

Foliage order also is not ordinal order. Fair traversal deliberately reaches
later transfinite lanes instead of exhausting an earlier infinite lane. It
must not be used to reconstruct a map, define member precedence, compact a
filtered map, or determine canonical source order.

The appropriate uses of foliage traversal in this work are bounded
observation, diagnostics, and tests. It is not the representation of a named
map.

## Required representation

Named structure must be retained when a map is constructed instead of being
recovered later by enumerating its values.

Introduce an internal capability along these lines:

```haskell
data NamedMapView = NamedMapView
  { namedMapOrderType :: Ordinal
  , namedMemberAt
      :: Ordinal
      -> Either InterpretingError (Maybe NamedMember)
  , namedMemberByName
      :: String
      -> Either InterpretingError (Maybe NamedMember)
  , selectNamedMembers
      :: NamedSelection
      -> Either InterpretingError NamedMapView
  }

data NamedMember = NamedMember
  { namedMemberName :: String
  , namedMemberValue :: InterpretedValue
  }

data NamedSelection
  = AllNamedMembers
  | PublicNamedMembers
```

The exact names are provisional. The important properties are:

- ordinal access remains ordinal-indexed;
- lookup by identifier does not scan an unbounded member sequence;
- failure remains an `InterpretingError`, rather than becoming `Nothing` or a
  deferred Haskell exception;
- visibility selection is supplied by the producer and preserves a defined
  result order;
- consumers can request one member without demanding all members;
- finite enumeration is an optional observation, not the primary
  representation.

Add the capability to `InterpretedValue`, in the same style as the existing
ordered-map and dependent-sum views. Do not overload
`interpretedMapComponents`: that field is an auxiliary semantic presentation
and is neither ordinal-indexed nor a reliable source-level member list.

## Construction rules

Every map constructor that can preserve named structure must construct or
compose a `NamedMapView` at the same time as its ordinary `InterpretedMap`.

### Finite map literals and argument maps

- Build an ordinal accessor and a strict finite name index from the written
  members.
- Preserve the current duplicate-name and private-name behavior.
- Retain argument-map written members without a separate special-case query.
- A positional or unnamed member makes the named-map capability unavailable,
  or produces the same checked failure currently returned by `namedMembers`.
  Choose one rule and apply it consistently at construction time.

### Concatenation, sequence, and expansion

- Compose ordinal access using the same ordinal arithmetic as the underlying
  map operation.
- Compose name lookup without enumerating either operand.
- Preserve the existing left/right precedence for duplicate names.
- Compose visibility selection from the operands' selected views.
- Do not derive the view by inspecting canonical rendering.

### Lazy and dependent maps

- Extend lazy map construction with an optional named-view producer.
- A producer must provide both ordinal access and name lookup. An arbitrary
  function `Ordinal -> Maybe InterpretedValue` is insufficient to answer an
  absent name query conclusively.
- Families with computable names, such as indexed templates, should provide a
  corresponding name decoder or name index as part of their construction.
- A lazy map without this capability remains an ordinary map and is rejected
  when used as a namespace, rather than being searched forever.

### Specifications and wrappers

- Identifier assignments, specifications, protection wrappers, canonical
  presentations, and total-map wrappers must preserve the named capability
  when they preserve ordinary map access.
- Operations that change member identity or order must explicitly transform
  or drop the capability.
- Add law tests ensuring that a retained named view agrees with ordinary map
  access at every tested ordinal.

## Canonical-value declarations

`val` is declaration metadata, not a transformation over a completed map.
When a declaration scope constructs a named member, its retained declaration
metadata determines whether that one identifier receives the
`$CanonicalValue` marker:

```text
position p -> source declaration p -> construct and conditionally mark member p
name n     -> source declaration n -> construct and conditionally mark member n
```

The named-map view must therefore retain the canonical-value bit beside each
member's name. Concatenation, selection, scope snapshots, and lazy ordinal
access must preserve that bit without inspecting or transforming neighboring
members. There is no global already-marked proof: invalid duplicate `val`
syntax is rejected when the declaration is formed.

## `public`

`public` is harder than per-member canonical marking because it filters and compacts members.
For a transfinite source, neither the result order type nor the source position
of result position `p` can generally be calculated by scanning successors:
that scan never crosses an `omega` boundary.

The named-map producer must therefore implement `PublicNamedMembers` as a
selection capability. The consumer must not attempt to derive it with
`filter`, a Haskell list, or foliage order.

The selected view must specify:

- its result order type;
- ordinal access in the selected order;
- direct lookup by public name;
- the treatment of duplicate names;
- a proof or invariant that every selected member is a valid named export.

Finite literal maps can derive this view eagerly. Symbolic transfinite maps
must provide it symbolically. Maps that cannot provide it are not valid inputs
to `public`.

## Scope and module lookup

`ScopeBindings` is currently list-based. Substituting an infinite lazy list is
not sufficient: lookup of an absent identifier would diverge.

Split bindings into finite lexical bindings and namespace resolvers:

```haskell
data Scope = Scope
  { scopeBindings :: ScopeBindings
  , scopeNamespaces :: [NamedBindingResolver]
  , ...
  }

type NamedBindingResolver =
  String -> Either InterpretingError (Maybe ScopeBinding)
```

Resolution order must remain explicit so lexical shadowing and imported-module
precedence do not change. A resolver must answer both hits and misses without
enumerating an infinite namespace.

Update these paths to use direct named lookup:

- module member access;
- opened module scopes;
- imported bindings;
- closure dependency resolution;
- canonical qualified-name lookup;
- shadowing-consistency checks.

APIs that genuinely request all export names must distinguish finite and
symbolic namespaces. They may return a finite list only when the view proves
finiteness; otherwise they need a summary or must report that enumeration is
unavailable.

## Syntax exports

Parser syntax cannot be discovered by searching an unbounded namespace at
parse time. Keep syntax export discovery as a separate finite manifest:

```haskell
data ModuleInterface = ModuleInterface
  { moduleValueExports :: NamedMapView
  , moduleSyntaxExports :: [SyntaxRule]
  }
```

A transfinite value namespace may therefore coexist with finitely many syntax
rules. Construct the syntax manifest from declarations when the module is
loaded; do not enumerate all values looking for functions with syntax bodies.

This also removes the current accidental coupling between value enumeration
and parser-rule installation.

## Canonical representation

Rendering an arbitrary transfinite map by listing every member is impossible.
Canonicalization must retain a finite symbolic source for any transfinite
named map that can escape evaluation.

- Preserve the constructor/application presentation that generated the map.
- Named access should compose with that presentation without enumerating the
  namespace.
- canonical-value metadata and `public` should compose with symbolic
  presentations for their selected views.
- If no finite symbolic presentation exists, canonical string conversion must
  return its existing typed failure rather than force the map.
- Canonical round trips must not demand export-name enumeration.

## API migration

1. Add `NamedMapView` and observations for ordinal access, direct name lookup,
   visibility selection, and proven finite enumeration.
2. Populate the view in finite map and argument-map constructors.
3. Compose the view through concatenation, expansion, specifications, and
   wrappers.
4. Replace `DatraHost.namedMembers` consumers with the narrow observation each
   operation actually needs.
5. Retain each declaration's canonical-value bit in its named member and add
   `$CanonicalValue` only when that member is materialized.
6. Reimplement `publicValue` using the producer-supplied public selection.
7. Add namespace resolvers to `Scope` and migrate module/open-scope lookup.
8. Separate finite syntax manifests from value exports.
9. Restrict complete export-name APIs to views proven finite.
10. Remove `namedMembers` once no runtime path needs complete eager
    enumeration.

At no stage should an infinite Haskell list replace the current finite list.
Every intermediate step must make absence, finiteness, and completeness
explicit.

## Tests

Add focused tests before removing the finite fallback:

- named access below `omega`, at `omega`, and after `omega`;
- access in maps with order types `omega + n`, `omega * 2`, and a higher
  Cantor-normal-form lane;
- absent-name lookup terminates with `Nothing` or the appropriate typed error;
- `val` preserves the exact containing order type and marks its member at
  `omega`;
- canonical and transparent declarations coexist in recursively constructed
  maps without changing each other's presentation;
- invalid nested declaration modifiers are rejected without enumerating the
  containing map;
- `public` preserves the producer-declared public order across a transfinite
  boundary;
- private members around `omega` do not shift public positions incorrectly;
- lexical bindings still shadow namespace-resolved bindings;
- an infinite value namespace with a finite syntax manifest parses normally;
- closure capture of one transfinite module member does not enumerate the
  module;
- canonical rendering and reparsing of a selected member are idempotent;
- requesting a complete export list from a non-finite namespace fails
  promptly;
- no test relies on a timeout to establish termination.

Use foliage traversal in property tests to sample positions fairly across the
ordinal lanes. Compare every sampled named-view result with ordinary ordinal
map access. Do not use foliage order as the expected source order.

## Completion criteria

This work is complete when:

- no named-map operation converts an arbitrary order type with
  `naturalAtOrdinal` merely to discover members;
- `public`, canonical-value export presentation, module access, and scope
  lookup operate through retained named capabilities;
- lookup at and beyond `omega` is covered by deterministic tests;
- absent-name lookup cannot diverge through enumeration;
- syntax discovery remains finite and independent of value-namespace size;
- finite programs retain their current behavior and diagnostics;
- canonical round trips do not force a transfinite namespace.
