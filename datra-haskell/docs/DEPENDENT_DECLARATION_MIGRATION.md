# Dependent-declaration migration: remaining work

## Stopping point

This document describes the current state of the `dependent-declarations`
branch at commit `f605564` plus the working-tree standard-library change to
`public`.

The standard library currently defines `public` with an argument-map-shaped
declaration row:

```datra
public := {_declarations : Collection
    {_key : InhabitedStr; _value : Any; $val?}} do
  yield (
    ((&_declaration :: _declarations) do
      yield if _declaration._key[0] = "_" then () else _declaration),
  )
```

`libs/std.datra` is user-owned during this work. Do not edit it, including for
temporary diagnostics or experiments.

The directly verified boundary is:

- evaluating `libs/std.datra` with `NoStandardLibrary` succeeds; this includes
  the outer application of `public this`;
- loading `libs/numbers.datra` with the qualified standard library still
  fails at its `public this` application;
- the focused test takes about 11 seconds and fails with:

  ```text
  libs/numbers.datra: unexpected parse failure:
  FunctionEvaluationFailed NoApplicableFunctionAlternative
  ```

Run the focused check with:

```sh
timeout 40s cabal test datra-parsing-test -f-liquid \
  --test-options='-p bundled'
```

The current failure is therefore not a failure to parse or bootstrap `Std`.
It is a failure to admit the `Numbers` namespace as the argument of the
already-defined `public` function.

## Settled semantics

These are language requirements and should not be weakened to make the tests
pass.

### One declaration abstraction

Every declaration is a `DependentDeclaration`. Simple names, evaluated heads,
quoted templates, and greedy templates use the same scope, lookup, overlap,
deferred-evaluation, named-map, and export machinery.

A simple declaration is the singleton case of the same family abstraction.
Do not restore a parallel table or evaluation path for ordinary identifiers.

### `let`

`let` only changes availability. A let declaration is visible throughout its
containing block, including before its source position. Its right-hand side is
still evaluated through the ordinary deferred-binding abstraction.

This applies equally to singleton and templated dependent declarations. Do not
introduce cycle rejection: a program such as the following is valid and may
diverge when forced.

```datra
begin
  let a := b
  let b := a
yield a
```

### `val`

`val` marks a declaration family as canonically presentable. It must be
accepted only when every greedy-template capture family participates in the
same ordinal/foliage mapping abstraction used by generic lazy map views.

Consequently, a capture such as `_Expr` cannot make a declaration `val`: there
is no enumeration of all expressions. A capture such as `Int` may be valid
because `Int` already has an ordered foliage view.

The standard-library form is a regular function whose body performs the AST
insertion:

```datra
let val := (_DependentDeclaration -> _DependentDeclaration) 'datra.val_body
```

A failed `val` declaration must report the ordinary declaration-cannot-be-val
error. Do not add errors specialized to particular capture types.

### `public`

`public` remains ordinary Datra code. Host code supplies namespace and
declaration abstractions, but it does not implement visibility filtering.

The function is transparent: returned rows remain the original declaration
descriptors, including their named-family and syntax behavior. Validating a
row may inspect its structural map view, but must not replace the row with an
ordinary Atlas-map shell.

The `$val?` field records whether a declaration is transparently treated as a
canonical value. Keep that marker until the representation is deliberately
redesigned; do not infer it again from rendered syntax.

### Collections

The standard library defines:

```datra
val Stream := &T? do yield fun T ; this
val Collection := &T? do yield (List T) | (Stream T)
```

`List T` is finite. `Stream T` has natural order type and validates members
lazily. A namespace can select either branch according to the order supplied
by its named-map/foliage projection.

Do not weaken the public boundary to `Any`, and do not materialize a namespace
as a finite host list. In particular, a syntax family with an `_Expr` capture
is represented by one declaration descriptor; it does not require enumerating
expressions. Canonical `val` families are the ones whose concrete members may
be traversed through their capture foliage maps.

### Simple function application

Function-application syntax applies only to simple identifiers, is greedy,
and participates in the ordinary syntax-rewrite federation. Collisions with
more complex syntax rules must therefore be detected by the same generic
overlap mechanism.

Host names such as `'datra.begin` are simple identifiers with module scope.
They must not require a separate eager-import or bootstrap application path.

## Implemented work

The branch now contains the following relevant pieces.

- Declaration scopes expose lazy `NamedMapView` projections. Direct name
  lookup and ordinal traversal share that representation.
- Non-`val` templated declarations contribute one descriptor row; their
  captures are metadata on the attached syntax callable rather than pretend
  concrete values.
- Canonical declaration families traverse capture products with the shared
  ordinal-indexed foliage machinery.
- `let` declarations use the existing deferred-binding evaluation path and
  are made visible ahead of their source position.
- Nested blocks install their own `this` level instead of suppressing it when
  an outer `this` exists. `it` and `this` use the ordinary contextual binding
  machinery.
- Imported declarations retain their loaded binder scope rather than
  reconstructing a module resource during invocation.
- `List` and `Stream` have distinct dependent-sum structures. Stream member
  validation is lazy, and transfinite values are no longer rejected merely
  because function argument pagination cannot enumerate them.
- Named namespace collection projections normalize transfinite source order
  through the common foliage traversal.
- Canonical template captures are rendered through the normal string
  conversion operation. The obsolete `renderCanonicalCapture` path and its
  `NoCanonicalStringConversion` error have been removed.
- `FunctionArgumentsRequireFinitePages` has been removed. Infinite maps remain
  one supplied argument until the selected domain decides how to consume
  them.
- The artificial cyclic-identifier error has been removed; recursive
  evaluation is allowed to diverge naturally.
- Temporary traces and special-case diagnostics are not part of the current
  implementation.

## Current failure

`Numbers` contains two ordinary, non-`val` declarations, `max` and `min`, and
then evaluates:

```datra
yield public this
```

The application still fails. The current generic error does not establish
whether the rejection occurs during `Collection` alternative selection,
list-member validation, function argument preparation, or evaluation of the
`public` body. Do not encode one of those possibilities as the diagnosis until
the actual failing operation has been identified.

The current host representation is produced by
`namedDeclarationMember`/`simpleIdentifierTypeValue`:

```text
canonical key, payload [, raw $val marker]
```

The shorter unmarked representation is not by itself a mismatch. In the
language, an optional argument and a `Maybe` argument coincide here:
`Maybe T` lowers through `nothing`, `nothing` lowers to `Nothing : ()`, and
that admits `()`. Therefore `$val?` can complete the omitted marker position.
Do not change the descriptor representation merely because an unmarked row
has one fewer materialized position.

`validateRecursiveElement` currently tries ordinary argument-schema
completion and, for identifier descriptors, retries against the descriptor's
structural map view. That preserves the returned descriptor. Whether this
operation is actually where `Numbers` fails remains to be established.

## Remaining implementation work

### 1. Locate the failing generic operation

Add narrow host-side regression coverage around the current public row type:

```datra
{_key : InhabitedStr; _value : Any; $val?}
```

Distinguish, without changing `libs/std.datra`, among:

- selection of the `List` or `Stream` alternative in `Collection`;
- matching one declaration descriptor against the row type;
- completion of the omitted `$val?` position through the ordinary
  `Maybe`/`nothing` path;
- preparation of the `_declarations` function argument;
- iteration and filtering inside the Datra-defined `public` body; and
- validation of the function result.

Use the same semantic operations exercised by Datra evaluation. A direct test
of an internal optional constructor is not equivalent when it bypasses the
standard-library `Maybe`/`nothing` lowering. Do not add a permanent trace,
hardcoded signature, declaration name, or special diagnostic to expose the
failure.

### 2. Keep validation and presentation separate

Collection checking may validate the descriptor's structural view, but the
selected collection member must remain the original descriptor value.

Do not:

- project every named member permanently into an ordinary map;
- erase syntax attached to a declaration-family descriptor;
- reconstruct `_key`, `_value`, `it`, or `this` through bespoke host records;
- introduce a special `public` evaluator;
- weaken the element type to `Any`.

### 3. Re-run the stopping test and inspect the next real failure

After fixing the identified operation, run:

```sh
timeout 40s cabal test datra-parsing-test -f-liquid \
  --test-options='-p bundled'
```

The immediate milestone is for both bundled module-shape checks (`Std` and
`Numbers`) to pass. Record the runtime and investigate any material increase;
the current failing run is approximately 11 seconds.

Then run focused public/import tests, especially:

- filtering of private declarations;
- transparent import of ordinary declarations;
- canonical presentation of `val` declarations;
- simple and templated dependent-declaration exports;
- nested-module `this` behavior;
- finite `List` and infinite `Stream` collection selection.

Finally run the complete test suite and `git diff --check`.

### 4. Review error cleanup

Keep failures expressed through existing generic operations. Do not restore:

- `CyclicIdentifierReference`;
- `ProductiveRecursiveReduction` as a workaround for ordinary deferred
  bindings;
- `NoCanonicalStringConversion`;
- `FunctionArgumentsRequireFinitePages`;
- errors hardcoded to a concrete declaration name, capture type, or function
  signature.

Any failed `val` foliage traversal should surface through the same generic
declaration-validity error as every other declaration that cannot be `val`.

## Useful code locations

- `app/Interpreting.hs`
  - recursive `List`/`Stream` recognition;
  - declaration named views and descriptor materialization;
  - contextual `it`/`this` bindings;
  - module export/import presentation.
- `src/DatraTypes/DatraTypes.hs`
  - `listTypeValue`, `streamTypeValue`, and recursive element validation.
- `src/DatraTypes/Evaluation/Identifier.hs`
  - simple identifier map shape and canonical-value marker handling.
- `src/DatraTypes/Evaluation/Value.hs`
  - named-map projections and foliage-normalized collection shells.
- `src/DatraTypes/Evaluation/Overload.hs`
  - evaluated argument schemas, optional slots, and row completion.
- `src/DatraTypes/Evaluation/Arguments.hs`
  - finite/transfinite argument presentation.
- `src/DatraTypes/Evaluation/OrdinalIndexedFamily.hs`
  - the shared ordered-family abstraction used by generics and canonical
    declaration captures.
- `src/DatraTypes/Evaluation/Specification/Subfederation.hs`
  - collection dependent-sum inclusion.
- `test/DatraParsingTests.hs`
  - bundled `Std`/`Numbers` module-shape check.

## Completion criteria

The migration is complete when:

1. `Std` and `Numbers` load through the same dependent-declaration pipeline;
2. `public` remains ordinary Datra and returns transparent descriptor values;
3. declaration rows satisfy the typed `_key`, `_value`, and `$val?` contract;
4. finite and infinite namespaces use `List` and `Stream` without eager
   materialization;
5. `let`, `val`, simple application, imports, and nested contextual scopes use
   their shared abstractions without identifier-specific shortcuts;
6. the focused and full test suites pass without a material performance
   regression; and
7. no temporary traces, hardcoded diagnostics, or standard-library probe edits
   remain.
