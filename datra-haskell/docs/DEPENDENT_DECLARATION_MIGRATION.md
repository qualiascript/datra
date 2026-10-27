# Dependent-declaration migration: PR finish handoff

## Current snapshot

- Repository: `datra-haskell`
- Branch: `dependent-declarations`
- Commit: `b8b856c` (`origin/dependent-declarations`)
- The worktree was clean before this document was replaced.
- The remaining completion gate is the dependent interpreter slice. Do not
  broaden the implementation until the failures below are understood through
  their existing generic abstractions.

Run the gate with:

```sh
timeout 180s cabal test datra-interpreting-test -f-liquid \
  --test-option=-p --test-option=dependent
```

Latest result:

```text
18 of 27 passed
9 of 27 failed
test time: 4.07s
whole command: 8.00s
peak RSS: 510848 KB
```

The build also reports one warning:

```text
app/Interpreting.hs:3340:53: -Wname-shadowing
appendPart ... (converted, captureSchema)
```

Rename that local binding during final cleanup.

## Remaining failures

### 1. Closed function reconstruction depends on `Std`

Test:

```text
canonical function reconstruction
  three dependency levels reconstruct independently
```

Location: `test/Datra/Interpreter/FunctionClosureTests.hs`.

Program under test:

```datra
base := 2
step := base + 1
next := step + 1
yield ({n? : Int} -> Int do yield n + next)
```

The original function is evaluated and rendered, the rendered expression is
parsed with the production parser, and the call is then evaluated through
`interpretClosedExpression`. That evaluator intentionally creates only a
Datra host root; it imports neither `Std` nor other modules.

Current failure:

```text
ModuleEvaluationFailed (ModuleNotLoaded "Std")
```

First inspect the rendered `text` in `roundTripWith`/`assertClosedCall` and
locate the retained `InModule "Std"` or equivalent dependency. Follow it
through:

- `closureResolver` and its `resolveDependencyModule` branch in
  `app/Interpreting.hs`;
- `valueExpression`, `closedSourceExpression`, and `defaultDefinitionScope`;
- `closeFunction`/`inlineDependencies` in `app/FunctionClosure.hs`.

The fix must make the rendered closure contain every dependency needed by its
body without requiring an ambient module. Do not make
`interpretClosedExpression` import `Std`; that would invalidate the property
this test is proving.

Focused check:

```sh
cabal test datra-interpreting-test -f-liquid \
  --test-option=-p \
  '--test-option=/canonical function reconstruction/&&/three dependency/'
```

### 2. Rewritten imported modules fail body validation

Five tests fail with exactly:

```text
ModuleEvaluationFailure OperationHasNoEffect
```

Tests:

- `declared name is independent of filename`
- `exported dependent declaration supports lookup`
- `scope-protected dependent declaration supports lookup`
- `import accepts a dependent identifier federation`
- `import accepts mixed simple and dependent binders`

Locations:

- tests: `test/Datra/Interpreter/ModuleTests.hs`
- fixtures:
  - `test/fixtures/modules/different_filename.datra`
  - `test/fixtures/modules/dependent_declarations.datra`
  - `test/fixtures/modules/dependent_export.datra`
  - `test/fixtures/modules/mixed_export.datra`

`OperationHasNoEffect` has one production site:
`validateFunctionBodyParts` in `app/Interpreting.hs`. Therefore these failures
occur while validating a rewritten `FunctionBody` or `Begin` entry, before
the intended module projection completes. Inspect the `ModuleSource` values
returned by `loadSourceImports` and identify the exact pre-yield entry which
no longer satisfies one of the validator's accepted categories:

- `dependentDeclaration part`;
- `Let`;
- `Val`; or
- an active assertion.

Fix the producer/validator representation mismatch. Do not suppress
`OperationHasNoEffect` globally and do not exempt these fixtures by name.

Relevant module architecture:

- `ModuleLoading` parses and rewrites each `ModuleSource` once and caches it by
  path.
- `loadedModuleResultWithBase` evaluates one module instance and produces
  `LoadedModuleBinder` values carrying both the evaluated value and its
  definition `Scope`.
- `ImportedBinding` retains that scope. `lookupModuleDefinitionScope` must
  prefer it; qualified `.`/`InModule` evaluation must not evaluate the module
  again in the caller's local scope.
- Module members remain declaration descriptors. Consumers obtain the payload
  through `moduleMemberPayload`, which uses ordinary map access at ordinal
  `1`.
- `moduleNamedMembers` uses the normal finite collection projection and falls
  back to the declared-family manifest for transfinite named maps. It must not
  enumerate a `Stream`.
- `public` is ordinary Datra code. Host code must not replace its descriptors
  with ad-hoc records or implement visibility filtering itself.

Useful focused checks:

```sh
cabal test datra-interpreting-test -f-liquid \
  --test-option=-p --test-option=modules
```

For a smaller first probe:

```sh
cabal test datra-interpreting-test -f-liquid \
  --test-option=-p '--test-option=/modules/&&/declared name/'
```

### 3. Generic dependent sums have three evidence/dispatch regressions

Locations: the `generic sums` group in
`test/Datra/Interpreter/StandardLibraryTests.hs`.

#### Named optional generic witness

Program:

```datra
Pair := (^T? :: Any) -> Any do yield (value? : T)
yield {T : Nat; value : 5} of Pair
```

Expected `true`; currently returns `false`. The positional equivalent passes,
as does rejection of a value outside the selected fibre. This narrows the
problem to preservation/routing of the explicit `T` name, not the basic
dependent-sum validator.

Trace the value through these generic paths:

- `argumentRows` in `src/DatraTypes/Evaluation/Arguments.hs`;
- `splitExistentialRow` and `validatePackageRow` in `app/Interpreting.hs`;
- `suppliedArgumentValue` in
  `src/DatraTypes/Evaluation/Overload.hs`;
- argument-map identifier matching in
  `src/DatraTypes/Evaluation/Specification/ArgumentMap.hs`.

`splitExistentialRow` must reuse the same name-erasure/routing evidence as
ordinary function application. Do not add a `Pair`, `T`, or two-slot special
case.

#### Forward and reverse specification

Programs:

```datra
Pair := (^T? :: Any) -> Any do yield (value? : T)
yield ({T : Nat; value : 5} ~> Pair) of Pair
```

```datra
Pair := (^T? :: Any) -> Any do yield (value? : T)
yield (Pair <~ {T : Nat; value : 5}) of Pair
```

Both should return `true`; both currently fail with:

```text
FunctionEvaluationFailed ExpectedFunctionValue
```

That error is constructed only by
`Evaluation.TypeFamily.Function.specifyFunction`. Inspect why a package value
carrying successful specification evidence is dispatched as a function
specification merely because `Pair` has both a function representation and a
dependent-sum view.

Relevant generic architecture:

- A generic-sum function keeps its ordinary function representation and gains
  an auxiliary `EvaluatedDependentSum` capability through
  `withDependentSumView`.
- Successful `specifyValues` keeps the source's runtime representation and
  attaches the proven target through `withSpecificationTargetEvidence`.
- `specifyValues` and `decideValueSubfederation` must choose between the
  function and dependent-sum capabilities from the actual source/target
  operation, rather than from a concrete parser shape.
- Forward and reverse syntax lower to the same `MapSpecification` evaluation;
  fix their shared semantic dispatch instead of treating them separately.

Focused check:

```sh
cabal test datra-interpreting-test -f-liquid \
  --test-option=-p '--test-option=/generic sums/'
```

## Invariants to preserve while fixing the failures

- All declarations use `DependentDeclaration`; simple identifiers are the
  singleton case, not a parallel binding implementation.
- Declaration overlap is decided through evaluated federation machinery
  (`eitherValue`), including string-template name families. Do not add lexical
  prefix, numeric, or parser-encoding overlap special cases.
- Validation evidence required by later evaluation must travel with the value;
  do not validate through a projected shell and then discard the proof.
- `it` and `this` use ordinary contextual-binding flows. Do not introduce a
  declaration-only evaluator for either name.
- `List T` is finite and `Stream T` has order type omega. Their separation is
  the generic map-length rule in `Evaluation.Either`, not recognition of a
  concrete recursive AST shape. The standard-library stream definition is:

  ```datra
  val Stream := &T? do yield fun (T ; this)
  ```

- Do not edit `libs/std.datra` to work around these failures.

## Completion sequence

1. Make the five module tests pass and run the whole `modules` group to catch
   projection/re-evaluation regressions.
2. Make the closed reconstruction test pass without giving the closed
   evaluator an implicit module environment.
3. Make all three generic-sum tests pass through shared argument/specification
   machinery.
4. Run the complete dependent slice until it reports `27 of 27 passed`.
5. Run:

   ```sh
   timeout 90s cabal test datra-parsing-test -f-liquid \
     --test-option=-p --test-option=bundled
   cabal build all -f-liquid
   git diff --check
   rg -n 'Debug\.Trace|traceM|traceShow|traceShowId|\btrace\s*\(' \
     --glob '*.hs' .
   ```

6. Remove dead diagnostic helpers and any temporary instrumentation before
   committing. The final build should be warning-free.
