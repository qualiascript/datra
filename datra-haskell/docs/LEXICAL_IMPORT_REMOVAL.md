# Lexical Import Removal and Explicit Module Inputs

## Status and scope

This document plans the temporary removal of Datra's lexical `import` feature.
It does **not** remove modules, module evaluation, qualified module access,
module-owned syntax, the implicit `Std` environment, or module provenance on
closures. Those mechanisms remain useful independently of the current import
syntax and evaluator.

Programs and tests which need an additional module will instead provide it as
an explicit command-line input:

```text
datra build --module path/to/library.datra --input program.datra
datra ast --module ordinals --input program.datra
datra interpret --module path/to/library.datra --input program.datra.ast
```

`--module` is repeatable. It establishes the modules available to the whole
compilation unit; it is not an expression, does not open their members, does
not create an `it` value, and has no lexical body.

`Std` is the exception to the explicit-input rule: it is automatically
available for ordinary commands unless the user explicitly disables it. By
default its public names and syntax are opened, matching today's CLI. The
existing `--qualified-std` mode keeps `Std` available but requires qualified
access. A new `--no-std` mode disables the automatic module entirely.

The stack rewrite algorithm is outside the scope of this work. Module-owned
syntax will continue to be supplied to it through the syntax catalog.

## Motivation

The current `import` feature combines several unrelated responsibilities:

1. Source rewriting discovers imports by partially rewriting the program.
2. The loader resolves files, recursively discovers their imports, and builds
   module syntax catalogs.
3. Runtime evaluation applies imported module federations to a synthesized
   function domain.
4. The body receives qualified module declarations, an `it` federation, and
   presentation dependencies which may escape in closures.

This makes loading a module depend on a source-level construct whose runtime
semantics are much broader than module availability. It also gives source
parsing and canonical-AST interpretation different ways to rediscover the
same external resources.

Until a replacement language design is ready, module availability should be
an explicit property of the command invocation. The language AST should not
carry paths or own filesystem loading.

## Required invariants

### Modules are not imports

A module is an evaluated resource with:

- one or more declared namespaces;
- public and private declarations;
- qualified syntax rules;
- a stable source identity; and
- provenance required to reconstruct escaped values and closures.

An import is only the current source-level operation which finds those
resources and opens them around a lexical body. Removing that operation must
not delete the module representation or its provenance.

### Module inputs are qualified

Providing `--module library.datra` installs the namespaces declared by that
module. It does not insert all exported members into the root scope. A program
uses `Library.member`, explicit `with`, or module-owned qualified syntax.

The namespace is derived from the evaluated module declaration, not from the
filename or the spelling passed to `--module`. A mismatch between filename
and namespace is therefore valid.

This does not change the special root policy for `Std`: automatic `Std` is
opened by default, qualified under `--qualified-std`, and absent under
`--no-std`. Other modules are always qualified until explicitly opened with
`with`.

### Availability is established before rewriting

All requested modules are loaded before the root source is rewritten or
evaluated. Their static syntax catalogs must be available to the stack
rewriter without evaluating selected syntax members or rematerializing parser
results. This follows the separation in
[PARSER_REMATERIALIZATION_REMOVAL.md](./PARSER_REMATERIALIZATION_REMOVAL.md).

### Canonical ASTs contain no resource paths

`datra ast` records only the semantic program. It does not serialize module
paths into the AST. Consequently, `datra interpret` must receive the same
`--module` inputs when the AST refers to those modules.

### Module installation is idempotent and collision-safe

The same resolved module supplied more than once is installed once. Two
different modules which claim the same namespace fail during command setup,
before root rewriting or evaluation. They are never resolved by flag order.

## Current flow

### Language surface and AST

`libs/std.datra` declares the `import` syntax and delegates its expansion to
`datra.import_body`. `DatraHost` lowers that expansion to:

```haskell
Import [String] Expression
```

Lowered and canonical representations repeat the concept as `ImportValue`,
`ImportForm`, and `ImportPathsForm`. Source rendering, pretty printing,
canonical parsing, traversal, normalization, and yielded-expression handling
all contain import-specific branches.

### Source discovery and loading

`parsedSourceImportInvocations` and `discoverImportInvocations` rewrite enough
of raw source to find expanded `Import` nodes. `ModuleLoading` then:

1. resolves relative paths and adds `.datra` when necessary;
2. recognizes bundled libraries;
3. reads and parses each module;
4. recursively scans its source imports;
5. detects cycles and caches resolved modules;
6. ensures qualified `Std` availability; and
7. rewrites each module with all dependency syntax catalogs.

The root rewrite finally receives the loaded modules' syntax rules through
`rewriteParsedDatraSourceWithImports`.

Canonical AST interpretation performs a second structural scan through
`loadExpressionImports`, because external paths are currently embedded in the
AST.

### Runtime lexical import

`evaluateImport` loads the requested module values from the catalog, combines
their export federations, constructs an argument schema, applies it, exposes
the resulting federation as contextual `it`, creates qualified runtime module
declarations, evaluates the lexical body, and preserves module provenance on
escaped values.

`prepareModuleResource` has a second import branch which installs requested
modules while preparing resource-level declarations. Together these paths
make import both a resource loader and a scope-forming language expression.

## Target command interface

Add a repeatable option to `build`, `ast`, and `interpret`:

```text
--module MODULE
```

All three commands also share one mutually exclusive standard-library mode:

```text
default          automatically provide and open Std
--qualified-std  automatically provide Std without opening its names or syntax
--no-std         do not provide Std
```

Thus most invocations need no `--module std`. Explicit module inputs augment
the automatic `Std` environment; they do not replace it. The same selected
standard-library mode applies while preparing requested modules, so
`--no-std` is a genuine whole-invocation opt-out rather than only hiding Std
from the root program.

The option accepts either:

- a filesystem path, resolved relative to the primary input file; or
- a bundled library name such as `ordinals`.

For `--source`, `--ast`, or stdin, relative module paths are resolved from the
current working directory. Diagnostics must display both the requested
spelling and the resolved location where applicable.

Repeated flags are processed from left to right. During the transitional
design, a later module may use namespaces and qualified syntax supplied by an
earlier module. Source-level transitive imports and import cycles do not exist;
the command line is the complete dependency list. If this ordering proves
unnecessary after test migration, module inputs can later be made explicitly
order-independent without changing the language AST.

Examples:

```text
datra build --module first.datra --module second.datra -i main.datra
datra ast --module ordinals --source 'Nat (1 up 3)' -o -
datra interpret --module ordinals --input main.datra.ast -o -
datra build --no-std --module minimal.datra -i standalone.datra
```

## Target loading pipeline

### Build and AST generation

```text
CLI module inputs
  -> establish automatic Std unless --no-std
  -> resolve and read each requested module
  -> parse/rewrite module using the selected Std mode and earlier catalogs
  -> evaluate module declarations and validate namespaces
  -> accumulate qualified runtime declarations and syntax catalogs

root source
  -> raw parse
  -> rewrite with Std plus requested module syntax catalogs
  -> canonical AST
  -> evaluate with requested modules installed       [build only]
```

### Canonical AST interpretation

```text
CLI module inputs
  -> same module preparation pipeline

canonical AST
  -> canonical parse
  -> evaluate with requested modules installed
```

The two commands share one prepared-module representation. `interpret` does
not inspect its AST for paths, and `build` does not rely on an `Import` node to
perform runtime installation.

### API shape

Replace import-oriented entry points with module-oriented ones:

```haskell
loadRequestedModules
  :: StandardLibraryVisibility
  -> FilePath
  -> [FilePath]
  -> IO (Either ModuleInputFailure PreparedModules)

rewriteParsedDatraSourceWithModules
  :: PreparedModules
  -> ParsedDatraSource
  -> Either ParseFailure (Located Expression)

interpretWithModulesAndStandardLibraryVisibility
  :: StandardLibraryVisibility
  -> PreparedModules
  -> Expression
  -> Either InterpretingError InterpretedValue
```

The exact record layout can follow existing `ModuleSource` and syntax-catalog
types. The important boundary is that `PreparedModules` contains both:

- static syntax information used by rewriting; and
- evaluated qualified module declarations used by interpretation.

It must not require the root expression to name an import operation before
those declarations become available.

## Code to retain

The following mechanisms are module infrastructure, not lexical-import
infrastructure, and remain:

- `ModuleSource`, loaded module results, and loaded declarations;
- module evaluation and public-export extraction;
- `standardModuleEnvironment` and implicit or qualified `Std` bootstrap;
- `InModule` and qualified module syntax catalogs;
- module source identity and closure reconstruction;
- `RuntimeImportedModule` and `runtimeDeclarationImport`, despite their stale
  names, until a separate mechanical rename;
- the behavior of `importLoadedModule`, renamed to `installLoadedModule` when
  doing so keeps the migration readable;
- closure dependency lookup through a module's retained scope;
- generic scope-building helpers whose names contain `importScope` but which
  do not implement the lexical import expression;
- `importNamedMembers` where it denotes a module's public named view; and
- module validation errors such as `ImportedModuleRequiresBlock` while they
  still describe invalid module structure.

Renaming all remaining uses of the word “import” is not a prerequisite. Names
should change only when their responsibility is clear and the rename does not
obscure the functional migration.

## Code to remove

### Language and canonical representation

Remove:

- `Expression.Import`;
- `OperatorExpression.ImportValue`;
- `ImportForm` and `ImportPathsForm`;
- every canonical parser, renderer, pretty-printer, traversal, normalization,
  lowering, and yielded-expression branch dedicated to those constructors;
- the `import` declaration in `libs/std.datra`; and
- `datra.import_body` in `DatraHost`.

Afterward, `import ...` is ordinary unresolved source syntax. It receives no
special parser or interpreter diagnostic until a future import design exists.

### Discovery and recursive source loading

Remove:

- `parsedSourceImportInvocations`;
- `discoverImportInvocations`;
- `importInvocation`;
- `loadSourceImports` and
  `loadSourceImportsWithStandardLibraryVisibility`;
- `loadExpressionImports`; and
- recursive dependency scanning, import-cycle detection, and caches whose
  only purpose is transitive source imports.

Refactor `ModuleLoading` into a smaller `ModuleInputs` module which loads the
explicit ordered list. Keep caching by resolved path only where it provides
idempotence for repeated flags.

### Runtime lexical behavior

Remove:

- `evaluateImport`;
- `importDomainValue`;
- `importArgumentDeclaration`;
- `prepareModuleResource`'s `Import` branches and local
  `importQualified` helper; and
- lexical-import-specific `it`, synthesized function application, overlap,
  and escape behavior.

The new interpreter entry point must proactively install prepared module
declarations. Merely extending the existing module catalog is insufficient:
today `interpretWithImports` supplies a catalog while `evaluateImport` performs
the actual scoped installation.

### Diagnostics

Replace `ModuleLoadFailure` import-discovery cases with errors specific to
explicit module inputs, for example:

```haskell
data ModuleInputFailure
  = ModulePathResolutionFailed FilePath FilePath String
  | ModuleReadFailed FilePath FilePath String
  | ModuleParseFailed FilePath ParseFailure
  | ModuleNamespaceCollision String FilePath FilePath
```

`ImportScanFailed`, `ImportPathResolutionFailed`,
`ImportedModuleParseFailed`, and `CyclicModuleImport` disappear with source
discovery and recursive imports. Structural module-evaluation diagnostics are
retained; they can be renamed separately if their terminology becomes
misleading.

## Test migration

### CLI tests become the integration boundary

Move behavior that genuinely requires external modules to CLI tests using
`--module`. Cover at least:

- qualified value access;
- a declared namespace independent of the filename;
- two modules in one compilation unit;
- public exports and private-member rejection;
- qualified module-owned syntax;
- closure provenance and reconstruction;
- explicit `with` over supplied modules;
- bundled modules such as `numbers` and `ordinals`;
- repeated identical module flags;
- missing, unreadable, malformed, and namespace-colliding module inputs; and
- equivalent module availability for `build`, `ast`, and `interpret`.

The generated-AST test must demonstrate the two-stage contract explicitly:
run `ast --module ...`, then run `interpret --module ...` on its output.

### Delete tests of the removed language feature

Remove expectations specific to:

- import-body return values;
- nested or lexical imports;
- import scopes leaking through functions or maps;
- the contextual `it` federation created by import;
- direct application of the `import` syntax adapter;
- transitive source imports; and
- import-cycle detection.

### Suite-specific changes

- `DatraParsingTests`: remove `Import` AST examples, generators, and canonical
  round trips.
- `DatraCliTests`: replace import-discovery coverage with a temporary module
  file supplied by `--module`.
- `Datra.Interpreter.ModuleTests`: retain pure module evaluation tests where
  useful; move filesystem and command integration cases to CLI tests.
- `FunctionClosureTests`: convert module-dependent reconstruction cases to
  two-stage CLI tests, or remove them temporarily if they only exercise the
  deleted lexical wrapper.
- `DatraInterpretingTests`: remove `requireOrdinalLibraryImports` and
  `withOrdinalLibrary`; run external-module cases through the CLI boundary or
  construct their non-loading semantic values directly.
- `Datra.TestSupport`: remove `runModuleProgram` and its `ModuleFailure`
  wrapper after callers migrate.
- integration fixtures such as `composed_features.datra`: remove lexical
  import wrappers and supply the dependency from the test command.
- delete import-only fixtures such as cycle pairs and nested import chains;
  retain module fixtures which test namespaces, exports, syntax, or closures.
- update the Cabal module list from `ModuleLoading` to `ModuleInputs` and drop
  test modules only when all retained assertions have moved.

## Implementation sequence

### Phase 0: lock the transitional contract

1. Record current parser, CLI, module, and `Std` baselines.
2. Add focused tests for path resolution, namespace derivation, qualified
   access, module-owned syntax, and all three Std visibility modes.
3. Keep known parser/`Std` failures separate from this migration.

### Phase 1: add explicit module inputs alongside import

1. Add `[FilePath]` module fields to all three command constructors.
2. Implement `moduleOption = many (strOption (long "module" ...))`.
3. Extend the standard-library option with an explicit `--no-std` case while
   retaining default opened Std and `--qualified-std`.
4. Introduce the shared `PreparedModules` loading/installing boundary.
5. Make root rewriting consume its syntax catalogs.
6. Make root evaluation consume its qualified runtime declarations.
7. Test `build`, `ast`, and `interpret` before deleting the old path.

This phase prevents test migration from depending on a half-removed language
feature.

### Phase 2: migrate tests and fixtures

1. Convert retained module behavior to `--module`.
2. Remove assertions which exist only for lexical import semantics.
3. Rewrite fixtures so their root programs contain no import wrapper.
4. Verify closure and qualified-syntax cases still exercise real module
   provenance rather than inlined declarations.

### Phase 3: remove the language surface

1. Delete the Std and host syntax declarations.
2. Delete `Import` from semantic, lowered, and canonical ASTs.
3. Remove all import-specific syntax plumbing.
4. Run parser properties to catch incomplete traversal or rendering removal.

### Phase 4: remove discovery and lexical evaluation

1. Delete raw-source and canonical-AST import scans.
2. Delete recursive source-import loading and cycle handling.
3. Delete lexical import evaluation and resource-preparation branches.
4. Rename public APIs from `WithImports` to `WithModules`.
5. Verify prepared modules are installed exactly once before root evaluation.

### Phase 5: simplify boundaries and diagnostics

1. Reduce `ModuleLoading` to explicit module-input preparation.
2. Replace import-discovery diagnostics with module-input diagnostics.
3. Rename `importLoadedModule` to `installLoadedModule` if the remaining call
   sites all use installation semantics.
4. Leave broader provenance and scope-helper renames for isolated cleanups.

### Phase 6: final audit

Run focused searches for removed surface and flow names, then run the complete
build and test suites. Any remaining occurrence of “import” must be classified
as one of:

- retained internal module provenance;
- a generic scope-building helper awaiting a later rename;
- historical prose intentionally describing the removed feature; or
- stale code which must be deleted.

## Acceptance criteria

The migration is complete when:

1. `build`, `ast`, and `interpret` accept repeatable `--module` inputs.
2. `Std` is automatically available and opened by default,
   `--qualified-std` retains qualified-only availability, and `--no-std`
   disables it for the whole invocation.
3. Requested module namespaces and qualified syntax are available before root
   rewriting and evaluation.
4. No module member is opened implicitly by `--module`.
5. Repeated identical modules are idempotent and namespace collisions fail
   deterministically during setup.
6. Canonical AST output contains no module paths and `interpret` works when
   given the same explicit module inputs.
7. `Expression`, `OperatorExpression`, and canonical forms contain no import
   constructor.
8. Std contains no `import` syntax rule and `DatraHost` contains no
   `import_body`.
9. Source and AST parsing do not scan for imports.
10. The interpreter contains no `evaluateImport`, import-domain synthesis, or
   import-specific resource-preparation branch.
11. Automatic and qualified Std bootstrap, module exports, module-owned
    syntax, explicit `with`, and closure provenance continue to work.
12. The stack rewrite algorithm is unchanged.
13. Parsing and Std-loading failures already tracked elsewhere are neither
    hidden nor broadened by this cleanup.

Useful final searches include:

```text
rg 'ImportValue|ImportForm|ImportPathsForm|import_body' app src libs test
rg 'parsedSourceImportInvocations|discoverImportInvocations|importInvocation' app src test
rg 'evaluateImport|importDomainValue|importArgumentDeclaration' app src test
rg 'WithImports|loadSourceImports|loadExpressionImports' app src test
```

## Non-goals

This migration does not design the eventual replacement for source-level
imports. It also does not:

- remove or flatten module namespaces;
- open command-supplied module members globally;
- serialize filesystem paths into canonical ASTs;
- change `with` ambiguity semantics;
- redesign public/private export calculation;
- change the stack rewrite algorithm;
- finish the broader parser rematerialization cleanup; or
- solve unrelated interpretation behavior merely because a migrated test
  exposes it.

Those concerns should remain separately diagnosable while the obsolete
lexical import path is removed.
