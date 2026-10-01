# Parser bootstrap: remaining work

This is an implementation handoff for finishing the declarative parser
bootstrap. The intended end state is that the ordinary parser reads a neutral
AST and declarations visible in the current Datra scope perform the second,
syntax-matching pass. `std.datra` must be an ordinary module; its only special
property is that the CLI imports `Std` by default unless the existing
no-standard-library mode is selected.

## Current pipeline

The production entry point in `app/Interpreting.hs` currently:

1. reads source with `parseDatraRawLocatedWithSourceName`;
2. loads the requested modules and the default `Std` module;
3. obtains structured rules from the declarations actually visible in scope;
4. rewrites the raw AST with `rewriteExplicitSyntax` or
   `rewriteImplicitSyntax`; and
5. evaluates the rewritten AST.

`app/SyntaxTemplateMatching.hs` owns matching one application AST against
structured templates. `app/SyntaxRewriting.hs` owns traversal, block extent,
scope changes, tentative/strict recursive passes, and local reassociation of
the neutral AST. AST output must be taken after this rewrite.

## Established invariants

- A template includes its complete literal spelling; the binding name is not
  prepended. Reverse lookup is by the maximal literal prefix before the first
  hole, so a binding and its surface spelling may differ.
- Visible declarations are attempted in declaration order. The first rule
  that matches wins. Inside that rule, matching is greedy but backtracks, and
  it may not cross the current AST boundary merely to obtain a longer match.
- `%` maps either one string or a nonempty sequence of strings to templates.
  `%>` attaches those templates to the function type. Ordinary function-call
  syntax remains available for every such function.
- A `$T` capture is accepted by ordinary evaluation/specification against
  `T`. The assembled captures must separately be a compile-time subfederation
  of the function domain. The domain never substitutes for hole validation.
- Alternative syntax functions use ordinary federation admission. Templates
  with an overlapping callable domain are rejected even if their surface
  templates differ, because the ordinary call would be ambiguous. A
  distinctness result is accepted only when proved; both refutation and an
  undecidable result reject the federation.
- Syntax rules have the same visibility as their bindings. Merely accessing
  `Module.name` or `super.name` does not activate a rule. Binding such a value
  into the current scope does. Private, non-imported bindings do not contribute
  rules.
- An inner scope can shadow an outer binding but duplicate declarations in one
  block are invalid. Values merely accessible from an outer scope are not
  automatically exported by the inner module value; `begin := begin` is a
  meaningful explicit member declaration.
- Recursive `let` declarations are discovered from `Let` AST nodes in a
  tentative pass, then the original AST is rewritten strictly with
  evaluator-backed hole checks. Do not reintroduce a token-level
  `predeclareLets` scan.
- `,` is map concatenation and `;` is sequencing inside argument maps as
  elsewhere. A postfix comma is represented by `MapConcatenation value ()`;
  separate `MapSplice`/`ArgumentMapSplice` nodes are obsolete.
- Function source syntax is `<function-type> <function-body>`. An external
  `!$~` value can inhabit `_Block` when used in that position; it does not
  universally mean “import a function body.”
- `Str` is declared as `>< (List Char)`. Its canonical expanded form is
  `>< (List Char)`, not `Str` and not `List Char`. String membership in this
  type is handled through generic dependent-sum selection; do not restore a
  `List Char` or `DependentSumSemantics "List Char"` compiler special case.

More detailed matcher invariants are in
`docs/DECLARATIVE_SYNTAX_INVARIANTS.md`.

## Remaining work

### 1. Establish a green baseline

Run the full non-Liquid suite once the worktree has been backed up:

```sh
cabal test -f-liquid all
```

The latest focused string-template tests pass, but a full suite has not been
completed after the current set of changes. Function-closure tests were
already slow and one factorial/reconstruction path appeared to stop making
progress. Diagnose that path independently; do not weaken canonical
round-trip checks or restore the removed `List Char` shortcuts to make it
finish.

### 2. Remove the superseded direct declarative parser

After the baseline is green, remove code paths that parse standard-library
word forms directly instead of passing through the post-AST rewrite. The main
audit target is `app/Parsing.hs`, especially the older syntax-aware entry
points and their cached `libraryRules`/`libraryDeclarations` bootstrap. Keep
only neutral AST reading plus the minimum structure needed to locate resource,
map, function-body, and operator boundaries.

Before deleting any provisional operator node, verify whether
`app/SyntaxRewriting.hs` still uses it as a temporary contextual tree.
`leftInfixContext` and `rightInfixContext` should contain only operators that
the neutral reader genuinely constructs before template rewriting. Word
operators now declared in `libs/std.datra` must not survive merely because an
old parser branch still recognizes them.

### 3. Finish the import bootstrap without a second syntax system

Import discovery currently has an early source/AST scan because imported
syntax rules must be known before the containing resource can be fully
rewritten. Preserve that ordering requirement, but converge on one semantic
representation of:

```datra
import "module"
import all "module"
```

Both spellings are alternatives of the declarative `import` function. Module
loading must not maintain an independent grammar for their final AST. Loaded
modules do not implicitly import `Std`; modules that need it, including
`ordinals.datra` and `numbers.datra`, declare `import all "std.datra"`
themselves. Only the entry resource receives the CLI's default `Std` import.

### 4. Eliminate remaining compiler knowledge of standard-library names

Audit `app/SyntaxDefinitions.hs`, `app/Interpreting.hs`, and
`DatraLanguage.AST.Reserved`. Native external symbols such as `datra.begin`
may map to host implementations, but the `datra.*` prefix itself must not
alter parsing or evaluation. `std.datra` must be loaded through the ordinary
module path, producing `Std`, followed by the same `import all` operation used
for any module.

`this` is a normal scope-provided binding, not a reserved parser word.
`yield` belongs to the declared `begin`/`do` templates, apart from whatever
neutral resource delimiter is strictly required before those templates can be
loaded. `import` is the declarative function above. Any remaining reserved-name
table must be limited to actual symbolic/core syntax and canonical rendering,
not used to reject ordinary identifiers.

### 5. Replace the remaining host AST-hole definitions

`_Expr`, `_Block`, and `_IdenExp` are still introduced through private
external values. Their matching behavior currently lives at the
`captureSyntaxHole` boundary. Move each rule into the implementation of its
declared Datra type so the matcher only asks ordinary membership/capture
operations. `_Block` must also expose declarations to later captures, and
binder captures must expose their names to a later body capture, without
adding template-specific parser cases.

### 6. Add declarative precedence only if ordering proves insufficient

The standard-library precedence block is ordered from lower to higher
precedence. Keep declaration order as the only precedence input until a real
counterexample demonstrates that it cannot describe the needed AST boundary.
If one exists, add precedence/associativity as data on `Template`; do not add a
new hardcoded word-operator table.

### 7. Complete syntax-template federation decisions

`compileSyntaxTemplateFederation` already requires a proved pairwise
distinction. Finish routing structured templates retained on evaluated
function values through the ordinary federation construction path. The AST
matcher should only receive admitted rules; it should never detect a tie and
throw an internal error at runtime.

## Focused regression commands

Use focused tests during cleanup; reserve the full suite for milestones and do
not run Liquid checks during this parser refactor.

```sh
cabal test -f-liquid datra-interpreting-test \
  --test-option=-p --test-option='string templates'
cabal test -f-liquid datra-parsing-test
```

Relevant regression areas include syntax aliases imported into scope,
recursive `let` template visibility, inner-scope shadowing, postfix templates,
`$Int` rejecting `Infinity`, multiple templates on one function, argument-map
comma/semicolon distinction, and `.ast` output reflecting the rewritten AST.
