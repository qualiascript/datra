# Parser cleanup plan

## Purpose

The source parser is temporary bootstrap infrastructure. Its responsibility
must shrink as dependent declarations and standalone language operators take
ownership of syntax. This cleanup removes stale paths, consolidates the
remaining concrete operator grammar, and makes unresolved source presentation
flow directly into the AST without being discarded and reconstructed.

The immediate goal is deliberately narrower than replacing the parser. After
this work:

- parsing tests pass;
- numerical parsing remains fixed;
- exact declaration matching retains spaces and newlines exactly;
- structural `$!` matching continues to ignore presentation whitespace;
- standard-library bootstrapping reaches the existing `Args` failure at
  `yield ((^n? :: Nat) do yield slots[0..n])`;
- no earlier parser, module-scanning, or syntax-environment failure is
  introduced; and
- the parser contains fewer paths and fewer responsibilities than it did
  before the cleanup.

This is a subtractive refactor. It must not introduce a replacement lexer,
parallel presentation model, compatibility layer, or generalized parser
framework.

## Target parser boundary

The ordinary source parser should retain only responsibilities that cannot yet
be expressed safely through dependent declarations or standalone operators:

1. Recognize concrete delimiters and preserve syntax boundaries.
2. Parse identifiers, quoted strings, and literal atoms.
3. Preserve unclaimed punctuation and whitespace as
   `UnresolvedSyntaxLiteral`.
4. Parse the core operators that have not yet moved to backtick declarations.
5. Establish the concrete extent of a comment invocation.
6. Construct the unresolved AST consumed by syntax rewriting.

The parser should not:

- assign application meaning to spaces;
- assign sequencing meaning to newlines;
- implement comment discard semantics;
- decide declarative matcher mode;
- recover source presentation after a token parser has erased it;
- normalize generic binders or function types;
- duplicate semantic constructors already owned by a language abstraction;
- render and reparse expressions to make parsing decisions; or
- inspect another complete grammar through lookahead.

The long-term direction is for this boundary to continue shrinking. Operators
such as `+` remain parser-owned only until the backtick form can express and
bootstrap them. This cleanup must not transfer those operators prematurely,
but it must also avoid expanding or polishing their temporary parser-specific
architecture.

## Design invariants

### One unresolved presentation representation

`UnresolvedSyntaxLiteral` is the only representation for unclaimed source
presentation. It may contain punctuation, spaces, tabs, carriage returns, or
newlines.

The cleanup must not add any of the following:

- a neutral lexer;
- a presentation AST;
- an unresolved token record;
- a separator record;
- an adjacent-value constructor;
- a layout node;
- a Boolean matcher-mode flag; or
- a string sentinel identifying a parser or matcher mode.

`ElidedSyntax` remains the distinct transient value for syntax which has been
consumed without producing an expression. It must never be represented or
rendered as `AtlasMap []` or `()`.

### Matching modes remain separate

Each declarative matcher knows its mode from its typed matcher plan and uses
only that mode's projection.

- Exact `$` matching compares retained presentation character for character.
  Spaces, tabs, carriage returns, newlines, and punctuation are literal data.
- Structural `$!` matching ignores presentation whitespace while matching its
  structural operands.
- Native application, comment, line-sequence, and horizontal-application
  rules retain their distinct typed plans and identities.
- Hole validation begins only after the selected matcher mode succeeds.

The cleanup may share application-spine utilities and typed match evidence. It
must not merge exact and structural literal matching.

### Dependent rule order remains semantic

The comment rule remains the earliest built-in dependent rule. It captures the
source following `#` through the active line or syntax boundary and expands to
`ElidedSyntax`.

The line-sequence and horizontal-application rules remain the final built-in
fallback rules. Visible declarations must be able to inspect exact retained
presentation before either fallback assigns meaning to it.

The rewrite scheduler must not change. The rules must continue to compose in
their current introduction order without scheduler re-enumeration.

### Operator ownership is typed

Every concrete operator recognized by the remaining parser must have a typed
owner in the existing operator abstraction. Raw source spellings must not be
dispatched independently throughout `Parsing`.

In particular:

- `.` becomes the source spelling of a typed scope-access operator;
- `::` becomes the source spelling of a typed generic-bound operator;
- `;` is owned by the typed sequential operator; and
- overlapping symbolic spellings use one shared maximal-run rule rather than
  per-operator negative lookahead.

Operator spelling is concrete syntax data. Matcher modes, semantic identities,
and parser control flow must not be encoded in operator strings.

### Lookahead is local

Remaining lookahead may establish only a local non-consuming boundary, such
as:

- the closing delimiter of the active syntax boundary;
- the terminator of a quoted string or comment remainder; or
- whether a complete maximal symbolic run equals a registered operator.

Lookahead must not:

- parse a complete expression;
- invoke the dependent-argument grammar;
- duplicate the operator precedence table;
- enumerate lower-precedence operators manually; or
- parse the same successful structure a second time.

## Aggressive deletion policy

Deletion is the default response to stale code.

1. Do not leave an old path beside its replacement.
2. Delete compatibility wrappers after migrating their callers.
3. Inline single-use helpers unless they state a real language invariant.
4. Delete arguments, constructors, and branches that cannot affect behavior.
5. Delete validation already guaranteed by the consuming parser.
6. Delete imports, exports, comments, tests, and documentation that describe a
   removed path in the same change.
7. Do not generalize transitional `$!` or core-operator machinery.
8. Use `rg` after each work package to prove that removed concepts have no
   remaining references.
9. Prefer a net reduction in source-parser code at each checkpoint. A new
   shared helper is justified only when it replaces and deletes more ad-hoc
   behavior than it introduces.
10. Keep the canonical AST reader separate from ordinary source parsing so its
    needs cannot justify retaining source-parser complexity.

## Non goals

This cleanup does not:

- implement the backtick declaration form;
- implement the `_StrExpr` replacement;
- transfer arithmetic operators such as `+` into dependent declarations;
- remove `$!` before its backtick replacement exists;
- redesign syntax-rewrite scheduling;
- make interpreting-focused tests the acceptance gate while dependent
  declarations remain in progress;
- add a new source token model; or
- reintroduce the dropped parenthesized-comment test.

The eventual backtick implementation will remove `$!` and allow more core
operators to leave the parser. This plan only removes infrastructure which is
already stale or can be consolidated without that feature.

## Work package 1 remove behavior-free code

Delete the code which has no remaining semantic distinction:

- remove `functionExpressionWith` and call `arrowExpressionWith` directly;
- remove the ignored type-annotation argument from `assignedValueFor`, then
  inline the helper if it has no independent meaning;
- remove `validDependentName`, which always succeeds;
- remove `simpleInterpolationWith`, which is `id`;
- remove `IdentifierSpelling` and `identifierSpellingValue`;
- make the relevant name parsers return `String` directly;
- remove `validateIdentifierSpelling`, which cannot fail;
- remove the redundant `isIdentifierValue` check after
  `bareIdentifierToken` has already consumed a nonempty identifier-character
  sequence; and
- remove the Boolean standard-library parsing wrapper after migrating tests
  and test helpers to `StandardLibraryVisibility`.

After these deletions, inline or remove aliases and single-use helpers exposed
by the smaller call graph. Do not preserve them as compatibility names.

### Checkpoint

The parsing suite passes without behavioral changes.

## Work package 2 consolidate concrete operators

Extend `DatraLanguage.AST.Operator` so it is the only registry for the concrete
operators still owned by the parser.

Add typed operators for source forms currently parsed ad hoc, including scope
access `.` and generic bounds `::`. Give the sequential operator its concrete
`;` spelling. Replace raw `char`, `chunk`, `continuedSymbol`, and standalone
separator dispatch for these forms with the shared typed operator parser.

The source operator parser should consume one maximal contiguous symbolic run.
A requested core operator succeeds only when that whole run equals its
registered spelling. If it does not, parsing backtracks without consuming any
of the run so unresolved syntax can retain it intact.

This one rule replaces the current per-operator exclusions. It must preserve
the following distinctions:

| Source | Required classification |
| --- | --- |
| `.` | Scope access operator |
| `..` | Range operator |
| `:` | Dependent argument type operator |
| `::` | Generic bound operator |
| `:=` | Assignment operator |
| `<` | Less-than operator |
| `<~` | Reverse specification operator |
| `<<` | Overload operator |
| `<<<` | Safe-overload operator |
| `+` | Existing core addition or prefix operator |
| `++` | One unresolved symbolic literal |
| `<~~` | One unresolved symbolic literal |

Unary, infix, and postfix uses may share a spelling. Their semantic ambiguity
belongs to the expression grammar, not the symbolic-run parser.

### Checkpoint

Run focused tests for every overlapping operator family, then run the complete
parsing suite.

## Work package 3 preserve presentation directly

Remove the source-parser convention in which token parsers consume horizontal
whitespace and application parsing later recovers it from matched source text.

The canonical AST parser may retain `astLexeme` because canonical AST notation
does not preserve ordinary source presentation. The ordinary source parser
must use token parsers which consume only their token.

Add two direct presentation parsers using Megaparsec's existing character
classes and `match`:

1. A horizontal parser which returns the exact spaces and tabs it consumed.
2. A line parser which returns the exact newline spelling and following
   indentation it consumed.

These parsers must not manually enumerate spaces, tabs, carriage returns, and
newlines throughout the grammar.

Application parsing should consume the exact presentation between two
operands and immediately construct the corresponding application spine:

```haskell
FunctionApplication
  (FunctionApplication left (UnresolvedSyntaxLiteral separator))
  right
```

Compact transitions between different lexical classes use an empty separator
and retain ordinary adjacency. For example, `Nat++` is an identifier followed
immediately by the unresolved symbolic literal `++`.

Delete:

- `trailingHorizontalSyntax`;
- the use of `match` around already parsed terms solely to recover trailing
  whitespace;
- `horizontalCharacter` and its manual line-boundary helpers;
- generic source `lexeme` and `symbol` combinators which erase presentation;
- reconstruction comments and compatibility paths; and
- any tests that assert the deleted recovery mechanism rather than retained
  source semantics.

Core operators still owned by the parser may accept layout around their
operands. Their operator combinator must consume that layout transactionally:
if the operator itself does not match, the layout remains available to
application parsing as exact presentation.

Only explicit non-candidate boundaries may discard layout, including the start
and end of a source phrase and layout immediately inside a concrete delimiter.

### Checkpoint

Raw parser tests must prove that:

- `Nat++`, `Nat ++`, and `Nat\n++` remain different presentations;
- multiple spaces remain distinct from one space;
- tabs remain distinct from spaces;
- CRLF and LF are retained exactly where supported by the source grammar;
- indentation following a newline is retained;
- `hello!!!!` remains available to exact matching;
- `2 + 2` continues to parse through the existing core addition grammar; and
- raw presentation does not introduce `ElidedSyntax`, `AtlasMap []`, or `()`.

## Work package 4 remove residual neutral lexing

Once typed operators and maximal symbolic runs exist, remove:

- `coreSourceSymbols`;
- `isUnresolvedSyntaxCharacter`;
- the hardcoded symbolic punctuation exclusion string; and
- grammar ordering or comments which exist only to support that classification.

Unresolved symbolic parsing should follow the ordinary source grammar
directly:

1. Structural delimiters are claimed by the structural grammar.
2. Identifier characters are claimed by the identifier parser.
3. Whitespace is claimed by the presentation parsers.
4. Quoted source is claimed by the string parser.
5. A registered core operator is attempted using the complete symbolic run.
6. Every remaining nonempty symbolic run becomes one
   `UnresolvedSyntaxLiteral`.

This is a parser ordering rule, not a parallel lexer or an admissibility
predicate. It must accept unclaimed punctuation generically rather than
selecting a hardcoded set of characters which dependent declarations may use.

`#` remains earlier than symbolic fallback because the parser must establish
its concrete source extent before the earliest dependent rule can discard it.

### Checkpoint

Test both known operators and previously unknown symbolic runs at prefix,
postfix, and infix positions. Exact matching must see the original run without
rendering or token normalization.

## Work package 5 tighten built-in dependent rule ownership

Restrict `DatraLanguage.Application` to structural application operations:

- application-spine selection;
- application construction;
- raw and structural phrase projections; and
- utilities which are independent of any built-in syntax rule.

Move whitespace classification and line or horizontal expansion beside the
built-in rules which own those semantics. The comment, line-sequence, and
horizontal-application rules should each own their matcher plan, identity, and
expansion behavior.

The parser should construct only concrete unresolved invocations and
boundaries. For a comment, that remains structurally equivalent to:

```haskell
FunctionApplication
  (UnresolvedSyntaxLiteral "#")
  (SyntaxRemainder source)
```

The parser does not decide that this invocation has no value. The earliest
comment rule expands it to `ElidedSyntax`. Likewise, the parser retains exact
line and horizontal separators while the final fallback rules assign sequence
and application meaning.

Keep the local non-consuming boundary check which terminates a comment at the
active line or syntax boundary. It establishes concrete extent and does not
duplicate an expression grammar. Do not use this work package to restore the
previously dropped test involving parentheses inside a comment remainder.

### Checkpoint

Existing comment tests pass. Line and horizontal fallbacks still run after all
visible declarations and reach the same rewritten AST as before.

## Work package 6 merge dependent argument construction

Replace `identifierDependentArgumentFrom`, `simpleDependentArgument`, and the
independent canonical AST construction path with one semantic construction
abstraction.

The ordinary source grammar should have:

1. One name parser which returns the name expression and optional-name state.
2. One suffix parser which distinguishes `:` from `:=`.
3. One pure constructor which creates the `DependentArgument` and optional
   `MapSpecification`.

Apply optionality to the name before constructing the dependent argument.
Delete the after-the-fact `optionalIdentifier` rewrite and its partial pattern
matching.

The canonical AST reader should reuse the pure constructor while retaining its
own concrete canonical grammar.

Federation parsing must resolve assignment ownership from parsed typed
branches rather than looking ahead through `dependentArgumentStart`. Preserve
both required cases:

```datra
Alias := Nat | Str
False := 0 | True := 1
```

The first assigns the complete federation. The second is a federation of two
declarations. Arithmetic and federation parsers must not invoke another
dependent-argument parser merely to decide whether they may consume an
operator.

### Checkpoint

Run all dependent-argument, optional-name, specification, reverse
specification, federation, and `Args` parser tests.

## Work package 7 remove duplicated semantic lookahead

Eliminate lookahead which parses or mirrors another grammar.

### Resource envelope

Parse top-level elements once. Classify a single top-level parenthesized
`SyntaxBoundary` as an explicit map envelope. Classify every other top-level
shape as an implicit block envelope. Delete `outerMapEnvelope` and the
full-expression lookahead which currently parses an explicit resource twice.

The following cases must remain distinct:

- `(a)` is an explicit envelope;
- `(a); (b)` is an implicit resource containing two entries;
- `a` is an implicit resource;
- an empty resource is an empty implicit resource.

### Ranges

Make the range operator own infix versus postfix selection through operand
success and expression precedence. Delete `postfixRangeEnd` and its manual list
of every lower-precedence operator.

### Reverse specification

Parse reverse specification once. Reject or leave an invalid repeated operator
at its natural grammar boundary instead of parsing the same operator again in
`notFollowedBy`.

### Dependent argument boundaries

Delete `dependentArgumentStart` lookahead from federation and arithmetic
operators. Work package 6 must make the parsed branch structure sufficient to
resolve those cases.

### Delimiters and terminators

Retain delimiter lookahead used by `elementsUntil` and terminator lookahead
inside comments and quoted strings. These checks are local and do not duplicate
semantic grammar.

### Checkpoint

Review every remaining `lookAhead` and `notFollowedBy`. Each use must document
one of these local purposes:

- closing delimiter;
- string or comment terminator; or
- complete maximal operator-token boundary.

No remaining use may invoke an expression, dependent-argument, range, or
precedence grammar.

## Work package 8 move semantic normalization out of parsing

Move the following code from `Parsing` into the function-type or generic
semantic abstraction which owns it:

- generic binder identity allocation;
- generic introduction collection;
- function-type identifier discovery;
- prepared function-domain types and lowering;
- generic bound preparation;
- forward generic-reference analysis;
- inferred function construction; and
- function-type AST reassociation helpers.

This is a move, not a rewrite. Parsing should invoke generic resolution after
constructing the AST. Interpreting should import the same functions from their
semantic owner rather than importing semantic behavior from `Parsing`.

Separate the canonical AST reader from the ordinary source parser
mechanically. Both parsers may use the shared typed operator registry, but only
the ordinary source parser participates in unresolved presentation and
dependent syntax bootstrapping.

Delete exports and imports exposed only by the former combined module.

### Checkpoint

Build all targets with warnings enabled. No semantic module should import
`Parsing` merely to obtain function-type or generic operations.

## Execution order

The work packages should be implemented in this order:

1. Delete behavior-free code.
2. Consolidate concrete operator spellings.
3. Preserve presentation directly.
4. Remove residual neutral lexing.
5. Tighten built-in dependent rule ownership.
6. Merge dependent-argument construction.
7. Remove duplicated semantic lookahead.
8. Move semantic normalization and separate the canonical AST reader.
9. Remove any compatibility paths exposed by the completed sequence.
10. Update the current design documents so they describe only the resulting
    architecture.

Operator consolidation precedes presentation cleanup because presentation
parsing needs a single answer to whether a symbolic run is core syntax or
unresolved data. Direct presentation precedes removal of the symbolic
predicate because the fallback must already have an exact AST destination.
Dependent-argument consolidation precedes removal of its semantic lookahead.

Do not combine all work packages into one unreviewable change. Each checkpoint
must compile and preserve the current Std bootstrap position before the next
package begins.

## Required test coverage

### Existing tests which must be retained

- The `Nat++` exact-matching tests.
- The distinction between `Nat++`, `Nat ++`, and newline-separated forms.
- Existing comment parsing tests.
- Dependent argument and optional-name tests.
- Generic `Args` parsing tests.
- Canonical AST round-trip tests.
- Numerical parsing regression tests.

The intentionally dropped parenthesized-comment example is not part of this
goal and must not be reintroduced.

### New or strengthened raw parser tests

Add focused raw-AST assertions for:

| Area | Cases |
| --- | --- |
| Exact horizontal presentation | One space, repeated spaces, tabs, mixed spaces and tabs |
| Exact line presentation | LF, CRLF where supported, indentation after a line break |
| Compact symbolic adjacency | `Nat++`, `hello!!!!`, `2++` |
| Spaced symbolic syntax | `Nat ++`, `2 ++` |
| Operator overlap | `.`, `..`, `:`, `::`, `:=`, `<`, `<~`, `<<`, `<<<`, `~`, `~>` |
| Unknown symbolic runs | Runs extending a valid operator, including `++` and `<~~` |
| Envelope classification | `(a)`, `(a); (b)`, `a`, and empty input |
| Dependent assignments | `Alias := Nat | Str` and `False := 0 | True := 1` |
| Transient elision | Consumed whitespace and comments never render as `()` |

### Focused test command

After each work package, run:

```bash
cabal test datra-parsing-test -f-liquid -j1 --test-show-details=direct
```

Use focused Tasty patterns during development where practical. Run the whole
parsing suite at every package checkpoint.

### Final build checks

After the parsing suite passes:

```bash
cabal build all --enable-tests -f-liquid -j1
cabal test datra-core-test datra-types-test datra-parsing-test \
  -f-liquid -j1 --test-show-details=direct
```

Do not use the full interpreting suite as the completion criterion. Dependent
declarations remain in progress, so interpreting failures may describe work
beyond this cleanup. Relevant interpreting tests may still be run to diagnose a
regression.

## Standard library acceptance condition

The standard-library bootstrap must progress through numerical parsing and
stop at the existing `Args` issue. The rendered failure must remain:

```text
ModuleEvaluationFailed
  (StandardLibraryParseFailure
    "std.datra"
    "operation has no effect inside block\n  expression: yield ((^n? :: Nat) do yield (slots[0 .. n]))")
```

Equivalent command-line wrapping is acceptable, but all semantic content must
match:

- the failing module is `std.datra`;
- the failure is `operation has no effect inside block`;
- the displayed expression is
  `yield ((^n? :: Nat) do yield (slots[0 .. n]))`;
- the failure does not occur earlier while scanning imports or constructing the
  syntax environment; and
- the diagnostic contains no inserted `()` or rendered `ElidedSyntax`.

## Completion criteria

The cleanup is complete when all of the following are true:

- parsing tests pass;
- core and type tests pass;
- standard-library bootstrap reaches the required `Args` failure;
- numerical parsing behavior remains unchanged;
- spaces and newlines are preserved directly rather than recovered;
- exact and structural matcher modes remain separate;
- `#`, line sequencing, and horizontal application remain dependent rules in
  their required introduction order;
- `.` and `::` have typed operator ownership;
- symbolic parsing has no hardcoded admissibility allowlist;
- `Parsing` contains no generic or function-type semantic subsystem;
- dependent arguments have one construction abstraction;
- no lookahead parses a complete semantic grammar;
- the rewrite scheduler is unchanged;
- no compatibility parser path remains beside its replacement;
- removed names have no references according to `rg`; and
- the parser is smaller and has fewer semantic responsibilities than before
  the refactor.

