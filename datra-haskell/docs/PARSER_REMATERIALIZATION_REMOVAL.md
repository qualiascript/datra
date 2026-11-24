# Parser Rematerialization Removal

## Current scope

The remaining parser rematerialization is in multi-part literal-pattern
matching. The parser already has an AST, but the matcher renders a candidate
selection back to Datra source and reparses every captured substring. That
round trip is still an alternate parser inside syntax rewriting. The current
block-syntax failure exposes the same matcher/projection boundary, although it
fails during candidate projection before the round trip is reached.

This document covers only:

- the remaining AST-to-text-to-AST matcher path;
- the dual matcher representation which keeps that path alive;
- the current `begin ... yield ...` candidate-projection blocker; and
- the separate runtime canonical-value render/parse bridge which must not be
  reused by parser syntax selection.

The rewrite-stack scheduler is not the current problem. Candidate scheduling,
deferred type constraints, child ownership, and selection order must remain
unchanged while the matcher projection is replaced.

## Required parser invariant

Once the concrete parser has produced an AST, syntax matching is structural:

1. A declaration head compiles to one identifier-expression pattern.
2. Candidate projection selects a source-order structural region from the raw
   AST.
3. Matching partitions that region into literal segments and captured AST
   regions.
4. Captures retain their original AST identity and boundaries.
5. The stack rewrites those captures and invokes the selected lowering once.

No step may render a candidate to source text and parse it again. Literal
strings are the constant case of the same string-family pattern as computed
identifier expressions; they are not a second matcher semantics.

`SyntaxBoundary` remains meaningful while raw syntax regions are being
matched. It is removed at the completed resource-rewrite boundary, after it
can no longer affect selection or grouping.

## Remaining parser rematerialization

The active path is in `StringInterpolation.Matching`:

```text
matchLiteralExpression
  -> applicationSelections
  -> literalExpressionCaptures
  -> renderSourceExpression selectedAST
  -> matchExactSegments
  -> decodeCapture
  -> parseExpressionText capturedSubstring
```

The one-capture pattern has already escaped this round trip:

```haskell
LiteralExpressionPattern [LiteralExpressionPatternCapture kind]
```

It retains the selected AST directly. Every multi-part pattern still uses the
render/reparse path.

This is semantically wrong even when the rendered text happens to parse to an
equivalent value:

- the rendered spelling, rather than the raw AST, decides capture extent;
- parser grouping and operator lowering can no longer be recovered reliably;
- `SyntaxBoundary` and logical line-break ownership are flattened into text;
- source spans and node identity are lost;
- a captured region can return with a different AST association; and
- the parser is invoked once during concrete parsing and again for every
  attempted capture split.

`ExpressionParser`, `expressionParser`, `parseExpressionText`, and
`decodeCapture` exist in syntax matching only to support this rematerialized
capture path.

## Dual matcher representation

Rule construction still chooses two matcher models:

- simple literal declaration heads become `IdentifierApplicationMatcher`;
- template and computed heads become `LiteralExpressionMatcher`.

The first matches application structure. The second renders that structure to
text. This is two spelling authorities for one identifier-expression family.
It also makes candidate activation and capture extent depend on which rule
constructor produced the declaration.

Every declaration head must instead compile through the same structural
identifier-pattern representation. A simple name is a pattern containing one
literal string segment. It may use a literal-prefix index as an optimization,
but that index cannot select different matching semantics.

Once the structural matcher covers the literal-name case, remove:

- `IdentifierApplicationMatcher` and `IdentifierApplicationPattern`;
- `identifierApplicationRule`;
- matcher-mode branches in candidate enumeration and rule activation; and
- matcher-provenance branches in capture-extent calculation.

## Current parser blocker

The failing bundled source begins as:

```datra
Std.(
  yield Numbers := begin
    ...
  yield public this
)
```

The `Std` catalog is present and contains the expected rules. Scoped natural
literals are rewritten successfully, so neither module catalog construction
nor scope installation is the failure.

The raw body is structurally equivalent to:

```text
SyntaxBoundary (
  UnresolvedApplication
    [ yield
    , MapSpecification begin (DependentArgument Numbers)
    , LineBreak
    , ... declarations ...
    , LineBreak
    , yield
    , public
    , this
    ])
```

The block rule needs the source region beginning at the `begin` expression and
ending after the later `yield` result. That region is not a node in the raw
AST:

- `begin` is nested inside the declaration's `MapSpecification`;
- the block declarations and closing `yield` are siblings in the enclosing
  unresolved application; and
- `applicationSelections` enumerates prefixes of the enclosing phrase, so
  every selection there begins with the outer `yield`.

At the enclosing phrase, the `begin ... yield ...` pattern is therefore not a
candidate. At the nested `begin` node, the matcher cannot see the following
siblings. The generic whole-capture natural-literal rule is the only candidate
at these positions; its host insertion rejects the non-natural capture as
inapplicable, after which ordinary traversal leaves the block syntax raw.

The blocker is therefore:

> Candidate projection has no structural representation for a contiguous
> source region which starts inside a core-operator node and continues through
> later siblings of that node's parent.

It is not a deferred-candidate scheduling bug, a catalog lookup failure, a
missing `SyntaxBoundary` case, or a reason to special-case the strings
`"begin"` or `"yield"`.

### Related implicit-resource symptom

The syntax-regression test for a top-level `yield this` fails through a
different projection edge. An implicit resource is parsed as an `AtlasMap` of
raw entries. Its assembler expects rewriting to have separated declarations
from the final result, but the raw terminal entry is still the ordinary
application `yield this`. No structural block selection claims the delimiter,
so the assembler produces:

```haskell
Begin [] (FunctionApplication yield this)
```

rather than:

```haskell
Begin [] this
```

This must not be repaired by giving `assembleImplicitSyntaxResource` a second
string-based interpretation of `yield`. An implicit resource is a block
context and must use the same structural block segmentation as the compiled
`begin ... yield ...` rule. The shared projection must represent the block's
declaration region and terminal result even when the source envelope supplies
the block context instead of an explicit `begin` token.

## Structural replacement

The matcher needs one source-order structural phrase view. That view must:

- preserve the raw AST nodes belonging to every source segment;
- project core operator nodes, including `MapSpecification`, back into their
  source order without rendering them;
- describe a contiguous interval independently of its AST parent/child
  boundary;
- reconstruct the selected expression and remaining phrase without reparsing;
- retain logical line breaks for block and expression extent rules; and
- carry enough structural position information for captures to remain owned
  by their original nodes.

This is a global projection used by every identifier-expression pattern. It
must not be a new `syntaxCaptureTarget`, a `begin` exception, or a revival of
`contiguousSubphrases` that blindly tries arbitrary AST fragments. The
projection defines which regions are valid once; the matcher consumes those
regions according to the compiled pattern.

The stack continues to receive the same conceptual result:

```haskell
StructuralCandidate
  { structuralCandidateSelection :: TemplateSelection Expression Expression
  , structuralCandidateCaptures :: [(DeclarativeCapture, Expression, CaptureExtent)]
  , structuralCandidateRemaining :: [Expression]
  , ...
  }
```

Only candidate projection and matching change. The stack remains responsible
for capture rewriting, constraint deferral, unlocking, candidate decisions,
and scheduling.

## Removal sequence

1. Define the structural source-order phrase projection and its reconstruction
   law. Add direct tests for regions crossing an operator-child/sibling
   boundary, including the `Numbers := begin ... yield ...` shape.
2. Compile all identifier expressions into one structural segment pattern.
   Treat a literal identifier as the one-literal instance of that pattern.
3. Match literal segments and captures directly against projected structural
   regions. Return captured AST regions without decoding source strings.
4. Delete the parser-facing render/reparse bridge:
   `ExpressionParser`, `expressionParser`, `parseExpressionText`,
   `decodeCapture`, and the `renderSourceExpression` dependency in
   `StringInterpolation.Matching`.
5. Remove `IdentifierApplicationMatcher` after simple identifiers use the
   shared structural pattern.
6. Delete matcher-provenance capture-extent rules. Capture extent must follow
   the compiled structural pattern itself.
7. Verify block, function-body, conditional, infix, optional, and literal-only
   patterns without changing the stack scheduler.

`matchExactSegments` remains valid for runtime string-template inversion,
where the input genuinely is a string. It must no longer be used to match an
AST by first rendering that AST to a string.

## Separate remaining runtime rematerialization

`closedSourceExpressionIn` is a second live render/parse bridge:

```text
InterpretedValue
  -> renderCanonicalResult
  -> parseSourceExpression
  -> rewriteStandaloneSyntax
  -> closure dependency inlining or canonical-string decoding
```

Its current consumers are runtime canonical-string decoding and closure
dependency serialization. This is genuine value rematerialization, but it is
not the syntax candidate engine and it is not the cause of the block parser
failure.

That bridge should eventually be replaced by a canonical AST codec or by
retaining the canonical expression alongside the evaluated value. Until then,
it must stay isolated from parser catalog construction, syntax candidate
selection, and capture preparation. It cannot be used as a fallback for the
structural matcher.

## Verification

The parser-facing cleanup is complete when:

1. `StringInterpolation.Matching` neither imports `renderSourceExpression` nor
   accepts an `ExpressionParser`.
2. No syntax capture is produced by parsing a rendered substring.
3. Simple and computed identifier expressions compile to one matcher type.
4. The `begin ... yield ...` rule selects the correct cross-boundary structural
   region in `libs/numbers.datra`.
5. An implicit resource's `yield this` is segmented through the same block
   mechanism, without a second delimiter recognizer.
6. Raw parser tests retain effective boundaries, while completed rewrite tests
   contain no inert `SyntaxBoundary` nodes.
7. The full parsing suite passes without a stack scheduling change or an
   execution-time regression.

## Non-solutions

The following preserve the broken ownership boundary:

- matching more strings produced by `renderSourceExpression`;
- reparsing only selected capture kinds;
- adding hard-coded recognition for `begin`, `yield`, `from`, or another
  standard-library spelling;
- adding `syntaxCaptureTarget` or another rule-specific target selector;
- restoring an unconstrained `contiguousSubphrases` search;
- allowing the generic natural-literal candidate to suppress the missing
  block candidate;
- routing syntax selection through `closedSourceExpressionIn`; or
- changing stack deferral or scheduling to compensate for a candidate that
  was never structurally enumerated.
