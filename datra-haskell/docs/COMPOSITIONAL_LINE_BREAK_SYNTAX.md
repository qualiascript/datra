# Compositional Line-Break Implementation Plan

## Goal

Represent a logical source newline as a transient `LineBreak` expression.
Declarative syntax gets the first opportunity to consume it as the literal
character `\n`. If no visible or scoped declaration accepts the complete
expression, a terminal structural fallback interprets the remaining line
breaks through the existing sequential operator `(<:>)`.

```text
source newline
  -> LineBreak in the raw application phrase
  -> visible and scoped declarative candidates
  -> terminal LineBreak fallback
  -> ordinary traversal and finalization
```

The existing rewrite stack remains unchanged. The fallback participates in
the existing candidate flow at a deliberately lower priority than every
declarative candidate.

## Core invariant

For every node entered by the rewriter, candidate order is:

1. visible declarative candidates;
2. scoped declarative candidates;
3. terminal structural fallback candidates; and
4. ordinary traversal only when no candidate applies.

This ordering has four consequences:

- a declaration always sees the complete node before a line is sequenced;
- a successful declaration consumes its `LineBreak` nodes and suppresses the
  fallback;
- when declarations decline the node, the fallback replaces the complete
  line-containing phrase before any of its original children are traversed;
  and
- the replacement is then traversed by the existing stack, so declarations
  produced by earlier sequence members become visible to later members.

The same invariant applies when the rewriter is entered for a root, a capture,
an expanded expression, or an ordinary child. A fallback must strictly remove
the transient structure which selected it, making repeated entry idempotent
and preventing fallback loops.

## Source representation

Add one nullary transient constructor:

```haskell
data Expression
  = ...
  | LineBreak
```

`LineBreak` represents one logical separator, not its physical spelling or
following indentation.

Required AST behavior:

- `normalizeExpression LineBreak = LineBreak`;
- traversal treats it as a leaf;
- source rendering is exactly `"\n"`;
- diagnostic rendering identifies it without assigning a semantic value;
- canonical persisted AST parsing does not produce it; and
- evaluation rejects a surviving `LineBreak` as unresolved syntax.

## Parser

### Horizontal spacing

Horizontal spaces and tabs are ordinary parser layout. They do not produce
`UnresolvedSyntaxLiteral`, `ElidedSyntax`, or another presentation node.

Application parsing consumes horizontal layout and constructs ordinary
`FunctionApplication` nodes. Compact and horizontally spaced applications
therefore have the same AST.

Delete the obsolete horizontal presentation machinery:

- `horizontalPresentation`;
- `presentedApplication`;
- `presentationLiteral` and its character-classification helpers; and
- horizontal-spacing elision cases in syntax finalization.

### Logical newlines

Delete `ElementSeparator`. `elementsUntil` directly handles semicolons,
comments, logical newlines, and the enclosing boundary.

The logical-newline parser consumes one or more physical newlines plus their
indentation and returns `()`.

When real expressions occur on both sides, retain the complete phrase by
inserting `LineBreak` into the application spine:

```haskell
lineApplication left right = applicationFrom
  (rawApplicationPhrase left <> [LineBreak] <> rawApplicationPhrase right)
```

The parser does not convert the newline to a sequence. It also does not need
to group or right-associate lines specially: the terminal fallback runs before
ordinary traversal of the original spine.

Semicolons remain explicit map-element separators and keep their current
behavior.

## Matching

### Exact literal expressions

Keep the existing exact literal-expression matcher. Because source rendering
maps `LineBreak` to `"\n"`, a newline in an exact pattern matches the retained
node without another candidate representation.

There is no `CandidatePresentation`, newline token stream, or new declarative
matcher mode for ordinary declarations.

### Identifier applications

`applicationPhrase` omits `LineBreak` when projecting semantic application
operands. Identifier application matching can therefore select an extent
which crosses a logical newline.

### Literal templates

Literal-template matching continues to use `rawApplicationPhrase` so source
order is preserved.

- Skip `LineBreak` before a realized pattern component.
- Permit a capture to contain internal line breaks.
- Do not allow a capture to end on `LineBreak`.
- Preserve longest-first capture selection.

No horizontal-spacing logic remains in these matchers.

## Terminal structural fallback

Add a focused module:

```text
app/SyntaxRewriting/PostRewrite.hs
```

It owns the line-break fallback and nothing else. The conceptual operation is:

```haskell
lineBreakFallback :: Expression -> Maybe Expression
```

The operation:

1. reads the current top-level `rawApplicationPhrase`;
2. declines the expression if the phrase contains no `LineBreak`;
3. splits the phrase at every remaining `LineBreak`;
4. declines malformed leading, trailing, or empty segments;
5. rebuilds each line with ordinary `applicationFrom`; and
6. joins the completed lines through `(<:>)`.

It handles every remaining top-level break in one expansion. It must not lower
one partial `left LineBreak right` subtree at a time, because `right` may be
only the first operand of a longer source line.

The fallback is adapted to one internal structural candidate and appended
after visible and scoped candidates in `structuralCandidatesFor`. Reuse the
existing candidate transition: when accepted, the stack replaces the current
node with the fallback expansion and traverses that replacement normally.

Keep the adapter narrow:

- do not register the fallback in `syntaxContext`;
- do not expose it as a user declaration;
- do not add it to imported or standard-library rule sets;
- do not produce ordinary candidate-rejection diagnostics for it; and
- do not generalize the module into a new rule framework until another real
  structural fallback exists.

The internal candidate needs no captures. Its return witness can use the same
empty-map witness previously used by non-semantic built-ins; the rewritten
replacement supplies the real structure during ordinary traversal.

## Sequential declaration publication

`(<:>)` constructs `MapSequence`. After the fallback expansion, the existing
stack traverses that container from left to right.

The syntax-rewriting configuration must publish a rewritten declaration child
of `MapSequence` in the same way it already publishes declaration children of
`AtlasMap`, `Begin`, and `FunctionBody`.

This is a container-semantics addition to the existing `stackPublishChild`
callback, not a change to the rewrite machine or its scheduling algorithm.
It is required so declarations on earlier source lines affect rewriting of
later source lines, including Std's declared syntax.

## Comments

Comments do not belong in the terminal fallback phase.

A line break is matcher-visible syntax with a fallback meaning. A comment is
lexical input whose contents must never be offered to declarative matching.
Putting comments after visible candidates would allow declarations to inspect
or capture comment text; putting them before visible candidates would give the
post-rewrite phase two incompatible priority rules.

Handle comments entirely in `Parsing.elementsUntil`:

- consume `#` up to, but not including, the following newline, enclosing
  boundary, or EOF;
- do not construct an expression for the comment;
- an inline comment leaves the expression before it unchanged;
- a leading or standalone comment is skipped before the next real expression;
- the newline after an inline comment remains a logical separator between real
  expressions; and
- comment-only lines do not introduce empty sequence members.

This removes the need for:

- `SyntaxRemainder` and `SyntaxRemainderValue`;
- their canonical and rendering forms;
- `commentSyntaxRule`;
- `SyntaxDiscard`; and
- `ElidedSyntax`, provided no remaining producer is found after the horizontal
  presentation cleanup.

Before deleting `ElidedSyntax`, verify by search that no non-comment feature
still relies on it.

## Implementation order

1. Finish the `LineBreak` AST, source-rendering, diagnostic, traversal, and
   evaluation cases.
2. Remove horizontal presentation nodes and make horizontal spacing parser
   layout.
3. Simplify comment parsing and remove `SyntaxRemainder`, the comment syntax
   rule, and now-unused discard/elision forms.
4. Remove `ElementSeparator` and make logical newlines insert `LineBreak` into
   the flattened raw application spine.
5. Update application projections and the three existing declarative matcher
   modes for structural `LineBreak`.
6. Add `SyntaxRewriting.PostRewrite.lineBreakFallback`.
7. Append its internal candidate after visible and scoped candidates without
   changing `SyntaxRewriting.Stack`.
8. Publish declaration children while traversing a fallback-produced
   `MapSequence`.
9. Remove the temporary ordinary-finalization line-break lowering; the
   terminal candidate is the sole fallback owner.
10. Update focused tests, load Std, and then run the parsing suite.

Do not modify the scheduling or state transitions in
`SyntaxRewriting.Stack`. Do not add host declarations or edit Std to make the
fallback visible.

## Verification

### Raw parsing

- `left\nright` contains `LineBreak`.
- No parser-produced `UnresolvedSyntaxLiteral` contains whitespace.
- Horizontal spacing creates no AST node.
- Multiple blank lines plus indentation create one logical `LineBreak`.
- Semicolons preserve their existing element behavior.
- Comments create no AST node and their contents are never parsed.

### Candidate precedence

- An exact `\n` declaration consumes `LineBreak` before the fallback.
- An identifier application can cross a line break.
- A literal template can cross and internally capture line breaks.
- A declaration which declines the complete phrase leaves it to the fallback.
- Visible and scoped declarations are always enumerated before the fallback.

### Fallback composition

- One unconsumed break becomes `left <:> right`.
- Multi-operand lines remain complete applications on each side.
- Three or more lines produce one flat `MapSequence`.
- A sequence already present on either side remains flat.
- Rewriting the result again does not select the fallback.
- A fallback selected for a capture follows the same invariant as a root.

### Comments

- Inline comments leave the preceding expression intact.
- A newline after an inline comment separates the surrounding expressions.
- Leading, trailing, consecutive, and comment-only lines add no empty member.
- Operator-looking and declaration-looking comment contents remain inert.

### Integration

- Earlier declarations in a fallback-produced sequence are visible while
  rewriting later members.
- `libs/std.datra` loads successfully.
- Std's `Args` declaration reaches the final outer `yield`, not the nested one.
- The focused Std-less line-break tests pass before the full parsing suite is
  run.
- Any unrelated parser failures are reported before they are changed.

## Completion condition

The implementation is complete when `LineBreak` is the only retained layout
node, declarations always receive first refusal over the complete phrase,
unconsumed breaks are handled by the terminal structural fallback, fallback
expansions publish declarations sequentially without changing the rewrite
stack, comments are parser-owned and leave no syntax nodes, Std loads, and the
line-break parsing tests pass.
