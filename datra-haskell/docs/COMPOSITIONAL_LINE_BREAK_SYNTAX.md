# Minimal Compositional Line-Break Syntax Plan

## Goal

Represent a logical source newline as a transient `LineBreak` expression.
The parser retains that expression in the application spine so declarative
syntax can match the complete phrase. While matching, `LineBreak` renders as
the literal character `\n`. If no declaration consumes the phrase, ordinary
syntax finalization lowers the line break through the existing sequential
operator `(<:>)`.

```text
source newline
  -> LineBreak
  -> declarative matching sees "\n"
  -> selected syntax consumes it, or
  -> ordinary finalization lowers it with (<:>)
```

This is the whole pipeline. There is no newline declaration, separator AST,
presentation taxonomy, matcher mode, candidate-presentation view, or injected
fallback rule.

## Current failure

`Parsing.elementsUntil` currently distinguishes separators with an
`ElementSeparator` type. Its newline branch captures the newline and following
indentation as a `String`, then inserts that string into the application spine
as `UnresolvedSyntaxLiteral`.

For example, the raw form of:

```datra
left
right
```

is effectively:

```haskell
FunctionApplication
  (FunctionApplication left (UnresolvedSyntaxLiteral "\n"))
  right
```

This happens to make the newline visible to the current rendered-string
matcher, but it gives the node no structural fallback meaning. Once visible
declarations decline the phrase, the unresolved newline remains an application
operand. Std therefore remains one large application instead of becoming a
sequence of block members, and module loading fails with
`ImportedModuleRequiresBlock`.

## AST representation

Add one nullary syntax-phase constructor:

```haskell
data Expression
  = ...
  | LineBreak
```

`LineBreak` represents one logical line separator. It does not retain the
physical newline spelling or following indentation. The parser already treats
one or more physical end-of-line sequences plus indentation as one logical
separator, and that behavior should remain unchanged.

The node has four rules:

- only source parsing produces it;
- its source rendering is exactly `"\n"`;
- declarative matching runs before its fallback meaning is applied; and
- it must not survive syntax rewriting into evaluation.

Add only the exhaustive cases required by the existing AST boundaries:

- `normalizeExpression LineBreak = LineBreak`;
- the shared traversal treats it as a leaf;
- `toOperatorExpression` can carry it far enough for source and diagnostic
  rendering; and
- evaluation rejects a surviving node as unresolved syntax.

Do not add `LineBreak` to canonical persisted AST syntax. It is transient.

## Parser changes

Delete `ElementSeparator`. `elementsUntil` can branch directly on the three
separators it already owns:

- a semicolon completes the current map member and parses the next member;
- a comment retains its existing concrete remainder ownership; and
- a logical newline reads the next expression and joins the two sides with
  `LineBreak`.

The newline parser should consume the same input as the current
`linePresentation`, but it should return `()` rather than captured source text.
The join is:

```haskell
lineApplication left right = applicationFrom
  (rawApplicationPhrase left <> [LineBreak] <> rawApplicationPhrase right)
```

This retains the complete application spine without deciding during parsing
that the newline is already a sequence.

The same join should be used when the expression following a newline is a
comment. Comment rewriting may later elide that expression, after which normal
line-break finalization preserves the sequence between the surrounding real
expressions.

Keep semicolon behavior unchanged. Keep horizontal spacing unchanged for this
change. After the parser change, no parser-produced `UnresolvedSyntaxLiteral`
may contain `\r` or `\n`.

## Matching

### Exact literal expressions

Keep the existing exact literal-expression matcher. It already matches the
rendered source of the selected application extent. Teach source rendering that
`LineBreak` is `"\n"`; an actual newline in a literal-expression pattern then
matches it without a second matcher representation.

There is no `CandidatePresentation` and no tokenization layer between the AST
and the existing exact matcher.

### Identifier applications and literal templates

Identifier application and literal-template matching still need to distinguish
retained spacing from semantic operands. Keep that as a small structural
predicate, not a presentation model:

```haskell
isRetainedSpacing :: Expression -> Bool
isRetainedSpacing LineBreak = True
isRetainedSpacing (UnresolvedSyntaxLiteral source) =
  not (null source)
    && all isSourceHorizontalPresentationCharacter source
isRetainedSpacing _ = False
```

Use this predicate where the current code uses `presentationLiteral`:

- `applicationPhrase` omits retained spacing for identifier application;
- the literal-template matcher may skip retained spacing before a realized
  component; and
- a capture may contain retained spacing internally but may not end on it.

Delete the broader presentation terminology around this behavior. In
particular, do not classify line and horizontal presentation into separate
types, and do not inspect newline characters inside
`UnresolvedSyntaxLiteral`. A newline is recognized structurally as `LineBreak`.

The full literal-template lexical-edge adjacency cleanup is independent of
this fix and should not be bundled into the first implementation.

## Unconsumed line breaks

`SyntaxRewriting.runRewriteStack` already has the required ordering:

1. enumerate declarations for the complete expression;
2. expand an accepted declaration; otherwise
3. traverse children and run ordinary finalization.

Add the fallback to `normalizeRewrittenSequence`:

```haskell
FunctionApplication
    (FunctionApplication left LineBreak)
    right ->
  left <:> right
```

Use `DatraLanguage.AST.Syntax.(<:>)`. It already flattens a sequence on either
side, so:

```datra
line1
line2
line3
```

becomes one flat sequence rather than nested sequences.

Keep narrow elision cases for comments:

```haskell
FunctionApplication ElidedSyntax LineBreak -> ElidedSyntax
FunctionApplication
    (FunctionApplication left LineBreak)
    ElidedSyntax -> left
```

Order those before the general `left LineBreak right` fallback so an elided
comment does not become a sequence member.

Horizontal spacing continues through its existing elision path, narrowed to
horizontal characters only. Delete helpers and comments which describe a raw
newline string as presentation or as a future syntax declaration.

A bare, leading, or trailing `LineBreak` is not assigned an empty-map meaning.
If one somehow survives to evaluation, reject it as unresolved syntax.

## Minimal implementation order

1. Add `LineBreak` and the required normalization, rendering, and evaluation
   cases.
2. Remove `ElementSeparator` and make the newline branch of `elementsUntil`
   insert `LineBreak` directly.
3. Replace `presentationLiteral` with the small `isRetainedSpacing` predicate,
   recognizing horizontal unresolved spacing and structural `LineBreak` only.
4. Render `LineBreak` as `"\n"` so the existing exact matcher reads it as a
   literal newline.
5. Lower an unconsumed complete line application through `(<:>)`, including
   the two comment-elision cases.
6. Update the focused parsing and matching tests, then load Std.

No changes belong in `DatraHost`, the standard-library declaration set,
`syntaxContext`, `SyntaxRuleSemantics`, or the generic exact-string matcher.

## Verification

### Raw parsing

- `left\nright` contains `LineBreak`, not
  `UnresolvedSyntaxLiteral "\n"`.
- indentation and blank lines still produce one logical separator.
- horizontal spaces retain their current representation.
- semicolons retain their current map-member behavior.
- comments do not absorb the following logical line break.
- no parser-produced unresolved syntax literal contains a line-break
  character.

### Matching

- an identifier application can select an extent containing `LineBreak`;
- a literal template can cross `LineBreak` and can capture an expression with
  internal line breaks;
- an exact literal-expression pattern containing `\n` matches the source
  rendering of `LineBreak`;
- compact, horizontally spaced, and newline-separated exact spellings remain
  distinct; and
- a successful declaration consumes the complete phrase before fallback
  sequencing runs.

### Fallback

- one unconsumed line becomes `left <:> right`;
- three lines produce one flat `MapSequence`;
- a sequence on either side remains flat;
- an elided comment does not introduce an empty sequence member; and
- horizontal application behavior is unchanged.

### Integration

- update the raw separator test to expect `LineBreak`;
- update the exact-newline matcher test to construct `LineBreak`;
- keep the existing Std-less unconsumed-line tests;
- load `libs/std.datra` successfully;
- verify the `Args` declaration reaches the final outer `yield`; and
- run the parsing suite before expanding verification to interpreter, module,
  CLI, and fixture suites.

## Initial completion condition

The initial work is complete when source newlines become `LineBreak`, the
existing exact matcher reads them as `\n`, declarations see the complete phrase
before fallback, unconsumed line breaks flatten through `(<:>)`, Std loads, and
the parsing tests pass without a newline syntax rule or a new presentation
abstraction.
