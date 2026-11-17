# Compositional Line-Break Syntax Plan

## Goal

Represent a logical source newline as a transient `LineBreak` AST node.
Declarative matchers can consume that node as presentation, including matching
an exact `\n`. If no declaration consumes it, ordinary syntax finalization
turns the surrounding expression into the existing sequential operator
`(<:>)`.

The resulting order is:

```text
source newline
  -> LineBreak in the retained application spine
  -> visible declarative rules get the complete spine
  -> a selected rule consumes the LineBreak, or
  -> ordinary finalization lowers it with (<:>)
```

This is deliberately compositional. `LineBreak` is one syntax component with
one matcher interpretation and one unconsumed interpretation. There is no
newline syntax declaration, host-injected fallback rule, matcher mode,
identity label, rendered-string probe, or special syntax boundary.

## Current flow and failure

### Parsing

`Parsing.elementsUntil` owns map-element separators. A semicolon immediately
starts another element. A newline currently takes a different route:

1. `elementSeparator` returns `LineSeparator String`.
2. `linePresentation` captures the newline and following indentation as raw
   text.
3. `presentedLineApplication` flattens the expressions on both sides and
   inserts `UnresolvedSyntaxLiteral separator` into the application spine.

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

This preserves the complete phrase for declarative matching, which is the
right ordering, but it does not distinguish a logical line separator from an
unknown symbol or horizontal presentation.

### Matching

`DatraLanguage.Application.presentationLiteral` currently discovers
presentation by inspecting the string in `UnresolvedSyntaxLiteral`.

- `IdentifierApplicationMatcher` uses `applicationPhrase`, which filters such
  presentation.
- `LiteralTemplateMatcher` uses `rawApplicationPhrase` and skips presentation
  between template components.
- `LiteralExpressionMatcher` renders a selected AST and runs the exact string
  matcher over the result.

Consequently a newline is visible only as an undifferentiated string operand.
The literal-template matcher can skip it, but there is no typed component for
an exact `\n` match and no safe final interpretation once declarations decline
the phrase.

### Finalization

`SyntaxRewriting.runRewriteStack` already supplies the required precedence:

1. `enterNode` enumerates declarative candidates for the complete node.
2. Accepted candidates expand before ordinary traversal.
3. Only after candidates are exhausted does `finalizeOrdinary` call
   `normalizeRewrittenSequence`.

Horizontal presentation is removed there today. After the experimental
newline rule was removed, an unconsumed newline remains an unresolved
application operand. Std therefore retains one enormous newline-containing
application instead of acquiring block members, and module loading eventually
fails with `ImportedModuleRequiresBlock`.

## AST representation

Add a nullary syntax-phase constructor:

```haskell
data Expression
  = ...
  | LineBreak
```

`LineBreak` represents one logical line separator, not the source spelling or
indentation following it. `linePresentation` already treats one or more
physical end-of-line sequences plus indentation as one element separator; the
new node preserves that existing logical behavior. Canonical source rendering
of the node is `"\n"`.

The node has these invariants:

- the source parser is its only producer;
- it exists only during syntax rewriting;
- it is never a value, callable operand, or syntax rule;
- it is either consumed as presentation by a matcher or lowered during
  ordinary finalization; and
- it must not reach evaluation.

Add the corresponding exhaustive traversal, normalization, source-rendering,
and diagnostic-rendering cases. If `OperatorExpression` remains the common
rendering boundary, add a transient `LineBreakValue` there as well. Evaluation
must reject a surviving line break as unresolved syntax rather than assigning
it a semantic value.

Do not store `String` in `LineBreak`. Exact source locations belong to the
parser's existing located diagnostics, while indentation is presentation that
does not affect newline matching or sequential semantics.

## Parser changes

Change the separator representation to distinguish logical structure at the
type level:

```haskell
data ElementSeparator
  = SemicolonSeparator
  | LineSeparator
  | CommentSeparator String
```

`linePresentation` should consume the same source as it does now but return
`()`. `elementsUntil` should retain the complete phrase by inserting
`LineBreak`:

```haskell
presentedLineApplication left right = applicationFrom
  (rawApplicationPhrase left <> [LineBreak] <> rawApplicationPhrase right)
```

This preserves the important current behavior: parsing does not decide that a
newline is a sequence before visible syntax has had the opportunity to consume
the complete expression.

Keep semicolons unchanged. They are explicit structural separators and may
continue to produce map members directly. Keep comment remainder ownership
unchanged; the newline after a comment becomes `LineBreak` between the reduced
comment phrase and the following expression.

After this change, establish the parser invariant that
`UnresolvedSyntaxLiteral` never contains a source line-break character. It can
continue to represent unknown symbolic syntax and retained horizontal
presentation until those paths are narrowed separately.

## Shared application and presentation abstractions

Extend `DatraLanguage.Application` rather than teaching each matcher about a
private newline spelling.

```haskell
data PresentationKind
  = HorizontalPresentation
  | LinePresentation

presentationKind :: Expression -> Maybe PresentationKind
presentationKind LineBreak = Just LinePresentation
presentationKind (UnresolvedSyntaxLiteral source)
  | not (null source)
  , all isSourceHorizontalPresentationCharacter source =
      Just HorizontalPresentation
presentationKind _ = Nothing
```

The exact names can follow existing module conventions. The required behavior
is:

- `presentationLiteral` recognizes both horizontal presentation and
  `LineBreak`;
- `applicationPhrase` filters both;
- `rawApplicationPhrase` retains both in source order; and
- a dedicated `linePresentationLiteral` recognizes only `LineBreak`.

This keeps identifier application, literal-template matching, comments, and
ordinary application on one shared projection.

## Matcher behavior

### Identifier applications

No new matcher mode is required. Because `IdentifierApplicationMatcher`
already uses `applicationPhrase`, it continues to see the semantic operands
on both sides of line presentation. It may therefore select an extent crossing
one or more `LineBreak` nodes.

### Literal templates

`LiteralTemplateMatcher` already walks `rawApplicationPhrase` and calls
`span presentationLiteral` before each realized component. Once
`presentationLiteral LineBreak` is true, the existing structural walk can
cross newlines without string inspection.

The component-adjacency implementation must retain the presentation it skips:

- a `LineBreak` counts as candidate whitespace;
- horizontal presentation also counts as candidate whitespace;
- equal lexical edge classes require at least one presentation component;
- differing lexical edge classes permit presentation but do not require it;
  and
- absent optional components are removed before adjacent realized components
  are compared.

Captures remain longest-first and must never end on `LineBreak` or horizontal
presentation. A selected capture can contain internal `LineBreak` nodes; the
capture's own syntax category decides whether that composed expression is
valid.

### Literal expressions

Compile a newline in an exact literal-expression pattern as a line-presentation
component, not as an arbitrary character in a rendered candidate string.
Matching that component succeeds only on `LineBreak` and contributes no
capture.

The shared exact matcher may continue to own boundary search, but its candidate
view should be compositional:

```haskell
data CandidatePresentation
  = CandidateExpression Expression
  | CandidateHorizontalPresentation String
  | CandidateLineBreak
```

The view is derived from `rawApplicationPhrase`. Literal text consumes the
appropriate presentation or expression component, and captures select a
consecutive component range which is rebuilt with `applicationFrom`. This
avoids rendering the complete AST, splitting a substring, and reparsing it to
recover the AST that was already available.

At minimum, the first implementation must route `"\n"` through
`CandidateLineBreak`. It must not recognize a line by searching text rendered
from a nested operand; only a `LineBreak` in the current candidate spine is a
separator available to that match.

## Lowering an unconsumed line break

Ordinary finalization owns the fallback meaning. Add a structural case to
`normalizeRewrittenSequence` after its children have been rewritten:

```haskell
FunctionApplication
    (FunctionApplication left LineBreak)
    right ->
  left <:> right
```

Use `DatraLanguage.AST.Syntax.(<:>)`, not direct `MapSequence` construction.
`(<:>)` flattens either operand when it is already a sequence, so repeated
unconsumed lines compose as:

```text
line1
line2
line3
```

```haskell
line1 <:> line2 <:> line3
```

rather than `[[line1; line2]; line3]`.

This fallback happens only after all candidates for that node have failed. If
a declaration such as `do ... yield ...` accepts the complete phrase, its
expansion replaces the original phrase and the consumed `LineBreak` nodes
never reach ordinary finalization.

A bare, leading, or trailing `LineBreak` should be impossible from
`elementsUntil`. If a future parser path produces one, leave it unresolved so
the existing syntax-rewrite diagnostic boundary reports it. Do not silently
erase it and do not lower it to an empty map.

## Required code changes

Implement in this order:

1. Add `LineBreak` and all exhaustive AST traversal, normalization, equality,
   source-rendering, and pretty-rendering cases.
2. Change `Parsing.elementSeparator`, `linePresentation`, and
   `presentedLineApplication` to construct the node.
3. Narrow `UnresolvedSyntaxLiteral` presentation to horizontal source only.
4. Update `DatraLanguage.Application` with the shared presentation
   classification.
5. Make all three declarative matcher modes consume that classification.
6. Implement literal-template lexical-edge adjacency using the retained
   presentation components.
7. Lower the unconsumed complete line pattern through `(<:>)` in
   `normalizeRewrittenSequence`.
8. Add an invariant check or diagnostic preventing `LineBreak` from reaching
   semantic evaluation.
9. Delete comments and helpers which still describe a later newline syntax
   declaration.

The change belongs in the parser, AST/application modules, declarative matcher,
and syntax finalizer. It does not belong in `DatraHost`, `syntaxContext`, the
standard-library declaration set, or `SyntaxRuleSemantics`.

## Verification

### Raw parsing

- `left\nright` contains `LineBreak`, not
  `UnresolvedSyntaxLiteral "\n"`.
- indentation and blank-line spellings produce the intended single logical
  separator.
- horizontal spaces remain horizontal presentation.
- explicit semicolons retain their current AST.
- comment remainder ownership ends before the following `LineBreak`.

### Matching precedence

- an identifier application can select an extent containing `LineBreak`.
- a literal template can skip `LineBreak` as candidate whitespace.
- an exact literal-expression `\n` component matches only a top-level
  `LineBreak`.
- a newline rendered from inside a nested operand is not visible to the outer
  matcher.
- captures are tried longest-first across nested `do ... yield ...` phrases.
- a successful declaration consumes the line nodes before finalization.

### Fallback composition

- one unconsumed line becomes `left <:> right`.
- three lines produce one flat `MapSequence`.
- a sequence on either side remains flat.
- no unit/empty-map member is introduced.
- horizontal application behavior is unchanged.

### Integration

- add Std-less tests for the raw `LineBreak`, matcher consumption, and
  unconsumed fallback independently.
- restore a focused greedy `do ... yield ...` test only after its capture
  targets are available in the chosen Std-less environment.
- load `libs/std.datra` and verify `Args` reaches the final outer `yield` rather
  than the nested one.
- run parser, interpreter, module, CLI, and fixture suites.
- verify no `LineBreak` reaches evaluation or canonical persisted AST output.

## Completion condition

The work is complete when newlines are represented structurally from parsing
through matching, visible declarations always run before fallback sequencing,
unconsumed lines flatten through `(<:>)`, Std loads, and no newline behavior
depends on raw string inspection or an injected syntax rule.
