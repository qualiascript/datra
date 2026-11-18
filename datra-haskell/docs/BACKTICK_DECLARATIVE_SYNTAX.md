# Literal Templates: Implementation Plan

## Proposal

Add backtick-delimited literal templates as the declarative syntax for matching
the surface form of dependent declarations.

```datra
`do %_Block? yield %_Expr`
```

The example contains two literals, `do` and `yield`, and two captures,
`_Block?` and `_Expr`. The literals decide whether the declaration matches.
Only the captures are supplied to the declared function.

The terminology is:

- `$` forms are **literal expressions**;
- `$!` forms are **obsolete literal templates** and will be removed; and
- backtick forms are **literal templates**.

This is one replacement feature. The implementation adds literal templates,
migrates the standard library and tests to them, and then deletes the obsolete
`$!` parser, AST, evaluator, renderer, and matcher paths. There is no period in
which the two template representations are allowed to interoperate.

Literal templates are a direct syntactic and semantic category. They are not
Atlas operands, strings which are reparsed, or literal expressions hidden
behind another operator. They also do not depend on the planned `_StrExpr`
feature. Captures retain ordinary Datra target expressions and use the syntax-
capture and specification mechanisms which already exist.

## Implementation status

This section records the repository state at the end of the current
implementation session. The rest of this document remains the feature design;
where an older implementation sketch conflicts with this status, the current
typed representation and the linked line-break plan are authoritative.

### Implemented

- Backticks parse directly as `LiteralTemplateExpression`.
- Literal-template syntax lives in `DatraLanguage.IdentifierExpression`, not a
  dependent-declaration-only module.
- The AST has type-safe literal, capture, group, sequence, either, and optional
  composition. Alternatives and optionality reuse the shared
  `IdentifierExpressionComposition` constructors rather than template-specific
  either/optional nodes.
- Captures reuse the quoted-interpolation parser for simple and parenthesized
  forms, while retaining the captured Datra expression directly.
- The parser enforces exactly one ASCII space between components, rejects
  newline layout inside a template, and preserves the proposed grammar.
- `MixedTemplateLiteral`, `InvalidLiteralTemplateSpacing`, and
  `NullableLiteralTemplate` are typed diagnostics rendered through the normal
  diagnostics modules.
- The parser rejects a wholly nullable template, so a declaration cannot match
  the empty identifier.
- Source and canonical renderers understand the literal-template AST.
- Dependent declarations distinguish ordinary identifier expressions from
  literal-template identifiers at the AST level.
- Literal templates compile into ordinary alternative branches containing
  `LiteralTemplatePatternLiteral` and `LiteralTemplatePatternCapture` parts.
- The literal-template matcher walks retained application components,
  attempts captures longest-first, and backtracks across later literal
  failures.
- Literal-template captures use `LiteralTemplateCapture` and the existing
  syntax/value capture path; there is no `_StrExpr` dependency.
- Matcher modes have the explicit names `IdentifierApplicationMatcher`,
  `LiteralTemplateMatcher`, and `LiteralExpressionMatcher`.
- The standard library has been migrated to backtick declarations.
- The obsolete `$!` parser, AST, renderer, evaluator, and matcher
  representations have been removed. The remaining `$!` occurrence in tests
  asserts that the obsolete spelling is rejected.
- Stale `DoOperator`, `BeginOperator`, `nativeApplicationPhrase`, built-in
  syntax identities, and host line/application fallback rules were removed.
- The experimental exact-string newline rule and its `SyntaxSequence`
  semantics were also removed; they are not part of the intended design.
- Logical newlines are retained as `LineBreak`, remain available to declared
  matchers as `\n`, and fall back through the post-rewrite `(<:>)` operation
  when no declaration consumes them.
- Horizontal source phrases are retained as `UnresolvedApplication`
  components. They are not folded into `FunctionApplication` by the parser.
- Post-rewrite operations run through a type-transparent scheduler hook after
  declared candidates are exhausted. They are not synthetic syntax rules and
  do not manufacture a candidate return type.

### Remaining

1. Complete verification of unresolved horizontal-application composition. A
   declared rule gets the first opportunity to consume the complete current
   phrase. If no rule matches, the post-rewrite fallback folds ordinary
   components left-to-right, preserving a suffix as one argument when a
   visible declaration begins there. Do not change the rewrite-stack scheduler
   or add an embedded-suffix matcher, horizontal-presentation type, or built-in
   matcher mode.
2. Parenthesize standard-library `do ... yield ...` results when a core parser
   operator belongs inside the final capture. In particular, `|` retains its
   ordinary parser precedence, so the `List`, `Maybe`, and `Collection`
   declarations must explicitly group their yielded federations.
3. Complete component-edge adjacency. The current matcher skips retained
   presentation but does not yet implement the full equal-edge/different-edge
   law specified below.
4. Finish typed capture integration for composed captures. Candidate
   classification and rewrite-result typing must agree for syntax-category
   captures which contain application structure or line breaks.
5. Add focused Std-less tests for structural literal-template matching,
   capture validation, line-break consumption, greedy backtracking, and
   fallback sequencing. Include ordinary `f x y` associativity, a function
   domain followed by `do ... yield ...`, a generic introduction followed by a
   function body, and the existing whole-application-spine precedence case.
6. Restore Std loading, then report the next unrelated parser failure without
   attempting to fix it as part of this work.
7. Resolve the remaining parser/rendering regressions, including the dedicated
   literal-template rendering assertion, and run all parser, interpreter,
   module, CLI, and fixture suites.
8. Clean all compiler warnings introduced or exposed by this work.
9. Update `GENERIC_STRING_EXPRESSIONS.md` to describe the final literal
   expression/literal template split and capture paths.
10. Delete this implementation-plan document after the feature, migration,
   verification, and documentation updates are complete.

## Surface syntax

### Grammar

The grammar remains the proposed literal-template grammar. Its `separator`
production is exactly one ASCII space. A newline, carriage return, tab,
repeated space, leading space, or trailing space is not template layout.

```text
literal-template ::= "`" template "`"

template         ::= sequence (either-operator sequence)*

sequence         ::= part (separator part)*

part             ::= atom ["?"]

atom             ::= literal
                   | capture
                   | group

group            ::= "(" template ")"

capture          ::= "%" simple-capture
                   | "%" "(" expression ")"

simple-capture   ::= quoted-string-simple-interpolation

literal          ::= identifier-literal
                   | symbolic-literal

either-operator  ::= separator "|" separator

separator        ::= " "
```

Templates and groups are nonempty. There is no padding just inside backticks
or group parentheses. `?` is adjacent to the atom it modifies. `|` has exactly
one space on each side.

The no-newline rule applies to everything between the backticks, including a
compound capture. The expression inside `%(` ... `)` otherwise uses the
ordinary Datra expression grammar.

Valid examples:

```datra
`do %_Block? yield %_Expr`
`if %Bool then %_Expr (else %_Expr)?`
`%Nat + %Nat`
`from %Int (to %IntLimit | %_Direction)`
`pair %(_x : Int) with %(_y : Int)`
```

Invalid spacing:

```datra
` do %_Expr`          # leading space
`do  %_Expr`          # repeated space
`do\t%_Expr`          # tab separator
`do %_Expr `          # trailing space
`( do %_Expr)`        # padding inside a group
`do
%_Expr`               # newline
```

### Captures

The parser after `%` is the same parser used by quoted interpolation. A simple
capture uses its simple form:

```datra
%Nat
%_Expr
%_Block?
```

The postfix `?` in `%_Block?` makes the template part optional. If `?` belongs
to the captured Datra expression, use a compound capture:

```datra
%(_Block?)
```

Compound capture syntax is also required for named captures and other
multi-token target expressions:

```datra
%(_x : Int)
%(List _Expr)
%(left? : Int | right? : Str)
```

Optional names remain distinct from optional values. In `%(_x? : Int)`, the
name is optional and the captured value is an `Int`. In `%(_x : Int?)`, the
name is required and the captured value belongs to `Int?`. Template
optionality is the postfix outside the completed capture, as in
`%(_x : Int)?`.

### Literals

An identifier literal is a nonempty run of ASCII letters, digits, `_`, and
`'`. It has no first-character restriction, so `2`, `2nd`, and `do` are all
valid identifier literals.

A symbolic literal is a nonempty ASCII run containing only non-identifier,
non-whitespace characters. Structural characters are recognized before
literal fallback:

- `%` starts a capture;
- `(` and `)` delimit a group or compound capture;
- `?` applies optionality;
- `|` composes alternatives; and
- a backtick closes the template.

The quoted-string escape rules, plus `\`` for a backtick, make a structural
character literal data. Decoding an escape must still produce a homogeneous
identifier or symbolic literal.

Literal fallback consumes one maximal non-whitespace run. The decoded run must
belong entirely to one lexical class. It is an error to combine identifier and
symbol characters in one literal:

```datra
`do+yield`            # mixed literal
`take, %Int`          # mixed literal
```

Write separate components instead:

```datra
`do + yield`
`take , %Int`
```

The separator spaces are template syntax, not literal data. The matcher can
therefore match `take, 3` even though the template spells `take , %Int`.

### Alternatives, groups, and optional parts

`|` uses the existing either/federation composition. It does not introduce a
literal-template-specific alternative type or evaluator. Parentheses group a
template, and `?` can make any completed atom optional.

```datra
`verify %_Expr | hard %_Expr`
`from %Int (to %IntLimit | %_Direction)`
`if %Bool then %_Expr (else %_Expr)?`
```

The existing optional, specification, and subfederation rules apply to the
resulting composition. The implementation must not add special cases keyed by
the names `_Expr`, `_Block`, or any standard-library binding.

## Semantic representation

The implemented representation is owned by the identifier-expression module.
It reuses one general composition type for identifier-expression grammars while
keeping literal-template leaves type-safe:

```haskell
data LiteralTemplateLiteral
  = IdentifierTemplateLiteral SimpleIdentifierString
  | SymbolTemplateLiteral SymbolLiteral

data IdentifierExpressionComposition value
  = IdentifierComposition value
  | EitherExpression
      (IdentifierExpressionComposition value)
      (IdentifierExpressionComposition value)
  | OptionalExpression (IdentifierExpressionComposition value)

newtype LiteralTemplate expression = LiteralTemplate
  { literalTemplateExpression
      :: IdentifierExpressionComposition
          (LiteralTemplateSequence expression)
  }

newtype LiteralTemplateSequence expression = LiteralTemplateSequence
  { literalTemplateParts
      :: NonEmpty
          (IdentifierExpressionComposition (LiteralTemplateAtom expression))
  }

data LiteralTemplateAtom expression
  = LiteralTemplateLiteralAtom LiteralTemplateLiteral
  | LiteralTemplateCaptureAtom expression
  | LiteralTemplateGroupAtom (LiteralTemplate expression)

data Expression
  = ...
  | LiteralTemplateExpression (LiteralTemplate Expression)
```

`EitherExpression` and `OptionalExpression` belong to the broader identifier
expression grammar; there is no `LiteralTemplateEither` or
`LiteralTemplateOptional`. A group is retained as a typed atom so the grammar
cannot admit an arbitrary Datra expression where only a template subtree is
valid.

These distinctions are required:

- identifier and symbolic literals have different validated payload types;
- a capture stores the ordinary Datra expression written after `%`;
- sequences are nonempty; and
- alternatives and optionality use the shared identifier-expression
  composition constructors.

Whitespace is validated while parsing and is not represented in the semantic
AST. The parser does not construct separator or layout nodes, retain a raw
template string, or produce a generic Atlas operand to inspect later.

The declaration-head AST distinguishes literal expressions from literal
templates before evaluation:

```haskell
data IdentifierExpression expression
  = IdentifierExpressionBody expression
  | LiteralTemplateIdentifier (LiteralTemplate expression)
```

The literal-template constructor is produced directly by the backtick parser.
It is never lowered through `AtlasIdentifierExpression` or discovered by
examining an evaluated expression.

## Parser implementation

Implement the parser in this order:

1. When a declaration head begins with a backtick, enter the literal-template
   parser and commit to that form.
2. Reject any newline or carriage return before parsing a template component.
3. Parse capture, group, alternative, and postfix structure before literal
   fallback.
4. Parse simple captures with the existing quoted-interpolation parser. Parse
   compound capture payloads with the ordinary expression parser, restricted
   to the current line.
5. Consume a maximal literal run and validate that it is entirely identifier
   or entirely symbolic.
6. Between sibling parts, require exactly one ASCII space. Around `|`, require
   exactly one ASCII space on each side. Reject leading, trailing, repeated,
   missing, tab, and newline spacing.
7. Construct the semantic tree directly and discard the accepted separator
   character.

The parser adds only three literal-template-specific diagnostics:

- `MixedTemplateLiteral`, located at the first transition between identifier
  and symbol characters in one maximal literal;
- `InvalidLiteralTemplateSpacing`, covering every violation of the one-space,
  no-newline rule; and
- `NullableLiteralTemplate`, reported when the complete composition can match
  no components.

Ordinary delimiter, interpolation, and expression failures use the parser's
existing diagnostics. Do not add any other literal-template-specific
diagnostic constructors. Other failures are already rejected by the grammar
which owns the construct.

Tests for the three diagnostics compare their typed constructors and source
locations. The design does not require a separate diagnostic model for every
literal-template production.

## Compilation

Compile a literal template into a matcher tree with two leaf kinds:

- a literal leaf constrains candidate syntax and produces no function
  argument; and
- a capture leaf retains its Datra target expression, selects candidate
  syntax, validates it, and produces one function argument.

Groups, optional parts, and alternatives compile recursively through their
existing language abstractions. Compilation must not render the template,
concatenate it into a string pattern, reparse it, infer a capture kind from a
type name, or build an Atlas-template compatibility value.

Literal expressions keep their existing exact-presentation matcher. Literal
templates get a separate matcher plan:

```haskell
data DeclarativeMatcherPlan
  = IdentifierApplicationMatcher IdentifierApplicationPattern
  | LiteralTemplateMatcher LiteralTemplatePattern
  | LiteralExpressionMatcher
      (LiteralExpressionPattern (StringExpression Expression))
```

Newline delineation will use a transient `LineBreak` AST component, not a
dependent declaration, matcher mode, or host-injected fallback rule. All
visible declarative candidates receive the complete line-break-containing
application first. If none consumes a line break, ordinary rewrite
finalization lowers it through `(<:>)`. See
[COMPOSITIONAL_LINE_BREAK_SYNTAX.md](COMPOSITIONAL_LINE_BREAK_SYNTAX.md).

The two declarative forms may share the interpolation parser, typed match
evidence, capture order, and final dependent-argument packaging. They do not
share literal matching, capture matching, whitespace rules, or a pre-match
template representation.

## Matching

### Candidate selection

The ordinary parser retains source application components in a transient
`UnresolvedApplication` node in the syntax AST. It does not create semantic
`FunctionApplication` nodes. The literal-template matcher works directly over
those retained components. It does not render an AST to choose a match,
reparse a selected substring, or introduce a second presentation layer.

Candidate selection and ordinary application compose in this order:

1. Every visible declared rule receives the complete current phrase in
   declaration order.
2. If a rule matches, its captures are rewritten and its expansion replaces
   the consumed phrase before any ordinary application fallback runs.
3. If no rule matches and an unconsumed `LineBreak` is present, the existing
   post-rewrite fallback splits the phrase through `(<:>)`.
4. Otherwise, post-rewrite application fallback examines ordinary argument
   boundaries from left to right. At the first boundary whose suffix has a
   structural candidate from the visible declared rules, it groups that suffix
   as the next argument. The child re-enters the same rewrite flow, so its
   declaration consumes its own prefix and determines its extent normally;
   the matcher itself does not search for or rewrite an embedded suffix.
5. If no declaration claims such an argument, the fallback folds that
   component into the accumulated function and continues left-to-right. Final
   semantic `FunctionApplication` nodes are therefore produced only after
   declared syntax has had its opportunity to determine the argument boundary.

For example, after `do` is declared, the unresolved phrase

```datra
&T? do yield value
```

first gives the complete phrase to declared rules. When none begins at `&T?`,
ordinary application exposes `do yield value` as its next argument. That child
expands to `FunctionBody`, after which ordinary composition yields
`FunctionApplication` of the generic introduction to the body. In contrast,
`f x y` has no declared argument boundary and finalizes as `(f x) y`.

This is an internal post-rewrite operation, not a `HorizontalApplicationMatcher`
or a synthetic declaration. It must reuse the existing candidate enumeration
and post-rewrite expansion path and must not modify the rewrite-stack scheduling
algorithm.

`UnresolvedApplication` is part of the primary transient syntax AST, not a
second presentation or matcher representation. It exists only until the
post-rewrite operation produces semantic application nodes and must not reach
evaluation or canonical persisted syntax.

### Horizontal application implementation plan

Keep this change within the existing parsing, candidate-enumeration, and
post-rewrite boundaries:

1. Keep declared-candidate enumeration and post-rewrite operations separate.
   `structuralCandidatesFor` enumerates only ordinary and scoped declarative
   rules. After those candidates are exhausted, `stackPostRewrite` invokes the
   terminal structural operation without candidate matching or typing.
2. Keep one shared terminal operation in `SyntaxRewriting.PostRewrite`. It
   first applies the existing first-unconsumed-`LineBreak` fallback. Only when
   there is no such split does it fold `UnresolvedApplication` components
   left-to-right. If the remaining suffix begins visible declared syntax, the
   operation preserves that suffix as the next argument so it re-enters normal
   rewriting as one child.
3. Use that same terminal operation in both places where a phrase becomes
   eligible for fallback: when no declared candidate matched the original
   phrase, and after a selected declaration has been expanded and its
   `structuralCandidateRemaining` components have been reattached. This is the
   compositional invariant: every declared extent is resolved first, and every
   still-unconsumed continuation passes through exactly the same line-break/
   application fallback ordering.
4. Pass a declared-extent query derived from the current `SyntaxContext` into
   the post-rewrite operation. The scheduler hook runs between candidate
   exhaustion and child traversal; a changed expression re-enters the same
   node under the same environment. Do not change literal-template matching,
   capture greediness, or `structuralCandidateRemaining`.
5. `Parsing.term` constructs `UnresolvedApplication` from two or more
   horizontal components. `applicationSelections` and `rawApplicationPhrase`
   expose those components directly to declared matching. Only the
   post-rewrite operation calls the semantic `FunctionApplication`
   constructor.
6. Add the focused regressions below before changing the standard library.
   Then parenthesize the three `|` expressions in `libs/std.datra`, load Std,
   and run the parser suite. If another unrelated parser failure appears,
   report it before making any further change.

The structural candidate which begins at an argument boundary supplies both
the selected argument extent and its unconsumed remainder. The argument
re-enters ordinary declared matching, while the remainder stays in the outer
left fold. Capture typing and candidate backtracking continue to run inside the
existing rewrite flow; the fallback does not duplicate or eagerly expand them.

Core operators retain the precedence assigned by the ordinary parser. A
literal-template capture does not reach outward through an already-parsed core
operator merely because its target is `_Expr`. Parentheses make that ownership
explicit. Thus this source leaves `|` outside the `do` expression:

```datra
&T? do yield fun () | (T; this)
```

while the intended `Either` remains inside `fun` when written as:

```datra
&T? do yield fun (() | (T; this))
```

For each rule, the matcher:

1. selects the candidate extent fixed by the enclosing declarative rewrite;
2. walks the compiled template from left to right;
3. matches literal leaves against retained identifier or symbolic syntax;
4. tries capture extents longest-first and backtracks when their target does
   not accept the selection or later parts fail;
5. applies optional and either/federation composition through the existing
   machinery; and
6. succeeds only when the complete candidate extent is consumed.

Declaration order continues to resolve competing rules. The existing matcher
policy resolves decompositions within one rule. Do not add a separate
literal-template ambiguity pass or diagnostic.

### Candidate whitespace

The exactly-one-space rule applies to the source of the literal template, not
to the candidate AST. Template spaces separate components and are not copied
into the matcher.

Each realized component exposes the lexical class of its first and last source
character:

```text
IdentifierEdge
SymbolEdge
```

Literal edges are known from their validated payload. Capture edges come from
the retained source boundaries of the selected candidate extent, never from a
rendered value.

For adjacent realized components:

- equal edge classes require candidate whitespace between them;
- different edge classes allow candidate whitespace but do not require it;
  and
- absent optional components are skipped before adjacency is computed.

This permits both presentations below:

```datra
2+2
2 + 2
```

to match:

```datra
`%Nat + %Nat`
```

It still prevents `do yield` from matching `doyield`, because two identifier
components require a candidate boundary.

### Direct capture validation

A literal-template capture is not a string expression. Its payload is the
ordinary Datra expression written after `%`, including any dependent-argument
name.

For each selected candidate extent:

1. evaluate the capture target in the declaration's lexical scope, including
   validation-only bindings established by earlier named captures;
2. if the evaluated target is a supported syntax category, use the existing
   syntax-capture operation;
3. otherwise evaluate the selected candidate expression and apply ordinary
   specification against the evaluated target; and
4. retain the selected source AST as the capture evidence and projected
   function argument.

This path reuses the implemented syntax-category and canonical value-capture
behavior. It does not construct `_StrExpr`, a string federation, a canonical
string codec, or a string-expression capture wrapper. A failed capture rejects
that candidate decomposition and lets the structural matcher backtrack.

### Capture projection

Only capture leaves contribute dependent-function inputs. Literals, groups,
optional wrappers, and alternative structure contribute match evidence but no
arguments.

Captures are projected in left-to-right source order. Existing dependent-
argument packaging remains authoritative for zero, one, and many captures,
capture names, duplicate-name validation, optional names, optional values, and
Atlas construction.

For example:

```datra
`do %_Block? yield %_Expr`
```

projects exactly `_Block?` and `_Expr`.

## Formatting

The Datra prettier is the only source renderer. It emits the canonical grammar:

- one ASCII space between sibling parts;
- one ASCII space on each side of `|`;
- no space just inside backticks or group parentheses;
- no space before postfix `?`; and
- escapes for literal structural punctuation.

Because newlines are illegal in a literal template, formatting never preserves
or introduces one between the backticks. Parsing prettier output reconstructs
the same semantic template tree.

## Standard-library migration

Migrate every obsolete template declaration in `libs/std.datra` in one change.
The resulting declarations are:

```datra
`begin %_Block? yield %_Expr` := datra.begin
`fun %_Expr` := (_Expr -> _Expr) datra.fun_body
`if %Bool then %_Expr (else %_Expr)?` :=
  (Bool; _Expr; _Expr? -> _Expr) datra.if_body
`import %(List Str) %_FunctionBody` :=
  (List Str; _FunctionBody -> _Expr) datra.import_body
`len %_Expr` := (Any -> NatLimit) datra.len_body
`with %(List _Expr) %_FunctionBody` :=
  (List _Expr; _FunctionBody -> _Expr) datra.with_body

# These parsing rules remain ordered from lower to higher precedence.
`%Bool or %Bool` := (Bool; Bool -> Bool) datra.or_body
`%Bool and %Bool` := (Bool; Bool -> Bool) datra.and_body
`%_Expr of %_Expr` := (_Expr; _Expr -> _Expr) datra.of_body
`not %Bool` := (Bool -> Bool) datra.not_body

`do %_Block? yield %_Expr` :=
  (_Block?; _Expr -> _FunctionBody) datra.do_body
let val `from %Int (to %IntLimit | %_Direction)` :=
  ({origin : Int; ((target? : IntLimit) | (direction? : _Direction))} -> IntValRange) datra.from_body
let val `range %IntLimit to %IntLimit` :=
  ({origin : IntLimit; target? : IntLimit} -> IntRange) datra.range_body
```

Keep the declarations in their existing order so precedence does not change.
Do not convert ordinary literal expressions such as `$"%(_NaturalLiteral)"`;
they are not obsolete literal templates.

Core parser operators inside a declarative capture must be parenthesized when
their ordinary precedence would otherwise place them outside the declared
form. The standard-library generic function declarations therefore use:

```datra
let val List := &T? do yield fun (() | (T; this))
let val Maybe := &T? do yield (nothing | Just T)
val Collection := &T? do yield ((List T) | (Stream T))
```

This is ordinary explicit grouping. Do not add declarative matcher projection
through `|` or another core operator to preserve an unparenthesized spelling.

Migrate test and fixture declarations by the same rules:

- `$literal` Atlas operands become literal-template literal components;
- nonliteral Atlas operands become `%` captures;
- a multi-token capture uses `%(` ... `)`;
- Atlas sequences become single-space-separated template parts;
- Atlas alternatives and optional groups become `|`, groups, and postfix `?`;
  and
- a mixed literal such as `$"take,"` becomes the two template components
  `take ,`, which still matches adjacent identifier and symbol presentation.

Examples:

```datra
# obsolete
$!($pair; (_x : Int); $with; (_y : Int)) := it

# replacement
`pair %(_x : Int) with %(_y : Int)` := it

# obsolete
$!(Int; $"++") := body

# replacement
`%Int ++` := body
```

Update design examples in other documentation at the same time; no maintained
documentation should teach `$!` syntax after the migration.

## Removal of obsolete literal templates

After the standard library, tests, fixtures, and documentation use backticks,
delete the obsolete implementation rather than retaining an adapter:

- remove `AtlasIdentifierExpression` and
  `AtlasIdentifierExpressionBody`;
- remove `AtlasIdentifierExpressionOperator` and the `$!` token;
- remove parser branches which construct Atlas identifier expressions;
- remove Atlas-template evaluation, declaration-head dispatch, matcher plans,
  and renderer branches;
- remove `AtlasSyntaxPattern`, `AtlasSyntaxPart`, and helpers which exist only
  for `$!` matching;
- remove compatibility conversions between Atlas operands and literal
  templates; and
- remove obsolete syntax tests after migrating every still-required semantic
  assertion to the literal-template path.

`$!` is rejected after this change. It is not an alias for backticks and does
not remain behind a feature flag.

## Verification plan

### Parser and AST

- Parse every literal, capture, group, optional, and alternative form.
- Prove templates and groups cannot be empty.
- Accept digit-leading identifier literals.
- Accept pure symbolic literals and escaped structural literals.
- Reject mixed identifier/symbol runs with `MixedTemplateLiteral` at the first
  transition.
- Reject leading, trailing, missing, repeated, tab, and newline spacing with
  `InvalidLiteralTemplateSpacing`.
- Prove no separator, raw whitespace, generic Atlas operand, or string pattern
  enters the semantic AST.
- Round-trip every semantic constructor through the prettier.

### Matching

- Match identifier and symbolic literals against retained candidate syntax.
- Match `%Nat + %Nat` against both `2+2` and `2 + 2`.
- Reject `doyield` for `do yield`.
- Cover optional literal, capture, and group parts.
- Cover grouped alternatives through the existing either/federation path.
- Cover full-consumption failures and trailing candidate syntax.
- Prove longest-first capture selection and backtracking follow the existing
  matcher policy.
- Prove literal components never enter the projected argument list.
- Prove capture order is stable source order.
- Prove a declared form gets the complete current application phrase before
  ordinary application fallback.
- Prove `&T? do yield value` becomes ordinary application of the generic
  introduction to the expanded `FunctionBody`.
- Prove ordinary `f x y` remains `(f x) y` when no declaration claims an
  argument boundary.
- Prove parenthesized `do yield (left | right)` captures the federation and
  unparenthesized `do yield left | right` retains the core parser's `|`
  ownership.

### Type-system interactions

- Cover syntax-category captures for expressions, blocks, function bodies,
  dependent declarations, dependent arguments, identifier expressions, and
  supported syntax lists.
- Cover ordinary value captures through evaluation and specification.
- Cover named captures, duplicate names, optional names, and optional values.
- Cover aliases, `Either`, `of`, specification, and subfederation without
  literal-template-specific name dispatch.
- Prove the literal-template AST, compiler, matcher, and tests have no
  dependency on `_StrExpr` or another planned string-expression feature.

### Migration and deletion

- Bootstrap the migrated standard library.
- Run the focused parser, matcher, interpreter, standard-library, module, and
  fixture tests through literal templates.
- Preserve standard-library precedence and declaration results.
- Search maintained source, tests, fixtures, and library files for `$!` and
  obsolete Atlas-template constructors.
- Verify literal expressions still use their exact-presentation path.
- Verify no compatibility route can lower a literal template into the removed
  Atlas representation.

The feature is complete only when the backtick path is fully exercised, the
standard library boots through it, and the obsolete `$!` representation and
dispatch paths have been deleted.
