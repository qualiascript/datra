# Backtick Declarative Syntax

## Status and scope

This document defines the parsing, representation, validation, and matching
rules for backtick declarative syntax. A backtick template describes the
surface form of a dependent declaration while making its captured operands
explicit.

```datra
`do %_Block? yield %_Expr`
```

The example has four parts: the literal `do`, an optional capture of `_Block`,
the literal `yield`, and a capture of `_Expr`. Matching consumes the entire
candidate syntax. Only the two capture parts are supplied to the declared
function.

Backtick templates are their own syntactic and AST category. They are not
Atlas expressions encoded behind an operator, and they are not reparsed
strings. The `$` operator continues to construct scalar literal expressions;
there is no `$!` token or corresponding AST constructor in this grammar.

This design uses the generic string-expression and inverse-selection model
defined in [GENERIC_STRING_EXPRESSIONS.md](./GENERIC_STRING_EXPRESSIONS.md).
It adds a typed declarative-template layer which retains literal boundaries,
grouping, optionality, and captures until matching is compiled.

## Source model

A backtick template is a nonempty, ordered tree of:

- identifier literals;
- symbolic literals;
- interpolation captures;
- grouped subtemplates; and
- ordinary optional and either/federation composition.

Sibling parts are delimited by template whitespace. Structural punctuation
belongs to the grammar and may be adjacent to the part it modifies.

```datra
`if %Bool then %_Expr (else %_Expr)?`
`%Nat + %Nat`
`from %Int (to %IntLimit)?`
```

The source whitespace delimits parts; it is not copied into an unstructured
pattern string. Match-time whitespace constraints are derived compositionally
from the parts on each side of a boundary.

## Lexical classes

### Identifier literals

An identifier literal is a nonempty `SimpleIdentifierString` whose characters
come from the ordinary Datra identifier-character class: ASCII letters,
digits, `_`, and `'`. There is no first-character restriction. `2`, `2nd`,
and `do` are all valid identifier spellings.

This simplification applies to identifier validation generally, not only to
backtick parsing. A parser position which explicitly expects an identifier,
such as `$` or a backtick literal, accepts `2`. In an ordinary expression
position, the lexer first consumes the maximal identifier-character run: an
all-decimal run is a numeric literal, while a run containing any other
identifier character is an identifier. Thus ordinary `2` remains a number,
ordinary `2nd` is an identifier, and `$2` and backtick `2` are explicitly
identifiers.

An identifier literal denotes the same scalar literal expression as the `$`
form with that identifier:

```datra
do       # denotes $do
yield    # denotes $yield
2        # denotes $2
```

The AST retains `SimpleIdentifierString`; it does not store the literal as an
unchecked `String`.

### Symbolic literals

A symbolic literal is a nonempty ASCII run whose characters do not belong to
the identifier class and are not whitespace. In particular, a symbolic
literal can never contain a space, tab, carriage return, newline, or any other
horizontal or vertical whitespace character. A symbolic literal denotes the
same scalar literal expression as a quoted `$` operand:

```datra
+        # denotes $"+"
++       # denotes $"++"
```

The AST retains a validated `SymbolLiteral` newtype whose smart constructor
checks all three properties: nonempty, ASCII, and entirely non-identifier,
non-whitespace characters. A symbolic literal is not represented by a bare
`String`, an identifier with an ad hoc flag, or a rendered expression.

The structural parser reserves punctuation only while it is unescaped and in
a position where a structural production applies. Once escaped, punctuation
may be symbolic literal data. This makes the semantic character predicate
simple:

```text
isSymbolLiteralCharacter c =
  isAscii c && not (isIdentifierCharacter c) && not (isWhitespace c)
```

### Structural punctuation

The backtick delimiters, `%`, parentheses, postfix `?`, and `|` are parsed as
grammar before the parser attempts literal fallback. Consequently they need
no exceptions in literal classification:

- `%` starts an interpolation capture;
- `(` and `)` delimit a grouped template or the payload of `%(`;
- `?` applies ordinary optionality to the immediately preceding template
  atom;
- `|` uses the ordinary either/federation composition; and
- `` ` `` terminates the template.

An escaped structural character is data rather than grammar. Backtick
templates use the quoted-string escape mechanism, extended with `` \` `` for
the delimiter. Escaped data is still required to form a homogeneous
identifier or symbolic literal after decoding. The usual escaped `%`, `?`,
`#`, backslash, newline, and hexadecimal characters retain their quoted-string
decoding, but the decoded character must satisfy the literal invariant. Thus
an escape which decodes to a space or newline is rejected as
`WhitespaceInTemplateLiteral`; escaping whitespace cannot smuggle it into a
symbolic literal.

`#` introduces the same line comment as it does inside quoted string
interpolation. The comment itself contributes no template part. An escaped
`#` contributes symbolic literal data.

### Mixed literals

Literal fallback consumes one maximal, non-whitespace source run after all
structural forms have had an opportunity to parse. The decoded run must be
homogeneous:

- all identifier characters produce an identifier literal;
- all symbolic characters produce a symbolic literal; and
- a run containing both classes is a compile-time `MixedTemplateLiteral`
  error.

Whitespace always terminates the run and belongs to template layout. It is
never retained by either literal constructor.

The parser must not repair a mixed run by splitting it at the lexical-class
transition. Thus this is invalid:

```datra
`do+yield`
```

and this is the explicit form:

```datra
`do + yield`
```

This rule is not implemented as a list of exceptions for `%`, `?`, or
parentheses. Those characters have already been consumed by the structural
grammar when literal fallback runs. A future structural form obtains the same
behavior by being added to the structural grammar, without changing mixed
literal validation.

## Grammar

The following grammar describes template structure. `hspace` is nonempty
horizontal whitespace. `linebreak` includes the following indentation and
comments. `expression` is parsed by the ordinary Datra expression parser.

```text
backtick-template  ::= "`" template-layout? template "`"

template           ::= sequence (either-operator sequence)*

sequence           ::= part (separator part)*

part               ::= atom ["?"]

atom               ::= literal
                     | capture
                     | group

group              ::= "(" template-layout? template template-layout? ")"

capture            ::= "%" simple-capture
                     | "%" "(" expression ")"

simple-capture     ::= quoted-string-simple-interpolation

literal            ::= identifier-literal
                     | symbolic-literal

either-operator    ::= template-layout? "|" template-layout?

separator          ::= hspace
                     | permitted-linebreak

permitted-linebreak
                   ::= linebreak
                       # valid only when the preceding part is a literal

template-layout    ::= hspace | permitted-linebreak
```

`simple-capture` is exactly the simple interpolation production used by
quoted strings. It accepts the same atom forms and stops at the same boundary.
Backtick parsing must call that shared parser rather than reproduce or extend
its token rules.

Postfix `?` then applies uniformly to the completed template atom:

```datra
%_Block?       # optional capture of _Block
keyword?       # optional identifier literal
%(_Expr)?      # optional compound capture
(else %_Expr)? # optional group
```

When `?` must be part of the captured Datra expression rather than template
optionality, it is written inside a compound interpolation:

```datra
%(_Block?)
```

Compound capture payloads use the quoted-interpolation spelling `%(` ... `)`:

```datra
`with %(List _Expr) %_FunctionBody`
```

Parentheses without a leading `%` group template parts. This is the template
counterpart of ordinary grouping and Atlas composition: it preserves the
contained part sequence and permits ordinary postfix optionality. It does not
turn the contained source into an opaque substring.

`|` uses the existing either/federation parser, precedence, AST, evaluation,
specification, and subfederation mechanisms. It is not a backtick-specific
branch list. Parentheses disambiguate its operands in the same way as ordinary
Datra expressions:

```datra
`verify (%_Expr) | (hard %_Expr)`
```

An escaped `\|` is symbolic literal data. Other ordinary Datra operators are
not automatically imported into the template grammar: an unescaped `+`, for
example, remains the symbolic literal in `%Nat + %Nat`.

The parser selects structural productions before literal fallback and commits
after consuming a structural introducer. A malformed capture or group is
therefore diagnosed as that construct; it is never reconsidered as literal
text.

## Relationship to `$` string-expression templates

Backtick templates and `$` string-expression templates share one capture
model but deliberately have different literal-matching models.

Both forms are ordered compositions of literal constraints and `%`
interpolations. In both forms:

- only interpolation nodes produce captures;
- literal nodes constrain the match and are never supplied to the function;
- captures retain their ordinary `_StrExpr T` provenance;
- capture order is left-to-right structural source order;
- optional, either/federation, and dependent-argument behavior reuse the
  existing language abstractions; and
- a successful match consumes the complete candidate presentation selected
  by the enclosing parser.

The difference is how literal constraints and their boundaries are read.

| Property | `$` string-expression template | Backtick template |
| --- | --- | --- |
| Literal domain | Arbitrary decoded ASCII string data | Typed identifier or symbolic literals |
| Literal matching | Exact decoded characters | Exact literal characters plus derived boundary whitespace |
| Spaces and newlines | Exact literal data | Template layout; never symbolic literal data |
| Mixed identifier/symbol text | Valid literal text | Invalid as one literal part |
| `%` interpolation | Quoted-string interpolation grammar | The same simple and compound interpolation grammar |
| `?`, `|`, parentheses | Literal unless part of an interpolated Datra expression | Structural template composition unless escaped |
| Captured values | Interpolation parts only | Interpolation parts only |
| Compiler | Exact string-expression concatenation | Typed component and boundary compiler |
| Matcher | Character-exact presentation matcher | Component matcher with lexical-edge constraints |

### Exact `$` literal matching

A `$` template literal consumes exactly the decoded characters written in its
string-expression literal component. Escape spelling and comments are resolved
by quoted-string parsing first; the resulting character sequence is what must
match. No tokenization, whitespace normalization, AST parsing, or lexical-edge
rule is applied to that literal sequence.

The direct quoted operand of `$` is parsed by the ordinary quoted
string-expression parser, including interpolation. Thus `$"literal"` is a
zero-capture exact template and `$"%Nat + %Nat"` is an interpolated exact
template. Parenthesized `$(expression)` remains available for a general string
expression; it is not required merely to enable quoted interpolation.

For example:

```datra
$"%Nat+%Nat"         # matches the presentation 2+2, not 2 + 2

$"%Nat + %Nat"       # matches the presentation 2 + 2, not 2+2

`%Nat + %Nat`        # matches both presentations
```

Inside each quoted string, every decoded space is an exact literal constraint.
Multiple spaces, tabs, and newlines are distinct and must not be collapsed. An
escaped literal `%` is exact literal data; an unescaped interpolation `%` is a
capture.

“Exact” refers to the candidate presentation supplied by its `_StrExpr`
codec. It does not require retention of incidental original source trivia when
that codec defines a canonical presentation. For direct string candidates,
the presentation is the string value itself. For syntax-category candidates,
the category's canonical-string codec defines the presentation. The matcher
must not independently render or parse an AST to choose a different notion of
exactness.

### Backtick boundary matching

Backtick source whitespace separates typed components rather than contributing
literal string data. The matcher uses the lexical-edge rule defined below, so
word-to-symbol and symbol-to-word boundaries may omit candidate whitespace,
while equal-class boundaries require it. This is why `%Nat + %Nat` accepts
both `2+2` and `2 + 2` without weakening the exact semantics of `$` templates.

### Required `$` implementation correction

The `$` declarative-template compiler must retain each decoded literal chunk
exactly. In particular, it must not:

- send a direct quoted operand through a literal-only parser which suppresses
  interpolation;
- split a literal with `words` or another whitespace tokenizer;
- join template components with `unwords` or inserted separators;
- parse literal text through the neutral Datra parser and match only the
  resulting AST shape; or
- include a literal component in the projected dependent arguments.

Adjacent literal chunks may be coalesced only by lossless string
concatenation. The compiled matcher is the ordinary exact concatenation of
singleton literal-string components and typed `_StrExpr T` capture components
described in [GENERIC_STRING_EXPRESSIONS.md](./GENERIC_STRING_EXPRESSIONS.md).
This exact matcher is not shared with backticks. The implementations share
only the generic capture-selection interface and typed evidence after their
respective literal and boundary matchers have succeeded.

### Compiler-path separation

The two forms have distinct declaration-head AST variants and distinct
compiled matcher plans:

```haskell
data DeclarativeIdentifier expression
  = ExactStringIdentifier expression
  | BacktickIdentifier (BacktickTemplate expression)

data DeclarativeMatcher expression
  = ExactStringMatcher (ExactStringTemplate expression)
  | BacktickMatcher (CompiledBacktickTemplate expression)
```

The names are schematic, but the sum types and separation are normative.
Neither variant is represented as an Atlas expression, and neither compiler
discovers its variant by inspecting an untyped expression after parsing.
The `ExactStringIdentifier` payload remains the ordinary string-producing
expression and retained concatenation provenance defined by the generic
string-expression design; this sketch does not reintroduce a closed semantic
`StringExpression` AST.

The paths may share:

- the quoted-string interpolation parser used after `%`;
- generic `_StrExpr T` inverse selection for a capture;
- typed match evidence and capture ordering;
- existing optional, either/federation, and specification machinery; and
- existing dependent-argument packaging after matching.

They must not share:

- a declaration-head AST constructor;
- literal tokenization or normalization;
- a lowered neutral-AST pattern;
- whitespace or boundary semantics; or
- a matcher plan which erases whether it came from `$` or backticks.

The common result of matching is typed selection evidence, not a common
pre-match template representation. The exact `$` compiler preserves decoded
string chunks. The backtick compiler preserves typed literals, structural
composition, and boundary constraints. Only after either matcher succeeds may
their capture selections enter the shared dependent-argument path.

### Removal of the Atlas-template operator

`$!` is not a compatibility spelling for backticks and has no place in the
resulting parser, AST, evaluator, prettier, source renderer, declaration-head
model, or matcher dispatch. The implementation must remove:

- `AtlasIdentifierExpression` and `AtlasIdentifierExpressionBody`;
- `AtlasIdentifierExpressionOperator` and the `$!` token;
- evaluated Atlas-identifier plans and their renderer branches;
- declaration branching which treats an Atlas operand as a template; and
- tests, fixtures, or standard-library declarations which retain `$!`.

Backtick templates are parsed directly into `BacktickTemplate`. They must not
be lowered to the former Atlas operand shape or routed through a compatibility
adapter. Likewise, exact `$` templates must not be routed through the backtick
compiler merely because both forms contain interpolation captures.

## Template whitespace

Horizontal whitespace may delimit any two sibling parts. A source line break
may delimit parts only when the immediately preceding completed part is an
identifier literal or symbolic literal.

```datra
`do
  %_Block? yield %_Expr`       # valid

`do %_Block?
  yield %_Expr`                # LineBreakAfterCapture
```

Closing a group or applying `?` does not disguise the preceding part for this
rule. A line break after a group is valid only when the group's rightmost
realized part is a literal on every branch. A line break after an optional
part is valid only when both the present and absent branches leave a literal
as the rightmost realized part. This branch-total rule prevents layout from
depending on whether an optional capture happens to match.

Line breaks within a `%(` compound capture belong to the ordinary Datra
expression parser and are not template separators. Comments follow the same
rule as the whitespace which terminates them.

Leading and trailing template layout is accepted only when it satisfies the
same line-break rule. In particular, a line break immediately before the
closing backtick is rejected when the template ends in a capture.

## Semantic AST

The semantic representation distinguishes concepts which have different
matching rules:

```haskell
data BacktickLiteral
  = IdentifierBacktickLiteral SimpleIdentifierString
  | SymbolBacktickLiteral SymbolLiteral

data BacktickPart expression
  = BacktickLiteralPart BacktickLiteral
  | BacktickCapturePart expression
  | BacktickGroupPart (BacktickTemplate expression)
  | BacktickOptionalPart (BacktickPart expression)

newtype BacktickSequence expression =
  BacktickSequence (NonEmpty (BacktickPart expression))

-- Conceptually: the existing Either/federation composition whose leaves are
-- BacktickSequence values.
type BacktickTemplate expression =
  ExistingFederationComposition (BacktickSequence expression)
```

Exact constructor names may follow local naming conventions, but the
distinctions and validated payload types are normative. In particular, the
implementation must reuse or generalize the existing either/federation
abstraction; it must not add a parallel `BacktickAlternative` evaluator,
specification rule, or subfederation rule.

The parser may retain a parser-local separator node:

```haskell
data TemplateSeparator
  = HorizontalTemplateSeparator
  | LineTemplateSeparator
```

That node exists only long enough to validate layout and attach precise
diagnostic spans. Raw whitespace is not part of the semantic template. The
semantic AST also does not contain a generic Atlas operand which later needs
to be inspected to discover literals and captures.

Literal nodes retain their lexical class until the matcher is compiled. Their
scalar `$` meaning is a semantic law, not an instruction to erase them early:
the lexical class is required by the adjacency rules below.

## Compilation and matching

### Components

Compilation produces an ordered matcher tree with two leaf kinds:

- a literal leaf constrains the candidate but produces no capture; and
- a capture leaf uses the ordinary inverse selection for the interpolation
  payload and produces one typed capture.

Groups compile recursively. Optional parts use the existing optional-value
and optional-name abstractions. `|` uses the existing either/federation
abstraction. Compilation does not render the AST and reparse it, infer a part
kind from a type name, or recover boundaries from concatenated text.

### Lexical edges

Each realized, nonempty matched component exposes its left and right lexical
edge:

```text
IdentifierEdge  # adjacent character is an identifier character
SymbolEdge      # adjacent character is a symbolic character
```

Literal edges are known statically. Capture edges come from the concrete
substring selected by the capture's ordinary string-expression inverse. A
group exposes the first and last edges of its realized children. An absent
optional part exposes no edges, so adjacency is computed across it.

For every pair of adjacent realized components:

- equal edge classes require at least one whitespace character between them;
- different edge classes permit zero or more whitespace characters; and
- an empty component is skipped before the rule is applied.

This is one boundary rule, not a collection of operator-specific cases.

```datra
`%Nat + %Nat`       # matches both 2+2 and 2 + 2
`do yield`          # matches do yield, never doyield
`+ -`               # requires whitespace between the two symbolic literals
```

The rule prevents two declared components from collapsing into a single
token of the same class. It still permits the normal lexical transition
between identifier-like and symbolic text.

Whitespace is matched at component boundaries rather than by inserting
literal spaces into the pattern. When whitespace is required, any whitespace
character accepted by the ordinary source lexer satisfies the boundary. The
template-source line-break restriction remains a separate construction-time
invariant.

A capture owns no leading or trailing template-separator trivia. The boundary
matcher owns that trivia, while whitespace internal to the captured ordinary
Datra expression remains part of the capture. The enclosing dependent-
expression parser fixes the candidate extent before template matching begins;
full consumption is measured against that fixed extent.

Comments in a backtick declaration are parser trivia. Candidate comments are
handled by the ordinary candidate parser before inverse selection. The
template matcher receives canonical candidate text and therefore matches
actual whitespace characters, never comment spellings.

### Full consumption and capture projection

A template match succeeds only when:

1. every required template part succeeds;
2. every chosen optional branch succeeds;
3. all adjacency constraints succeed; and
4. the candidate extent is consumed completely.

A prefix match with an unconsumed suffix is not a successful match for the
same candidate extent.

Only `BacktickCapturePart` nodes contribute function inputs. Literal leaves,
groups, separators, and optional wrappers never enter the dependent-argument
projection. Captures are projected in left-to-right depth-first source order
using the existing dependent-argument packaging. For example:

```datra
`do %_Block? yield %_Expr`
```

produces exactly the `_Block?` and `_Expr` selections. The literal `do` and
`yield` matches remain evidence that the declaration applied, but are not
passed to the function.

The existing dependent-argument abstraction remains authoritative for the
zero-, one-, and many-capture cases, capture names, duplicate-name validation,
and Atlas construction. Optional parts use ordinary optional semantics for
their projected captures; nested optionality, aliases, and optional names are
normalized by the existing optional-value machinery. `|` combines projections
through ordinary either/federation evaluation and specification. Backtick
matching adds no capture container, absence sentinel, positional reconciliation
algorithm, or branch-specific calling convention.

### Ambiguity and admissibility

Each capture is selected through its retained `_StrExpr T` provenance and the
ordinary specification engine. Aliases, optional names, `Either`, `of`, and
subfederations therefore keep their ordinary semantics. Backtick matching
must not introduce a separate name-based table for `_Expr`, `_Block`, or
other syntax categories.

An admissible template has a unique stable decomposition for every accepted
candidate. If adjacent captures, empty-producing captures, or optional
branches permit more than one decomposition or capture projection, declaration
validation reports an ambiguity before the declaration can be invoked.

The admissibility decision must make structural progress on either the finite
template tree or the retained operand of `_StrExpr`. It must not recursively
reconstruct the same template or string-expression query. Existing
specification/subfederation cycle detection remains authoritative.

## Diagnostics

Parsing and validation report typed diagnostics with source spans. Rendering
those diagnostics to text is a separate concern. At minimum the diagnostic
model distinguishes:

- `UnterminatedBacktickTemplate`;
- `MixedTemplateLiteral` with the first lexical-class transition;
- `WhitespaceInTemplateLiteral` with the decoded offending character;
- `InvalidTemplateSymbol`;
- `MissingTemplateSeparator`;
- `MalformedTemplateCapture`;
- `UnbalancedTemplateGroup`;
- `TemplatePostfixWithoutOperand`;
- `LineBreakAfterCapture`;
- `AmbiguousBacktickTemplate` with competing decompositions.

Parser and test helpers inspect these constructors, not fragments of rendered
messages. The ordinary diagnostic renderer owns labels, source excerpts, and
human-readable explanations. Invalid optional, either/federation, and
dependent-argument compositions reuse their existing typed diagnostics; the
backtick implementation must not wrap them in new stringly typed errors.

## Empty forms and canonical formatting

Empty templates and empty groups are invalid. Their semantic representations
use `NonEmpty`, so they cannot reach matching, optionality, or ambiguity
checking as degenerate cases.

The prettier emits one ASCII space between sibling parts, one ASCII space on
each side of `|`, no space just inside group parentheses, and no space before
postfix `?`. It emits the escape needed whenever symbolic literal data would
otherwise be parsed as structural punctuation. Source newlines are layout,
not semantic data, and canonical output normalizes them to spaces.

## Required invariants

### Construction invariants

1. Every semantic template and grouped sequence is nonempty.
2. Every literal is nonempty and belongs to exactly one lexical class.
3. Identifier literal payloads are validated `SimpleIdentifierString` values;
   validation has no first-character restriction.
4. Symbol literal payloads are validated `SymbolLiteral` values containing no
   whitespace characters.
5. A mixed literal never enters the semantic AST.
6. Structural punctuation is consumed before literal fallback; it is not
   excluded by an independently maintained exception list.
7. Every successful parser branch consumes input. Repetition cannot accept an
   empty part or loop without progress.
8. Layout is validated once at AST construction. Later phases do not inspect
   source text to rediscover separators.
9. Backtick simple captures call the exact parser used by quoted-string simple
   interpolation, and direct quoted `$` operands call the full quoted
   string-expression parser.
10. Postfix `?` may wrap every completed template atom.
11. Unescaped `|` is parsed by ordinary either/federation composition before
    symbolic literal fallback.

### Representation invariants

12. Backtick templates have one parser, one semantic AST, and one compiler.
13. No Atlas expression is used as an intermediate encoding of a template.
14. No `$!` operator, compatibility constructor, or dual matching path exists.
15. `$` retains only its scalar literal-expression meaning.
16. A `$` string-expression template retains every decoded literal chunk
    exactly, including all whitespace and punctuation.
17. `$` and backtick declaration heads have distinct typed AST variants,
    compilers, and matcher plans.
18. The two paths meet only at typed match evidence, generic capture
    selection, and existing dependent-argument packaging.
19. Literal lexical class, grouping, optionality, and capture identity remain
    explicit until matcher compilation.
20. Either/federation, optionality, and dependent-argument packaging reuse the
    existing language abstractions and decision procedures.
21. No semantic decision is made by comparing rendered source, diagnostic
    text, or type-name strings.
22. The Datra prettier is the only semantic source renderer, and parsing its
    canonical output reconstructs the same template tree.

### Matching invariants

23. A successful match consumes the complete candidate extent.
24. Every candidate position is consumed at most once along a selected branch.
25. Captures cannot consume leading or trailing template-separator trivia.
26. Literal parts in both template forms constrain matching but never
    contribute function arguments.
27. Every capture node contributes exactly one stable, typed capture position.
28. Capture order is structural source order and is independent of optional
    branch selection.
29. `$` literal components match exact decoded character sequences and never
    use lexical-edge whitespace rules.
30. Backtick whitespace requirements are computed solely from adjacent
    realized edge classes.
31. Equal backtick edge classes require whitespace; unequal edge classes do
    not.
32. Empty and absent backtick components are removed before adjacency is
    computed.
33. Capture selection, `of`, optional values, aliases, and subfederation use
    the ordinary specification machinery.
34. Candidate comments are handled before matching and never interpreted by
    the template matcher.
35. Ambiguous decompositions are rejected during declaration validation rather
    than resolved by parser order or longest-match accidents.
36. Matching and admissibility terminate by structural descent and existing
    specification cycle detection; they never render and reparse candidates.

### Diagnostic invariants

37. Every rejected structural form has a typed diagnostic and a precise
    source span.
38. Once a structural introducer is consumed, failures remain attributed to
    that structure and cannot fall back to a misleading literal diagnostic.
39. Diagnostic tests compare structured failures. Rendered wording is tested
    only in the diagnostic-renderer suite.
40. Failed parsing or matching never leaves a partially constructed semantic
    template or dependent-argument projection observable.

## Verification

The implementation is complete only when the following are covered by focused
unit tests and end-to-end declaration tests:

1. identifier and symbolic literal construction, including digit-leading
   identifiers, invalid symbolic characters, and mixed runs;
2. shared-parser tests proving that `$` and backtick simple captures have
   exactly the same interpolation boundaries as quoted strings;
3. postfix optionality on literals, simple captures, compound captures, and
   nested groups;
4. horizontal separators and every allowed and forbidden line-break boundary;
5. escapes and comments, including escaped structural punctuation and
   rejection of escaped spaces and newlines as literal data;
6. exact `$` literal tests covering zero, one, and multiple spaces, tabs,
   newlines, punctuation, escaped `%`, and adjacent literal chunks;
7. paired tests proving that `$` templates distinguish `2+2` from `2 + 2`
   while `` `%Nat + %Nat` `` accepts both presentations;
8. paired capture tests proving that both forms pass only interpolation
   selections and never their literal constraints;
9. full-consumption failures and trailing candidate text in both matcher
   paths;
10. `2+2`, `2 + 2`, `do yield`, `doyield`, and consecutive symbolic
    backtick cases;
11. parenthesized `|` composition, escaped literal `\|`, and equivalence with
   the ordinary either/federation evaluator;
12. ambiguity from adjacent or empty-producing captures;
13. optional captures, aliases, optional names, `of`, specification, and
    subfederation interaction through the existing implementations;
14. equivalence with existing dependent-argument packaging for zero, one, and
    many captures, including named and duplicate-name cases;
15. parser/prettier round trips for every template constructor and normalized
    spacing around `|` and `?`;
16. property tests that mixed literals cannot be constructed through any
    public smart constructor;
17. property tests that successful matching consumes the candidate exactly
    once and returns only the structurally declared captures;
18. tests showing that exact `$` compilation never calls the neutral structural
    parser and backtick compilation never constructs an exact-string matcher;
19. diagnostics asserted by constructor and span rather than rendered text;
20. standard-library and fixture declarations expressed exclusively with
    backtick syntax; and
21. source-wide checks proving that `$!`, its AST/operator constructors, and
    the shared `$`/Atlas-template lowering path no longer exist.
