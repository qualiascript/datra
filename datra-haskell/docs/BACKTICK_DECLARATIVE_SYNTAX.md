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

The parser constructs a dedicated literal-template tree:

```haskell
data LiteralTemplateLiteral
  = IdentifierTemplateLiteral SimpleIdentifierString
  | SymbolTemplateLiteral SymbolLiteral

data LiteralTemplateAtom expression
  = LiteralTemplateLiteralAtom LiteralTemplateLiteral
  | LiteralTemplateCaptureAtom expression
  | LiteralTemplateGroupAtom (LiteralTemplate expression)

data LiteralTemplatePart expression
  = RequiredTemplatePart (LiteralTemplateAtom expression)
  | OptionalTemplatePart (LiteralTemplateAtom expression)

newtype LiteralTemplateSequence expression =
  LiteralTemplateSequence (NonEmpty (LiteralTemplatePart expression))

type LiteralTemplate expression =
  ExistingFederationComposition (LiteralTemplateSequence expression)
```

Names may follow local conventions, but these distinctions are required:

- identifier and symbolic literals have different validated payload types;
- a capture stores the ordinary Datra expression written after `%`;
- grouping and optionality remain explicit;
- sequences and groups are nonempty; and
- alternatives reuse the existing either/federation representation.

Whitespace is validated while parsing and is not represented in the semantic
AST. The parser does not construct separator or layout nodes, retain a raw
template string, or produce a generic Atlas operand to inspect later.

The declaration-head AST distinguishes literal expressions from literal
templates before evaluation:

```haskell
data DeclarativeIdentifier expression
  = LiteralExpressionIdentifier expression
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

The parser adds only two literal-template-specific diagnostics:

- `MixedTemplateLiteral`, located at the first transition between identifier
  and symbol characters in one maximal literal; and
- `InvalidLiteralTemplateSpacing`, covering every violation of the one-space,
  no-newline rule.

Ordinary delimiter, interpolation, and expression failures use the parser's
existing diagnostics. Do not add any other literal-template-specific
diagnostic constructors. Other failures are already rejected by the grammar
which owns the construct.

Tests for the two new diagnostics compare their typed constructors and source
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
data DeclarativeMatcherPlan expression
  = LiteralExpressionMatcher (CompiledLiteralExpression expression)
  | LiteralTemplateMatcher (CompiledLiteralTemplate expression)
  | NativeApplicationMatcher NativeApplicationPattern
  | LineSequenceMatcher
  | HorizontalApplicationMatcher
```

The two declarative forms may share the interpolation parser, typed match
evidence, capture order, and final dependent-argument packaging. They do not
share literal matching, capture matching, whitespace rules, or a pre-match
template representation.

## Matching

### Candidate selection

The ordinary parser retains candidate presentation in the existing syntax AST.
The literal-template matcher works over that retained structure and its source
boundaries. It does not render an AST to choose a match and does not reparse a
selected substring.

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
to candidate presentation. Template spaces separate components and are not
copied into the matcher.

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
