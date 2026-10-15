# Optional value lookup and canonical string-template capture

## Summary

Change `~` from name-oriented parser sugar into a first-class prefix operator
over string expressions.

For a concrete string, the operator searches the current lexical scope and
returns a `Maybe` containing both the requested key and the resolved value:

```datra
begin
  a := "x"
  x := 123
yield ~a
```

The operand of `~a` is evaluated. The example therefore queries `"x"`; it does
not query the literal name `"a"`. A literal-name lookup must be written
`~"a"`.

Conceptually, a successful result is:

```datra
Just {key : "x"; value : 123}
```

and an absent binding produces `nothing`. The concrete rendering of the
existing `Just` assignment wrapper may differ, but the contained value is an
argument map with `key` and `value` slots in that order.

When the operand evaluates to a string template with capture holes, `~`
returns a function. Its domain is the argument map formed by the capture
domains in source order. Applying the function validates the supplied values,
renders their canonical forms into the template, and performs the same
optional lookup:

```datra
~"arg%Nat" 4
```

has domain `{Nat}`, constructs the key `"arg4"`, and returns either `nothing`
or `Just {key : "arg4"; value : <the value of arg4>}`.

This work also changes reverse string-template matching. Captures must use the
same preparation and validation rules as function arguments and must be in
canonical form. Generic `of` membership is no longer the implementation of a
string capture.

## Goals

1. Make the right operand of `~` an evaluated string expression.
2. Make failed lookup an ordinary `Maybe` result rather than an
   `UnknownIdentifier` error.
3. Preserve the queried key together with the resolved value.
4. Turn capture-bearing string templates into functions whose domains describe
   their captures.
5. Use function-domain validation for both template application and reverse
   string-template matching.
6. Require canonical captured text, including for dependent or named capture
   domains.
7. Preserve a distinct, strict representation for compiler-generated lexical
   references and ordinary identifier evaluation.

## Non-goals

- `~` does not search an arbitrary map. It searches the lexical scope captured
  when the operator is evaluated.
- This change does not alter ordinary identifier references or `value.name`
  scope access.
- This change does not alter declarative syntax matching introduced with the
  syntax `%` operator. Syntax holes continue to capture ASTs according to the
  syntax-rewriting rules; they are not canonical string captures.
- This change does not make every lookup failure optional. Errors encountered
  while evaluating an existing binding, ambiguity errors, protection errors,
  and reduction failures remain errors.

## Current behavior

`Parsing.valueOfExpression` currently parses only one or more names. It then
expands each name into:

```haskell
ScopeAccess
  (contextualAccess (IdentifierString "_this"))
  (IdentifierReference name)
```

Consequently:

- `~a` treats `a` as syntax naming the binding `a`;
- `~(a, b)` is a special list of two strict accesses;
- a missing name raises `UnknownIdentifier` or a named-access error;
- the identifier wrapper is discarded and only its payload is returned; and
- no `~` node survives in the AST, so the interpreter cannot distinguish a
  user lookup from an ordinary opened-scope access.

`DatraLanguage.AST.Source` recognizes the expanded shape and renders it back as
`~`. `FunctionClosure` and canonical dependency rendering also rely on that
same shape for strict generated references. That coupling must be removed:
after this change, an optional dynamic lookup cannot be used to reconstruct a
strict closure dependency.

String templates currently become string federations. A concrete string is
selected from such a federation by `selectStringFederationMember`, whose leaf
checks call the general federation-selection logic used by `of`. This can
accept a canonical identifier assignment as a member of a dependent identifier
domain even when the desired capture is its underlying value. For example, it
can give `"arg%(_x : Nat)"` the spelling `"arg(_x := 4)"`. The desired lookup
key is instead the literal canonical rendering of the captured value:
`"arg4"`.

## Language semantics

### Concrete-string lookup

For `~keyExpression`:

1. Evaluate `keyExpression` in the current scope.
2. Require exactly one total ASCII string.
3. Resolve that string as a name in the current lexical scope using ordinary
   identifier resolution order, including canonical aliases and normal
   shadowing behavior.
4. If no binding exists, return `nothing`.
5. If a binding exists, evaluate it normally and return a `Just` value whose
   payload is `{key : queriedString; value : resolvedValue}`.

The `key` field contains the string supplied by the program, not an internal
alias or dependency name reached during resolution. The `value` field is the
same value an ordinary strict reference to the resolved binding would produce,
including its scope-protection and handoff behavior.

Only absence becomes `nothing`. In particular, an existing deferred binding
that fails to evaluate still reports its original error.

The operator is implemented in the core interpreter and constructs the
existing internal `Nothing | Just T` representation directly. It must not
depend on whether the user has imported the `Std.Maybe` or `Std.nothing`
bindings.

### Result shape

Introduce one helper that constructs the success payload rather than assembling
identifier values at every call site:

```haskell
lookupPairValue
  :: String
  -> InterpretedValue
  -> Either InterpretingError InterpretedValue
```

It constructs an argument map with two named members:

```text
key   : <the queried string>
value : <the resolved value>
```

These are simple named members, constructed with the same identifier-value
machinery as other named argument-map fields; they are not lossy coercions to
`Str` and `Any`. The runtime values therefore remain precise. Where a stable
function result contract is required, it can be described broadly as
`Maybe {key : Str; value : Any}` while returning the precise pair. A second
helper wraps the pair as `Just`, while the miss path uses the core `Nothing`
constructor.

### Capture-bearing template lookup

A string-template value must retain a capture plan:

```haskell
data EvaluatedStringTemplate = EvaluatedStringTemplate
  { stringTemplateSegments :: [EvaluatedStringTemplateSegment]
  , stringTemplateCaptures :: [InterpretedValue]
  }

data EvaluatedStringTemplateSegment
  = EvaluatedStringLiteral String
  | EvaluatedStringCapture CaptureIndex InterpretedValue
```

The exact representation is provisional. The required properties are:

- literal text and capture order are retained;
- each capture retains its pre-`toString` value/domain;
- the existing converted string federation remains available for ordinary
  string specification and projection; and
- the plan survives aliases and other wrappers that currently preserve a
  `TemplateForm`.

`interpretStringTemplateWith` already evaluates every interpolation before
calling `toStringValue`. It should build the capture plan at that boundary.
Interpolations which evaluate to total values are folded into literal text and
do not add parameters. A template with no remaining captures is therefore a
concrete-string lookup. A template with one or more captures produces a
function.

The function has:

- a domain made with `makeArgumentMapPreservingSingleton` from the capture
  domains in source order;
- a codomain equivalent to `Maybe {key : Str; value : Any}`;
- a captured lexical scope equal to the scope in which `~template` was
  evaluated; and
- no lookup side effect until invocation.

Examples:

| Template | Function domain |
| --- | --- |
| `"arg%Nat"` | `{Nat}` |
| `"cell%Nat-%Bool"` | `{Nat; Bool}` |
| `"arg%(_x : Nat)"` | `{_x : Nat}` |
| `"arg%(2 + 2)"` | no function; immediate lookup of `"arg4"` |

Invocation must go through the same argument schema and preparation path as an
ordinary function call. In the current implementation that means sharing the
logic behind `argumentSchemaFromValue` and `overloadArgumentSchemaComplete`,
not merely checking `supplied of domain` with `subfederationValues`.

After preparation, the invocation extracts each prepared capture's payload,
converts it with the canonical string codec, and substitutes that text into the
corresponding segment. Named and private domain slots affect argument matching,
but their assignment syntax is not inserted into the key. Thus:

```datra
~"arg%(_x : Nat)" 4
```

queries exactly `"arg4"`, never `"arg(_x := 4)"`.

Supplying a non-total value, a value outside the domain, a missing required
capture, or ambiguous named arguments produces the same function-argument
error as an ordinary call. A successfully prepared invocation whose final key
is absent still returns `nothing`.

### Canonical reverse matching

String-template matching needs a dedicated capture operation shared by:

- string specification and `of` checks;
- template-selection projections such as `[1]`; and
- tests or internal operations which invert a template.

Keep the existing finite split search over literal delimiters, but replace the
leaf call to general federation membership with domain-driven capture:

```haskell
matchCanonicalTemplate
  :: CanonicalStringCodec
  -> EvaluatedStringTemplate
  -> String
  -> Decision PreparedTemplateCaptures
```

For each possible split, the matcher:

1. decodes each captured substring with `decodeCanonicalString`;
2. discards candidates whose presentation is not exactly canonical by checking
   that canonical re-rendering equals the captured substring;
3. submits the candidate tuple to the same argument-schema preparation used by
   function application;
4. extracts the prepared capture payloads;
5. reconstructs the complete template string from those payloads; and
6. accepts only when the reconstruction equals the original input byte for
   byte.

Distinct splits which prepare to the same capture tuple are one match. Distinct
prepared tuples retain the existing ambiguity behavior.

The reconstruction check is important. Domain validation may accept a named
assignment as an input representation and normalize it to its payload. Only
the payload's canonical text is part of a string template. Therefore:

```datra
"arg4" of "arg%(_x : Nat)"             # true
"arg(_x := 4)" of "arg%(_x : Nat)"     # false
```

The successful selection witness must retain the prepared capture tuple so
`Evaluation.Specification.Projection` can continue to expose the whole string
at position zero and the captures at subsequent positions. Projections expose
the validated capture values, not the textual assignment form used by an
unsuccessful candidate.

This canonical rule applies to string templates. It does not change `%` syntax
patterns, which match source AST structure rather than canonical string
encodings.

## Syntax and AST

### Parsing

Add a real expression constructor:

```haskell
ValueLookup Expression
```

and the corresponding `OperatorExpression` constructor. `~` remains a tight
prefix operator. Its immediate operand is one accessed term; application then
continues normally. Consequently:

```text
~a                 == ValueLookup (IdentifierReference "a")
~"a"               == ValueLookup (AsciiStringLiteral "a")
~"arg%Nat" 4       == FunctionApplication (ValueLookup <template>) 4
~(a + b)           == ValueLookup (Addition a b)
```

Parentheses are required when the key expression contains a looser infix or
map operator. This keeps `~template argument` useful without making the lookup
operand greedily consume the function argument.

Remove `namedAccessNames` and `expandedNamedAccess` from the `~` parser path.
`~(a, b)` is no longer two lookups; it is one lookup whose parenthesized
expression must evaluate to a string.

The lone token `~` remains a parse error. Existing guards which distinguish
`~`, `~>`, `<~`, and other operator prefixes remain in place.

### Rendering and traversal

Update all exhaustive AST operations, including normalization, child traversal,
source rendering, canonical AST rendering, syntax rewriting, closure analysis,
and parsing of serialized ASTs.

Source rendering prints `~` followed by the operand at prefix precedence,
adding parentheses when required. It must round-trip to `ValueLookup`; it must
not recognize a `ScopeAccess` shape and silently render that shape as `~`.

### Strict generated references

Compiler-generated closure and canonical-dependency references must remain
strict. Continue to represent them as `IdentifierReference` or explicit
`ScopeAccess` nodes, and render an explicit current-scope access when a quoted
name is required:

```datra
this."value with spaces"
```

Remove the `scopeNames` rendering shortcut which turns current-scope access
into `~...`. Update `FunctionClosure` regressions to expect explicit strict
references. Generated code must never use `ValueLookup`, because doing so would
change both the result type and missing-name behavior.

## Interpreter structure

Keep optional lookup separate from `ScopeAccess`. A suggested decomposition is:

```haskell
evaluateValueLookup
  :: ReductionContext
  -> Scope
  -> [String]
  -> InterpretedValue
  -> Either InterpretingError InterpretedValue

resolveOptionalScopeValue
  :: ReductionContext
  -> Scope
  -> [String]
  -> String
  -> Either InterpretingError (Maybe InterpretedValue)
```

`resolveOptionalScopeValue` should share alias selection and binding evaluation
with `resolveIdentifierAccess`. Refactor that function so the lookup phase can
report an absent binding without catching every `UnknownIdentifier` produced
later while evaluating an existing binding. This distinction prevents a
broken binding from being mistaken for a missing one.

Template functions can use the existing `EvaluatedFunction` representation.
Their `functionPrepare` callback is the ordinary domain preparation callback;
their invocation callback receives the prepared argument, builds the key, and
calls `resolveOptionalScopeValue` against the captured scope. Normal
`applyFunction` result checking and scope handoff remain in effect.

## Diagnostics

Add lookup-specific diagnostics for errors that are not ordinary function
argument failures:

- `ValueLookupRequiresString` when the operand is neither a concrete string nor
  a capture-bearing string template;
- `ValueLookupRequiresConcreteKey` when a non-template operand still denotes
  multiple or non-total strings; and
- `ValueLookupCaptureNotRenderable` if a prepared capture cannot produce one
  canonical concrete string. This should normally be prevented by domain
  preparation, but retaining a checked boundary avoids partial construction.

Missing bindings are values (`nothing`), not diagnostics. Errors from resolving
or evaluating a present binding retain their existing diagnostic constructors.

## Compatibility

This is intentionally source-incompatible with the old `~name` behavior.

| Old source | Old meaning | New meaning | Replacement for old meaning |
| --- | --- | --- | --- |
| `~a` | strict lookup of `a` | optional lookup at the string value of `a` | `a` for an ordinary lexical reference |
| `~"a"` | strict lookup of `a` | optional lookup of `a` | use `a`, or `this."a"` when quoting is required |
| `~(a, b)` | concatenate two strict lookups | one lookup at the value of `(a, b)` | `(a, b)` for two ordinary references |

Canonical rendering, retained begin-block rendering, and serialized closures
must be migrated in the same change so newly rendered programs never give old
strict references the new optional meaning.

## Test plan

### Parser and rendering regressions

Update the `value lookup` cases in `DatraParsingTests` to assert the new
`ValueLookup` node.

Add coverage for:

- `~a`, `~"a"`, and `~(a + b)`;
- `~"arg%Nat" 4` parsing as application of the lookup-produced function;
- access and optional suffix precedence after a lookup;
- rejection of a lone `~`;
- `~(a, b)` no longer expanding into two scope accesses;
- source and canonical AST round trips for `ValueLookup`; and
- explicit rendering of generated strict references as `this.name` or
  `this."quoted name"`.

### Concrete lookup regressions

Add standard-library/interpreter cases for:

- a literal key finding a public binding;
- a variable containing a key, proving that `~a` evaluates `a`;
- a missing key returning `nothing`;
- a private quoted key following the established lexical-access rules;
- a success payload exposing `key` and `value` by name;
- alias and shadowing behavior matching ordinary identifier resolution;
- a non-string operand producing `ValueLookupRequiresString`;
- a non-total, non-template string producing
  `ValueLookupRequiresConcreteKey`; and
- an existing binding whose evaluation fails propagating that failure rather
  than returning `nothing`.

### Template lookup regressions

Add cases for:

- `~"arg%Nat" 4` finding `arg4`;
- the same call returning `nothing` when `arg4` is absent;
- a template stored in a variable before `~` is applied;
- two captures and their source-order domain;
- named arguments matching named capture slots;
- a type mismatch using the ordinary function-domain diagnostic;
- a total interpolation such as `~"arg%(2 + 2)"` performing immediate lookup;
- lexical capture: invoking the function outside its creation block still
  searches the creation scope; and
- successful results exposing both the generated key and resolved value.

### Canonical matching regressions

Add direct membership/specification and projection cases proving that:

- `"arg4"` matches `"arg%(_x : Nat)"`;
- `"arg(_x := 4)"` does not match that template;
- noncanonical spellings such as a padded natural do not match;
- the projected capture is the prepared natural value `4`;
- multiple holes use ordinary argument-map ordering and name rules;
- ambiguous delimiter splits are still rejected; and
- declarative `%` syntax matching retains its existing, non-string behavior.

### Cross-feature regressions

Update expectations in `FunctionClosureTests`, retained-block rendering tests,
CLI golden AST/output fixtures, and any source snapshots containing the old
lookup sugar. Add a closure round-trip test demonstrating that a generated
strict dependency is not converted into a `Maybe` lookup.

## Implementation sequence

1. Add the AST constructors and make traversal, normalization, parsing, and
   rendering exhaustive. Migrate generated strict-reference rendering.
2. Refactor scope resolution into an absent-aware lookup phase and a separate
   binding-evaluation phase.
3. Implement concrete optional lookup and the `{key; value}` payload helper.
4. Retain evaluated string-template capture plans and synthesize lookup
   functions from them.
5. Extract the reusable function-domain preparation interface needed by both
   normal calls and template capture.
6. Replace string-template leaf membership with canonical, domain-driven
   matching while retaining projection witnesses.
7. Update existing regressions and add the parser, interpreter, canonical
   matching, closure, and golden tests above.

Each stage should keep ordinary strict identifiers, `ScopeAccess`, and
non-string federation selection unchanged. The final test run should include
the parsing, interpreting, standard-library, function-closure, module, CLI, and
cross-feature suites because the old `~` expansion appears in all of those
layers.

## Acceptance criteria

The change is complete when all of the following hold:

1. `~a` evaluates `a` as a string expression and never treats its spelling as
   the lookup key.
2. A concrete hit returns `Just` with named `key` and `value` fields; a concrete
   miss returns `nothing`.
3. A capture-bearing template produces a callable value whose domain is the
   argument map of its captures.
4. `~"arg%Nat" 4` queries `"arg4"` in the lexical scope captured by `~`.
5. `"arg%(_x : Nat)"` accepts the canonical capture text in `"arg4"` and
   rejects `"arg(_x := 4)"`.
6. String-template projections return the values prepared by function-domain
   validation.
7. Compiler-generated strict references round-trip without using `~`.
8. Updated and new regression suites pass without changing declarative `%`
   syntax matching.
