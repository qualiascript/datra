# Generic String Expressions

## Status and scope

This document defines a follow-up design for generic string expressions. Its
implementation is outside the identifier-expression pull request.

The proof and inverse required by a canonical string image are defined in
[DEPENDENT_DECLARATION_INJECTIVITY.md](./DEPENDENT_DECLARATION_INJECTIVITY.md).
`_StrExpr` consumes that generic federation insertion; it does not establish
injectivity independently.

The design replaces the closed Haskell `StringExpression` representation with
the ordinary Datra type family `_StrExpr T`. It also represents interpolation
as concatenation of Datra strings and Datra string-expression values. String
expressions have no dedicated semantic AST nodes and no fixed list of
supported source types.

Identifier expressions and dependent declarations use this facility as
clients. Their exact `$` and structural backtick matcher plans remain distinct
as defined in
[BACKTICK_DECLARATIVE_SYNTAX.md](./BACKTICK_DECLARATIVE_SYNTAX.md). This
facility replaces capture-specific conversion tables; it does not merge
matcher dispatch or literal semantics.

## Public type family

The standard library publishes one generic type family:

```datra
let val _StrExpr := &T? do yield datra.StrExpr T
```

`_StrExpr T` is the federation of canonical string representations of members
of `T`. `T` is an ordinary evaluated Datra type or federation. It may be an
alias, a specification, an `Either`, an optional value, a syntax category, a
user-defined structural type, or any future type; `_StrExpr` does not dispatch
on a closed set of type names.

Whenever the canonical insertion for `T` is proved:

```datra
(_StrExpr T) of Str
```

must be proved. A refuted or undecidable canonical insertion prevents
construction of `_StrExpr T`; it cannot produce a value outside `Str`. This is
a law of the `StrExpr` type family, not a special case in the `of`
implementation for selected operands.

The family has these additional laws:

1. If `T` already produces only strings, `_StrExpr T` is extensionally `T`.
   In particular, `_StrExpr Str` is `Str`.
2. For every literal string `s`, `_StrExpr s` is equal to `s`.
3. The family is idempotent: `_StrExpr (_StrExpr T)` is equal to
   `_StrExpr T`.
4. `_StrExpr Never` is `Never`.
5. If `S of T`, then `_StrExpr S of _StrExpr T`.
6. A total member of `T` produces its single canonical string.
7. A non-total `T` produces the pointwise canonical-string image of `T`.
8. Aliases and optional names do not change the resulting federation. An
   optional value `T?` remains an ordinary, distinct operand to `_StrExpr`.

The result contains strings, but retains its source operand as semantic
provenance. That provenance is what permits target-directed selection to
recover a member of `T` from a matched string.

## Internal hook

`datra.StrExpr` is the single host hook for the family. Applying it to an
evaluated `T` constructs the ordinary internal string federation for the
canonical-string image of `T` and retains `T` for inverse selection.

The hook asks the federation machinery for the operand's canonical string
insertion:

- forward conversion renders each member of `T` canonically;
- inverse conversion selects exactly one semantic source member through the
  proven insertion;
- string-producing operands use the identity conversion;
- non-total operands retain the generic injected federation image and its
  source witness; and
- a refuted or undecidable canonical insertion does not produce `_StrExpr T`.

Syntax-category types use the same family. Their canonical-string
insertion may call the application-owned parser capability, but the generic
`StrExpr` representation stores only the operand and the proven insertion.
It does not turn `_Expr`, `_Block`, `_FunctionBody`,
`_DependentDeclaration`, `_DependentArgument`, or `_IdentifierExpr` into
separate string-expression variants.

This hook is an evaluated-value/type-family capability. It is not an AST
constructor. The surface expression `_StrExpr T` parses as ordinary Datra
application and access to the `_StrExpr` binding.

## Interpolation model

An interpolation is an ordinary source-order concatenation whose components
are:

- ordinary Datra string values; or
- values of `_StrExpr T` for arbitrary `T`.

The parser represents every quoted component with
`StringTemplateInterpolation expression`. A literal component is
`StringTemplateInterpolation (AsciiStringLiteral text)`. Literal and dynamic
components therefore share one wrapper and one traversal path.

For example, a syntax presentation equivalent to the following sequence has
no separate template object:

```datra
"if ", (_StrExpr Bool), " then ", (_StrExpr _Expr)
```

Literal components are singleton string federations. String-expression
components are the generic pointwise string federations described above. The
ordinary concatenation representation retains component boundaries and
selection provenance, so matching does not need a parallel
`StringInterpolationTemplate` tree.

Quoted interpolation syntax remains parser sugar. A quoted source such as:

```datra
"%(left) and %(right)"
```

lowers immediately to ordinary concatenation of `left`, the singleton string
`" and "`, and `right`. Each hole must evaluate to a string-producing value:
either a string federation or `_StrExpr T`. Interpolation does not insert
`_show`, dispatch on an AST category, or implicitly canonicalize an arbitrary
non-string value.

An empty interpolation is `""`; a single component is that component; and
adjacent literal strings may be coalesced. Parser-local concrete-syntax data
may be used while reading the quoted form, but no string-template or
string-expression node survives in the semantic `Expression` AST.

Source rendering is owned by the Datra prettier. Semantic interpolation code
must construct the ordinary string-template expression and pass it to the
prettier; it must not maintain a parallel stringly typed renderer.

## Matching and capture

Matching is defined by the evaluated concatenation federation:

1. A singleton string component consumes exactly its literal text.
2. A `_StrExpr T` component selects a substring against its retained string
   federation.
3. Successful inverse selection produces the corresponding member of `T` as
   the capture.
4. Concatenation combines the component selections in source order.

The selected whole string and the typed captures remain available as ordinary
selection evidence. Dependent syntax uses those typed captures exactly as it
uses values selected by any other Datra type.

Ambiguity and overlap are properties of the concatenated string federation.
The existing injectivity requirements for declared syntax remain in force:
an interpolation is admissible only when its component split and inverse
selections are stable. Admissibility, refinement, and overlap therefore
operate on string federations and their retained provenance rather than on a
closed set of hole tags.

Matching must not render an AST and reparse it merely to discover its string
expression category. Parsing is used only by a canonical-string insertion
whose inverse requires parsing.

## Specification and subfederation

`_StrExpr T` participates in the ordinary specification and subfederation
engines as a regular Datra type.

Selection of a concrete string against `_StrExpr T` succeeds exactly when the
canonical insertion recovers one member admitted by `T`. Successful selection
retains that member of `T`; refutation means the string has no preimage in
`T`; an undecidable underlying membership check remains undecidable.

Subfederation follows the laws of the family:

- `_StrExpr T of Str` is always proved;
- `_StrExpr S of _StrExpr T` is decided from `S of T`;
- ordinary string-producing types compare by their existing string-federation
  rules;
- comparisons involving `Either`, specifications, aliases, optional values,
  and structural types recurse through their ordinary type semantics.

The decision procedure must unwrap one `StrExpr` layer before recurring on
its operand. It must not recursively reconstruct `_StrExpr` during the same
decision, so generic support does not introduce a termination cycle.

Specification in either direction delegates to the same family operations
and inverse-selection evidence. There is no second specification table for
syntax categories or string interpolation.

## Representation boundaries

Responsibilities are divided as follows:

- DatraTypes owns the generic canonical-string image, inverse selection,
  injectivity evidence, and `StrExpr` specification/subfederation behavior.
- The closed `StringExpression` module remains in DatraTypes until it is
  eliminated by this generic representation; it is not a DatraLanguage AST
  abstraction.
- DatraLanguage owns only the syntax-level `StringTemplateInterpolation`
  wrapper, whose payload is an ordinary expression.
- DatraHost exposes that implementation as `datra.StrExpr`.
- `std.datra` publishes the `_StrExpr` family with the definition above.
- The application parser owns quoted interpolation syntax and any parser
  capability required by a syntax-category insertion.
- Syntax rewriting and dependent declarations consume evaluated string
  federations and ordinary typed selection evidence.

Exact `$` matching retains literal presentation character for character,
including spaces and newlines. Backtick matching uses its own typed component
and boundary projection. `_StrExpr` supplies inverse selection for capture
substrings only after the selected matcher plan has matched its literals and
candidate extent. It must not introduce a common pre-match string
representation which erases the mode.

No semantic module may recover a string-expression kind by comparing a type
name, inspecting rendered source, or enumerating syntax-category constructors.

## Required simplification

The implementation must remove the superseded representation rather than
keep it beside `_StrExpr`:

- remove `StringExpression.StringExpression` and all of its
  constructors;
- remove `StringInterpolationTemplate` dispatch where interpolation can be
  represented by ordinary concatenation;
- remove `specializeStringExpression`, `mapStringExpression`, and constructor
  classification based on `_Expr`, `_Block`, or other selected types;
- remove any string-interpolation rendering helper; the prettier is the only
  source-rendering implementation;
- remove constructor-specific branches from capture, matching, admissibility,
  equality, rendering, and rewrite-candidate typing;
- lower quoted interpolation before the semantic AST is produced;
- make `FunctionSyntax` retain ordinary string-federation presentations and
  typed selection evidence instead of a parallel template AST.

Temporary compatibility constructors or dual matching paths are not part of
the design. All remaining clients must use `_StrExpr T` and the generic
internal hook.

## Required invariants

1. `_StrExpr` is defined exactly as
   `let val _StrExpr := &T? do yield datra.StrExpr T`.
2. Every successfully constructed `_StrExpr T` is a subfederation of `Str`.
3. `_StrExpr` attempts every Datra type without a constructor or name-based
   allowlist; success is determined only by the canonical insertion decision.
4. String-producing operands are converted by identity.
5. `_StrExpr` preserves literal strings exactly and is idempotent.
6. Non-total operands produce pointwise string federations with retained
   inverse-selection evidence.
7. Interpolation concatenates only strings and string-expression values.
8. Interpolation never inserts `_show` or implicitly converts an arbitrary
   non-string value.
9. String expressions are ordinary Datra types and values, not semantic AST
   nodes.
10. Every syntax-level template component is a `StringTemplateInterpolation`;
   literal payloads are ordinary `AsciiStringLiteral` expressions.
11. Matching, refinement, overlap, specification, and subfederation use the
   generic operand retained by `StrExpr`.
12. Syntax-category parsing remains application-owned behind the
    insertion/parser capability boundary.
13. The prettier is the only source renderer for interpolations.
14. No old `StringExpression` constructor path remains after the replacement.
15. Replacing capture-specific conversion paths does not merge exact `$` and
    structural backtick matcher plans.
16. `_StrExpr` never assigns application, sequencing, comment, or whitespace
    semantics; those remain declarative syntax rules.

## Verification

1. Prove `(_StrExpr T) of Str` for representative primitive, structural,
   function, syntax-category, `Either`, optional, aliased, total, and
   non-total operands.
2. Prove monotonicity with representative `S of T` pairs and verify refuted
   and undecidable operand relations remain refuted and undecidable where
   appropriate.
3. Verify `_StrExpr Str` and every other string-only operand use identity
   conversion.
4. Verify `_StrExpr "literal"` equals `"literal"` and
   `_StrExpr (_StrExpr T)` equals `_StrExpr T` for total and non-total `T`.
5. Verify concrete strings select the correct typed member through the
   retained insertion preimage.
6. Verify declared syntax can interpolate `_StrExpr T` for a user-defined
   type that has no syntax-specific constructor.
7. Verify expression, block, function-body, declaration, dependent-argument,
   and identifier-expression captures all use the same generic path.
8. Verify zero-, one-, and multiple-component quoted interpolation lowers to
   ordinary string concatenation and rejects non-string holes.
9. Verify admissibility, refinement, overlap, and capture selection directly
   on concatenated string federations.
10. Verify optional names are transparent and optional values remain distinct
   operands.
11. Verify the semantic AST, public DatraLanguage API, and syntax-rewriting
    code contain no `StringExpression` or string-template constructors.
