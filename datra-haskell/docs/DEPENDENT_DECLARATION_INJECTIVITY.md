# Injective `val` Values

## Status

Injective `val` construction is intentionally not implemented.

The former implementation inferred injectivity from rendered strings. That
code has been removed so the next implementation starts from a clean semantic
boundary rather than preserving a misleading approximation.

Every evaluated dependent declaration carrying `DeclarationVal` now reaches
`requireImplementedDeclaration` and fails with:

```text
InjectiveValueConstructionNotImplemented
```

The parser and AST still retain the `val` modifier. No declaration marker,
rendered name, string alphabet, delimiter, or sample of values is accepted as
injectivity evidence.

## Removed implementation

The cleanup removed:

- `Evaluation/ToString/Injectivity.hs`;
- `StringConversionProperties`, `ProvenInjectiveToString`, and
  `ToStringInverseDecision`;
- `ToStringAtlasMapFederation` and its specification, projection, access,
  `Either`, concatenation, and subfederation branches;
- string-language prefix, alphabet, exact-string, delimiter, and inverse
  checks used as injectivity evidence;
- `RuntimeFunctionInsertion`, its forward-only application path, and the
  range wrappers which used it;
- the unused `CanonicalStringImplementation` tag previously stored on every
  `DatraType` as alleged evidence;
- the synthetic insertion attached to dependent declaration family
  functions;
- the `$val` runtime marker and every presentation branch which treated it as
  canonical identity;
- the stale non-injective string and dependent-declaration diagnostics;
- canonical decoding by rendering a semantic value, parsing the text, and
  rewriting it back into an AST; and
- evaluator-owned lookup of the standard-library name `Str` to validate
  declaration name families.

`toStringValue` now converts only values which are already strings or have a
total concrete value. A pointwise conversion of a non-total federation reaches
the same intentional unimplemented boundary.

The existing tests were deliberately left unchanged. Some still describe the
removed behavior and must be replaced when structural injectivity is built.

## Required semantic invariant

For one prepared declaration branch, let:

- `C` be the federation of valid capture tuples;
- `name : C -> Str` evaluate the declaration name template; and
- `value : C -> V` evaluate its implementation.

A `val` declaration requires executable insertions for both maps:

```text
name^-1(name(c)) = c
value^-1(value(c)) = c
```

Equality is semantic equality after removing presentation. References, module
paths, markers, or different renderings do not make equal results distinct.

Once both insertions are proved, canonical naming is composition:

```text
canonicalName     = name . value^-1
canonicalName^-1  = value . name^-1
```

For a range value, `value^-1` must recover its endpoints. For a constant
dependent family, two distinct captures provide a collision witness and the
family is refuted. Infinite families are never accepted from sampling.

## Future representation

DatraTypes needs one general evaluated insertion representation shared by all
target types. It must retain:

- the source federation;
- the target federation;
- an executable forward map;
- an executable preimage operation; and
- a decision result distinguishing proved, refuted, and undecidable cases.

The constructor must be restricted to structural proof rules, typed
insertions, or exhaustive finite decisions. A forward function without a
preimage is an ordinary callable function, not an insertion.

The image of an insertion must retain its source witness. Selection of an
image member must select the target member, recover its unique source, and
verify that source belongs to the source federation.

## Decision rules

The future decision procedure should be structural:

- identity is injective;
- a singleton source is injective after its one result evaluates;
- proved insertions compose;
- products and records retain every varying source discriminator;
- `Either` requires injective branches with disjoint target images;
- map, expansion, coalization, concatenation, and ordinal families preserve
  their federation structure;
- a finite source may be checked exhaustively and must retain either an exact
  inverse table or a collision witness;
- an infinite primitive is accepted only with a structural insertion supplied
  by that primitive; and
- unsupported cases are undecidable.

String alphabets, delimiters, prefixes, and rendered round trips may describe
a target string language. They are not evidence that the source-to-value map
is injective and must not return to evaluation as a proof mechanism.

## Preparing a dependent `val`

The future implementation should:

1. construct the capture federation without erasing witnesses;
2. evaluate and decide `name : C -> Str`;
3. evaluate the implementation while retaining the same witnesses;
4. decide `value : C -> V`;
5. retain both insertions on the prepared declaration and image; and
6. derive canonical naming from their composition.

The retained evidence must travel with scoped declarations, declaration
layers, prepared modules, imports, aliases, and projections. Non-`val`
declarations use ordinary lookup without requiring implementation injectivity.

The final decision has exactly three outcomes:

- proved: retain the insertion and admit the `val`;
- refuted: report a collision with two distinct captures and one semantic
  result; and
- undecidable: report the unsupported structural operation.

Until that complete path exists, `InjectiveValueConstructionNotImplemented`
remains the only `val` outcome.
