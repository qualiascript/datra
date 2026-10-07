# Direct syntax-template operator plan

## Goal

Datra syntax-function types use `~%` to attach surface templates to a function
signature. The left operand is written directly and does not use string
extraction:

```datra
'for :=
  ("for $_IdenExp of $_Expr" ~%
    (_AST, _AST -> _AST) !~"datra.for") |
  ((
      "for $_IdenExp in $_Expr do $_Expr"
      "for $_IdenExp $IntValRange do $_Expr"
    ) ~%
    (_AST, _AST, _AST -> _AST) !~"datra.forIn")
```

The operator accepts either:

- one compile-time string template; or
- a compile-time-materializable, inhabited total map whose every member is a
  string template.

Every template must pass the syntax-template character check before the
declaration contributes any rewrite rule. A failure in one member rejects the
whole operand; template installation is atomic.

## Language contract

The source form is:

```text
SyntaxFunctionType ::= TemplateOperand "~%" FunctionType
TemplateOperand    ::= CompileTimeString
                     | CompileTimeTotalMap<CompileTimeString>
```

`CompileTimeString` includes a plain string and a string template whose
interpolations can be retained as syntax holes. Compilation must be able to
recover every map member without evaluating arbitrary runtime code. The
initial implementation should support the compile-time map structure already
represented by `AtlasMap`, including maps written with semicolons or line
breaks.

The operand is valid only when all of the following hold:

1. It is a single string or an inhabited total map.
2. Every map member is a compile-time string template.
3. Every literal portion passes `invalidSyntaxTemplateCharacter`.
4. Every interpolation is one of the interpolation forms supported by syntax
   templates; weak or otherwise non-invertible interpolation is rejected.
5. The complete template collection is available before syntax rewriting
   begins.

Member order is preserved and determines rule order. Existing overlap and
decidability checks remain responsible for rejecting template federations
whose alternatives cannot be distinguished.

`%` remains the independent string-extraction operator. It has no role in a
`~%` operand. `%>` is not an alias for `~%`.

## Implementation plan

### 1. Operator vocabulary and parsing

Update `DatraLanguage.AST.Operator` so `SyntaxTypeOperator` has `~%` as both
its canonical and source spelling. Keep the `SyntaxType` AST constructor; the
semantic construct is unchanged apart from its operand contract and source
notation.

Update the neutral parser so:

- `~%` is recognized as the syntax-type suffix;
- prefix `~` does not consume the first character of `~%`;
- symbolic-literal reservation and maximal-munch tables include the new
  spelling automatically through the operator vocabulary;
- a parsed `~%` expression becomes `SyntaxType operand signature`, leaving
  operand validation to syntax-template compilation rather than using an
  extraction-shaped parser guard; and
- precedence remains the same as the current syntax-function type operator,
  including interaction with `->`, `|`, function bodies, specifications, and
  declarations.

Remove the parser's dependency on `syntaxTemplatesFromExpression` once the
shape guard is no longer required. Invalid operands should reach the dedicated
compile-time diagnostic instead of being reported as unrelated parse errors.

### 2. Atomic compile-time template compilation

Replace the extraction-specific `syntaxTemplatesFromExpression` contract with
a single template-operand compiler. It should return either a complete ordered
list of `SyntaxTemplate Expression` values or a structured failure.

The compiler should:

1. Accept `AsciiStringLiteral` and supported `StringTemplate` values directly.
2. Recursively collect members of a compile-time total `AtlasMap`.
3. Reject an empty map because it cannot install a syntax alternative.
4. Reject non-total map forms, non-string members, runtime-dependent map
   expressions, and unsupported interpolation forms.
5. Run `invalidSyntaxTemplateCharacter` on every compiled template.
6. Return rules only after the entire collection succeeds.

Keep decomposition, interpolation conversion, and character validation in one
shared abstraction. Declaration discovery and evaluated function-syntax
construction must not maintain separate definitions of a valid operand.

### 3. Declaration discovery and failure propagation

Syntax rules are needed while rewriting the surrounding scope, before normal
evaluation. Integrate template compilation at the point where declarations
are introduced into the rewrite environment.

Change declaration-rule discovery to propagate template-compilation failures
instead of silently producing no rules. Thread that failure through syntax
rewriting and translate it into the normal source-compilation diagnostic at
the outer parsing/interpreting boundary.

No member of a multi-template operand may be installed until all members have
compiled successfully. This prevents an invalid later string from leaving an
earlier syntax alternative visible during the same compilation.

The `SyntaxType` interpreter should reuse the already-defined operand compiler
when building `FunctionSyntax` and `functionSyntaxSource`. This preserves one
validation rule for declarations, standalone syntax-function values, external
adapters, and function bodies.

### 4. Rendering and diagnostics

Update `DatraLanguage.AST.Source` to render syntax-function types with `~%` and
without an extraction prefix. Rendering must round-trip both a single string
and a parenthesized total map of strings.

Add or refine structured failures so diagnostics distinguish:

- an operand that is neither a string nor a total map of strings;
- an empty template map;
- a map that is not compile-time materializable or total;
- a non-string map member;
- an unsupported interpolation; and
- a forbidden literal character.

Retain `InvalidSyntaxTemplateCharacter` for the last case. Rewrite its English
and Romanian explanatory text to name `~%` and the neutral-parser constraint.
Do not reuse extraction-specific wording for invalid `~%` operands.

### 5. Standard library, fixtures, and documentation

Rewrite every syntax declaration in `libs/std.datra` to use a direct string or
string map followed by `~%`. Apply the same notation to module fixtures,
integration fixtures, and embedded Datra programs in the test suite.

Update comments and design documentation that define syntax-template operands
so they describe direct validated strings and compile-time total maps. Keep
the `%` extraction documentation limited to extraction semantics.

### 6. Regression coverage

Add focused parser and AST tests for:

- a direct string on the left of `~%`;
- a multiline and semicolon-separated total map of strings;
- supported string-template interpolation;
- `~%` maximal-munch behavior next to prefix `~` and `%`;
- precedence with `->`, `|`, `~>`, `of`, declarations, and attached bodies;
- canonical rendering and parse/render round trips; and
- rejection of `%>`, extracted `~%` operands, and incomplete `~`/`%` token
  combinations.

Add syntax-compilation and interpreter tests for:

- successful installation from one string and from several strings;
- source-order preservation for multiple alternatives;
- rejection of a non-string operand;
- rejection of a total map containing one non-string member;
- rejection of partial, runtime-dependent, and empty maps;
- rejection of every forbidden literal character;
- atomic failure when a later member is invalid;
- unsupported or weak interpolation;
- standalone syntax-function types, external implementations, and declarative
  function bodies;
- optional declaration names; and
- syntax attachment identity under specification (`~>`) and subfederation
  (`of`).

Update localization tests for the exact English and Romanian messages. Update
function-closure tests so canonicalized functions do not retain `~%` syntax
when the existing closure contract says syntax metadata should be erased.

## Verification

Run verification in increasing scope:

1. `datra-parsing-test` for tokenization, precedence, AST shape, and round trips.
2. Focused `datra-interpreting-test` cases for declared syntax and the standard
   library.
3. `datra-types-test` for structured and localized diagnostics.
4. Module and integration tests for imported syntax declarations.
5. One complete test-suite pass with LiquidHaskell disabled using `-f-liquid`.

LiquidHaskell verification is outside this change unless the implementation
modifies a refined library module that requires a separate proof update.

## Completion criteria

The change is complete when:

- every syntax-function type uses `~%`;
- no syntax declaration needs `%` extraction around its template operand;
- a string or compile-time-materializable inhabited total map of valid strings
  installs syntax successfully;
- any invalid member rejects the complete declaration before rule
  installation;
- `%>` is rejected;
- canonical rendering emits only the new notation;
- optional-name, specification, and subfederation behavior remains consistent;
  and
- the focused and full test runs pass.
