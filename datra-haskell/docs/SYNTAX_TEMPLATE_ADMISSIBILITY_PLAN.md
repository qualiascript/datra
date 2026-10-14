# Syntax-template admissibility

## Purpose

The left operand of the syntax-type operator `%` describes source syntax for a
function. A template must be accepted only when the neutral source parser can
preserve its literals and the syntax rewriter can recover its holes without
changing their order or meaning.

Admissibility must be a property of the complete template, not a property of
its individual characters. This is necessary for context-sensitive core
operators. For example, `~name` is a complete value-of expression that the
neutral parser preserves, while a trailing `~` has no operand and cannot occur
in a parsed invocation.

The implementation must also remain correct as operators move out of the core
grammar and become declarations in `libs/std.datra`. Adding or migrating an
operator must not require updating a separate template-character blacklist or
operator allowlist.

## Required semantic rule

A syntax template is admissible exactly when its literal-and-hole structure is
losslessly representable by the declaration-independent neutral parser.

More precisely, let `T` be a template and let each hole be replaced by a fresh
placeholder valid for that hole's syntactic category. Parsing the instantiated
template must produce a neutral AST from which the syntax matcher can recover:

1. every literal in `T`, in source order;
2. every placeholder exactly once, in source order;
3. the boundary between each literal and hole; and
4. no additional literal or hole introduced by parsing.

Recovery is allowed to ignore insignificant whitespace, but not grouping,
operator structure, or token boundaries. The recovered template must be equal
to `T` after whitespace normalization.

This rule applies to the complete pattern. A literal must not be rejected just
because it contains a character that is also used by a core operator, and it
must not be accepted merely because every character belongs to a permissive
symbol alphabet.

Expected examples:

| Template | Result | Reason |
| --- | --- | --- |
| `"call ~"` | reject | `~` requires a name, so the witness cannot be parsed |
| `"call ~name"` | accept | the complete value-of expression is preserved and renders as `~name` |
| `"call (%Int)"` | reject | grouping is consumed structurally and the literal parentheses cannot be recovered |
| `"take,%Int"` | accept | the comma structure is visible to the existing boundary rewriter |
| `"%Int++"` | accept | the postfix literal is retained as an opaque symbolic word |
| `"left %Int middle %Int"` | accept | both holes and both delimiters remain independently observable |

The rule should reject an entire map of alternative templates if any member is
inadmissible, matching the existing all-or-nothing behavior of `%`.

## Neutral parsing is the source of truth

The validator must call the same neutral parsing machinery used for real source
files. It must not reproduce any of these facts independently:

- core operator spellings;
- operator precedence or associativity;
- prefix, infix, or postfix ownership;
- reserved symbolic runs or prefixes;
- grouping and map delimiters;
- the alphabet accepted by the opaque-symbol fallback; or
- the boundary shapes understood by syntax rewriting.

The existing character predicate remains useful to the lexer when reading an
opaque symbolic run, but it must not decide whether a complete syntax template
is valid. Character-level rejection can still be used to improve a diagnostic
after whole-pattern validation fails; it is not the semantic test.

The neutral parser entry point used for validation must not load imports,
consult declared syntax, perform evaluation, or bootstrap `Std`. It should
parse one synthetic phrase using only the grammar that is available before
declarative syntax rewriting. This keeps validation deterministic and prevents
a syntax declaration from being needed in order to validate itself.

## Validation design

### 1. Build typed witnesses

Replace every template hole with a unique placeholder. Placeholder construction
must be centralized and cover all hole kinds:

- expression and value holes use fresh atomic expressions;
- identifier-expression holes use fresh valid identifier-expression forms;
- block holes use a minimal block whose entries contain unique markers; and
- function-body holes use a minimal function body with unique markers.

The identifiers must be impossible to collide with template literals or user
bindings. The witness builder should return both the source phrase and the
expected marker ASTs.

Neutral parsing is sensitive to expression shape and precedence. Validation
must therefore use a finite representative basis for any hole kind that can
contain general expressions. The basis must cover the neutral parser's
structural classes, including:

- an atom;
- an application;
- prefix and postfix forms;
- each infix precedence and associativity class;
- map concatenation and sequence boundaries; and
- declaration or block boundaries where the hole kind permits them.

These representatives must be derived from parser-owned operator metadata or
constructed through parser APIs. The validator must not maintain a handwritten
list of operator symbols.

### 2. Parse through the neutral entry point

Parse each witness exactly as an invocation would be parsed before syntax rules
are installed. A parse failure makes the template inadmissible. This rejects a
pattern such as `"call ~"`: the parser consumes `~` as the core value-of prefix
and then fails because no name follows it.

### 3. Project through the real matching boundary

Run the parsed witness through the same structural projection and candidate
generation used by syntax rewriting. Validation succeeds only if that
projection reconstructs the original template and identifies every marker as
the corresponding hole.

This projection must be shared code. The validator must not implement a
simplified application-spine matcher because real templates can cross infix,
concatenation, declaration, and block boundaries.

An effective implementation is to construct a temporary syntax rule whose
expansion is a unique marker, apply the ordinary matcher to the neutral witness,
and verify the marker and captured placeholders in the result. If the ordinary
matcher needs a smaller reusable interface, extract its neutral-shape
projection rather than duplicating it.

### 4. Require stability

Render the recovered neutral shape canonically and parse it again. Its second
projection must equal the first. This catches patterns whose apparent literals
are only artifacts of one parse or whose grouping disappears during canonical
rendering.

All witness variants must pass. One successful atomic witness is insufficient
when another legal hole expression changes how an adjacent operator binds.

## Module responsibilities

Refactor toward the following ownership boundaries:

- `DatraLanguage.SyntaxTemplate` owns template, piece, and hole data types plus
  traversal and rendering. It does not define whole-template validity.
- The neutral parser owns lexical symbol recognition, core operator ownership,
  precedence, and the declaration-independent phrase parser used by both real
  source and witnesses.
- A syntax-template admissibility module owns witness construction, invokes the
  neutral parser, and checks recovery through shared matcher projection.
- `SyntaxDefinitions` converts string expressions into structured templates and
  delegates admissibility to that module.
- `SyntaxRewriting` and `SyntaxTemplateMatching` expose or share the smallest
  structural projection needed by both matching and validation.

Avoid a module cycle by moving template compilation and declaration-rule
construction out of `SyntaxDefinitions` if necessary. Data definitions should
remain below parsing and rewriting; orchestration may live in an application
module that depends on all three.

The existing `invalidSyntaxTemplateCharacter` function should be removed once
all callers use whole-pattern validation. `isSymbolicSyntaxCharacter` should be
kept only as parser-owned lexical policy, either in `Parsing` or in a small
neutral-lexer module.

## Operator evolution and `Std`

Core and standard-library operators have different ownership:

- A core operator is recognized structurally by the neutral parser. A template
  may contain it only when the complete pattern supplies a parseable and
  recoverable core expression shape.
- A standard-library operator is declarative syntax. Before its rule is
  installed, its nonstructural spelling must survive neutral parsing as an
  opaque symbolic or identifier literal.

The admissibility algorithm must adapt automatically when an operator moves
between these categories:

1. Removing an operator from the core parser causes its spelling to flow
   through the neutral opaque-symbol path.
2. Its declaration in `std.datra` is validated against that same neutral path.
3. Installing the declaration gives the spelling its operator behavior during
   syntax rewriting.
4. No validator table or forbidden-character set changes.

Structural source delimiters cannot become ordinary standard-library operators
merely by adding a declaration. If a desired spelling is consumed by grouping,
strings, comments, resource separation, or another nonrecoverable grammar
boundary, the neutral parser must first gain an explicit lossless representation
for it. The validator should reject the declaration until that parser support
exists.

Operator metadata used to generate witness variants must come from the core
parser's actual operator definitions. Standard-library coverage must come from
compiling the declarations in `std.datra`, not from a Haskell enumeration of
library operators. This gives both categories a single authoritative source.

## Diagnostics

Replace the character-only compilation failure with a pattern-level failure
that retains the offending template and a structured reason. At minimum,
distinguish:

- neutral parse failure;
- literal or hole lost during projection;
- literal or hole reordered or duplicated;
- unstable parse/render round trip; and
- invalid left operand that is not a compile-time string or inhabited total map
  of strings.

When the neutral parse failure identifies a specific character or operator,
localization may include it. For `"call ~"`, the English diagnostic should say
that the syntax pattern ends with the incomplete core operator `~`, rather than
claiming that `~` is universally forbidden.

Add equivalent Romanian localization and keep the existing structured
diagnostic tests. User-facing diagnostics should describe the source-level
problem without mentioning synthetic witnesses.

## Verification

Add focused parsing and standard-library tests for:

1. rejection of `"call ~"` at the `%` expression, before any attempted use;
2. acceptance and successful invocation of `"call ~name"`;
3. continued rejection of literal grouping and other unrecoverable delimiters;
4. continued acceptance and invocation of comma and postfix templates;
5. rejection when any member of a template map is inadmissible;
6. every hole kind, including block and function-body patterns;
7. adjacency on both sides of holes;
8. each parser-derived precedence and associativity representative; and
9. stable parse/project/render/parse round trips.

Add a fixture operator that exists only as a declarative standard-library-style
rule, using a spelling such as `++` that is not a core operator. The fixture must
validate, install, and execute without any validator-specific registration.
This is the regression test for future operator migration.

Add a generated core-operator conformance test based on the parser's operator
inventory. For each source spelling, the test should verify that incomplete
uses are rejected unless the token is independently parseable, while complete
representative patterns are accepted only when their neutral shapes are
recoverable. Because the cases are generated from parser metadata, removing an
operator from the core grammar automatically removes it from this suite.

Finally, compile every syntax declaration in `libs/std.datra` through the same
admissibility entry point during tests. This makes the standard library itself
the inventory of declarative operators and prevents drift between library
syntax and validator policy.

## Implementation sequence

1. Extract a declaration-independent neutral phrase parser suitable for
   generated witnesses.
2. Extract or expose the matcher projection needed to recover literal and hole
   boundaries across all supported AST contexts.
3. Implement typed witness construction and parser-derived structural variants.
4. Add whole-template admissibility and structured failure reasons.
5. Route both evaluated `%` expressions and declaration-rule collection through
   the new validator.
6. Replace character-based diagnostics and remove semantic use of the character
   blacklist.
7. Add focused regressions, generated core-operator conformance, and complete
   `std.datra` declaration validation.

The fix is complete when `%` rejects patterns that cannot be invoked, accepts
patterns whose complete neutral form is recoverable, and requires no validation
code change when a nonstructural operator moves between the core grammar and
the standard library.
