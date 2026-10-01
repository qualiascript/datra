# Declarative syntax invariants

Declared syntax is matched after source has been read into an AST. Matching
uses canonical AST presentation and never observes the source's original
spaces or line breaks.

## Expressed by declarations

- The complete syntax phrase is declared by the template. Its first literal is
  the surface identifier; the parser does not prepend the binding identifier.
- The maximal literal prefix before the first hole is matched before any hole
  parsing. Its first literal supplies the reverse-lookup key and its remaining
  literals filter that bucket. A binding named `abc` may therefore deliberately
  declare a template beginning with `def`; matching `def` expands to `abc`.
- A template without a literal prefix cannot use that index and remains on a
  less-optimized fallback path. Current standard declarations all have one.
- `%>` accepts one or more templates. Its own operation enforces that
  nonempty shape; it does not depend on the separately declared
  `InhabitedList` type.
- `%` maps a single string or an inhabited list of strings pointwise into
  templates. Thus `%"..."` is the unary spelling and
  `%("..."; "...")` supplies multiple templates without introducing a
  special `%>` list grammar.
- The public template type is `Template := !$~"datra.Template"`.
- The quoted spelling is represented as a structured `SyntaxTemplate`; rules,
  matching, and future federation validation consume that same structure.
- Its host type is introduced privately by the standard library as
  `_SyntaxTemplate := !$~"datra.SyntaxTemplate"`; it is implementation support
  for `%>`, not a public user-facing type.
- A `$T` hole uses ordinary Datra membership in `T`; the function signature
  does not replace or widen that match.
- After every hole has matched, the assembled capture argument must be
  compile-time proved to be a subfederation of the function domain. Hole
  membership and function-domain membership are separate mandatory checks.
- `Str` and `IdenStr` captures require explicit `"` delimiters in a `%>`
  template. Neither type is currently used by a declared syntax template.
- `%>` always permits both the declared syntax spelling and ordinary function
  application (`<identifier> <expression>`).
- The right-hand signature and implementation control the resulting call.
- `%>` and the structured templates remain attached to the internal
  function type for matching and federation decisions. Canonicalization erases
  that attachment and presents the ordinary explicit function application.
- Templates follow the visibility, import, and recursive `let` behavior of
  their bindings. A recursive binding is available while its value is read.
- Recursive blocks are matched in two phases. The tentative phase discovers
  `let` declarations without evaluating value holes. The strict phase reruns
  the original AST with evaluator-backed membership. Inner declarations
  shadow outer declarations, while duplicate declarations in one block remain
  invalid.
- The current outer application spine supplies a hard matching boundary.
  Matching never descends through an argument's nested AST merely to obtain a
  longer match.
- Within that boundary, declarations are tried in source order. The first
  declaration with a valid match wins. Within that declaration, the matcher
  greedily tries the longest contextual prefix, and each hole greedily tries
  the longest available AST sequence. Both backtrack when membership or the
  remaining template does not match. Arguments after the matched prefix are
  reapplied to the rewritten AST.
- The federation represented by alternative syntax templates must be
  disjoint. The AST matcher accepts only a federation whose pairwise
  distinctions were admitted at construction, so an invalid semantic overlap
  cannot reach matching as a runtime/internal-error case.
- Template alternatives go through the existing federation decision shape.
  `Proved` means they are disjoint and is the only accepted result. `Refuted`
  means an overlap was proved, and `Undecidable` means no applicable proof of
  disjointness exists; both reject construction of the federation.

## Not yet expressed declaratively

The implementation must not silently decide these points. Each item needs
either a consequence of ordinary AST/value semantics or an explicit Datra
representation.

- How the enclosing AST identifies the complete candidate syntax phrase.
- How unresolved identifiers in a candidate receive canonical values for hole
  membership without introducing a second parser-side type system.
- Value-hole type references are resolved in the same lexical/module context
  as the rest of the function type. Standard-library host types used by syntax
  templates are therefore declared before those templates; recursive `let`
  references continue to use the existing fixed-point scope.
- A syntax template cannot be eagerly lowered to the current character-string
  template representation: that representation requires injective string
  splitting, while syntax templates resolve captures greedily inside bounded
  AST structure. The structured template therefore needs a syntax-template
  disjointness procedure inside the existing federation mechanism, while
  delegating hole-domain decisions to ordinary value federations.
- The Datra-level definitions of the `_Expr`, `_Block`, and `_IdenExp` AST
  matchers.
- How raw or lazy AST captures are passed to control implementations without
  evaluating unselected branches.
