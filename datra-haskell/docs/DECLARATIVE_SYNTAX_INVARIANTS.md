# Declarative syntax invariants

Declared syntax is matched after source has been read into an AST. Matching
uses canonical AST presentation and never observes the source's original
spaces or line breaks.

## Expressed by declarations

- The binding name is the first literal in a syntax phrase.
- The explicit leading AST identifier resolves one binding before template
  matching begins. Only templates attached to that binding participate; a
  template belonging to another identifier is never a competing match.
- The quoted template supplies the remaining literals and holes.
- The quoted spelling is represented as a structured `SyntaxTemplate`; rules,
  matching, and future federation validation consume that same structure.
- A `$T` hole uses ordinary Datra membership in `T`; the function signature
  does not replace or widen that match.
- `Str` and `IdenStr` captures require explicit `"` delimiters in an `as`
  template. Neither type is currently used by a declared syntax template.
- `as` permits only the declared syntax spelling. `as?` permits both that
  spelling and ordinary function application.
- The right-hand signature and implementation control the resulting call.
- Templates follow the visibility, import, and recursive `let` behavior of
  their bindings. A recursive binding is available while its value is read.
- The current outer application spine supplies a hard matching boundary.
  Matching never descends through an argument's nested AST merely to obtain a
  longer match.
- Within that boundary, branches greedily try the longest prefix, and each
  hole greedily tries the longest available AST sequence. Both backtrack when
  membership or the remaining template does not match. Arguments after the
  matched prefix are reapplied to the rewritten AST.
- The federation represented by alternative syntax templates must be
  disjoint. If two distinct matches consume the same longest contextual
  prefix, matching throws an internal error: the overlap should have been
  rejected when the federation was constructed.
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
- Evaluated syntax functions currently retain the `as`/`as?` flag but discard
  their structured template. The template federation must remain available
  long enough for alternative branches to be checked for overlap
  declaratively.
- A template hole's type must remain an AST identifier reference, not merely
  an unscoped string label. Closure reconstruction, module qualification, and
  recursive binding must rewrite that reference in the same way they rewrite
  the function signature.
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
