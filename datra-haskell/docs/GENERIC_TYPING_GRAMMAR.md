# Generic Typing Grammar

Status: design specification.

## Purpose

Generic typing introduces dependent product and dependent sum variables directly
in a function type. These variables belong to the function interface: the
interface uses them to match, infer, validate, and package values, while the
function body receives only ordinary arguments.

Generic typing is the language's sole type-level dependent binding mechanism.
There is no `with` construct and no type-level `for` binder or independent
dependent-container binding semantics. Product and sum polarity compose only
through one ordered generic telescope, where `&` and `^` binders may alternate.

The word `for` is reserved for comprehension shorthand. Its forms are:

```datra
for i in values do expression
for i from 0 to 3 do expression
```

The second line represents the closely related form in which an integer valued
range follows the binder directly; `from 0 to 3` is only one example. Both are
surface syntax for a `for` type defined in terms of generic interfaces. `for`
is not a second primitive dependent binder and requires no special dependent-
type evaluator. There is no corresponding `with` form.

The two prefixes select the dependent polarity:

```datra
&T
^T
```

- `&` introduces a dependent product generic.
- `^` introduces a dependent sum generic.

An optional infix `::` clause constrains the generic's supertype:

```datra
&T :: IntLimit
^T :: Any
```

When the clause is absent, the supertype is `Any`.

## Preferred surface grammar

Conceptually:

```text
generic-introduction := generic-polarity generic-name generic-bound?
generic-polarity     := "&" | "^"
generic-name         := private-name
                      | required-public-name
                      | optional-public-name
generic-bound        := "::" expression
```

Examples:

```datra
&_T
&T :: IntLimit
&T? :: Any

^_T
^T :: IntLimit
^T? :: Any
```

The prefix is part of the generic introduction. `::` is an infix operator
between that introduction and its supertype. In application position, grouping
makes the intended argument boundary explicit:

```datra
Args (&_T :: IntLimit)
Box (^T :: Any)
```

The right-hand side of `::` accepts the same annotation expression class as a
function parameter type. Its extent ends at the enclosing expression's normal
delimiter or precedence boundary.

`for T of Bound` is not a grammar form, and `with` is not a keyword or
construct. The comprehension spelling is recognized only by `in ... do` or by
the valued-range-plus-`do` production; it never denotes a type-level binder.

## Named functions and canonical lowering

The symbolic generic operators have ordinary identifier names:

| Surface operator | Function identifier | Meaning |
| --- | --- | --- |
| `&` | `forall` | dependent product / universal selection |
| `^` | `some` | dependent sum / existential packaging |

Program source should normally use the compact `&` and `^` forms. The names
`forall` and `some` are the functions to which the generic string templates
lower, following the same model as standard-library syntax such as `begin`.

Schematically, after string-template expansion:

```datra
&T :: Int  ->  forall($T; Int)
^T :: Int  ->  some($T; Int)
```

Here `$T` stands only for the generic identifier supplied as data to the named
function. The string template should capture this argument through the existing
`$_IdenExp` hole if that hole can represent all three generic name modes. If
generic names require stricter recognition, the parser may add a dedicated
identifier-expression hole with those rules instead. In either case, the
captured value must preserve the private, required-public, and optionally named
modes. An omitted bound is lowered by supplying `Any`.

`forall` and `some` otherwise behave like normal functions: their explicit
forms use normal application syntax, participate in ordinary name resolution,
and are the forms retained in canonical function expressions after string
templating has been resolved. The resulting generic introduction is still
owned by the nearest function type and is normalized into the same
`GenericBinder` representation regardless of whether it originated from a
symbolic template or an explicit named application.

## Identifier modes

Generic identifiers reuse the language's three-way identifier distinction:

| Form | Visibility at the call boundary | Witness selection |
| --- | --- | --- |
| `_T` | private | inferred |
| `T` | public | explicitly supplied by name |
| `T?` | public | explicitly supplied by name or position |

The trailing `?` makes the public name optional; it does not make the generic
witness or its value optional.

The same modes apply to both polarities:

```datra
&_T :: IntLimit
&T :: IntLimit
&T? :: IntLimit

^_T :: Any
^T :: Any
^T? :: Any
```

`_T?` is outside the three-way identifier grammar and is rejected.

## Function-type ownership

A generic introduction is valid only inside a function type. The nearest
enclosing function arrow owns it.

```datra
max := {Args (&_T :: IntLimit),} -> _T do
  # body
```

Here `_T` belongs to the type of `max`. Function-type resolution collects it
before resolving any ordinary type in the signature, so it is available
throughout both the domain and codomain.

The marker may occur in the codomain while declaring a generic used in the
domain:

```datra
preserve := {value? : T} -> (&T :: Any) do
  yield value
```

The marker determines the generic's polarity, name mode, and bound; its textual
position does not begin its scope.

A nested function type creates a nested generic scope. Its introductions do
not become generics of the outer function:

```datra
apply := {f? : ({x? : (&T :: Any)} -> T); x? : Any} -> Any do
  # T belongs to f's function type
```

A generic introduction in a standalone map, application, or type alias without
an enclosing function arrow is a parse or normalization error.

## Scope collection and generic prefix

Function-type resolution uses two passes over the complete outer signature.
The scan includes the domain and codomain, but treats nested function types as
separate declaration scopes.

The collection pass records every generic introduction owned by the outer
function in source order and replaces the marked occurrence with a stable
binder reference. These declarations form a virtual prefix before every
ordinary domain and codomain type. The resolution pass then resolves the whole
ordinary signature against the complete prefix. It therefore permits an
ordinary type to use a generic whose marked declaration appears later in the
same map or across the arrow:

Collection visits the domain before the codomain and preserves lexical order
within each expression. This gives every generic a deterministic position in
the prefix without making that position a scope boundary.

```datra
choose := {left? : T; right? : (&T :: Any)} -> T do
  yield left
```

The interface schema for this domain is ordered conceptually as:

```text
generic T :: Any
left  : T
right : T
```

The marked `right` position remains an ordinary `T` argument after declaring
the generic. The declaration location defines `T`'s polarity, name mode,
supertype, source location, and relative position among the generic prefix.

Generic bounds are resolved in generic-prefix order. A bound may refer to an
earlier generic declaration, while ordinary parameter and result types may
refer to any generic in the complete function prefix:

```datra
pair := {pair? : Pair T U; types? : Pair (&T :: Any) (&U :: T)}
  -> Pair T U do
  yield pair
```

Here `T` precedes `U` in the prefix, so the bound of `U` may reference `T`.
A bound that depends on a later generic declaration is invalid.

This makes higher-order interfaces direct:

```datra
map := {
  values? : List (&A :: Any)
  transform? : A -> B
} -> List (&B :: Any) do
  # body sees values and transform
```

The collection pass produces the prefix `[A, B]` before resolving
`values`, `transform`, or the result. `A` can be inferred from `values`, and
`B` can be inferred from the supplied `transform` function type. Neither
generic is included in the body-visible arguments.

A second marked introduction with the same name in one function scope is a
duplicate declaration. Plain occurrences of that name are references,
regardless of whether they appear textually before or after its marker.

The ordered generic prefix forms a telescope. Product and sum binders may
alternate in that telescope, and a later binder may depend on any earlier
binder regardless of polarity:

```datra
mapPacked := {
  value? : (^_Source :: Any)
  fallback? : (&Target :: Any)
  transform? : _Source -> Target
} -> Target do
  yield transform value
```

This signature first opens a hidden source type and then selects a target type
from the supplied fallback and transformation. The body receives `value`,
`fallback`, and `transform`; the two generic witnesses remain at the interface
boundary.

## First-class representation

Generic typing is represented directly in the function type. A suitable AST
shape is:

```haskell
data GenericPolarity
  = GenericProduct
  | GenericSum

data GenericNameMode
  = PrivateInferred
  | PublicRequired
  | PublicOptionalName

data GenericBinder = GenericBinder
  { genericPolarity :: GenericPolarity
  , genericName     :: IdentifierString
  , genericNameMode :: GenericNameMode
  , genericBound    :: Expression
  }

data FunctionType = FunctionType
  { functionGenerics :: [GenericBinder]
  , functionDomain   :: Expression
  , functionCodomain :: Expression
  }
```

Stage 1 operators and Stage 2 named applications both normalize to the same
`GenericIntroduction`. Function-type resolution then:

1. scans the outer domain and codomain for introductions in source order,
   without collecting declarations owned by nested function types;
2. allocates stable binder identities and builds one function generic prefix;
3. replaces each introduction occurrence with a reference to its binder;
4. resolves generic bounds sequentially in prefix order;
5. resolves every ordinary domain and codomain type against the complete
   prefix; and
6. attaches the ordered prefix to the owning `FunctionType`.

Binder identity, rather than identifier text alone, distinguishes shadowed
generics in nested function types.

Expression traversal, normalization, free-identifier analysis, closure
dependency collection, and specification must all preserve the generic binder
and its references. The resolved `FunctionType` stores the polarity and binder
directly rather than retaining a surface spelling.

## Dependent product generics

A dependent product generic describes a function that works for a selected
type satisfying the declared supertype.

### Private inferred product

```datra
max := {Args (&_T :: IntLimit),} -> _T do
  # `it` contains Args, but no `_T` witness
```

At a call, the function interface:

1. collects constraints for `_T` from the supplied `Args` value;
2. selects one unique type within `IntLimit` that satisfies those constraints;
3. substitutes that type into the complete function signature;
4. validates the ordinary arguments against the specialized domain;
5. invokes the body with the ordinary arguments only;
6. validates the result against the specialized `_T` codomain.

The caller cannot explicitly bind `_T`.

### Public required product

```datra
identity := {value? : (&T :: Any)} -> T do
  yield value

yield identity {T := Nat; value := 5}
```

`T` is a required public interface witness. The supplied witness is checked
against `Any`, and `value` is checked against the selected `T`.

### Public optionally named product

```datra
identity := {value? : (&T? :: Any)} -> T do
  yield value

yield identity (Nat; 5)
yield identity {T := Nat; value := 5}
```

Both calls provide the witness. The first provides it positionally; the second
uses its public name.

## Dependent sum generics

A dependent sum generic associates a hidden or explicit type witness with
ordinary values at a function boundary.

In a function domain, the interface opens the incoming dependent package,
validates its related values with one witness, and passes only the ordinary
values to the body:

```datra
render := {
  value? : (^_T :: Any)
  render? : _T -> Str
} -> Str do
  yield render value
```

The call interface infers `_T` from the incoming dependent values. The body can
use `value` and `render`, but `_T` is not a body binding and is not a member
of `it`.

In a function codomain, the interface infers or accepts the witness from the
returned ordinary value, validates the dependent result, and seals the witness
in the result package:

```datra
parse := Str -> {value : (^_T :: Any)} do
  yield {value := parseValue it}
```

A private sum witness remains hidden when the package leaves the function. A
public `T` witness is required at the relevant boundary, while `T?` may be
provided positionally or by name. All three modes use the same body-erasure
rules.

## Inference and constraint solving

Private generic inference is part of function matching. Declaration location
does not determine the evidence source. A product generic is resolved before
body invocation from its dependent domain occurrences, an explicit public
witness, or an expected result constraint. A sum generic is opened from
dependent input evidence when available and may be established and sealed by
dependent result evidence after the body returns.

For each private binder, matching must find one unique canonical candidate
that:

1. satisfies every dependent occurrence of the binder;
2. satisfies its declared supertype;
3. is consistent with already resolved earlier generics; and
4. makes the specialized domain or codomain valid.

Binders are resolved in telescope order. Resolving one binder substitutes its
evidence into the bounds and dependent occurrences of all later binders. This
allows a sum witness to constrain a later product, a product witness to
constrain a later sum, and longer alternating dependency chains.

For an `Args _T` occurrence, all supplied arguments contribute constraints to
the same `_T`. In the intended range test:

```datra
my_max := {Args (&_T :: IntLimit),} -> _T do
  # implementation

result := my_max (Args (from -128 to 127))
```

the inferred return type is the unique integer-range type selected for those
arguments, subject to `IntLimit`.

An unconstrained private product may remain symbolic at its declared bound when
the executed path and returned value are valid for every permitted
instantiation. For example, `nothing` inhabits `_T?` for every
`_T` within `IntLimit`. This does not expose a generic witness to the body or
select an arbitrary concrete subtype.

Matching reports a structured generic error when:

- a concrete witness is required but no argument, expected result, or valid
  symbolic-bound interpretation can supply it;
- evidence admits more than one canonical candidate;
- dependent occurrences impose conflicting constraints;
- a candidate lies outside the declared supertype;
- a required public witness is absent; or
- an explicit witness conflicts with dependent values.

Overload selection must retain these errors when the generic candidate is the
relevant function, rather than reducing them to silent candidate loss.

## Erasure and invocation

Generic witnesses are interface data. They are absent from the body's named
scope and from the body-visible `it`, regardless of identifier mode.

The prepared interface layout places generic evidence first and ordinary body
arguments after it:

```text
[generic interface slots 0 .. genericCount - 1]
[ordinary body arguments genericCount .. end]
```

The function schema records `genericCount`. A generic interface slot contains
resolved evidence when that evidence is known before invocation and a sealed
pending slot when a result-side sum will establish its evidence after the body
returns. For an ordered internal argument vector, constructing the body-visible
`it` is equivalent to:

```haskell
bodyValues = drop genericCount preparedValues
```

Named and structurally mapped domains perform the same operation by projecting
the schema's ordinary slots. The generic-count boundary remains the canonical
ordering rule, so erasure does not require rediscovering generic fields by
identifier text.

For `{x? : T; y? : (&T :: Any)}`, the prepared interface vector is
conceptually `[T, x, y]`, `genericCount` is `1`, and the body-visible `it` is
`[x, y]`.

Invocation has an external and internal boundary:

```text
call arguments
    -> resolve public witnesses and infer private witnesses
    -> specialize and validate the function signature
    -> project ordinary body arguments
    -> invoke the internal closure
    -> validate or package the result
```

The external function value owns the `FunctionType`, generic schema, inference
logic, and result checking. The internal closure owns the body and receives the
projected ordinary arguments. This may be represented as two runtime values or
as one function value with separate preparation and invocation stages.

Recursive `this` calls target the external function interface. Each recursive
call therefore performs generic matching and specialization for its own
arguments.

Erasure is semantic rather than necessarily physical. A private dependent sum
may retain sealed runtime evidence for validation and later opening, but that
evidence is not available as an ordinary field or body name.

## Escape rules

A dependent product generic may appear in the codomain because the caller has
selected or inferred it from the function domain:

```datra
head := {values? : List (&_T :: Any)} -> _T do
  # implementation
```

A private dependent sum witness cannot appear as an unsealed public result or
escape into a type position outside its owning package. It may leave the
function only through a dependent sum package that retains its hidden evidence,
or through a result widened to a type independent of that witness.

Escape checking operates on binder identity after function-type scope
resolution. An illegal escape produces a structured error naming the affected
generic and its source location.

## Combining products and sums

A function type may contain both product and sum generics. Their source order
defines the nesting order of the dependent quantifiers:

```datra
adapt := {
  source? : (^_Source :: Any)
  fallback? : (&Target :: Any)
  proof? : (^_Proof :: Any)
  adapter? : _Source -> Target
  check? : Target -> _Proof
} -> Target do
  # body sees source, fallback, proof, adapter, and check
```

Conceptually, this is an ordered generic prefix containing a sum, a product,
and a sum before the ordinary signature types. It cannot be reduced to one
sum-or-product classification for the whole function. Interface preparation
processes each binder in order, carrying the resolved environment forward to
the next binder.

Mixed polarity is therefore not classified at the container level and has no
mixed-binder rejection. The ordered telescope is the only place where product
and sum binders are combined.

## Dependent family construction

Reusable dependent families are generic functions or type constructors.
Dependent packages are introduced by `^` binders owned by a function type, not
by standalone maps that declare binders. A type constructor that needs a
selected witness to construct its result does so through generic
specialization at the interface boundary, or through an internal primitive
with exactly the same semantics. Generic evidence never becomes an ordinary
body argument merely to make family construction possible.

## `for` comprehension type

The standard-library `for` type owns the generic interface needed to relate the
input family, each selected member, and the resulting fibres. The two
comprehension forms are syntax templates over that type, not distinct evaluator
operations and not special cases in the generic constraint solver. Its
definition uses no `for`-specific host primitive or privileged generic rule.

`for i in values do expression` supplies `values` to the generic `for` type and
supplies the captured expression as its member transformation. Each selected
member is available to that transformation as the ordinary lexical name `i`.
Generic evidence used by the `for` type obeys the same inference, telescope,
specialization, and erasure rules as every other generic function call.

`for i <integer-valued-range> do expression` first normalizes the valued range
as the source and otherwise lowers to the same `for` application. Finite
sources produce finite comprehensions. Infinite sources retain lazy result
construction and must not be enumerated eagerly.

The source and transformation may themselves use generic functions and
dependent packages. Those nested generics form their own function-owned
scopes. The comprehension name remains an ordinary lexical name and cannot be
confused with a generic declaration of the same spelling.

## Delivery stages

### Stage 1: core generic operators

Implement `&`, `^`, and `::` as special parser and evaluator operators backed
directly by `GenericIntroduction`, `GenericBinder`, and the ordered telescope.
This stage establishes all generic scope, inference, specialization,
packaging, erasure, escape, and mixed-polarity semantics without depending on
the standard library or its string-template bootstrap.

Stage 1 does not need `some` or `forall` bindings in `std.datra`, and it does
not need to express the symbolic grammar through standard-library templates.
The operator behavior must nevertheless match the named-function lowering
specified for Stage 2 so that integration does not change generic semantics.

### Stage 2: standard-library naming and templates

Define the ordinary functions `forall` and `some`, attach the `&`/`^`/`::`
string templates to them, and lower the preferred symbolic source syntax to
normal applications of those functions. Canonical template-resolved function
expressions then use the named applications, while function-type resolution
continues to produce the same generic telescope as Stage 1.

Stage 2 also defines the standard-library `for` type in terms of these generic
interfaces and lowers both comprehension templates to ordinary `for`
applications.

## Parser and scope-resolution plan

1. In Stage 1, parse prefix `&` and `^` followed by the shared three-way
   identifier rule as core syntax.
2. Parse an optional `:: expression` bound, defaulting the bound to `Any`.
3. Produce a `GenericIntroduction` directly containing polarity, name mode,
   bound, and source location.
4. Resolve introductions only while constructing a function type.
5. Pre-scan the complete outer function signature, traversing its domain and
   codomain in source order while treating nested function types as separate
   declaration scopes.
6. Build one generic prefix before all ordinary signature types and replace
   marked occurrences with stable generic references.
7. Resolve generic bounds sequentially within prefix order, allowing only
   dependencies on earlier generic binders.
8. Resolve every ordinary domain and codomain type against the complete prefix.
9. Resolve nested function types independently, while allowing their ordinary
   types to reference generics from enclosing function scopes.
10. Reject duplicate declarations, invalid generic names, unresolved generic
    references, and introductions without a function-type owner.
11. Preserve the first-class semantic representation through AST round trips.
12. In Stage 2, attach the `&`/`^`/`::` string templates to the ordinary
    `forall` and `some` functions.
13. Capture the generic identifier through `$_IdenExp`, or a stricter dedicated
    identifier-expression hole if required, and make expansion produce normal
    `forall` or `some` application with that identifier and the
    explicit/defaulted bound as arguments.
14. Normalize the named application to the same `GenericIntroduction` accepted
    by function-type resolution, and use the named application as the canonical
    template-resolved expression form.
15. Parse `for identifier in expression do expression` and
    `for identifier integer-valued-range do expression` as comprehension
    templates that lower to the generic `for` type.
16. Reject type-level `for ... of ...`; reserve no grammar production or
    keyword role for `with`.
17. Represent a comprehension as the ordinary application produced by its
    syntax template; do not give it a dependent-binder AST node.
18. Ensure the template-resolved expression AST and its canonical renderer
    contain named generic applications and ordinary lowered comprehension
    applications, but no `ForBinding` or `WithBinding` forms.

Prefix parsing must remain compatible with surrounding operator precedence.
In particular, grouping such as `Args (&_T :: IntLimit)` must make `Args` an
application of the resolved generic reference, while the bound remains
`IntLimit`.

The parser must distinguish the `for` comprehension structurally,
not merely by seeing the token `for`. A missing `in`/valued-range and `do`
is a parse error, and invalid binder-like input cannot silently select another
parse branch.

## Semantic implementation plan

1. Add generic polarity, name mode, binder identity, and function generic
   schema to the AST as the Stage 1 core.
2. Implement function-owned two-pass prefix collection and semantic rendering.
3. Extend function argument schemas with virtual generic witness slots that
   precede and remain distinct from body argument slots, recording the generic
   count explicitly.
4. Implement public required and public optionally named witness matching.
5. Implement private product constraint collection and unique-candidate
   inference.
6. Specialize dependent domain and codomain annotations with resolved evidence.
7. Project the suffix beginning at `genericCount` before invoking the body and
   keep all generic names out of the body environment and `it`.
8. Implement domain-side sum opening and codomain-side sum packaging, retaining
   sealed evidence where required.
9. Add private-sum escape analysis.
10. Replace whole-function mixed-polarity classification with ordered generic
    telescope evaluation, allowing `&` and `^` binders to alternate.
11. Reuse common specification and subfederation operations for specialized
    dependent values.
12. In Stage 2, define ordinary `forall` and `some` functions whose applications
    construct the product and sum generic introductions established in Stage 1.
13. Define the symbolic string templates in terms of those functions and make
    named applications the canonical expression form after template expansion.
14. Define the standard-library `for` type entirely with generic interfaces and
    implement both comprehension templates as ordinary applications of it,
    including finite and lazy/infinite source behavior; add no `for`-specific
    host primitive or evaluator branch.
15. Express all standard-library and fixture dependencies through `&`/`^`,
    generic type constructors, and the generic `for` type.
16. Remove every parser, syntax, AST, evaluator, library, and diagnostic use of
    `with`.
17. Use generic telescope evaluation in place of binder-specific evaluation,
    static substitution, validation, and container-kind classification.
18. Remove `ForBinding`, `WithBinding`, `MixedDependentBinders`, and every
    parser, renderer, evaluator, diagnostic, and test branch specific to them.

The implementation should use one generic-binder descriptor and one scope
resolver rather than duplicating polarity and identifier-mode logic across the
parser, interpreter, and closure builder. The `for` type uses those public
generic semantics through ordinary function construction and application.

## Regression test plan

### Parsing and scope

- `&_T`, `&T`, and `&T?` produce the three product name modes.
- `^_T`, `^T`, and `^T?` produce the three sum name modes.
- Every form accepts an explicit `:: Bound`; an absent bound records `Any`.
- Stage 1 parses and evaluates all symbolic forms without loading `std.datra`.
- In Stage 2, every `&` form expands through `forall` and every `^` form expands
  through `some`.
- The generic template path captures `_T`, `T`, and `T?` and passes their name
  modes through unchanged.
- Explicit `forall` and `some` calls use ordinary function application syntax
  and resolve through ordinary identifier lookup.
- Symbolic and named forms normalize to identical polarity, name mode, bound,
  binder ownership, and binder identity behavior.
- Canonical function expressions after template expansion contain `forall` and
  `some` applications rather than the symbolic template spelling.
- `_T?` is rejected for both polarities.
- `Args (&_T :: IntLimit)` parses the application and bound correctly.
- Multiple introductions are collected into a generic prefix in
  first-occurrence order.
- An ordinary field may reference a generic whose marked declaration occurs
  later anywhere in the outer function signature.
- `(x : T, y : &T)` resolves both ordinary fields against the prefixed `T`.
- `{value : T} -> (&T)` resolves the domain reference against the codomain
  marker.
- `map` resolves `B` in `transform : A -> B` against the marker in its outer
  codomain.
- A later generic bound may reference an earlier generic binder; a generic
  bound that references a later binder fails.
- Product and sum introductions may alternate in one function scope.
- Cross-polarity bounds resolve against earlier binders in telescope order.
- Duplicate declarations in one function type fail structurally.
- Every outer-function generic is available throughout the ordinary domain and
  codomain, independent of marker location.
- Nested function types own independent generic scopes.
- Ordinary types in a nested function may reference enclosing generics, while
  marked introductions in that nested function belong to the nested function.
- A generic introduction without a function-type owner is rejected.
- Canonical lowering, rendering, and parsing preserve polarity, identifier
  mode, bound, binder identity, and ownership.
- Type-level `for ... of ...` is rejected, and `with` has no grammar role.
- Neither excluded spelling appears in canonical source output.

### `for` comprehension semantics

- `for i in values do expression` lowers to an application of the generic
  `for` type and binds `i` only in the member transformation.
- `for i <integer-valued-range> do expression` lowers to the same application
  with a normalized valued-range source.
- The `for` type passes its tests as an ordinary generic definition, without a
  dedicated dependent-binder evaluator path or host primitive.
- Its generic evidence is absent from ordinary projections and `it`.
- Finite sources produce their fibres in source order.
- Infinite valued ranges remain lazy and allow finite access without eager
  enumeration.
- Nested generic functions in the source and body own independent generic
  scopes.
- Reusing the same spelling for an iteration name and a nested generic does not
  merge their binder identities.
- `with` is not recognized as a comprehension keyword.

### Product semantics

- A required public product witness is accepted by name and is required.
- An optionally named public product witness works positionally and by name.
- A private product witness cannot be supplied explicitly.
- A private product is inferred from one dependent argument.
- Multiple dependent arguments contribute consistent constraints.
- Conflicting, ambiguous, absent, and out-of-bound evidence each produce a
  structured error.
- Domain specialization validates dependent arguments.
- Codomain specialization validates the returned value.
- `my_max` over `Args (from -128 to 127)` has the inferred range return type.

### Standard-library generic targets

The standard library is expressed entirely in terms of generic typing and the
generic `for` comprehension type.

- `forall` and `some` are the ordinary function identifiers for product and sum
  generic introduction; the attached `&`/`^`/`::` templates lower to normal
  applications of them. Authored source normally uses the symbols, while
  canonical template-resolved expressions use the names.
- `for` is an ordinary named type defined entirely through `&`/`^` generic
  interfaces; the evaluator has no built-in knowledge of that name.
- `List`, `InhabitedList`, `Just`, and `Maybe` are generic type constructors
  whose element/type parameter is declared with `&`, with public name modes
  matching their intended named and positional application interfaces.
- `Args` is a generic type constructor over its element type. Its generated
  numbered slots and length-indexed alternatives use the `for` comprehension;
  neither stage uses a separate sum-binding construct.
- Any standard-library dependent package uses `^` in an owning function type
  and preserves sealed witness evidence through that generic interface.
- Syntax declarations expose the symbolic generic templates and the two `for`
  comprehension templates, but no type-level `for` or any `with` adapter.
- Loaded library source, canonicalized library AST, fixtures, and generated
  source contain no `ForBinding` or `WithBinding` node.

Generic type constructors may use interface specialization or generic-aware
intrinsics to construct their result type. Their witnesses remain absent from
ordinary body arguments and body-visible `it`.

### Numbers module regression target

The `Numbers` implementations of `max` and `min` use one private product
generic for their variadic element and result type. Each applies an anonymous
recursive function directly to the nonempty variadic split:

```datra
max := {Args (&_T :: IntLimit),} -> _T? do
  yield it !? fun {candidate? : _T, remaining? : List _T} -> _T do
    yield if candidate = Infinity or remaining = () or
      candidate >= (next : this remaining[0; 1..]) then
        candidate else next

min := {Args (&_T :: IntLimit),} -> _T? do
  yield it !? fun {candidate? : _T, remaining? : List _T} -> _T do
    yield if candidate = -Infinity or remaining = () or
      candidate <= (next : this remaining[0; 1..]) then
        candidate else next
```

The list-sequencing operator `values !? function` abbreviates
`values! ?? function it`. It guards on a successful, nonempty list split—not
general Boolean truthiness—and leaves an empty input as `nothing`.

The `_T?` codomain applies the ordinary optional-value operator to the generic
reference `_T`; it is not a generic declaration or optional generic name. The
inline helper signatures resolve `_T` from the enclosing function's generic
prefix, while runtime body lookup still has no `_T` binding. The `fun` operator
gives each helper a fixed point: inside it, `this` refers to the helper itself,
so recursion does not require a `maximum` or `minimum` binding.

Regression coverage must establish that:

- nonempty positional arguments infer one shared `_T` and produce the correct
  maximum or minimum;
- the observable result type is `_T?`, specialized from the argument evidence
  rather than widened to `IntLimit?`;
- an `Args (from -128 to 127)` instantiation retains that inferred range in the
  result type;
- zero arguments return `nothing` without choosing an arbitrary concrete `_T`;
- named and reordered variadic arguments preserve their existing behavior;
- negative integers, `Infinity`, and `-Infinity` preserve their existing
  comparison behavior;
- the anonymous helper signatures use the enclosing `_T` and recurse through
  `this` without capturing `_T` as a runtime body value; and
- body-visible `it` contains only the variadic number arguments, with the
  generic interface prefix erased.

### Sum semantics

- A required public sum witness is accepted at its boundary and is required.
- An optionally named public sum witness works positionally and by name.
- A private domain sum is inferred and opened from dependent input values.
- A private codomain sum is inferred and sealed from dependent result values.
- Multiple fields use the same witness and conflicting fields fail.
- Hidden evidence is absent from ordinary projections, rendering, the body
  environment, and `it`.
- A private sum cannot escape outside its package or owning function scope.

### Erasure and closure behavior

- Public and private generic witnesses are absent from the body-visible `it`.
- Generic names are unresolved if referenced as body variables.
- The interface schema places every generic slot before every ordinary slot.
- `genericCount` identifies the exact suffix used to construct body `it`.
- Ordinary arguments retain their existing names and positions after erasure.
- The external wrapper validates results after the internal closure returns.
- Recursive `this` calls re-enter generic matching.
- Closure dependency collection does not capture generic witnesses as ordinary
  lexical values.

### Required language interactions

Cover both product and sum function types with:

- forward specification using `~>`;
- reverse specification using `<~`;
- subfederation using `of`;
- named and positional calls for public optionally named witnesses;
- ordinary optional parameter names, kept distinct from generic name mode; and
- nested closures and recursive calls.

### Rejections

- A generic bound that references a later product or sum binder is rejected as
  an invalid prefix dependency.
- A mixed generic telescope with unsatisfied or cyclic evidence reports the
  binder at which resolution failed.
- An unsupported escape reports the generic binder and source location.
- An invalid public/private witness match is a structured matching error.
- A generic parse failure cannot silently select a different grammar branch.

## Completion criteria

### Stage 1 core milestone

Stage 1 is complete when the symbolic `&`, `^`, and `::` operators implement
the full generic binder, telescope, inference, packaging, erasure, and escape
semantics without loading `std.datra`. Standard-library `some`/`forall`
functions, their string templates, and named canonical lowering are explicitly
not prerequisites for this milestone.

### Stage 2 full completion

The full feature is complete when:

1. both prefixes parse with private, required-public, and optionally named
   public identifiers;
2. omitted bounds resolve to `Any` and explicit bounds preserve their full
   expression;
3. every generic is owned by exactly one function type, collected into an
   ordered prefix, and available to every ordinary type in that function's
   signature;
4. private products infer uniquely from dependent inputs;
5. sums open and package dependent values with sealed evidence;
6. public witness modes match according to their identifier form;
7. all generic evidence precedes ordinary arguments and is erased from the body
   environment and `it` using the recorded generic count;
8. dependent results are validated at the external function boundary;
9. private sum escape is checked;
10. products and sums can alternate in one ordered function generic telescope;
11. cross-polarity dependencies resolve in source order;
12. `~>`, `<~`, and `of` interactions pass for both polarities and mixed
    telescopes;
13. `List`, `InhabitedList`, `Just`, `Maybe`, `Args`, and every other standard-
    library dependent definition use generic typing;
14. both `for` comprehension forms lower to the generic `for` type and preserve
    finite and lazy/infinite behavior without a host primitive or evaluator
    special case;
15. type-level `for`, the `with` keyword, and their syntax adapters are absent;
16. `ForBinding`, `WithBinding`, `MixedDependentBinders`, and their dedicated
    parser, AST, evaluator, renderer, diagnostic, and test paths are absent;
17. `forall` and `some` exist as ordinary standard-library function identifiers
    for product and sum generic introduction;
18. `&`/`^`/`::` string templates lower to those functions, explicit named calls
    use normal application syntax, and canonical template-resolved function
    expressions use the named forms;
19. focused parser, interpreter, standard-library, and closure tests pass; and
20. the full non-Liquid test suite passes once, serially, as final validation.
