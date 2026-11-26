# Lean/LiquidHaskell alignment plan for `DatraCore`

## Purpose

This document specifies the alignment of Lean with the **current executable
representation** in `../src/DatraCore`. The executable model connects that
representation to the preprint's mathematics and guides checked LiquidHaskell
contracts for both primitive operations and their derived construction packages.
Removing trust directives is one completion requirement; it does not establish
the missing representation bridges or assembly contracts.

The governing rule is:

> Haskell defines the executable representation; Lean proves that representation
> correct and relates it to the abstract mathematics in the preprint.

This is deliberately stronger than renaming Lean declarations to resemble the
Haskell API. In particular, the new Lean layer must model Haskell's finite folio
GADT, full-spine page-element traces, normalization idempotent, dependent Atlas
data action, and symbolic `AtlasHom` syntax. The existing Mathlib-based model
should remain as the denotational specification.

There is no expectation that Lean proof terms can be pasted into
LiquidHaskell. Proof transfer means aligning definitions and theorem statements,
proving the result in Lean, and then porting the same structural argument to a
LiquidHaskell-friendly first-order proof function. Lean is the reference model
and regression oracle; LiquidHaskell remains the checker for the Haskell code.

## Current state

### Lean

`datra.lean` imports the formalization from `datra-lean`. The written preprint
sections and their mathematical definitions live in `datra-lean/Semantics.lean`,
under `Datra.Semantics`. This denotational layer is mostly extensional:

- `Dominion` stores a carrier and an embedding into `Nat`.
- `Chain` stores a linearly and well-founded ordered carrier with order type
  below `omega0 ^ omega0`.
- `Folio` stores a positive finite diagram `Fin length -> CoCon` and obtains the
  infinite spine by padding with the final page.
- `Folio.El` is Mathlib's category of elements of the page diagram.
- `Pag` wraps a folio; pagination morphisms are arbitrary functors between the
  stored element categories.
- `Atl` stores a pagination, a functor `Pa.El -> DomIns`, and pagewise
  disjointness.
- `AtlHom` stores a page functor and a natural transformation.
- `TallAtlas` and `Atl.coherence` expose the padded-spine presentation and prove
  that its coherence map is idempotent and not generally the raw identity.
- `DaTra` is then the ordinary Mathlib presheaf category `Atl^op -> Type`.

The `datra-lean/Executable` modules model the executable representations and
prove their interpretations into this denotational layer. Executable Dominion is
universe-polymorphic, accommodating dependent carriers that retain their page
presentation. Its conversion to the written Dominion applies to small carriers;
coalition's canonical carrier is equivalent to its small covered-data carrier.
Derived construction bridges still need work; the correspondence manifest records their coverage
separately. Presheaf and Yoneda packages have checked construction and elimination
laws in both languages, with no LiquidHaskell trust directives. The executable coalition-to-inclusion
arrow and inclusion action on insertions have interpretation theorems, including
identity and composition in the stable-transversal category. The one-page
interpretation lifts to a stable-transversal isomorphism. It transports the
written Dominion-inclusion hom equivalence, and both executable hom maps have
full interpretation and inverse laws. The forward naturality laws also preserve
the stored partial inverses. Haskell assembly certificates still need checking.
The public Atlas interface exposes the exact normalized insertion from its
retained presentation. The Dominion-inclusion owner uses this equation to prove
that transport has the constant identity forward map and decoder on every valid
owning arrow. Lean proves equality of the entire insertion after the carrier
identification, including inverse lookups. These facts provide the source-action
equations used by the inclusion assembler's checked constant-component
naturality callback. That callback combines constant-cell reconstruction with
the target Atlas identity law on accepted data at a valid normalized occurrence.
The exposed `DomanialInclusion.Action` interface owns the constant object-map
symbol and callback. The callback retains every target field, the complete untyped occurrence, and its owning
trace validity. Its checked page-arrow certificate sends every source pair,
including raw source occurrences, to the same normalized target identity.
Both callbacks are used by the inclusion assembler, and Lean's constructor uses
the corresponding constant object and identity-arrow operations. Public-client
checks require the valid target, preserve its fields, and prevent switching its
owner or contradicting the page law.
The component helper constructs directly at the selected dependent target while
keeping the object-map symbol abstract. It retains membership in both owning
Atlases, the forward callback, and the original decoder's result on every raw
target value. Source-membership evidence wraps successful decoded values without
filtering or changing them. Lean models this through the retained owner's accepted
constant carrier and proves that erasing the evidence recovers every original
lookup. The inclusion assembler uses this shared helper, with rank-polymorphic
inverse evidence at occurrences equal to the selected target. Public-client
checks reject missing constant-target, reachability, or inverse premises and
contradictions of the retained callbacks.
The complete primitive assembly still needs to connect the specialized dependent
component callbacks to its data-naturality certificate. The component-membership
contracts and the constant-data naturality theorem are checked separately; their
composition through the concrete object-map specialization is not yet checked.
The transposal, coverage, and stable-owner construction contracts remain separate
obligations.
The Charter object has an executable
coverage-enumeration Dominion, guarded data-arrow inverses, and an isomorphism
to the written covered-subtype Atlas. The complete-action helper preserves
the dependent cell and both directions of its insertion, including under
padding normalization. Charter's runtime arrow action restricts that complete
action and uses checked source-inclusion inverse evidence. The complete Charter
arrow, unit, counit, lift, and lower operations have semantic bridges. Its full
identity, composition, inverse, and naturality laws follow through a transported
hom equivalence. The Atlas-map and transversal-map wrappers preserve their
stored arrows, and their inclusion actions agree with the semantic full
subcategories. Charter coverage witnesses reuse the original Atlas decoder's
region and recompute the charted caches, matching the Haskell algorithm.

Primitive Atlas morphism actions retain their page-arrow and data-naturality
laws in a checked record tied to the stored owners, object map, and dependent
components. Public observations expose the normalized page action and invoke
those same certificates. Construction retains both owners and the exact
callbacks, including each component's entire partial inverse. Lean retains the
same operations and laws in its primitive morphism structure. Public-client
checks consume these contracts through the checked `Atlas.Morphism` interface
re-exported by `Atlas`. Rejection checks prohibit replacing a stored callback
without its certificates and contradicting the observed laws or retained owners,
object operation, forward component, or partial inverse. Matching the
intermediate owner of composed stable insertions remains a separate contract.
Primitive action normalization also uses this checked interface. It retains the
source and target owners, normalizes the object operation at both boundaries,
and selects the original complete insertion at the normalized source cell.
Idempotence proves the page-arrow and naturality laws for the rebuilt callbacks.
The chosen partial inverse is retained for every target datum, including failed
lookups. Lean proves the same callback retention and equality of the complete
normalized morphism image. Charter consumes this shared normalization operation
before restricting the complete action.
The primitive object callback retains owning trace validity: a source passing
the stored source Atlas's trace test maps to a target passing the stored target
Atlas's test. The checked record, constructor, and public observation retain
this conditional contract. Normalization carries it through both boundary
normalizations; its certificate remains unevaluated at runtime. Lean proves
the corresponding trace tests for the original and normalized object maps.
Identity assembly uses a checked raw object callback preserving its page,
position, trace, and cell, and a checked page-arrow preservation certificate
for the normalized callback. Lean proves the matching identity-object and
page-arrow laws. Identity data-naturality assembly remains open: the Haskell
type-family specialization must retain the dependent identity insertion's
application equation across the mapped-object type.
Primitive components are insertions between their stored owners' accepted
carriers. The forward map preserves target membership, and successful inverse
lookups preserve source membership. The record, constructor, and public
component observation retain these predicates. Normalization retains the same
entire insertion and transports both membership predicates by Atlas coherence.
Naturality requires valid owning source arrows and accepted source data, matching
Lean's accepted-carrier action. Lean explicitly reindexes each primitive
component through the actual allocations' accepted-carrier equivalences and
proves preservation of both callbacks. Public-client checks enforce membership
in both directions, the retained target owner, and naturality's domain premises.
Constructor checks retain both morphism-law certificates while independently
rejecting either missing component-membership guarantee. The module remains partial: the full
carrier interpretation must also retain dependent payload invariants, and
generic identity/composition assembly and matching intermediate owners remain
separate obligations.

Primitive transversal actions store their exact-image coverage law in a checked
record. The image operation retains the dependent target cell and datum before
the public coverage constructor packages them. Their shared primitive mapper
retains validity for the action's stored target Atlas and the exact witness
returned by its coverage callback. Both languages check these guarantees;
rejection checks prevent substituting another target owner or coverage witness.
The categorical mapper retains an unchanged image or a certified image paired
with its actual target owner. Identity retains the caller's source owner;
composition keeps the intermediate owner when the second map is an identity
and otherwise retains the second map's target. A checked public eliminator
requires source owning validity and supplies target owning validity to its
rank-polymorphic callback. The raw covered-element mapper erases this same
result, so it shares the certified execution path. Lean proves the composite
equation and preserves the semantic interpretation for that path. Coalition's
checked mapping worker consumes this interface and retains target ownership
through canonicalization. Its raw-result wrapper shares the same worker.
Atlas maps likewise store their
owning Atlas, canonical origin, and accepted-datum coverage law together. Their
extent eliminator exposes that owner to its callback. Coverage of an arbitrary
accepted datum follows by transporting it to the stored origin and applying the
checked origin-rank preservation theorem. The shared coverage-transport lemma
and the Atlas-map result contract are checked in both languages. These interfaces
keep coverage constructors private. Derived constructions allocate and retain
their owners through exposed interfaces; their outstanding assembly contracts
are tracked separately from this ownership boundary.

Total Atlas maps store singleton certificates for accepted data at each valid
final-page occurrence of their retained Atlas map. The checked constructor and
public eliminator keep the owner, final-region predicate, and membership
restriction together. The singleton constructor retains its selected value;
uniqueness applies only to the certified carrier. Lean models the raw package
against its retained `AtlasAllocation`, including the scalar trace test, final
page test, and membership subtype. Its interpretation uses the allocation's
accepted-carrier equivalence and preserves the owner and selected raw datum.
Transporting a singleton certificate to the categorical carrier and back
recovers the complete certificate. Every semantic territory is then inhabited
and subsingleton, establishing the written totality predicate. The raw
constructor/eliminator equation is proved in Lean. Conversely, written totality
supplies singleton certificates on genuine occurrences, and reconstruction with
the retained Atlas map recovers the categorical package exactly. This reverse
interpretation is noncomputable; Haskell construction still requires explicit
singleton evidence. The module remains partial:
the public Haskell contracts retain the owning domain, but do not yet expose
that exact construction/observation equation. Public positive checks exercise accepted selection, restricted
uniqueness, and reconstruction through the eliminator. Rejection checks prevent
dummy uniqueness proofs, owner substitution, unchecked region lookup, rejected
selected values, and uniqueness claims about unaccepted candidates. The runtime
regression uses a singleton accepted subset of a larger datum type and excludes
padded occurrences from the genuine final regions.

The ranked-Dominion cell model retains its raw ranking, decoding, forward maps,
and partial inverses. The extent is equivalent to the original Dominion and
preserves its rank. A final region is the fiber of that rank embedding at the
selected natural position, so absent ranks give empty regions and occupied
ranks give singleton regions. Region decoding checks the forward rank of the
candidate, even when the original decoder returns a value outside its image.
Lean proves cell round trips, membership preservation, padding normalization,
and forward/inverse composition; inverse composition covers arbitrary raw
target data. The shared extent/region datum representation and retagging
operation reuse the chained cell model. The exposed Haskell
`RankedDominionAtlas.Data` component checks both cell Dominions, their restricted
round trips, and their exact rank and decoder functions. The runtime factory
uses these checked Dominions and the explicit tag-and-rank membership predicate
for both allocation and its stored action. Public contract checks exercise both
round trips and decoder equations; rejection checks rule out wrong tags, wrong
region ranks, rejected decoder results, and changes to either stored decoder.
`RankedDominionAtlas.Action` checks the classifier, normalization, admissible
cell endpoints, membership preservation in both directions, and the insertion's
left inverse. The runtime uses that checked insertion. Identity and composition
preserve the exact forward map and partial inverse, including inverse lookups
on arbitrary raw target data. The cell shape is shared with the chained
construction; region positions are natural ranks. Disjointness follows from
the rank associated with each accepted region datum. Public checks retain the
raw identity and composition laws and reject incompatible endpoints, unchecked
source data, rejected inverse results, and false action equations.
`RankedDominionAtlas.Presentation` checks that owning two-page arrows supply
compatible cell endpoints, preserving the exact forward and inverse callbacks.
Its identity, composition, normalization, and disjointness certificates assemble
the accepted data action into an Atlas presentation. Disjointness uses the
actual natural spine and its checked finite-position law through the public
`Chain` interface. `TwoPagePresentation` supplies shared occurrence normalization,
arrow normalization, and final-position agreement for both ranked and chained
presentations. `RankedDominionAtlas.Pagination` checks the fixed recipe's exact
folio, two-page length, and natural final chain. The runtime factory allocates
this checked presentation through `withAtlasPresentation`. Public checks retain
the supplied pagination, exact data action, and fixed final chain. Rejection
checks enforce owning trace validity, accepted source and target data, the
two-page condition, and the natural spine required by region selection.
`RankedDominionAtlas.Owner` retains the exact presentation and supplied Dominion
through generative allocation. Its checked selectors expose the two-page folio,
natural spine, membership predicate, cell Dominions, and stored insertion action.
Membership agrees on every raw occurrence; forward and inverse observations
agree with the cell action on valid arrows and accepted data. The public data
lookup retains the original cell's rank and complete decoder after normalization,
including failed lookups. A checked Atlas-extent observation expresses the origin
rank as the retained origin Dominion's rank of the transported datum. Construction
checks the concrete presentation before passing the retained owner to the
generative callback. Coverage, maps, and traversals use this public owner interface.
Public checks preserve presentation identity, the supplied Dominion, membership,
and both insertion directions. Rejection checks prevent uncertified retention,
Dominion substitution, and false presentation, membership, or inverse equations.
`RankedDominionAtlas.Coverage` checks the region selected by the datum's Dominion
rank, its accepted region datum, and equality of the source and region images at
the origin. Coverage transport proves that the resulting witness covers the
original accepted datum, including its owning occurrence. The Atlas-map factory
uses this checked coverage callback. `TwoPageCoverage` supplies final-region
self-coverage to both ranked and chained constructions; both Lean models reuse
the corresponding shared proof. The origin-rank observation identifies the
coverage witness's cache with the original Dominion rank.
`RankedDominionAtlas.Coalition` checks the constructor's validity, canonical
origin, and exact cached rank. Its raw inverse decodes that cache with the stored
Dominion before applying the supplied partial inverse, including on uncertified
records. Dominion coherence and the supplied insertion's left-inverse law prove
the coalition insertion's round trip; its public contract retains both callbacks.
Public-client rejection checks enforce the lookup's exact rank and decoder,
the coalition's owning origin and cached rank, both raw decoder outcomes, and
the insertion's left inverse.
The traversal's component inverse applies the supplied partial inverse to the
raw target datum's value, including uncovered data. Its checked left-inverse
certificate uses the transported datum's origin rank, the coalition's cached
rank, and Dominion coherence to recover the original source. The traversal
supplies that certificate at its retained target origin. The shared checked
component constructor is exposed through `DomanialInclusion.Component`.
Its contract retains the complete forward and inverse callbacks: the forward
map projects the constant source datum and transports its coalition image;
the inverse invokes the supplied decoder and restores the constant-cell wrapper.
The constant-cell projection exposes both stored functions, and its reconstruction
law proves the component round trip. Lean uses the same decoder composition and
proves both callback equations, including failed and off-image lookups.
Public-client checks reject replacing either callback or dropping every image.
Lean assembles the two-page presentation's identity, composition, normalization,
and disjointness laws, retains the original Dominion with its exact allocation,
and relates the resulting Atlas data functor to the accepted runtime action.
The normalized action preserves both raw insertion directions. The two-page
arrow-position argument is shared with the chained presentation. Coverage
selects the final region at the original datum's Dominion rank and proves that
its image at the origin equals the source datum's image. The resulting Atlas
map covers every accepted extent datum. Its certified coalition carrier is
equivalent to the original Dominion, retaining the exact cached origin rank.
The coalition insertion's raw inverse decodes that stored rank before invoking
the supplied partial inverse; it preserves that algorithm even on uncertified
records. On certified records it agrees with transport through the coalition
equivalence. The complete ranked traversal has a semantic interpretation through
the shared Dominion-inclusion hom map. LiquidHaskell verification of the generic
traversal assembler's owning domains and coherence laws remains unfinished; the public
ranked module is partially aligned.

The chained-Dominion Atlas distinguishes extent-tagged data from region-tagged
data in its membership predicate. A region accepts only the value at its selected
chain position, including on padded occurrences. Its exposed
`ChainedDominionAtlas.Data` component checks the restricted cell Dominions.
`ChainedDominionAtlas.Action` supplies the shared cell classifier, membership,
and insertion used by the runtime presentation. Compatible endpoints are either
the extent or occurrences of the same selected region. The action checks both
directions of identity and composition, source/target membership, and separation
of distinct region images. Inverse composition retains failed lookups as well
as successful ones. The classifier is unchanged by the two-page normalization,
including on malformed raw traces. Lean models these same operations and proves
their laws, with a certified insertion preserving the raw forward and inverse
functions. Its extent carrier is
equivalent to the original Dominion, and each accepted region carrier has an
explicit singleton certificate. `ChainedDominionAtlas.Presentation` derives
endpoint compatibility from owning-trace validity in a two-page folio: both
non-origin endpoints normalize to page one, where transport preserves position.
The public PageElements interface supplies that same-page theorem. The runtime
mapper uses the resulting checked insertion, retaining accepted source and target
carriers and its exact forward and inverse callbacks. Lean proves the same
normalization argument and callback equations. A checked selection theorem
connects each valid non-origin occurrence to the selected value at its actual
page position, requiring the supplied chain to equal the owning final chain.
The two-page presentation combines these theorems into checked identity,
composition, coherence, and pagewise-disjointness witnesses. Named law functions
retain their refinements through polymorphic assembly, and the public constructor
retains the supplied pagination, membership predicate, and exact data action.
Lean packages the same laws in `AtlasMembershipAction.Laws` and retains them in
its `AtlasPresentation`. The runtime folio builder uses the shared checked origin
extension and retains its two-page length and exact final chain. Public rejection
checks require both assembly premises and reject changed pagination or action.
The runtime generative allocator retains the supplied first value, chain, and
Dominion with the actual allocated Atlas. Its public handle exposes the exact
final chain, two-page length, stored action, membership predicate, cell Dominions,
and insertion callbacks. The raw handle constructor is private; retention requires
these certificates, and coverage and traversal consume public observations. Lean
retains the same four runtime fields with an owning-presentation certificate and
proves that allocation preserves the supplied inputs. The public field observers
keep the owning refinement explicit and eliminate the record directly. Public
allocation callbacks retain all three inputs while reading the final chain from
the actual Atlas. Public rejection checks prevent uncertified retention, changed
inputs or action, Dominion substitution, and owner-scope escape or coercion.
The public membership observation agrees with the checked extent/region
predicate after the allocated Atlas's own normalization. Lean recovers the
stored datum family and proves the same observation equation, including on
padded occurrences. The allocated transport also agrees with the checked cell
map at both original endpoints, including the padded tail.
`ChainedDominionAtlas.Canonical` checks both fixed-recipe
instances and retains the class's first value, chain, and Dominion through the
shared checked owner constructor. Its public result exposes the exact canonical
pagination and complete presentation, and the underlying Atlas's final chain
is the recipe's chain. The main interface reexports this constructor. Lean
models the fixed dictionary tuple, shared page and Atlas recipe allocators, and
retained owner. It proves the input and observation equations and equality of
the canonical and runtime allocations' stored presentations. Coverage selects
the actual final region at the datum's chain position and proves that both
accepted data have the same origin image. Its public constructor requires the
owning trace and accepted datum and returns coverage for that exact source and
datum. The Atlas-map wrapper uses this checked coverage callback. Lean retains
the actual allocation, recovers its tagged carrier, and proves the same
coverage construction through the shared accepted-carrier interpretation.
The public coalition constructor uses that coverage to retain a valid canonical
coalition at the actual origin. Its value observer recovers the supplied value;
Lean proves the same observation through the retained tagged carrier.
Public rejection checks enforce coverage's trace and datum premises and reject
changed coalition values, invalid coalitions, and a different origin.
Canonical coalition reconstruction recovers the entire cached carrier from its
extent value. The checked coalition insertion retains its exact forward map,
partial inverse, target validity, and origin. Its inverse reads the retained
value before invoking the supplied insertion's partial inverse. Lean identifies
both directions with transport through the value/coalition equivalence, including
failed inverse lookups. The traversal uses this checked insertion. Constant and
chained Dominion construction and primitive stable transversals share the public
coalition insertion constructors, which preserve membership and the exact
origin on their restricted carriers.
The remaining traversal assembly and identification with the written Atlas
construction still need their complete checked contracts. Charter and the
chained construction share `DomanialInsertion.Core.insertionOn` to retain source
and target predicates while packaging their callbacks.

Coverage validation checks the retained region's owning trace, datum membership,
final page, and both cache equalities. Matching the source's origin rank is only
accepted after that validation. Lean proves that the executable validator is
equivalent to a genuine territory representative, so checked covered-element
packaging derives that representative from its coverage evidence. The Haskell
payload keeps its dependent region and datum together; the abstract
`CoverageWitness` type exposes the three owner parameters directly in checked
contracts, and `AtlasCoverageWitness` is its object-indexed form. Public
elimination retains the final-region, membership, and cached-rank certificates;
rank observation keeps the constructor private. Coalition stores the shared
canonical `ChartedDatum` at its origin, together with the cached origin rank.
Its finite decoder canonicalizes successful codes, and coverage witnesses are
recovered through Charter's checked interface. `CoveredPageElement` and
`CoalitionData` expose the Atlas scope,
page scope, and datum family directly to checked contracts; their object-indexed
forms are aliases. All three parameters have nominal roles, and the constructors
remain private. The public coalition constructor/eliminator law retains the exact
stored source and datum for a rank-polymorphic callback. Lean proves the same law
for the certified constructor. A public read-only `CoalitionView` exposes those
dependent values through a first-order constructor law; it cannot construct a
coalition. The constant-value projection uses this view so its checked equation
does not depend on storing a polymorphic callback. Covered-element construction and decoding retain
`coveredPageElementValid` for the supplied Atlas. Its certified eliminator exposes
the exact source and witness together with owning-trace, datum-membership, and
coverage certificates. The coalition interface additionally retains its canonical
origin and the equality between a recovered witness's cached rank and the
coalition's rank observation. Coalition ranking reads the stored canonical code;
construction obtains it through the public witness-bounded search. The coalition
Dominion uses Charter's checked finite decoder and reconstructs the cached origin
rank from its returned canonical datum. Both languages prove that decoding the
stored code recovers the exact coalition record. The Haskell package retains its
rank and decoder functions and restricts its carrier to owning validity and the
exact canonical origin. Lean relates the stored code to the least coverage rank
and proves that projecting a decoded coalition yields the original Atlas decoder's
result, including failure. The Lean forward map acts on the full canonical
coalition record: it recovers the covered source, applies the transversal,
transports the image to the target origin, and retains its certified coverage
witness when building the canonical target cache. Its value
projection agrees with the covered-data map, and its semantic interpretation
agrees with the written extent map. Canonical-carrier extensionality proves
that rebuilding this value recovers the entire mapped record and that the
identity transversal returns the exact input record. Haskell's checked mapping
worker requires a valid canonical source and gives its callback a valid canonical
target with the retained owner. The owned-operation interfaces retain one target
Atlas together with a function mapping every accepted source to that Atlas's
valid covered or canonical coalition carrier. Identity carries the caller's
source domain through the callback package; composition retains the final
mapped owner and composes the stored functions. Pointwise observations use
this same operation. Coalition actions store their source owner, target owner,
and canonical function together; raw mapping and both owned observations
select that function. The public callbacks retain pointwise equality to the
raw coalition mapper, allowing its supplied inverse law to certify the owned
function without changing either executable direction. Lean models the
complete operation and proves that its application and composition agree
with the covered and coalition maps.
A primitive stable action stores its source
Atlas together with an insertion restricted to that Atlas's valid canonical
coalitions. The stored forward function is exactly the coalition mapper, and
every successful inverse result satisfies the same source-domain condition,
including on inputs outside the forward image. Primitive assembly also retains
the canonical mapper's actual target Atlas and a checked certificate that every
accepted source maps to a valid canonical coalition for that owner. The inverse
continues to accept all raw target records; its off-image behavior is unchanged.
Lean derives the matching target-validity certificate from the retained forward
equation. The declared extent target and the mapper's retained target remain
separate ownership obligations until their value-level correspondence is proved.
The generic insertion eliminator
and its identity/composition cases still need contracts retaining those domains.
The exposed `DomanialInsertion.Core` interface checks the composed forward
equation and both partial-inverse cases: failure of the second inverse is
retained, and its successful intermediate is passed to the first inverse.
Lean proves these same equations for arbitrary target inputs. These generic
composition laws do not by themselves connect a stable action's target owner
to the next action's source-domain predicate.
The public inverse callback retains source ownership through the full stable
syntax. Its hidden function package stores the source Atlas and an inverse
whose every successful result is a valid canonical source, including for raw
targets outside the forward image. Identity retains the caller's target owner.
Composition retains the first inverse's owner and uses the same checked
partial-inverse composition helper as ordinary domanial insertions. The package
is built independently of a target lookup. The callback requires a valid
canonical target, supplies a valid canonical source, and preserves failed
lookups. Lean proves that this observation agrees with the existing carrier
insertion's partial inverse for every canonical target. The generic insertion
accessor's forward-domain contract remains separate from this inverse boundary.
Lean accepts a stable
primitive's explicit inverse on canonical coalition records and transports it
through the covered-value equivalence. Returning to the record carrier recovers
the exact forward map and supplied inverse, including failed lookups. Identity,
composition, the left-inverse law, and interpretation into the written stable
coalition map hold on that record carrier. Certified
elimination also proves that rebuilding from the recovered datum and witness
returns the exact original coalition record. Canonical-code uniqueness proves
construction independent of the supplied coverage witness in both languages.
Equal dependent views reconstruct equal canonical carriers. The checked view
source law and constant-datum reconstruction transfer this equality to the
Dominion value projection without exposing private constructors to clients.
Negative checks reject elimination without owning
validity, substitution of the stored witness, changed coalition origin or rank,
and loss of the decoder's payload-validity certificate. Coalition Dominion guards
reject ranking without owning validity or the canonical origin, a decoding result
different from the stored record, invalid or non-origin decoder payloads, and
the claim that every candidate decodes successfully.

Coalition datum transport requires an owning target and the stored source's
page-order and trace-transport conditions. Its checked result belongs to the
target carrier and retains the coalition's cached origin rank. Coverage transport
uses the same certified witness: a shared checked equivalence relates coverage
before and after an Atlas data arrow. The Dominion-inclusion component requires
valid canonical coalitions with those transport conditions from its forward
callback, and its insertion retains target-carrier membership. Its separately
supplied component inverse still handles uncovered target data. Lean models the
same arrow conditions, certified inputs, and transported rank. Negative checks
reject missing target ownership or arrow evidence, a changed origin rank, loss
of coverage for the transported datum, and an inverse that drops every image
even when all forward-input conditions are supplied.
Coalition's checked covered-element conversion retains its source and witness
origin rank. The reverse conversion transports the covered datum to the owning
origin, retains that witness's rank, and computes the canonical cache through the
checked constructor. Equal cached origin ranks imply equal canonical coverage
codes; the checked finite decoder then identifies the complete records. This
extensionality law proves exact record recovery for a coalition converted to
covered data and back in both languages. `Coalition.Element` is the exposed interface; its checked
carrier implementation is separate from transversal assembly, allowing the
forward mapper to use both checked conversions. The transversal's checked image
eliminator supplies its actual target owner. `withMappedCoalitionElement` uses
that owner for canonicalization and retains target validity and the canonical
origin for its callback. `mapCoalitionElement` erases this callback boundary; it
takes only the source Atlas and transversal, since the target comes from the
certified image. This raw-result wrapper also checks owning validity and the
canonical source origin. Stable primitive construction retains that domain in
its insertion record instead of reflecting a weaker imported mapper signature.
Lean models the stored insertion from certified source records to raw target
records, including its inverse on arbitrary raw targets. Restricting the target
input to certified records recovers the existing categorical insertion with
the exact forward map and inverse. Lean uses the same callback path and proves
its equality to the record-level forward action.
Consumer-level rejection checks import only the exposed interface and reject
missing owning validity, changed origin or witness rank, equality without equal
ranks, and a round trip that changes the stored record.

Finite coverage decoding retains source-datum membership and coverage of that
exact returned datum. Its public interface can package the result as a covered
page element. Ordinal and coverage enumeration share one total Cantor pair and
finite-list codec, with both inverse laws and the decreasing bounds checked in
LiquidHaskell and Lean. Both languages check an inclusive bounded coverage search
and its least-match law. A covering witness supplies a checked successful
encoded candidate. The public rank operation searches only through that candidate;
LiquidHaskell checks termination and successful decoding, and Lean proves equality
with the least rank. The interval search and its least-result, trimming, and
uniqueness laws are shared predicate-based operations in `NaturalSearch`.
A canonical code is the successful rank selected by searching through that code;
two canonical codes for one datum are equal. The public rank operation retains
this certificate, and a public finite decoder recovers coverage evidence at an
already certified code. These laws are checked in both languages. Charter retains
the datum and its canonical code. Checked introduction, witness recovery, and
cache extensionality make equality independent of which final-region witness
establishes coverage. Local pullback
matches a requested datum exactly when their origin images agree. Consequently,
equal origin images have identical successful-code tests and identical canonical
codes. The public transport law derives this equality for every valid Atlas data
arrow using origin-rank preservation. The finite search's pointwise-congruence
law and the decoder argument are checked in both languages. Charter construction
stores this code, and its checked data-arrow helper preserves it. Transversal mapping
uses target coverage to compute the target Atlas's canonical code. The assembly
contracts connecting these operations remain to be checked.
Encoding first reconstructs the territory occurrence selected by the retained
region's position and transports the datum along its checked arrow before taking
the local rank. The public final-page index lookup and territory reconstruction
retain successful lookup, owning validity, and the requested coordinates. Lean
proves that this reconstruction preserves the mathematical code. Both checkers
prove that unranking the selected region datum and pulling it back through the
source insertion recovers the original source datum when their origin images
agree. The checked position codec recovers the exact selected index, and the
territory eliminator retains equality with the selected region. Together these
laws certify the finite bound in both languages. Charter uses the public finite
ranking and witness-recovery interfaces. Final-page selection retains the requested chain position
through the public page-element and territory interfaces. The singleton case
uses the general fact that a chain with a unique carrier value has position zero;
appended and singleton folios share the final-page lookup and trace-chain
construction.
Focused negative checks reject unproved carrier uniqueness, bounded ranks beyond
the supplied limit, minimality without a successful selected rank, and a changed
final-page position through either the implementation or its public interface.
The reconstruction checks also reject nonfinal input, absent territory lookup,
changed positions, mismatched source origin images, and a shifted region rank.
Witness bounds and finite ranking require evidence covering the requested datum;
validity of an unrelated region alone is insufficient.

The shared Atlas extent module is LiquidHaskell-checked. Its origin-rank
insertion requires explicit page-order and trace-transport conditions connecting
the source to this Atlas's origin. Lean derives these conditions for every valid
full-spine element. The Haskell module checks that each mapped source datum is
accepted by cell membership and that every successful inverse has the requested
rank. Public page lookup retains a typed folio prefix with the original origin
chain and value. LiquidHaskell checks its padding count, the generated trace's
length and origin suffix, and the origin arrow for the resulting page element.
A checked record retains the selected value at its actual position in the
prefix's final chain before the existential index hides its carrier types.
The trace is constructed while that carrier is known and stored with its exact
equality to the prefix's recursively generated padded trace. Its checked
invariants retain the requested page and position, exact trace length, starting
position, and origin suffix through the Atlas lookup callback. The Lean index
record models the stored trace and its equality to that computation. Lookup
walks the owning folio and retains an equation between the returned trace and
that folio's canonical trace lookup. Lean models this selection, proves that
the selected prefix belongs to the original folio, and proves agreement of the
returned trace with the canonical lookup, including unsuccessful lookups.
Lean proves that every genuine-page entry of the native cached trace is the
prefix's interval transport and every padded entry retains the final position.
The Atlas lookup wrapper requires both a matching origin and the owning-folio
trace equation. Its callback and the merge/sequence resolvers retain
`cellTraceValid` for the selected owner. Native lookup retains its entire
optional trace result, including failure, so the owner certificate implies
both exact trace length and the requested starting position. Both checkers
use these scalar conditions to prove that a suffix arrow reads the target's
position at the target page. Atlas ordering and transposal ordering share the
same Natural-indexed trace lookup; cross-language fixtures include offsets
larger than a machine integer. Negative checks reject omitting either endpoint's
trace shape, using the shape proof without an owner certificate, or dropping a
successful native lookup. Normalization preserves the same owner certificate:
canonical lookup at the clamped page equals lookup at the original page with
its trace trimmed to the owning folio's length. Genuine-page traces stay fixed;
padded traces trim to the exact native final-page trace. The Atlas object and
arrow normalization proofs retain that certificate using the checked equality
between the pagination's cardinality and its stored folio length. These are
scalar trace certificates; derived arrow membership preservation and the full
dependent-carrier assembly still need checked contracts. The cached folio counts are constructor
invariants: an origin has length one and an append increments the previous
length. Negative checks reject malformed counts, missing padding, a trace
that discards the origin or current occurrence, a stored value at an unrelated
position, a forged cached transport trace, lookup that shifts the requested
page, and Atlas lookup without its owning-folio trace equation. A runtime
regression distinguishes folios with the same origin, page sizes, and selected
coordinates but different intermediate transports, including padded pages.
Lean proves the corresponding trace and count laws. The shared Atlas lookup
callback retains the source's origin-arrow condition. Merge and sequence
resolve component cells through this callback, and their membership modules
are LiquidHaskell-checked. Both resolvers consume accepted cells from their
native page chains and retain the component's exact trace, page, and encoded
position. Sequence selection first recovers the member at the native cell's
index, with its list bound and accepted trace, then unpacks that member's Atlas.
Its callback retains the exact owning-member equation. Lean proves that these
accepted-trace callbacks always succeed and agree with component resolution.
Negative checks reject unaccepted native cells, changing the selected member
or component page, discarding the transport trace, and out-of-range indices.
Their full Atlas assembly
still needs the stronger validity and membership-preservation conditions for
data arrows and inclusion callbacks; generative scope alone does not establish
these value-dependent conditions.

Consolidation and opposite transport retain both order predicates through
identity and composition. The opposite wrapper declares invariant predicates,
so subtyping cannot replace the nested map's orders. `Consolidation.Ordered`
retains the actual source and target chains and checks monotonicity against
their executable position comparisons. Its composition requires the exact
middle chain to match. Lean proves that these comparisons agree with the
semantic orders and models the same concrete-chain package. Negative checks
reject changing the opposite wrapper's orders, dropping an ordered-input
condition, composing mismatched chains, and using identity between unrelated
orders. Folio presentations store each prefix and its ordered transition in a
checked `FolioStep` before hiding the preceding carrier. The next page is the
transition's source chain; its target must equal the prefix's final chain.
Origin transport and interval composition retain these exact endpoints.
`withFolioMap` exposes the ordered certificate to its callback, including the
chosen preimage and checked right-inverse law. Native traces use the stored
forward map and preimage. Negative checks reject mismatched preceding chains
and appending a map without evidence for the actual page orders. Native adjacent
trace transport preserves order on both genuine and padded pages. Its checked
consolidation retains the canonical trace carriers, predecessor, and stored
choice of preimage. `restrictedConsolidation` preserves both carrier predicates
through construction. The trace transition requires the actual position
functions to be trace heads; the native chain constructor exposes this equality.
Lean models the same restricted construction and proves native predecessor
monotonicity. Negative checks reject unordered pairs, traces from outside the
owning page, and unrelated position functions. A runtime regression checks
non-default chosen preimages and order preservation across padding.
`Consolidation.Sum` combines ordered component maps while retaining their
forward maps and chosen preimages. Its source and target position functions
must be the corresponding ordinal sums. Both checkers prove the four
same-component and cross-component order cases, including reflection of order
under an ordinal offset. Negative checks reject unrelated endpoint positions,
missing source order, and exchanged summand tags. A runtime regression checks
components with different source and target order types and non-default
preimages. `Consolidation.Reindex` transports the checked source and target
orders through carrier equivalences, retaining both directions of the map.
Merge page transitions sum the native component transitions and reindex them
through the tagged-cell encoding. Checked position transport exposes their
canonical position functions, and endpoint transport retains the actual
preceding page as the transition's exact target. The folio builder appends these
ordered transitions behind a checked singleton origin, choosing the left
component's canonical origin trace for the first transition's preimage.
LiquidHaskell checks accepted carriers, prefix endpoints, positive depth,
length, and termination throughout assembly. Lean proves that the endpoint
chains, forward map, and chosen preimage agree with the mathematical merge
transition. Sequence transitions recursively sum the checked member maps and
retag the cells, preserving both the forward map and chosen preimage. Endpoint
transport attaches the resulting map to the actual preceding page chain.
The folio step's source accessor has a checked endpoint contract and an opaque
logical symbol, so reflected lookup does not unfold an existential carrier's
transition selector. The correspondence inventory records opaque reflection;
negative checks reject false endpoint equations through this accessor.

Atlas data stores its four law witnesses with their refinements intact. The
owning Atlas checks that the stored normalization bounds match its pagination,
and its identity, composition, coherence, and disjointness accessors recover
the corresponding equations for the public data action. Pagination stores one
page-element category and recovers its folio from that category. The shared
extent module uses the retained composition law to prove that transport
preserves origin ranks and accepted cell membership. It also checks that every
accepted cell rank belongs to the extent, and that distinct cells on one
genuine page cannot accept a common rank. The latter proof recovers source data
from the checked inverses, then combines origin-rank injectivity with the
stored disjointness law. Lean's merge and sequence transport proofs reuse these
shared membership lemmas. Merge's executable membership consumes an
explicit resolved-source value: origin, left cell, or right cell. Its checked
source predicate retains the component's origin and owning trace. The component
transport relation allows movement within that component or into the fresh
origin; LiquidHaskell proves that it preserves accepted ranks, including the
phantom datum retag. Lean identifies this relation with its component-arrow
relation and proves the matching preservation theorem. Raw merge lookup returns
the same resolved values and retains their requested page and encoded position.
The shared Atlas lookup exposes its complete optional cell and trace result,
with the callback consuming that same lookup. Its owning-trace certificate also
proves membership in the component's native trace chain. Both checkers derive
native component transport from a suffix arrow between constructed merge
prefixes: equal-page suffixes identify the same native cell by chain-position
injectivity, and earlier-page suffixes follow the stored predecessor recursively.
The owning-folio lookup equation identifies each non-origin raw trace with its
constructed prefix, including prefixes beyond the stored folio's length.
Padded lookup adds the final position to the preceding trace. Both components
are padded beyond the merge's maximum depth, so their predecessor retains the
encoded merge position and the page order type. Successful resolutions of any
raw merge arrow therefore satisfy the component transport relation, including
padded arrows and arrows into the fresh origin. Valid raw occurrences always
resolve: genuine lookup yields an accepted native cell at the requested position,
and padded lookup descends one page before lifting the cell through the native
preimage. The decoder's checked success equation connects this witness to its
existing lookup. Both checkers prove raw-arrow membership preservation, and
the merge data insertion consumes that proof through a checked action module.
The complete raw data-action package retains the actual merge folio, membership
predicate, Dominion callback, and arrow callback. A generic predicate-action
constructor checks the rank-polymorphic packaging before the concrete phantom
data family is supplied. Both checkers establish its identity, composition,
normalization coherence, and disjointness. The shared Atlas disjointness witness
normalizes arbitrary full-spine occurrences before using the stored genuine-page
law. Component origin-rank disjointness therefore applies to padded pages inside
a deeper merge. The checked merge constructor consumes all four callbacks through
the public predicate-based Atlas constructor. Its pagination continuation retains
the accepted final native-cell type. Lean assembles the corresponding raw action
and laws into a canonical Atlas. Raw cell lookup agrees with component resolution,
including padded occurrences. The canonical accepted carrier and indexed merge
carrier are equivalent without changing stored data; this equivalence preserves
ranking, optional unranking, forward maps, and partial inverses. Their data
functors are naturally isomorphic, and the raw construction has a rank-preserving
isomorphism to the written bouquet Atlas. The Haskell inclusion certificates
still need verification.
Negative checks reject missing padding bounds, unaccepted native cells, missing suffix transport,
missing owning-lookup or target-owner evidence, a data insertion without both
owning traces, an unaccepted source datum, unrelated encoded positions or resolver
coordinates, disjointness applied to the
same cell and extent membership without an accepted source rank. The correspondence
inventory includes the logical predicate and refinement-type aliases used to
state these contracts. Atlas actions retain their native folio domain and a
first-order membership package. Lookup requires a valid occurrence in that
domain; transport requires valid source and target occurrences. The stored
Atlas action's domain must equal its owning pagination, including its
normalization bounds. Object Dominions and both directions of data insertions carry the appropriate
cell predicate. Atlas laws quantify over accepted data. Merge and sequence
store their membership predicates through the restricted-action constructor.
Extent and territory packages retain a `MembershipDominion`, so existential
elimination does not widen its carrier to the ambient Haskell type. Coherence
uses the identity insertion on this accepted carrier, with a checked equality
to the stored normalization action. Lean interprets the raw membership package
as a canonical indexed Atlas. Native lookup agrees with the canonical full-spine
trace, so every canonical occurrence satisfies the stored domain predicate.
Normalization preserves that predicate. The interpretation requires the same
folio ownership equality as Haskell's Atlas constructor, and supplies the
lookup and transport certificates from those proofs. Valid occurrences with the same genuine cell
have equal normalizations, so the accepted family follows from folio validity
without an extra assumption about the supplied predicate. The bridge transfers
all four Atlas laws and preserves ranking, decoding, forward transport, and
partial inverses. A natural isomorphism connects its data functor to the runtime
accepted-carrier functor. Merge and sequence reuse the shared carrier
equivalence operations for their indexed Dominions and insertions.
The merge page-chain constructor restricts each component carrier to the exact
trace returned by that component's native folio lookup. Native lookup succeeds
exactly below the selected page's ordinal and retains its starting position.
The trace chains are summed and retagged through a checked carrier equivalence
that explicitly retains target membership. Lean proves equality of this native
construction with the merge page model, including the executable decoder, and
identifies each native trace chain with its original dependent page. Negative
checks reject a false carrier equivalence and either trace-chain carrier being
widened to arbitrary raw traces. The checked predecessor drops one transport
step and preserves membership in the preceding page of the same component,
including across genuine and padded pages. Its checked preimage follows the
stored choice of preimage in each genuine transition and duplicates the final
position on padded pages. The result belongs to the next page and its
predecessor is exactly the original trace. Lean identifies both operations with
the dependent page transport and its chosen preimage. Haskell merge folio
assembly retains these checked transitions. Its transition interface also exposes
exact stored forward and chosen-preimage functions: the forward map is the
component-tagged trace predecessor, and the inverse follows the same component's
stored choice. The native trace consolidation, sum, and reindex interfaces retain
these equations through endpoint transport. A shared checked function-replacement
operation proves pointwise equality with both stored functions and preserves the
exact page chains. Lean proves that this replacement is equal to the original
consolidation, including its chosen inverse. The scalar consolidation accessors
have checked equations to their stored fields and opaque logical symbols, keeping
polymorphic selectors out of clients' proof unfolding. Full merge Atlas assembly
still requires checked data-transport and inclusion certificates. Sequence page chains
use a checked recursive sum of the members' native trace chains. Each cons step
preserves the first member's trace carrier and increments the tail's member
tags through a checked equivalence. The empty tail has an empty accepted
carrier. Canonical position transport retains the recursive ordinal-sum
formula. Lean proves equality with the finite sequence page chain after carrier
translation, including the decoder and rejection of out-of-range positions.
The exposed member interface retains the owning folio's trace membership,
page order, origin, predecessor, and chosen preimage, including padded pages.
Sequence origin selection uses its first member's canonical origin trace.
Negative checks reject arbitrary raw cells, changing a preimage's owning member,
unrelated transition positions, and encodings that discard accepted carriers.
The complete sequence folio is LiquidHaskell-checked: the maximum member length
is positive, the first chosen cell belongs to its page, and every append retains
the correct accepted carrier, prefix length, and exact preceding endpoint.
The recursion terminates at the prescribed depth. Merge and sequence share
checked origin-collapse, page-append, and tail-recursive prefix-extension
operations. The extension interface retains each page's accepted carrier,
canonical position function, actual preceding endpoint, and exact resulting
length. Appending preserves lookups at every earlier genuine page; lookup on the
new page returns the trace obtained from its stored transition. The shared
extension proves that every lookup within its supplied prefix remains unchanged,
including a prefix obtained by stopping the same extension at an intermediate
depth. Both Atlas constructors expose their actual finite prefixes and reduce
genuine-page lookups in the completed folio to the corresponding prefix.
Accepted native cells on appended pages resolve to that prefix's exact transport
trace; the singleton origin has its separate checked lookup law. The initial
merge and sequence pages use a shared origin-extension certificate retaining
their accepted carrier, length, canonical position, and exact two-entry trace:
the native cell position followed by the fresh origin's zero position. The
singleton chain exposes a checked position law, and the folio certificate derives
its initial trace from the existing trace-length and origin-suffix laws. Both
constructors expose this base case for their actual finite prefixes. The shared
extension identifies its final trace with
the last stored transition into the preceding constructed prefix. Merge and
sequence specialize this to the canonical cell position followed by the preceding
prefix's trace of `previousMergeCell` and `previousSequenceCell`, respectively.
Sequence member transitions, recursive sums, carrier reindexing, and endpoint
wrappers retain the exact predecessor and chosen-preimage functions. A shared
head/tail mapping operation handles both directions of the indexed-cell encoding;
its function replacements have checked pointwise equality with the original maps.
Lean models the same tail-recursive extension and proves equality with the
structural finite-prefix builder, including transition maps and chosen preimages.
Extending by one more page is exactly the corresponding append, yielding the
same trace equation. The component assemblies
specialize this shared operation. Lean proves equality of the
native sequence transitions, chosen preimages, and assembled finite folio with
the sequence model, including agreement of the recursive maximum with the
specified depth. Negative checks reject malformed prefixes, page-zero
transitions, unaccepted native cells, padded pages used as genuine pages,
intermediate prefixes beyond the final depth, substituted cell traces,
incorrect initial or recursive prefix-trace heads, and identity substitutions
for sequence transitions.
The nonempty-member-list adapter has a checked positive-length
contract and an opaque logical symbol; its constructor decomposition is checked
without exposing foreign datatype selectors to downstream reflection.

The shared Atlas native-trace lookup retains the exact trace, page, position,
and origin evidence in its callback and guarantees success for accepted traces.
Merge resolution decodes the native page chain used by its folio assembler,
then consumes the tagged component trace through this lookup. Its callbacks
retain the component tag and the component-page and merged-position equations.
Lean proves that this native lookup succeeds and returns the same component
cell as the component-resolution model. Rejection checks prohibit unaccepted
traces or cells, substituted traces, and shifted component pages.

Consumers must import exposed interfaces rather than another component's
`Internal` or `LiquidInternal` module. The primitive interfaces are `DatraOrdinal.Laws`,
`Chain.Sum`, `Chain.Position`, `Chain.Singleton`, `Consolidation.Core`, `Consolidation.Ordered`,
`Consolidation.Sum`, `Consolidation.Reindex`, `Consolidation.Endpoints`,
`DomanialInsertion.Core`, `Folio.Presentation`, `Folio.Assembly`, `PageElements.Structure`,
`PageElements.TraceChain`, `Atlas.Morphism`, `AtlasMerge.Assembly`, `AtlasMerge.Data`, and
`AtlasSequence.Data`, `AtlasSequence.Member`, `AtlasSequence.Page`, and `AtlasSequence.Assembly`.
Their definitions and refinement contracts are checked in
the exposed modules, including the logical record selectors used by clients.
The alignment checker enforces the `LiquidInternal` boundary in the library,
tests, and application. Cross-component `Internal` imports are also prohibited; all library, test, and
application consumers use exposed interfaces. The
merge modules use public component interfaces, including checked pagination and
Atlas constructors and a prefix-lookup wrapper that retains the success and
position contracts. Private implementation imports belong within their owning component.
The public `Pagination.paginationFromPageElements` constructor retains the
existing occurrence category and its scope. Generative pagination delegates to
the public page-elements allocator. Fixed folios use `PageElements.Construction`:
a pure class instance chooses the entire folio, and a nominal scope records the
recipe and both carrier types. Its checked constructor preserves the exact
recipe folio. Dominion inclusion and ranked Dominion paginations
use this interface. Runtime chains allocate pagination and Atlas owners once
through the public generative constructors. Chained Dominion handles retain the
chain, Dominion, and Atlas together; coverage, maps, and traversals reuse them.
Generic indexed maps expose the retained handle through an existential callback.
Range values retain their construction alongside their bounds, and their nominal
scope records both owners and the element membership tag. Canonical super-ellipsis
rank witnesses supply a fixed chain-and-Dominion recipe. No derived construction
uses the deleted scoped pagination allocator.
Lean models the fixed recipe and proves that pagination wrapping preserves its
folio and valid elements. Rejection checks enforce scope and recipe separation.
External-client guards reject escaped chained or indexed owners, mixed Atlas or
pagination scopes, and coercion of elements between different owning ranges.
The alignment checker rejects cross-component private imports on every run.
Dominion inclusion retains a generatively allocated Atlas in an abstract nominal
owner. Its coalition maps, hom equivalence, and traversals reuse that owner.
Dot uses a fixed `CanonicalDominion` instance through `Atlas.Construction`: the
complete presentation has no runtime configuration, and its nominal scope
records the recipe and every presentation index. Lean models allocation of this
fixed presentation. The inclusion's fixed recipe, one-page presentation, and
coverage helper are checked. Its retained owner stores the one-page certificate,
constant membership, and identity insertion action. Generative and canonical
allocation preserve the exact raw presentation through the exposed presentation
and fixed-recipe interfaces. Lean retains this raw allocation before interpreting
its accepted carriers; the Dominion owner certifies both directions of the
constant insertion. Its carrier equivalence recovers the original constant value
and commutes with normalized forward maps and partial inverses. Fixed Atlas scopes retain the recipe and every presentation
index, and their allocator exposes its defining equation and exact presentation
and pagination preservation. The public folio observation retains its equality with
the owning pagination's folio. The inclusion's Atlas-map constructor supplies its
one-page coverage through the checked public `AtlasMap` constructor, which retains
the origin, owning-trace, and accepted-datum conditions on its callback. Lean models
both allocation paths and proves coverage for the resulting Atlas map. A public
Atlas lemma relates datum membership to the retained presentation's normalized
action. The Dominion helper uses it to prove that every constant datum is
accepted. Coalition-element construction is checked through the public coalition
constructor with that membership fact, the canonical origin's owning trace,
and one-page coverage. Lean packages the same origin datum with its canonical
coverage code as a certified coalition element. The constructor retains the equation that
reading the constant datum recovers the original value. This checks the
value-to-coalition insertion, including its exact forward function, inverse,
and left-inverse law, in both languages. The isomorphism uses this checked
insertion. Coalition's public `Eq` compares cached origin ranks. Canonical-code
uniqueness and the fixed origin make equality of certified coalition values
imply equality of their stored records. Lean proves this extensionality law and
the allocated owner's reconstruction law, then packages the constructor and
value projection as an equivalence on the canonical carrier. The reverse
insertion reconstructs the exact canonical carrier in both languages.
Haskell checks both insertions and the public isomorphism package, including its
left- and right-inverse eliminators. Their contracts retain owning validity and
the exact canonical origin. The construction helpers preserve these two carrier
conditions separately when instantiating the insertion datatype. The larger
hom-correspondence assembly still needs checked contracts.
Ranked Dominion construction allocates an Atlas through the public generative
constructor. A retained handle ties the supplied Dominion to that exact Atlas;
coverage, maps, and insertion traversals reuse it. Its region decoder uses the
checked `Dominion.lookupRank`, which accepts a candidate only at its forward rank
and preserves decoding at every inhabited rank. Both cell Dominions have checked
Haskell contracts through `RankedDominionAtlas.Data`. Lean proves the complete
normalized action and its Atlas interpretation, coverage, coalition equivalence,
and insertion traversal. Haskell checks the cell action and its connection to
owning page arrows, including all four presentation laws. The retained owner
preserves the exact presentation and both normalized insertion directions.
Coverage selects the region at the original Dominion rank and certifies the
source datum through the common origin. Coalition and traversal contracts are
still partial.
The public Dominion constructor and insertion core retain both supplied
executable functions in their checked result contracts. `DomanialInclusion.Data`
checks the constant carrier's rank, raw decoder, round trip, and identity
insertion, including its inverse. The raw decoder preserves off-image results
exactly as supplied by the original Dominion. The coalition-dependent assembly
uses this exposed carrier interface. Public page allocation likewise carries
the input-folio equality through its callback; pagination preserves that owner.
Rejection checks prohibit changed ranks, discarded successful decoder results,
changed identity data, discarded identity inverses, and substituted allocation
folios. `DomanialInclusion.Presentation` checks the complete constant action's
normalized identity, composition, coherence, and disjointness laws, retaining
the supplied pagination and action in its result. Disjointness requires a
one-page folio and uses the checked fact that valid transport within one page
preserves position. Lean uses the same argument in the inclusion's actual data
assembly. Its fixed recipe has a checked class-method contract guaranteeing one
page, and the actual presentation caller checks that premise. Lean models the
predicate-action package, its accepted carriers, and both executable directions;
erasing the always-true membership proofs gives a natural isomorphism to the
constant functor used by the inclusion interpretation. Ranking and decoding,
including off-image decoder results, agree through this carrier equivalence.
The checked coverage helper uses the normalized source as its final region and
transports the witness back along coherence. Lean's inclusion coverage theorem
uses the same cached-witness construction. Rejection checks require a one-page
owner, a valid owning trace, and accepted data. The coalition equivalence and
hom-map assemblies still need their full contracts checked. The inventory records refined instances, and the trust gate
rejects assumptions nested inside their method signatures.
Merge, sequence, the empty Atlas, and Dominion inclusion share the checked
singleton-chain constructor. Lean uses the same singleton chain and the common
carrier-reindexing operation in its derived folios.

Merge and sequence components use a shared origin-rank insertion. Its inverse
checks the candidate's forward rank, because Dominion unranking and insertion
preimages may return arbitrary candidates outside their images. LiquidHaskell
checks the rank insertion's round trip and inverse soundness. Lean identifies
its accepted ranks with the semantic image Dominion and proves rank preservation;
Atlas cell and extent membership use this operation. Identity, composition,
and induced source rankings are checked in the insertion implementation module;
the public Category instances delegate to those operations. Lean also models
the opposite insertion wrapper and its reversed composition. The merge's tagged
data, parity decoding, and membership invariant have an executable model for
each successful cell-resolution branch. Its Dominion is equivalent to the
semantic root-map image, preserving ranks. Data arrows commute with that
interpretation, preserve identity and composition including their stored partial
inverses, and both inclusion components satisfy naturality. The finite merge
folio stores tagged full traces, builds the component pages by a checked chain
sum, and appends them behind a fresh singleton origin. Its page order agrees
with the written bouquet pages; adjacent transports and their chosen preimages
agree with the component consolidations. Its stored and semantic lengths agree
with the bouquet length. The cell resolver gives an equivalence between actual full-spine
merge occurrences and the fresh origin plus left/right component occurrences.
Both inclusions resolve back to the exact source occurrence, including padding,
and satisfy their page-number and ordinal-position equations. Stored-page
resolution preserves every actual page-element arrow, is invariant under
normalization, and agrees with full-spine resolution on normalized occurrences.
Checked position lookup recovers valid occurrences without choice. The merge
Atlas has a computable genuine-cell data family and checked identity,
composition, coherence, and pagewise-disjointness laws. Its normalized data
action commutes with the semantic root-image interpretation and preserves ranks.
The finite page equivalences intertwine every interval map and induce mutually
inverse functors between the finite element categories. Runtime membership
accepts exactly the ranks in the corresponding written bouquet data fibre;
the resulting rank-preserving data equivalences are natural. Together these
give an isomorphism from the complete executable merge Atlas to the written
bouquet Atlas, including both inverse laws. The canonical inclusion object
maps use checked full-spine page lookup, with proved normalized object
insertions. Their optional inverse decoders have round-trip and inverse-soundness
laws and reject the opposite component. Prefix ordinal subtraction has an
exact coefficient model and a checked relation to sum-interval subtraction.
Both inclusion object maps agree with the written finite inclusions and have
normalized arrow certificates. Their dependent data insertions accept exactly
the source cell ranks, including padding pages inside a deeper merge, and
satisfy normalized naturality. The resulting executable morphisms and checked
object inverses assemble into complete transposals. A common-page transport
argument proves strict-order preservation for both inclusions, giving executable
ordered transposals. The written bouquet has canonical inclusion morphisms
whose data components are the tagged origin images. Both complete executable
inclusion morphisms, including the ordered wrappers, commute with the merge
interpretation isomorphism and these written inclusions. Haskell assembly
certificates remain to be checked. The merge's
shared datum module is LiquidHaskell-checked: parity decoding and retagging
preserve ranks, retagging round trips, and membership-filtered unranking is
sound and round-trips accepted data. The checked module packages a Dominion
on that restricted carrier and an insertion between accepted-data carriers,
requiring explicit preservation of the target membership predicate. The merge
assembly uses these constructors. The datum's nominal cell role prevents
coercion between distinct cell identities. The Atlas assembly still needs to
establish and retain those membership preconditions for its dependent data
family, including the membership-preservation witness for each data arrow.

Sequence has a checked finite-member datum model. Its radix encoding is
`memberCount * originRank + memberIndex`; decoding requires a positive member
count, and its round-trip theorem requires a member index below that count.
LiquidHaskell checks these conditions, membership-filtered decoding, and the
restricted Dominion constructor. The runtime sequence uses this constructor
and a checked membership-preserving data insertion, with a nominal datum cell
role. Lean models the corresponding finite family of source cells, proves
that membership implies a bounded member index, and supplies data-action
identity, composition, and member-component naturality laws. Its accepted-data
carriers have rank-preserving equivalences with images in the finite tagged
sum of member extents, and the data action commutes with these equivalences.
The sequence folio has a computable finite ordinal-sum page chain, tagged
transport traces, adjacent consolidations with checked preimages, and the
maximum-depth finite spine. The prefix accumulator and optional-subtraction
member scan have exact roundtrip, soundness, bounds, and ordering laws.
Padded-page lookup preserves the requested full-spine page number. Resolving
a sequence occurrence and rebuilding it from its member occurrence are inverse
operations; canonical member objects satisfy their page and prefix-position
equations. Binary merge and sequence share the finite-prefix folio constructor,
structural page indices, interval-resolution and pagewise-separation proofs,
and padding/cast lemmas. Every sequence arrow resolves to a checked member
transport or to the fresh origin. The stored resolver is invariant under
normalization and agrees with full-spine resolution on normalized occurrences.
The sequence Atlas has a computable genuine-cell data family and checked
identity, composition, coherence, and pagewise-disjointness laws. Its data
action commutes with the tagged root-image interpretation and preserves radix
ranks. Canonical member inclusions have checked object lookups, optional inverse
round trips and inverse soundness, and reject objects from other members. Their
normalized arrow maps preserve the actual sequence intervals. Their dependent
data insertions accept exactly the source ranks, including padding inside a
deeper sequence, and satisfy normalized naturality. These assemble into complete
executable ordered transposals. Merge and sequence share the clamping and
constant-page-shift order proofs. The semantic finite-family
folio uses lexicographically ordered tagged member cells, componentwise
consolidations, and one fresh singleton origin. Its finite sums retain the
ordinal chain bound. Executable page equivalences preserve order, identify the
maximum depth, and commute with every finite interval. The resulting element
functors are mutually inverse. Merge and sequence share the general finite-folio
comparison construction. The semantic sequence data functor uses images in the
finite tagged union of member extents. Its identity, composition, and pagewise
disjointness laws are checked. Bounded executable data membership agrees exactly
with the ranks in each semantic cell; quotient/remainder decoding gives a
rank-preserving data equivalence. Together with the folio comparison this proves
a complete Atlas isomorphism. The canonical member morphisms, including their
ordered-transposal presentations, commute with this isomorphism. Merge and
sequence share the rank-preserving Atlas comparison and origin-membership proofs.
The runtime Atlas assembly
must also establish the membership conditions and arrow-preservation evidence
required by its checked helpers.

Charter's higher-level map and adjunction assembly still needs LiquidHaskell
contracts. Propagation of coverage and inverse certificates across those public
entry points remains to be checked. Cached construction, witness recovery, canonical equality,
and both directions of data insertion have checked helpers. Data preimages check
the actual forward image before retaining a target's cache; successful preimages
are certified to map back to the requested charted datum. Assembly uses those
checked constructors and insertions through `Charter.Data`; the raw datum/code
constructor remains hidden by that exposed interface. Identity, composition, coherence, and disjointness
have pointwise laws for whole cached values. Their proofs use the public Atlas
law observers and canonical-cache extensionality. The public normalization arrow
retains its owning trace and exact endpoints. Checked normalization equalities connect
Atlas operations to their owning PageElements operations; the exposed interface
retains the final-page bound and unchanged cell position. Normalization preserves the whole
Atlas data insertion, both coverage-code predicates, Charter membership, and
the complete transported cache. The origin-rank normalization correspondence
links the checked rank-preservation proof. The action package retains the
canonical membership predicate and the exact Dominion and insertion callbacks.
Assembly delegates all four constructor laws to normalized-insertion helpers
whose inputs require membership at the normalized source. Lean packages the
cached action on genuine-cell indices and proves that this change of index
preserves ranking, decoding, forward mapping, and partial inverses. Its complete
cached Atlas has a natural data-functor isomorphism to the covered-value model
and a whole-Atlas isomorphism to the written covered-subtype definition. The
Haskell presentation assembly is checked through the public `AtlasPresentation`
constructor, retaining the owning pagination and the exact certified action. Its
normalized laws use the explicit normalization equalities. Stable object
allocation uses the exposed `Atlas.Construction` interface. A pure construction
instance fixes the data-family recipe, and the recipe together with the original
owner determines the nominal output scope. Charter uses that interface for its
object and morphism scopes. Lean models the fixed object recipe and its retained
pagination, and relates presentation allocation to that object action. Focused
rejection checks protect the normalized laws, retained pagination and action,
instance method contracts, and scope identity.
Lean proves that cached ranking, finite unranking, and both directions of data
insertion agree with the covered-carrier model.
The checked insertion helpers alone do not discharge those assembly obligations;
these modules remain partially aligned. The runtime Atlas membership checks
accepted data and canonical codes. Counit and mapping insertion contracts restrict
both their carriers and inverse callbacks to that membership; projecting arbitrary
datum/code pairs would not be injective. The Dominion constructor uses that same
membership contract. Its finite decoder
canonicalizes successful codes, and its round-trip proof identifies the decoded
datum through the public exact-decoder law and then applies canonical-code
uniqueness.
The charted carrier retains its datum and canonical coverage code. Construction
obtains that code from checked coverage;
finite decoding canonicalizes any successful input code. Intra-Atlas data
arrows preserve the code by the checked transport law. Transversal mapping between
Atlases must obtain target coverage from the transversal and compute the target's
canonical code. Witness recovery uses the stored code directly. Equality and
inverse laws must include the canonical-code uniqueness argument, so different
initial region witnesses do not distinguish charted values.

### Haskell and LiquidHaskell

The current `DatraCore` representation is executable and intensional:

- `Dominion` has `rank`, executable `unrank`, and a checked round-trip law.
- `Ordinal` is a canonical Cantor-normal-form value below `omega^omega`.
- `Chain` has an explicit order type, position function, lookup function, bounds,
  injectivity, and surjectivity witnesses.
- `FolioData` is a nonempty, type-aligned GADT built from an origin and `SnocPage`
  steps, each carrying an adjacent coconsolidation.
- `PageElement` stores a page number, ordinal position, full transport trace,
  and existential cell. Arrows are characterized by reverse page order plus the
  trace-suffix transport relation.
- Pages beyond the finite presentation are real full-spine occurrences. They
  normalize to their last genuine representatives by clamping the page and
  trimming repeated trace entries.
- `Pagination` gives a folio a generative phantom scope and retains its owning
  page-element category in a named private field. A public measure exposes that
  exact category to checked contracts. Its morphisms are object maps plus an
  arrow-preservation witness.
- `Atlas` has a second generative identity and a dependent `cellData` family.
  `AtlasData` stores the object/action operations plus identity, composition,
  full-spine coherence, and pagewise-disjointness witnesses.
- Primitive Atlas morphisms normalize at source and target and carry page-arrow
  preservation and data-naturality witnesses.
- Primitive Atlas transversals certify coverage of the actual mapped source datum.
  Their callback receives only the covered source; the shared image operation
  supplies the dependent target datum used by the coverage predicate.
- Primitive stable Atlas transversals carry an explicit coalition inverse and
  its left-inverse certificate for the actual forward coalition action.
  Identity and composition derive the insertion and its certificate
  structurally; coverage preservation alone does not supply an executable inverse.
- The executable coalition-to-inclusion construction additionally takes a component
  inverse on target cell data, with a checked left-inverse certificate for the
  transported coalition action. Uncovered target data need no coverage search.
- Charter counits and the lowering hom map take an explicit inverse on original
  cell data, with a checked left-inverse certificate. `chartCellData` constructs
  a charted datum from checked coverage evidence.
- Charter data arrows verify inverse candidates against the target Dominion's
  rank before retaining them. Their origin-image equation then reflects target
  coverage back to the source cell.
- `chartMap` and `charterFunctorHom` take the source's covered-inclusion inverse
  and left-inverse certificate. Complete components use this inverse to retain
  source coverage. `chartLift` derives it from its source Atlas-map evidence.
- `AtlasMorphism` and `AtlasHom` explicitly represent identity and composition.
  A materialized identity is the Atlas normalization/coherence idempotent, and
  composite evaluation inserts the middle Atlas coherence.
- Presheaves take an indexed value family of kind `Type -> Type`.
  `DataTransformationValue values atlas` is ordinary family application, and
  `YonedaPresheaf represented` is the family `Yoneda represented`. Named action
  and component wrappers retain the rank-polymorphic operations and their laws.

### Trust boundary

`DatraCore` contains no LiquidHaskell `assume` or `ignore` directives. The
alignment gate rejects these directives even while other representation bridges
remain unfinished. `DataTransformation.Core` checks generic presheaf and natural
transformation packages, the pointwise Yoneda laws, the representable package,
and its action equation. Its public constructors retain their law obligations.
The small `DataTransformation.LiquidInternal` assembly uses those exposed
contracts to check the representable natural transformation.

## Architectural decision: two Lean layers

The rewrite should not discard the existing abstract development. It should
separate it into two connected layers.

### 1. Executable layer

Create a `Datra.Executable` namespace whose definitions mirror the Haskell data
constructors, eliminators, and recursive functions closely enough that every
LiquidHaskell theorem has a Lean counterpart over the same cases.

Suggested modules:

```text
datra-lean/Executable/Ordinal.lean
datra-lean/Executable/Dominion.lean
datra-lean/Executable/Chain.lean
datra-lean/Executable/Consolidation.lean
datra-lean/Executable/Folio.lean
datra-lean/Executable/PageElements.lean
datra-lean/Executable/Pagination.lean
datra-lean/Executable/Atlas/Data.lean
datra-lean/Executable/Atlas/Morphism.lean
datra-lean/Executable/DataTransformation.lean
```

`datra.lean` is the import entry point. The literate preprint material remains
beside the corresponding semantic definitions in `datra-lean/Semantics.lean`.
The full preprint must include only Lean code relevant to the preprint's
definitions, constructions, and results. Each section's code must correspond
to its written definitions; those written definitions remain unchanged. The
source appendix must not automatically include the entire `Executable`
alignment layer merely because it is reachable through local imports.
`PREPRINT_SOURCES` in `datra-docs/Makefile` selects `datra-lean/Semantics.lean`.
The extractor's `--exact-sources` mode includes only that explicit selection,
without expanding local imports. This selection is separate from the complete Lean
build: all executable models and interpretation proofs remain in the project
and continue to compile, while only code needed for the preprint's exposition
is included in `make preprint-full`. Check this target once at final completion,
including its source selection and the rendered document.

### 2. Semantic layer

Move or retain the existing Mathlib definitions under `Datra.Semantics`. This
layer contains the ordinary categories, functors, presheaves, adjunctions, and
monoidal results.

The bridge from the executable layer should provide:

- an interpretation of executable ordinals and chains into the Mathlib order
  model;
- an interpretation of a GADT-style folio as the current finite diagram;
- an equivalence between trace-based page elements and the appropriate category
  of elements;
- an interpretation of normalized executable Atlases into stored finite
  semantic Atlases;
- preservation of identity and composition; and
- compatibility of the derived constructions that the Haskell implementation
  exposes.

The target is not necessarily definitional equality. Named equivalences and
commuting theorems are preferable to pervasive casts.

## The Atlas alignment in detail

Atlas is the critical boundary because its dependent data action and ownership
contracts underpin the derived constructions. The structural Atlas and presheaf
laws are checked without assumptions; the remaining work connects executable
representations and their complete assembly contracts to those laws.

### A. Reproduce the executable foundations

1. Define an executable dominion with `rank`, `unrank`, and
   `unrank (rank x) = some x`. Prove that `rank` is injective and provide a
   forgetful map to the current `Dominion`.
2. Define the executable ordinal representation used by Haskell, including
   canonical coefficients and comparison. Prove its interpretation is below
   `omega0 ^ omega0`, and prove correctness of comparison and the operations
   needed by chains and sums.
3. Define an executable chain using `orderType`, `position`, and `lookup` plus
   the three Haskell laws. Derive `LinearOrder`, `WellFoundedLT`, and the current
   semantic `Chain`. Conversely, identify exactly which semantic chains admit
   an executable lookup; do not claim an equivalence for noncomputable chains.
4. Mirror `Consolidation` as a monotone map with chosen executable preimages and
   the corresponding right-inverse proof. Prove identity and composition both
   extensionally and at the stored representation level.

### B. Make the finite folio representation explicit

Introduce a dependent nonempty sequence corresponding to Haskell's
`OriginFolio`/`SnocPage`:

- the origin page includes a selected value and uniqueness proof;
- each snoc step includes the next chain and the adjacent coconsolidation;
- `length`, `origin`, `last`, interval transport, and padded lookup are recursive
  functions with the same equations as Haskell; and
- interval identity/composition theorems are proved independently of the
  Mathlib functor laws.

Then construct the current finite `Folio.core` functor and prove that its map on
an interval is the composite generated by the GADT. If useful in the opposite
direction, add a noncomputable conversion from a finite semantic folio to an
executable folio, clearly marking its use of choice.

### C. Formalize traced page elements

Mirror the implementation-level objects:

- a dependent/existential cell carrying its chain and value;
- `PageElement` with page, position, trace, and cell;
- existential `SomePageElement` for dynamic lookup;
- `pageElementPrecedes` and the trace-suffix relation;
- `PageElementArrow` as evidence of both predicates;
- identity and composition of arrows;
- `trimTrace`, page clamping, and element/arrow normalization; and
- reachability, preservation of arrows, and idempotence of normalization.

The Haskell phantom `scope` should correspond in Lean to ownership by a
particular folio/pagination value, preferably through dependent indices. Lean
does not need to simulate `runST`-style generativity; it needs a type-level
invariant strong enough to prove that elements from different paginations
cannot be mixed.

Prove a representation theorem:

> Valid traced page elements and arrows are equivalent to objects and arrows in
> the category of elements of the padded folio diagram.

This theorem is the bridge between executable predicates and the existing
categorical formulation.

### D. Define the executable Atlas data action

The new Lean Atlas should expose the same obligations as the Haskell smart
constructor:

- dependent data carrier at each page element;
- a `Dominion` for each carrier;
- a `DomanialInsertion` for each page-element arrow;
- identity action;
- composition action;
- normalization/coherence action is the identity insertion pointwise; and
- pagewise disjointness after transport to the common origin.

The existing semantic `Atl` stores only a functor and disjointness because its
finite presentation makes stability implicit. The executable Atlas must store
or derive the explicit coherence law because Haskell exposes the full padded
spine. Prove that the identity and composition witnesses construct a semantic
functor, and that executable disjointness implies `IsPagewiseDisjoint`.

### E. Model the correct category of Atlas morphisms

The finite semantic category and the Haskell runtime category must not be
silently identified:

- In the finite `Atl` category, identity is an ordinary functor identity.
- On the padded spine, Haskell's identity is normalization/coherence, which is
  idempotent but is not generally the raw identity.
- Haskell primitive maps are normalized at both boundaries, and composite
  evaluation inserts the middle coherence.

Formalize this as a category of split idempotents (or an equivalent explicit
`NormalizedAtlas`/Karoubi construction):

- an object carries its tall Atlas and normalization idempotent `e`;
- a morphism `f : X -> Y` satisfies `f = e_X ≫ f ≫ e_Y` in Lean's
  source-to-target `≫` convention (equivalently `e_Y . f . e_X` in Haskell's
  right-to-left `(.)` notation);
- object identity is `e`; and
- composition is coherence-sandwiched and associative.

Then mirror Haskell's two syntactic types:

- `AtlasMorphism`: primitive, identity, or composite materialized operations;
- `AtlasHom`: typed symbolic primitive, identity, or composite nodes with the
  same identity simplifications as `composeAtlasHoms`/`presheafCompose`.

Prove:

1. page-object mapping preserves both arrow predicates;
2. dependent data components satisfy the normalized naturality equation;
3. materialization respects symbolic composition;
4. symbolic identity materializes to the object's coherence;
5. `presheafCompose` has right identity and is associative by structural
   induction; and
6. the normalized full-spine category is equivalent to the finite stored Atlas
   category, or at minimum connected by full/faithful functors with an explicit
   essential-image theorem.

The existing `Folio.collapse_include`, `Folio.include_collapse_ne_id`,
`Atl.coherence_idempotent`, and `AtlHom.coherence_left/right` results are the
starting lemmas for this step.

## Phased implementation plan

### Phase 0: freeze the correspondence surface

- Record the Haskell constructors, reflected functions, and refinement theorems
  in a checked manifest, grouped by module.
- Give every cross-language theorem a stable identifier, for example
  `PE-NORMALIZE-IDEMPOTENT` or `ATLASHOM-ASSOC`.
- Add a short comment containing that identifier at both the Lean theorem and
  LiquidHaskell proof function.
- Track the explicit trust inventory in CI so new assumptions cannot
  be introduced unnoticed.

Exit criterion: every core Haskell representation and every trusted assumption
has an assigned Lean target.

### Phase 1: executable ordinal, dominion, chain, and consolidation

- Implement the representations and interpretation functions.
- Port the Haskell property names and recursive equations.
- Prove identity, composition, bounds, lookup/position round trips, and chain
  sum behavior.
- Add small cross-language golden vectors for ordinal encoding, comparison,
  addition, chain lookup, and chain sum. These test computation; the Lean proofs
  establish the general facts.

Exit criterion: no Atlas-level proof depends on an unmodeled primitive or on an
unexplained semantic/executable mismatch.

### Phase 2: folios, page elements, and pagination

- Implement the GADT-equivalent folio and padded page lookup.
- Implement traces and trace-derived arrows.
- Retain genuine-page identity in the phantom cell index: equal chain/value
  payloads on different genuine pages may have different covered sub-dominions.
  Padding normalization must preserve this identity.
- Prove page-element category laws and all normalization lemmas.
- Build the equivalence with the semantic category of elements.
- Model pagination ownership and morphisms as object maps with an arrow witness.

Exit criterion: Lean can state and prove the same contracts as
`Folio.Presentation`, `PageElements.Structure`, and
`Pagination.LiquidInternal` without appealing to the old `Pag` morphism type.

### Phase 3: Atlas objects and morphisms

- Implement `AtlasDataAction`, its four laws, and the executable Atlas smart
  constructor.
- Implement primitive normalized Atlas morphisms and data naturality.
- Formalize the normalized/Karoubi category.
- Implement symbolic `AtlasHom`, `presheafIdentity`, and `presheafCompose` with
  the Haskell equations.
- Prove interpretation into the existing finite `Atl` category.

Exit criterion: `presheafRightIdentity` and `presheafAssociativity` are theorems
over a faithful model of the actual Haskell syntax and evaluation, not merely
consequences of Mathlib's unrelated category instance.

### Phase 4: remove the structural LiquidHaskell assumptions

Port the Lean proofs for the two structural facts back to Haskell:

1. Make `presheafRightIdentity` a reflected/PLE proof by the exact constructor
   cases used in Lean.
2. Make `presheafAssociativity` recurse on the same `AtlasHom` argument as the
   definition of `presheafCompose`.
3. If LiquidHaskell cannot reason directly through the GADT equality witnesses,
   factor out a first-order spine for the symbolic composition shape and prove:
   - erasure commutes with `presheafCompose`;
   - the first-order spine has identity and associativity; and
   - reconstruction/materialization preserves the erased shape.

Do not replace these assumptions with a differently named assumed lemma or an
unchecked `unsafeCoerce` boundary.

Exit criterion: both structural laws are checked without trust directives and
`make verify-liquid` passes.

### Phase 5: align presheaves and Yoneda packaging

Define in Lean the same indexed-family interface used in Haskell:

- a family `values : Type -> Type` and its application to an Atlas;
- a rank-polymorphic contravariant action;
- stored identity and composition eliminators;
- natural-transformation components and naturality eliminators;
- `YonedaPresheaf`, `Yoneda`, `mapYoneda`, and `mapYonedaNatural`.

Prove the representable laws from the symbolic Atlas composition theorems. Keep
these separate:

- pointwise Yoneda identity/composition/naturality; and
- safe storage of those pointwise results in the rank-N packages.

The first group is mathematics; the second is an encoding theorem specific to
GHC and LiquidHaskell.

Exit criterion: Lean models both the mathematical law and the exact indexed,
rank-polymorphic packaging boundary checked by LiquidHaskell.

### Phase 6: checked Yoneda packaging

`DataTransformation.Core` stores actions and components in named wrappers and
checks their identity, composition, and naturality dictionaries. The value
family is a higher-kinded parameter, so specialization does not cross an open
type-family coercion. `mapYoneda`, `yonedaIdentity`, and `yonedaComposition`
quantify the represented Atlas before the varying Atlas arguments. This preserves
the checked pointwise contracts when those functions are stored in the rank-N
representable package.

`yonedaActionAgrees` exposes the package's exact action, and
`yonedaComponentAgrees` certifies postcomposition in the stored component. The natural-transformation
assembly invokes that equation at the source and target, then invokes the checked
`yonedaNaturality` theorem. The assembly module uses `--fast` to disable inference
at polymorphic type applications; the explicit constructor and helper contracts
remain checked. Negative checks reject arbitrary action and component packages
with dummy law callbacks, and reject substituted action/component equations.

Lean models the named wrappers, law-bearing packages, their constructors and
eliminators, and both Yoneda packages over the same indexed value families.

Exit criterion: no `assume` or `ignore` remains, the packages verify, and the
public callers and focused presheaf/navigation tests pass.

### Phase 7: migrate derived constructions in dependency order

Once core Atlas and presheaf parity is established, align the remaining Lean
and Haskell modules in this order:

1. Atlas extent, territory, and covered page elements.
2. Atlas transposals, ordered transposals, transversals, and stable transversals.
3. Dominion inclusion, charter, coalition, and cartography. Charter must restrict
   the complete transversal action; arbitrary intermediate Atlas morphisms need
   not preserve coverage. Its inverse candidates must retain source coverage.
4. Empty Atlas, merge, sequence, confederation, federation, and horizontal sum.
5. Data transversals, stable data transversals, navigation, expedition, and
   Data Transformation Maps.
6. Stable confederal data, Day convolution, monoidal structure, and Kleisli
   structure.

At each step, prove that the executable operation interprets to the existing
semantic operation before changing downstream definitions.

Exit criterion: the public Haskell `DatraCore` API has a named Lean model and
the major categorical results are recovered through the bridge.

## Proof-transfer workflow

For every assumption or difficult LiquidHaskell theorem:

1. **Normalize the statement.** Write a first-order equation or predicate over
   named executable functions. Avoid relying on an implicit Mathlib instance.
2. **Prove it in Lean over the executable datatype.** The induction variable
   and recursive calls should match the Haskell function's recursion.
3. **Record a proof recipe.** In a comment beside the Lean theorem, list the
   constructor cases, rewrite lemmas, and induction hypothesis used.
4. **Port the recipe.** Implement a total Haskell function returning `()` with
   the corresponding refinement, using `seq` only to expose recursive proof
   calls when required by PLE.
5. **Check the leaf theorem and the package theorem separately.** This prevents
   a rank-N packaging failure from being mistaken for a mathematical hole.
6. **Run both checkers.** A theorem is closed only when Lean builds and the
   LiquidHaskell-enabled Haskell library builds.
7. **Delete the assumption and ignore directives in the same change.** The CI
   gate should reject reintroduction.

Lean should not be used as an external oracle that emits `True` certificates;
that would leave the executable/refinement connection trusted. The Haskell
proof must still be checked against the Haskell definition.

## Validation and CI

The final workflow should provide one top-level target, for example
`make verify-formal`, that performs:

```sh
lake build
make -C datra-haskell verify-liquid
make -C datra-haskell check-alignment
```

For this alignment goal, runtime validation is limited to the core-library
suite. Do not run parsing, interpreting, or CLI tests, or the mixed
`datra-types-test` suite's evaluation tests. The general `make check` target
remains available for other development work. Report these exclusions in the
final validation results; do not repair `ModuleRequiresBlock` for this goal.

Add an assumption gate equivalent to:

```sh
if rg -n '(^|[[:space:]])assume[[:space:]]|\{-@[[:space:]]+ignore' \
  datra-haskell/src/DatraCore; then
  echo "Unexpected LiquidHaskell trust escape in DatraCore" >&2
  exit 1
fi
```

Maintain three kinds of tests:

- **Lean theorem tests:** compilation of every executable and bridge theorem.
- **LiquidHaskell verification:** refinements for the implementation itself.
- **Cross-language computation fixtures:** shared inputs and expected outputs
  for ordinal, chain, trace, normalization, and composition functions. These
  catch definition drift but do not replace proofs.

Rejection checks must locate every reported type error in the injected negative
case. An error in its supporting implementation or positive examples invalidates
the check instead of counting as a successful rejection.

Pin Lean/Mathlib, GHC, LiquidHaskell, and Z3 versions in CI. Yoneda packaging is
compiler/elaborator-sensitive, so version changes must rerun the assumption-free
verification rather than relying on cached results.

## Deliverables

1. A componentized executable Lean layer mirroring `DatraCore` foundations.
2. A preserved semantic layer containing the abstract category theory.
3. Interpretation/equivalence theorems connecting both layers.
4. A formal normalized/Karoubi Atlas category matching Haskell identity and
   composition.
5. Lean proofs of symbolic Atlas identity and associativity.
6. LiquidHaskell implementations of those proofs with no `assume`.
7. A refactored Yoneda packaging boundary with no `assume` or `ignore`.
8. An assumption gate and a combined formal-verification target.
9. A theorem correspondence manifest and cross-language fixtures.
10. A working `make preprint-full` with an explicitly selected Lean source
    appendix relevant to the preprint, excluding the wholesale `Executable`
    alignment layer.

## Definition of done

The alignment is complete when all of the following hold:

- Lean definitions cover the actual executable representations, including
  traces, normalization, generative ownership, and symbolic Atlas arrows.
- The executable Atlas category's identity and composition agree with Haskell's
  coherence-sandwiched behavior.
- The executable model is related by proved interpretation theorems to the
  existing finite semantic Atlas model.
- `presheafRightIdentity`, `presheafAssociativity`, `yoneda`, and
  `yonedaNatural` are checked rather than assumed.
- No `assume`, relevant `ignore`, `unsafeCoerce`, or equivalent trust escape is
  present in `DatraCore`.
- `lake build`, `make verify-liquid`, and `make check-alignment` pass in the pinned toolchain.
- Derived constructions use the aligned core or have explicit, documented
  bridge theorems showing why the old semantic definition is equivalent.
- `make preprint-full` succeeds with the split Lean modules, includes only
  preprint-relevant Lean code, and places code corresponding to the unchanged
  written definitions in each section. Its appendix does not include the entire
  `Executable` alignment layer. The complete Lean project still builds.

## Main risks and mitigations

- **Mistaking semantic category laws for implementation proofs.** Prove the
  laws over the reified Haskell syntax first, then interpret them.
- **Dependent casts overwhelming the Lean development.** Isolate sigma/GADT
  transport in constructors and extensionality lemmas; expose typed eliminators
  analogous to the Haskell rank-N callbacks.
- **Treating normalization as raw identity.** Use the explicit split-idempotent
  category and keep `include_collapse_ne_id` as a regression theorem.
- **LiquidHaskell rank-N/type-family limitations.** Separate pointwise proofs
  from storage, prefer named reflected accessors, and introduce specialized
  smart constructors before changing the public representation.
- **Claiming computability for every semantic chain.** The executable-to-semantic
  direction is canonical; any reverse construction using choice must be marked
  noncomputable and must not be used to justify runtime behavior.
- **A long-lived duplicate formalization.** Require every executable definition
  to gain its semantic bridge before downstream migration, and retire obsolete
  compatibility aliases after their callers move.

## Current implementation priorities

1. Retain the stored canonical source domain through the generic stable-insertion
   eliminator and its identity/composition cases. Primitive construction and
   the raw coalition mapper already check that domain.
2. Connect each mapped target's validity to the next insertion's source domain
   when composing stable insertions, preserving the exact forward/inverse laws.
3. Complete the Charter and Dominion-inclusion assembly contracts, preserving
   their existing Lean interpretation and inverse laws.
4. Finish the remaining core representation bridges and derived constructions
   in Phase 7's dependency order. Keep the manifest's partial and pending
   statuses until their complete obligations are checked.
5. Remove superseded code and perform the final validation and preprint audit
   required by the definition of done.

The module-loading failure (`ModuleRequiresBlock`) is outside this alignment
task; its repair belongs to the bootstrap work in `DATRA_HOOK_MODULE.md`.
Report its effect on final runtime validation without attempting that repair.

Use focused positive and rejection checks while completing each construction.
Rebuild the affected public interfaces before testing refinement-only changes:
GHC export hashes need not change with LiquidHaskell contracts, so cached
re-exports can retain stale specifications. Final LiquidHaskell verification
must use fresh `datra-haskell` library artifacts to check the complete dependency
graph against the final contracts.
The absence of trust directives is an invariant throughout this work, not a
substitute for the remaining representation and assembly proofs.
