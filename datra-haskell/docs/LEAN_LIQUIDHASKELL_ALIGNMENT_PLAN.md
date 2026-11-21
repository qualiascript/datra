# Lean/LiquidHaskell alignment plan for `DatraCore`

## Purpose

This document proposes a staged rewrite of the Lean formalization so that it
models the **current executable representation** in `../src/DatraCore`,
then uses that model to remove the remaining LiquidHaskell assumptions.

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
prove their interpretations into this denotational layer. Derived construction
bridges still need work; the correspondence manifest records their coverage
separately. Presheaf and Yoneda packages have checked construction and elimination
laws in both languages, with no LiquidHaskell trust directives. The executable coalition-to-inclusion
arrow and inclusion action on insertions have interpretation theorems, including
identity and composition in the stable-transversal category. The one-page
interpretation lifts to a stable-transversal isomorphism. It transports the
written Dominion-inclusion hom equivalence, and both executable hom maps have
full interpretation and inverse laws. The forward naturality laws also preserve
the stored partial inverses. Haskell assembly certificates still need checking.
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

Primitive transversal actions store their exact-image coverage law in a checked
record. The image operation retains the dependent target cell and datum before
the public coverage constructor packages them. Atlas maps likewise store their
owning Atlas, canonical origin, and accepted-datum coverage law together. Their
extent eliminator exposes that owner to its callback. Coverage of an arbitrary
accepted datum follows by transporting it to the stored origin and applying the
checked origin-rank preservation theorem. The shared coverage-transport lemma
and the Atlas-map result contract are checked in both languages. These interfaces
keep coverage constructors private; the remaining ownership-sensitive derived
constructions still require migration to public interfaces.

Coverage validation checks the retained region's owning trace, datum membership,
final page, and both cache equalities. Matching the source's origin rank is only
accepted after that validation. Lean proves that the executable validator is
equivalent to a genuine territory representative, so checked covered-element
packaging derives that representative from its coverage evidence. The Haskell
payload keeps its dependent region and datum together; the abstract
`CoverageWitness` type exposes the three owner parameters directly in checked
contracts, and `AtlasCoverageWitness` is its object-indexed form. Public
elimination retains the final-region, membership, and cached-rank certificates;
rank observation keeps the constructor private. Coalition uses the shared
covered-element carrier, its finite decoder, and its public constructors and
eliminators. Its ranking uses the public witness-bounded search through the exposed coverage
interface.

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
`PageElements.TraceChain`, `AtlasMerge.Assembly`, `AtlasMerge.Data`, and
`AtlasSequence.Data`, `AtlasSequence.Member`, `AtlasSequence.Page`, and `AtlasSequence.Assembly`.
Their definitions and refinement contracts are checked in
the exposed modules, including the logical record selectors used by clients.
The alignment checker enforces the `LiquidInternal` boundary in the library,
tests, and application. The remaining cross-component `Internal` imports need
migration to exposed interfaces; the strict completion gate rejects them. The
merge modules use public component interfaces, including checked pagination and
Atlas constructors and a prefix-lookup wrapper that retains the success and
position contracts. Private implementation imports belong within their owning component.
The public `Pagination.paginationFromPageElements` constructor retains the
existing occurrence category and its scope. Generative pagination delegates to
the public page-elements allocator. Fixed folios use `PageElements.Construction`:
a pure class instance chooses the entire folio, and a nominal scope records the
recipe and both carrier types. Dominion inclusion and ranked Dominion paginations
use this interface; a runtime chain requires a separately owned construction.
Lean models the fixed recipe and proves that pagination wrapping preserves its
folio and valid elements. Rejection checks enforce scope and recipe separation.
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
- `Pagination` gives a folio a generative phantom scope. Its morphisms are
  object maps plus an arrow-preservation witness.
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
The preprint extractor follows the local imports and includes every module in
the full source appendix.

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

Atlas is the critical boundary because every remaining assumption concerns the
Atlas category or presheaves over it.

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

Exit criterion: the first two `assume` declarations are gone and
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

Exit criterion: Lean models both the mathematical law and the exact packaging
boundary at which LiquidHaskell currently fails.

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
cd datra-haskell && make verify-liquid
cd datra-haskell && make check
```

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
- `lake build`, `make verify-liquid`, and `make check` pass in the pinned toolchain.
- Derived constructions use the aligned core or have explicit, documented
  bridge theorems showing why the old semantic definition is equivalent.

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

## Recommended first vertical slice

The first implementation change should be deliberately narrow:

1. Add executable `AtlasHom` syntax in Lean with exactly the Haskell constructors.
2. Port `presheafIdentity` and `presheafCompose` verbatim at the equation level.
3. Prove right identity and associativity by structural induction.
4. Connect syntax evaluation to the existing `AtlHom` composition where possible,
   using the current coherence lemmas for the padded presentation.
5. Port the two proof recipes to LiquidHaskell and remove the first two
   assumptions.

This slice tests the proof-transfer method against real trust holes before the
larger representation migration. The full Atlas rewrite should follow once it
has confirmed which indexed/GADT proof patterns both Lean and LiquidHaskell can
support cleanly.
