# Declarative Matcher Replacement

## Scope

This document defines the matcher correction needed for current dependent
declarations. It covers two declaration forms:

- ordinary bare-name application declarations; and
- exact `$` string-expression declarations.

Both forms must compile directly to their own matcher plan. They may share
typed capture selection after a match, but they must not share a lowered
neutral-AST template.

## The issue

The current matcher replaces interpolation captures with generated natural
expressions, renders the resulting pieces with inserted spaces, reparses that
text with the neutral parser, and then searches the parsed AST for the
generated expressions. It tries successive natural values until every marker
occurs exactly once.

That is not a stable representation of a capture. A decimal spelling is now
an ordinary identifier at the parser boundary; its natural value is assigned
later by dependent declaration rewriting. Consequently, a generated marker
such as `0` reparses as an identifier reference rather than as the
`EllipsisNatural 0` node sought by the matcher. No generated marker can pass
the occurrence check, and the unbounded marker search does not terminate.

The nontermination exposes a more general invariant violation: a capture is
being identified by the incidental AST produced by rendering and reparsing a
value chosen from the user language. Any user-representable marker can
collide, change meaning as parsing evolves, or be normalized away.

The same lowering is also semantically wrong for exact string templates.
Splitting literals with `words`, joining pieces with `unwords`, and matching
the reparsed AST loses exact whitespace and character boundaries. Exact `$`
templates must constrain the candidate presentation, not the AST shape of a
normalized approximation.

This failure occurs while matcher candidates are being enumerated. The
rewrite stack is waiting for enumeration to finish; changing its traversal
algorithm would not correct the problem.

## Required matcher plans

`SyntaxRule` must retain which matcher was compiled from the declaration
head. The representation should have the following conceptual shape:

```haskell
data DeclarativeMatcherPlan
  = NativeApplicationPlan NativeApplicationPattern
  | ExactStringPlan ExactStringPattern
```

The concrete names may follow local conventions. The important invariant is
that dispatch is explicit and structural. Matcher kind must not be recovered
by inspecting a rendered expression or an untyped list of template pieces.

### Native application plan

A bare declaration name compiles to a native application pattern containing:

- the literal `SimpleIdentifierString` head;
- the capture descriptor for its application operand;
- the declaration branch and implementation metadata already carried by a
  syntax rule.

Matching operates directly on `applicationSpine`:

1. compare the candidate head with the stored literal identifier;
2. enumerate admissible nonempty operand extents in longest-first order;
3. construct the captured operand with `applicationFrom`; and
4. return any unconsumed application arguments separately.

No source rendering, neutral parsing, marker generation, or recursive AST
shape comparison is involved. The existing application-spine helpers may be
reused, but they should live with the native matcher rather than with a
generic string-template projection module.

### Exact string plan

An explicit `$` string expression compiles to an ordered exact pattern:

```haskell
data ExactStringPart capture
  = ExactLiteral String
  | ExactCapture capture
```

Literal payloads are the decoded characters produced by the ordinary string
parser. They are retained without tokenization or whitespace normalization.
Adjacent literals may be coalesced only by lossless concatenation.

Matching uses the candidate presentation supplied by its string conversion
capability:

1. match every literal part character-for-character;
2. enumerate capture boundaries only where the surrounding exact literals
   permit them;
3. decode each captured substring with that capture's inverse string
   capability;
4. select the decoded value through its declared type; and
5. require the pattern to consume the complete candidate presentation.

Only capture parts are returned to the declaration function. Literal parts
constrain the match and never become arguments.

The matcher must not parse the complete interpolated presentation as one
neutral Datra expression. A capture-specific inverse may use the application
parser when that capture's string codec requires it; that is a property of
the capture type, not a reconstruction of the whole template as an AST.

## Shared capture result

The two matcher plans should converge on one result shape after their own
matching rules have succeeded:

```haskell
data DeclarativeMatch capture = DeclarativeMatch
  { matchedWhole :: Expression
  , matchedCaptures :: [capture]
  , unmatchedApplicationTail :: [Expression]
  }
```

Each capture must carry the typed selection evidence required by later
rewriting, not merely a substring or an unvalidated AST node. Capture order is
the declaration's left-to-right interpolation order.

The syntax-rewrite scheduler consumes this explicit list. An atomic capture
with no structural children must be checked immediately against its capture
descriptor; it must not acquire synthetic children from a marker expression.
This preserves the current stack algorithm while removing the false child
work created by template lowering.

## Admissibility, refinement, and overlap

These operations must be defined over matcher plans rather than tested by
rendering a finite collection of generated witnesses.

For a native application plan:

- admissibility validates the stored head and capture descriptor;
- refinement compares the capture families with the ordinary subfederation
  mechanism; and
- overlap requires the same literal head and overlapping capture families.

For an exact string plan:

- admissibility requires every capture to provide stable inverse selection
  and rejects ambiguous capture boundaries;
- refinement compares exact literal constraints and the capture families at
  compatible boundaries; and
- overlap solves the intersection of the two ordered exact patterns, using
  ordinary capture-family overlap at aligned capture positions.

The result must be independent of chosen example values. Generated natural
witnesses are neither a proof of admissibility nor a sound overlap decision.

## Invariants

1. Matcher compilation is total and terminating for every accepted
   declaration head.
2. A capture has a structural slot identity; it is never represented by a
   user-language sentinel expression.
3. Bare application matching operates on application spines directly.
4. Exact `$` literals preserve every decoded character, including repeated
   spaces, tabs, and newlines.
5. Exact matching consumes the complete candidate presentation.
6. Literal parts are constraints only; only interpolation parts are captured.
7. Capture values are returned with typed selection evidence in source order.
8. Whole-template rendering and reparsing is not part of compilation,
   matching, admissibility, refinement, or overlap.
9. Candidate enumeration does not depend on semantic rewriting of generated
   syntax.
10. The rewrite stack receives the real capture list and requires no
    matcher-specific traversal behavior.

## Removal boundary

Once both plans are connected, remove the superseded machinery rather than
retaining it as a fallback:

- `lowerTemplate`, `LoweredTemplate`, marker occurrence counting, and the
  marker-based AST matcher;
- unbounded marker selection;
- `templateWitnesses` and witness rendering used as matcher proofs;
- `words`-based literal splitting and `unwords`-based reconstruction; and
- parser callbacks whose only remaining purpose is generating neutral marker
  witnesses.

Helpers with independent meaning, such as application-spine decomposition,
should move to the matcher that owns them instead of being deleted.

## `_StrExpr` sequencing decision

The replacement requires a capture descriptor that exposes string
presentation, inverse decoding, and typed selection. The planned generic
`_StrExpr` abstraction is a natural provider of that interface, but this
document does not decide whether `_StrExpr` migration happens before the
matcher replacement or whether the replacement is first implemented behind
the current capture interface.

Either order is acceptable only if the matcher depends on the capability
boundary above. It must not add a new closed allowlist of capture kinds or
make the replacement depend on the obsolete marker path.

## Verification

- Standard-library bootstrapping terminates when natural-looking identifiers
  such as `0` are ordinary declaration names at parse time.
- A native bare-name rule captures its application operand directly and
  preserves unconsumed arguments.
- Exact `$` templates distinguish `2+2`, `2 + 2`, repeated spaces, tabs, and
  newlines according to their written literal chunks.
- Zero-, one-, and multiple-capture exact templates return only their
  interpolation captures and preserve source order.
- Adjacent or otherwise ambiguous captures are rejected by admissibility
  rather than resolved using example markers.
- Refinement and overlap results do not change when natural identifier
  declarations are added or removed from scope.
- Candidate enumeration and rewrite-stack tests contain no synthetic marker
  children.
