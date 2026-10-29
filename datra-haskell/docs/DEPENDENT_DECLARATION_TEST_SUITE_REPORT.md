# Dependent declaration test suite report — 2026-10-29

## Current declaration model

`Scope` has one declaration environment: its dependent-declaration layers.
There is no parallel lexical-binding table or fallback name resolver. Exact
lookup, discovery, overlap checks, definition protection, closure dependency
collection, module projection, and contextual lookup all use the same indexed
dependent-declaration abstractions.

Runtime singletons are the native fast representation of simple dependent
declarations whose value already exists. Their stored value and provenance are
payload metadata; they are still indexed, discovered, shadowed, and protected
as declarations. This retains constant-time exact-name candidates without
introducing a second declaration system or a linear fallback scan.

## Contextual declarations

`ContextualRole` is a semantic type outside the AST. It is the only place that
owns the four surface spellings:

| Role | Private declaration | Surface declaration |
| --- | --- | --- |
| `ContextualThis` | `_this` | `this` |
| `ContextualIt` | `_it` | `it` |

All four names are definitions (`def`) and follow the same shadowing rules.
They are installed only in semantic scopes where their contextual values
exist. Generic runtime-declaration extension does not add contextual aliases.

The private declarations `_this` and `_it` use runtime-singleton declaration
payloads because their values are supplied by the interpreter. Beside each
private declaration, the interpreter installs an ordinary simple dependent
declaration:

```datra
def this := _this 0
def it := _it 0
```

Here `_this 0` and `_it 0` are ordinary function applications. `this` and `it`
are not syntax rules, parser substitutions, or special AST nodes. The syntax
rewriter leaves their identifier references alone, and evaluation resolves
them through normal dependent-declaration lookup.

Tests that attempted to redefine `_this` or `_it` inside scopes where those
private contextual definitions already exist were removed. They asserted an
invalid form of shadowing. The top-level resource test that defines `_this`
remains: that resource does not introduce a contextual `this`, so no `_this`
definition exists there to conflict with it.

## Closure and recursion handling

Closure traversal now carries explicit typed state instead of synthesizing
names such as `__closure` or underscore-prefixed generated roots. The removed
generated-binder mechanism is no longer part of dependency discovery.

Productive-recursion recognition resolves ordinary declarations before
checking for a contextual self-reference. This is required because recursive
Std definitions now encounter `this` as the declaration
`def this := _this 0`, rather than as an AST rewrite to `_this 0`.

Std's recursive list definition is retained in its source form:

```datra
let val List := &T? do yield fun () | (T; this)
```

The interpreter follows the `this` declaration to recognize the private
contextual application. It does not rewrite the source AST to expose that
application. This removed the unbounded fixed-point expansion that previously
exhausted memory while materializing Std.

## Current verification

The current tree builds with:

```sh
cabal build test:datra-interpreting-test test:datra-parsing-test -f-liquid
```

The focused generic-source parsing test passes, including the expectation that
nested contextual source remains an ordinary `this` identifier reference in
the parsed AST. `git diff --check` also passes.

The formerly memory-exhausting focused contextual test now terminates under a
hard timeout and memory limit. It reaches a bounded, pre-existing Std failure
after approximately 16 seconds instead of expanding until it hangs or runs out
of memory:

```text
SourceParseFailure
  (ParseFailure
    { parseFailureMessage =
        "FunctionEvaluationFailed NoApplicableFunctionAlternative"
    })
```

A temporary diagnostic trace, removed after the observation, placed the error
during Std syntax validation around these declarations:

```datra
let val NatLimit := from 0 to Infinity
let val IntLimit := >< (NatLimit; $Complement?)
```

The same failure occurs for a focused test whose body does not reference
`this`, so it is not evidence of a remaining contextual-alias or closure
failure. This pass did not investigate the Std error beyond locating it well
enough to report the blocker.

## Remaining work

- Diagnose the bounded Std `NoApplicableFunctionAlternative` separately from
  the contextual-declaration refactor.
- Once Std loads again, run the dependent-declaration, scope, closure,
  interpreter, types, parsing, core, and CLI suites to obtain meaningful
  post-refactor results.
- Profile the full successful path before making further performance changes.
  The current focused failure takes about the same time as the pre-refactor
  failure, so no new timing regression has been established.

No complete-suite pass count is reported here because Std currently fails
before the selected interpreter test bodies execute.
