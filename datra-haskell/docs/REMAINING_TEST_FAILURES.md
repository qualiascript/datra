# Remaining Test Failures

This document records the 2 failures that remain after fixing imported
standard-library syntax precedence, import-all value resolution, and the CLI
canonical-AST golden file. The failures are listed in test-suite order.

The complete test run used:

```sh
cabal --project-file=cabal.project test all -f-liquid -j1 \
  --test-show-details=direct --test-option=--hide-successes
```

The four former `ModuleEvaluationFailure (UnknownIdentifier "if")` failures in
the `numbers` module are resolved. The two CLI golden-file failures were also
resolved separately and passed focused retesting. The following failures are
still outstanding.

## 1. A template may begin with a postfix operand hole

**Test:** `standard library and declarative syntax / declared patterns / a template may begin with a postfix operand hole`

**Input:**

```datra
increment := %"$Int++" %> ({value?:Int} -> Int) do yield value+1
yield 2++
```

**Expected output:**

```text
3
```

**Actual output:** A source parse failure at the end of `yield 2++`:

```text
unexpected end of input
expecting "!~", "...", '"', '$', '%', '(', '*', '{', '~', or integer
```

## 2. One function accepts an inhabited list of templates

**Test:** `standard library and declarative syntax / declared patterns / one function accepts an inhabited list of templates`

**Input:**

```datra
increment := %("$Int++"; "increment $Int") %> ({value?:Int} -> Int) do yield value+1
yield (2++; increment 2)
```

**Expected output:**

```text
(3; 3)
```

**Actual output:** A source parse failure at the opening parenthesis of the
yielded expression:

```text
unexpected '('
expecting "!?", "%>", "->", "<<", "<<<", "<=", "<~", "=/=", ">=", ">>",
">>>", "??", "~>", '!', '*', '+', ',', '-', '.', ';', '<', '=', '>', '?',
'@', '[', '^', '|', end of input, or end of line
```
