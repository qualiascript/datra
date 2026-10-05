# Remaining Test Failures

This document records the 4 failures that remain after fixing imported
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

## 1. Unnamed `NatLimit` functions accept finite and limit values

**Test:** `standard library and declarative syntax / integer limits and infinity / types / unnamed NatLimit functions accept finite and limit values`

**Input:**

```datra
identity := (NatLimit -> NatLimit do yield 'it)
yield (identity 3; identity Infinity)
```

**Expected output:**

```text
(3; Infinity)
```

**Actual output:**

```text
SourceEvaluationFailure (FunctionEvaluationFailed NoApplicableFunctionAlternative)
```

## 2. Finite and infinite values inhabit their limit types

**Test:** `standard library and declarative syntax / integer limits and infinity / types / finite and infinite values inhabit their limit types`

**Input:**

```datra
yield (0 of Nat; 23 of Nat; not (-1 of Nat);
  0 of NatLimit; Infinity of NatLimit;
  not (-Infinity of NatLimit);
  -23 of Int; 23 of Int; not (Infinity of Int);
  Infinity of IntLimit; -Infinity of IntLimit)
```

**Expected output:**

```text
(true; true; true; true; true; true; true; true; true; true; true)
```

**Actual output:**

```text
(true; true; true; false; true; true; true; true; true; true; true)
```

Only the fourth result differs: `0 of NatLimit` evaluates to `false`.

## 3. A template may begin with a postfix operand hole

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

## 4. One function accepts an inhabited list of templates

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
