# Remaining Test Failures

This document records the 8 failures that remain after fixing imported
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

## 1. Standard-library syntax and string-template decoding

**Test:** `cross-feature regression programs / standard-library syntax and string-template decoding`

**Input:**

```datra
successor := %"successor $Nat next" %> ({value? : Int} -> Int) do
  assert value of Nat
  yield value + 1
assert successor 4 next = 5
assert successor of ({value? : Nat} -> Int)
assert %("from 2 to 5" ~> "from %Int to %Int")[1] of Int
assert %("from 2 to 5" ~> "from %Int to %Int")[2] of Int
```

**Expected output:**

```text
()
```

**Actual output:**

```text
SourceEvaluationFailure (UnknownIdentifier "value")
```

## 2. Right overload reverses the operands

**Test:** `overloading and assertions / overload operators / right overload reverses the operands`

**Input:**

```datra
yield 5 >> {a? : Nat := 3}
```

**Expected output:**

```text
a? : Nat := 5
```

**Actual output:**

```text
5
```

## 3. Reverse safe overload reverses the operands

**Test:** `overloading and assertions / overload operators / reverse safe overload reverses the operands`

**Input:**

```datra
yield "a" >>> {x? : Nat := 2; Str}
```

**Expected output:**

```text
{x? : Nat := 2; $a}
```

**Actual output:**

```text
$a
```

## 4. Fixed-point reverse specification

**Test:** `standard library and declarative syntax / inline fixed points / fixed point reverse specification`

**Input:**

```datra
yield Nat <~ (fun 5)
```

**Expected output:**

```text
5 ~> Nat
```

**Actual output:**

```text
Nat
```

## 5. Unnamed `NatLimit` functions accept finite and limit values

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

## 6. Finite and infinite values inhabit their limit types

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

## 7. A template may begin with a postfix operand hole

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

## 8. One function accepts an inhabited list of templates

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
