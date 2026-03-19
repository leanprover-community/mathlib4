# Project Euler 1 in Lean 4

Project Euler Problem 1 asks for the sum of all natural numbers below `1000` that are divisible by `3` or `5`.

## The Lean file

The code for this post lives in [`ProjectEuler/Problem01.lean`](../ProjectEuler/Problem01.lean).

```lean
import Mathlib

namespace ProjectEuler

def problem1Numbers (n : Nat) : List Nat :=
  (List.range n).filter fun k =>
    decide (k % 3 = 0) || decide (k % 5 = 0)

def problem1Answer : Nat :=
  (problem1Numbers 1000).sum

example : problem1Numbers 10 = [0, 3, 5, 6, 9] := by native_decide

example : problem1Answer = 233168 := by native_decide

end ProjectEuler
```

## How to read it

`def` introduces a new definition.

`problem1Numbers` takes an input `n : Nat`.
That means `n` is a natural number.

`List.range n` builds the list `[0, 1, 2, ..., n - 1]`.
So `List.range 10` is the list of numbers below `10`.

`filter` keeps only the elements that satisfy a condition.
Here the condition is:

```lean
fun k => decide (k % 3 = 0) || decide (k % 5 = 0)
```

`fun k => ...` is an anonymous function.
You can read it as "take a number `k` and test something about it".

`k % 3 = 0` means "the remainder when dividing by `3` is `0`".
That is Lean's way of saying "`k` is divisible by `3`".

`decide` turns a proposition into a Boolean value.
This matters because `List.filter` wants a test that returns `true` or `false`.

`||` means logical "or".
So the filter keeps numbers divisible by `3` or divisible by `5`.

Finally, `.sum` adds the list entries together.

## Why the examples matter

This line:

```lean
example : problem1Numbers 10 = [0, 3, 5, 6, 9] := by native_decide
```

acts like a tiny executable test.
It checks that our helper definition behaves the way we expect on a small input.

The last line:

```lean
example : problem1Answer = 233168 := by native_decide
```

checks the final Euler answer.

`native_decide` asks Lean to compute the result and confirm that the equality is true.
This is a nice pattern for beginner projects:

- define the function clearly
- test it on a small example
- verify the final answer

## What this problem teaches in Lean 4

- how to define functions with `def`
- how to work with `Nat`
- how to build lists with `List.range`
- how to filter lists with an anonymous function
- how to convert propositions to booleans with `decide`
- how to use `example` plus `native_decide` as lightweight tests
