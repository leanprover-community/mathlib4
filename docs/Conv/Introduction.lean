/-
Copyright (c) 2018 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Kyle Miller
-/

/-! # Introduction to the conversion mode tactic

Inside a tactic block, one can use the `conv` tactic to enter conversion
mode. This mode allows one to travel into subexpressions inside assumptions
and goals, even inside lambda functions and foralls, to apply targeted rewrites,
simplifications, and other tactics.

This is similar to the conversion tacticals (tactic combinators) found in
other theorem provers like HOL4, HOL Light or Isabelle.

## Basic navigation and rewriting

As a first example, let us prove
`example (a b c : ℕ) : a * (b * c) = a * (c * b)` (examples in this file
are somewhat artificial since the `ring` tactic from
`Mathlib.Tactic.Ring` could finish them immediately). The naive first attempt is
to enter tactic mode and try `rw [mul_comm]`. But this transforms the goal
into `b * c * a = a * (c * b)`, after commuting the very first
multiplication appearing in the term. There are several ways to fix this
issue, and one way is to use a more precise tool: the
conversion mode.  The following code block shows the current target after
each line. Note that the target is prefixed by `|` where normal tactic mode
shows a goal prefixed by `⊢`. Both cases are still called "goals" though.

```lean
example (a b c : ℕ) : a * (b * c) = a * (c * b) := by
  conv =>          -- `| a * (b * c) = a * (c * b)`
    lhs            -- `| a * (b * c)`
    congr          -- 2 goals : `| a` and `| b * c`
    rfl            -- skip `| a` goal
    rw [mul_comm]  -- `| c * b`
```

The above snippet show three navigation commands:
* `lhs` navigates to the left-hand side of a relation (here
  equality), there is also a `rhs` navigating to the right-hand side.
* `congr` creates as many targets as there are arguments to the current
  head function (here the head function is multiplication)
* `rfl` goes to the next target

Once we arrive to the relevant target, we can use `rw` as in normal tactic mode.
At the end, `conv` will automatically use `rfl` to skip the last remaining target.

The second main reason to use conversion mode is to rewrite subexpressions
involving bound variables ("rewrite under binders").
Suppose we want to prove `example : (fun x : ℕ => 0 + x) = (fun x => x)`.
The naive first attempt is to enter tactic mode and try `rw [zero_add]`.
However, this fails with a frustrating
```text
tactic 'rewrite' failed, did not find instance of the pattern in the target expression
  0 + ?a
⊢ (fun x ↦ 0 + x) = fun x ↦ x
```

The solution is:
```lean
example : (fun x : ℕ => 0 + x) = (fun x => x) := by
  conv =>          -- | (fun x ↦ 0 + x) = fun x ↦ x
    lhs            -- | fun x ↦ 0 + x
    ext x          -- | 0 + x
    rw [zero_add]  -- | x
```
where `ext` is the navigation command entering inside the `fun` binder (the `x` argument
is optional). Note that this example is somewhat artificial, one could also do:
```lean
example : (fun x : ℕ => 0 + x) = (fun x => x) := by
  ext
  rw [zero_add]
```

All of this is also available for converting a hypothesis `H` in the local context by
using the syntax `conv at H => ...`.

Here are a more ways to navigate expressions:
* `arg i` navigates to the `i`th explicit argument. It is like doing `congr` and the
  appropriate number of `rfl`s for all but the `i`th argument.
* `arg @i` navigates to the `i`th argument, counting both explicit and implicit arguments.
* `enter [...]`, where the `...` consists of a list of arguments appropriate for `arg` or `ext`,
  and then runs the corresponding `arg` and `ext` commands.
  For example, `enter [1,@2,x,3]` is the same as `arg 1; arg @2; ext x; arg 3`.

## Pattern matching

Navigation using the above commands can be tedious. One can shortcut it
using pattern matching as follows:

```lean
example (a b c : ℕ) : a * (b * c) = a * (c * b) := by
  conv in b * c =>  -- | b * c
    rw [mul_comm]   -- | c * b
```

This `in` clause is short for
```lean
example (a b c : ℕ) : a * (b * c) = a * (c * b) := by
  conv =>           -- | a * (b * c) = a * (c * b)
    pattern b * c   -- | b * c
    rw [mul_comm]   -- | c * b
```

As usual for `=>` block tactics, the body can be placed on a single line with tactics
separated by semicolons. This yields a one-liner:
```lean
example (a b c : ℕ) : a * (b * c) = a * (c * b) := by
  conv in b * c => rw [mul_comm]
```

Of course placeholders are allowed:
```lean
example (a b c : ℕ) : a * (b * c) = a * (c * b) := by
  conv in _ * c => rw [mul_comm]
```

In all those cases, only the first match is affected.
One can also specify which occurrences to convert using an `occs` clause, which
creates goals for every matched occurrence. These can then all be handled at once
using the `all_goals` combinator.
The following performs rewriting only for the second and third occurrences of `b * c`:
```lean
example (b c : ℕ) :
    (b * c) * (b * c) * (b * c) = (b * c) * (c * b) * (c * b) := by
  conv in (occs := 2 3) b * c =>
    all_goals rw [mul_comm]
```
This can also be done using `pattern` and the `<;>` combinator, where, like
in normal tactic mode, `t1 <;> t2` means to run `t1` and then run `t2` for every goal
produced by it.
```
example (b c : ℕ) :
    (b * c) * (b * c) * (b * c) = (b * c) * (c * b) * (c * b) := by
  conv => pattern (occs := 2 3) b * c <;> rw [mul_comm]
```

## Sub-conversions

The `conv` tactic supports nested `conv` mode. This allows one to do a targeted rewrite
using the power of `conv` mode and then return to the original position with the rewritten
expression.
```lean
example (a b : ℕ) :
    a * b * (a * b) = b * a * (a * b) := by
  conv =>
    -- | a * b * (a * b) = b * a * (a * b)
    conv => pattern (occs := 2) a * b; rw [mul_comm]
    -- | a * b * (b * a) = b * a * (a * b)
    rw [mul_comm]
    -- | b * a * (a * b) = b * a * (a * b)
```

## Other tactics inside conversion mode

Besides rewriting using `rw`, one can use `simp`, `dsimp`, `change`, `equals`, `ring`, `norm_num`,
`push_neg`, `unfold`, among others.

See the [`conv` guide](https://leanprover-community.github.io/mathlib4_docs/docs/Conv/Guide.html)
for a more in-depth overview.

-/
