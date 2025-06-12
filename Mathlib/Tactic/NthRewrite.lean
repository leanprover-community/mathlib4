/-
Copyright (c) 2022 Moritz Doll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Doll
-/

import Mathlib.Init

/-!
# `nth_rewrite` tactic

The tactic `nth_rewrite` and `nth_rw` are variants of `rewrite` and `rw` that only performs the
`n`th possible rewrite.

-/
namespace Mathlib.Tactic

open Lean Elab Tactic Meta Parser.Tactic

/-- `nth_rewrite` is a variant of `rewrite` that only changes the `n₁, ..., nₖ`ᵗʰ _occurrence_ of
the expression to be rewritten. `nth_rewrite n₁ ... nₖ [eq₁, eq₂,..., eqₘ]` will rewrite the
`n₁, ..., nₖ`ᵗʰ _occurrence_ of each of the `m` equalities `eqᵢ`in that order. Occurrences are
counted beginning with `1` in order of precedence.

For example,
```lean
example (h : a = 1) : a + a + a + a + a = 5 := by
  nth_rewrite 2 3 [h]
/-
a: ℕ
h: a = 1
⊢ a + 1 + 1 + a + a = 5
-/
```
Notice that the second and third occurrences of `a` from the left have been rewritten by
`nth_rewrite`.

To understand the importance of order of precedence, consider the example below
```lean
example (a b c : Nat) : (a + b) + c = (b + a) + c := by
  nth_rewrite 2 [Nat.add_comm] -- ⊢ (b + a) + c = (b + a) + c
```
Here, although the occurrence parameter is `2`, `(a + b)` is rewritten to `(b + a)`. This happens
because in order of precedence, the first occurrence of `_ + _` is the one that adds `a + b` to `c`.
The occurrence in `a + b` counts as the second occurrence.

If a term `t` is introduced by rewriting with `eqᵢ`, then this instance of `t` will be counted as an
_occurrence_ of `t` for all subsequent rewrites of `t` with `eqⱼ` for `j > i`. This behaviour is
illustrated by the example below
```lean
example (h : a = a + b) : a + a + a + a + a = 0 := by
  nth_rewrite 3 [h, h]
/-
a b: ℕ
h: a = a + b
⊢ a + a + (a + b + b) + a + a = 0
-/
```
Here, the first `nth_rewrite` with `h` introduces an additional occurrence of `a` in the goal.
That is, the goal state after the first rewrite looks like below
```lean
/-
a b: ℕ
h: a = a + b
⊢ a + a + (a + b) + a + a = 0
-/
```
This new instance of `a` also turns out to be the third _occurrence_ of `a`.  Therefore,
the next `nth_rewrite` with `h` rewrites this `a`.
-/
macro "nth_rewrite" c:optConfig ppSpace nums:(num)+ s:rwRuleSeq loc:(location)? : tactic => do
  `(tactic| rewrite $[$(getConfigItems c)]* (occs := .pos [$[$nums],*]) $s:rwRuleSeq $(loc)?)

/--
`nth_rw` is a variant of `rw` that only changes the `n₁, ..., nₖ`ᵗʰ _occurrence_ of the expression
to be rewritten. Like `rw`, and unlike `nth_rewrite`, it will try to close the goal by trying `rfl`
afterwards. `nth_rw n₁ ... nₖ [eq₁, eq₂,..., eqₘ]` will rewrite the `n₁, ..., nₖ`ᵗʰ _occurrence_ of
each of the `m` equalities `eqᵢ`in that order. Occurrences are counted beginning with `1` in
order of precedence. For example,
```lean
example (h : a = 1) : a + a + a + a + a = 5 := by
  nth_rw 2 3 [h]
/-
a: ℕ
h: a = 1
⊢ a + 1 + 1 + a + a = 5
-/
```
Notice that the second and third occurrences of `a` from the left have been rewritten by
`nth_rw`.

To understand the importance of order of precedence, consider the example below
```lean
example (a b c : Nat) : (a + b) + c = (b + a) + c := by
  nth_rewrite 2 [Nat.add_comm] -- ⊢ (b + a) + c = (b + a) + c
```
Here, although the occurrence parameter is `2`, `(a + b)` is rewritten to `(b + a)`. This happens
because in order of precedence, the first occurrence of `_ + _` is the one that adds `a + b` to `c`.
The occurrence in `a + b` counts as the second occurrence.

If a term `t` is introduced by rewriting with `eqᵢ`, then this instance of `t` will be counted as an
_occurrence_ of `t` for all subsequent rewrites of `t` with `eqⱼ` for `j > i`. This behaviour is
illustrated by the example below
```lean
example (h : a = a + b) : a + a + a + a + a = 0 := by
  nth_rw 3 [h, h]
/-
a b: ℕ
h: a = a + b
⊢ a + a + (a + b + b) + a + a = 0
-/
```
Here, the first `nth_rw` with `h` introduces an additional occurrence of `a` in the goal. That is,
the goal state after the first rewrite looks like below
```lean
/-
a b: ℕ
h: a = a + b
⊢ a + a + (a + b) + a + a = 0
-/
```
This new instance of `a` also turns out to be the third _occurrence_ of `a`.  Therefore,
the next `nth_rw` with `h` rewrites this `a`.

Further, `nth_rw` will close the remaining goal with `rfl` if possible.
-/
macro "nth_rw" c:optConfig ppSpace nums:(num)+ s:rwRuleSeq loc:(location)? : tactic => do
  `(tactic| rw $[$(getConfigItems c)]* (occs := .pos [$[$nums],*]) $s:rwRuleSeq $(loc)?)


end Mathlib.Tactic
