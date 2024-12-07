/-
Copyright (c) 2022 Moritz Doll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Doll
-/

import Mathlib.Init
import Lean.Elab.Tactic.Rewrite

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
Notice that the second occurrence of `a` from the left has been rewritten by `nth_rewrite`.

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
syntax (name := nthRewriteSeq) "nth_rewrite" optConfig ppSpace num+ rwRuleSeq (location)? : tactic

@[inherit_doc nthRewriteSeq, tactic nthRewriteSeq] def evalNthRewriteSeq : Tactic := fun stx => do
  match stx with
  | `(tactic| nth_rewrite $cfg:optConfig $[$n]* $_rules:rwRuleSeq $[$loc]?) =>
    let cfg ← elabRewriteConfig cfg
    let loc := expandOptLocation (mkOptionalNode loc)
    let occ := Occurrences.pos (n.map TSyntax.getNat).toList
    let cfg := { cfg with occs := occ }
    withRWRulesSeq stx[0] stx[3] fun symm term => do
      withLocation loc
        (rewriteLocalDecl term symm · cfg)
        (rewriteTarget term symm cfg)
        (throwTacticEx `nth_rewrite · "did not find instance of the pattern in the current goal")
  | _ => throwUnsupportedSyntax

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
Notice that the second occurrence of `a` from the left has been rewritten by `nth_rewrite`.

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
macro (name := nthRwSeq) "nth_rw" c:optConfig ppSpace n:num+ s:rwRuleSeq l:(location)? : tactic =>
  -- Note: This is a direct copy of `nth_rw` from core.
  match s with
  | `(rwRuleSeq| [$rs,*]%$rbrak) =>
    -- We show the `rfl` state on `]`
    `(tactic| (nth_rewrite $c:optConfig $[$n]* [$rs,*] $(l)?; with_annotate_state $rbrak
      (try (with_reducible rfl))))
  | _ => Macro.throwUnsupported

end Mathlib.Tactic
