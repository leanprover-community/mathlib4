/-
Copyright (c) 2022 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard
-/
module

public import Batteries.Tactic.Init
public import Mathlib.Tactic.Push

/-!
# The `by_contra` tactic

The `by_contra!` tactic is a variant of the `by_contra` tactic, for proofs of contradiction.
-/

public meta section

namespace Mathlib.Tactic.ByContra
open Lean Parser.Tactic

/--
If the target of the main goal is a proposition `p`,
`by_contra!` reduces the goal to proving `False` using the additional hypothesis `this : ¬ p`.
`by_contra! h` can be used to name the hypothesis `h : ¬ p`.
The hypothesis `¬ p` will be normalized using `push_neg`.
For instance, `¬ a < b` will be changed to `b ≤ a`.
`by_contra!` can be used with `rcases` patterns.
For instance, `by_contra! rfl` on `⊢ s.Nonempty` will substitute the equality `s = ∅`,
and `by_contra! ⟨hp, hq⟩` on `⊢ ¬ p ∨ ¬ q` will introduce `hp : p` and `hq : q`.
`by_contra! h : q` will normalize negations in `¬ p`, normalize negations in `q`,
and then check that the two normalized forms are equal.
The resulting hypothesis is the pre-normalized form, `q`.
If the name `h` is not explicitly provided, then `this` will be used as name.
This tactic uses classical reasoning.
It is a variant on the tactic `by_contra`.
Examples:
```lean
example : 1 < 2 := by
  by_contra! h
  -- h : 2 ≤ 1 ⊢ False

example : 1 < 2 := by
  by_contra! h : ¬ 1 < 2
  -- h : ¬ 1 < 2 ⊢ False
```
-/
syntax (name := byContra!)
  "by_contra!" optConfig (ppSpace colGt rcasesPatMed)? (" : " term)? : tactic

local elab "try_push_neg_at" cfg:optConfig h:ident : tactic => do
  Push.push (← Push.elabPushConfig cfg) none (.const ``Not) (.targets #[h] false)
    (failIfUnchanged := false)

local elab "try_push_neg" cfg:optConfig : tactic => do
  Push.push (← Push.elabPushConfig cfg) none (.const ``Not) (.targets #[] true)
    (failIfUnchanged := false)

macro_rules
| `(tactic| by_contra! $cfg $[$pat?]? $[: $ty?]?) => do
  let pat ← pat?.getDM `(rcasesPatMed| $(mkIdent `this):ident)
  let replaceTac ← match ty? with
    | some ty => `(tactic|
      replace h : $ty := by try_push_neg $cfg; exact h) -- Let `h` have type `ty`.
    | none => `(tactic| skip)
  -- We have to use `revert h; rintro $pat` instead of `obtain $pat := h`,
  -- because if `$pat` is a variable, `obtain $pat := h` doesn't do anything.
  `(tactic| (
    by_contra h;
    try_push_neg_at $cfg h; $replaceTac;
    revert h; rintro ($pat:rcasesPatMed)))

end Mathlib.Tactic.ByContra
