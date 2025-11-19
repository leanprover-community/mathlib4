/-
Copyright (c) 2022 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard
-/
import Batteries.Tactic.Init
import Mathlib.Tactic.Push

/-!
# The `by_contra` tactic

The `by_contra!` tactic is a variant of the `by_contra` tactic, for proofs of contradiction.
-/

namespace Mathlib.Tactic.ByContra
open Lean Lean.Parser Parser.Tactic Elab Command Elab.Tactic Meta

/--
If the target of the main goal is a proposition `p`,
`by_contra!` reduces the goal to proving `False` using the additional hypothesis `this : ¬ p`.
`by_contra! h` can be used to name the hypothesis `h : ¬ p`.
The hypothesis `¬ p` will be negation normalized using `push_neg`.
For instance, `¬ a < b` will be changed to `b ≤ a`.
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
syntax (name := byContra!) "by_contra!" optConfig (ppSpace colGt binderIdent)? Term.optType : tactic

local elab "try_push_neg_at" cfg:optConfig h:ident : tactic => do
  Push.push (.const ``Not) none (.targets #[h] false) (← Push.elabPushConfig cfg)
    (failIfUnchanged := false)

local elab "try_push_neg" cfg:optConfig : tactic => do
  Push.push (.const ``Not) none (.targets #[] true) (← Push.elabPushConfig cfg)
    (failIfUnchanged := false)

macro_rules
  | `(tactic| by_contra! $cfg $[: $ty]?) =>
    `(tactic| by_contra! $cfg $(mkIdent `this):ident $[: $ty]?)
  | `(tactic| by_contra! $cfg _%$under $[: $ty]?) =>
    `(tactic| by_contra! $cfg $(mkIdentFrom under `this):ident $[: $ty]?)
  | `(tactic| by_contra! $cfg $e:ident) =>
    `(tactic| (by_contra $e:ident; try_push_neg_at $cfg $e:ident))
  | `(tactic| by_contra! $cfg $e:ident : $y) => `(tactic|
       (by_contra! $cfg h
        -- if the below `exact` call fails then this tactic should fail with the message
        -- tactic failed: <goal type> and <type of h> are not definitionally equal
        have $e:ident : $y := by { try_push_neg $cfg; exact h }
        clear h))

end Mathlib.Tactic.ByContra
