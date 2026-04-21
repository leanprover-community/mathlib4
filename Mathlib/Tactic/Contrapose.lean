/-
Copyright (c) 2022 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
-/
module

public import Mathlib.Tactic.Push

/-! # Contrapose

The `contrapose` tactic transforms the goal into its contrapositive when that goal is an
implication or an iff. It also avoids creating a double negation if there already is a negation.

* `contrapose` turns a goal `P → Q` into `¬ Q → ¬ P` and a goal `P ↔ Q` into `¬ P ↔ ¬ Q`
* `contrapose!` runs `contrapose` and then pushes negations inside `P` and `Q` using `push Not`
* `contrapose h` first reverts the local assumption `h`, and then uses `contrapose` and `intro h`
* `contrapose! h` first reverts the local assumption `h`, and then uses `contrapose!` and `intro h`
* `contrapose h with new_h` uses the name `new_h` for the introduced hypothesis

-/
set_option backward.defeqAttrib.useBackward true

public meta section

namespace Mathlib.Tactic.Contrapose
open Lean.Parser.Tactic

/-- An option to turn off the feature that `contrapose` negates both sides of `↔` goals.
This may be useful for teaching. -/
register_option contrapose.negate_iff : Bool := {
  defValue := true
  descr := "contrapose a goal `a ↔ b` into the goal `¬ a ↔ ¬ b`"
}

-- `contrapose₃`, `contrapose₄` and `contrapose_iff₄` don't depend on any axioms.
lemma contrapose₁ {p q : Prop} : (¬ q → ¬ p) → (p → q) := fun h hp ↦ by_contra fun h' ↦ h h' hp
lemma contrapose₂ {p q : Prop} : (¬ q → p) → (¬ p → q) := fun h hp ↦ by_contra fun h' ↦ hp (h h')
lemma contrapose₃ {p q : Prop} : (q → ¬ p) → (p → ¬ q) := Imp.swap.mp
lemma contrapose₄ {p q : Prop} : (q → p) → (¬ p → ¬ q) := mt

lemma contrapose_iff₁ {p q : Prop} : (¬ p ↔ ¬ q) → (p ↔ q) := not_iff_not.mp
lemma contrapose_iff₂ {p q : Prop} : (p ↔ ¬ q) → (¬ p ↔ q) := (iff_not_comm.trans Iff.comm).mp
lemma contrapose_iff₃ {p q : Prop} : (¬ p ↔ q) → (p ↔ ¬ q) := (not_iff_comm.trans Iff.comm).mp
lemma contrapose_iff₄ {p q : Prop} : (p ↔ q) → (¬ p ↔ ¬ q) := fun ⟨h₁, h₂⟩ ↦ ⟨mt h₂, mt h₁⟩

/--
`contrapose` transforms the main goal into its contrapositive. If the goal has the form `⊢ P → Q`,
then `contrapose` turns it into `⊢ ¬ Q → ¬ P`. If the goal has the form `⊢ P ↔ Q`, then `contrapose`
turns it into `⊢ ¬ P ↔ ¬ Q`.

* `contrapose h` on a goal of the form `h : P ⊢ Q` turns the goal into `h : ¬ Q ⊢ ¬ P`. This is
  equivalent to `revert h; contrapose; intro h`.
* `contrapose h with new_h` uses the name `new_h` for the introduced hypothesis. This is equivalent
  to `revert h; contrapose; intro new_h`.
* `contrapose!`, `contrapose! h` and `contrapose! h with new_h` push negation deeper into the goal
  after contraposing (but before introducing the new hypothesis). See the `push Not` tactic for more
  details on the pushing algorithm.
* `contrapose! (config := cfg)` controls the options for negation pushing. All options for
  `Mathlib.Tactic.Push.Config` are supported:
  * `contrapose! +distrib` rewrites `¬ (p ∧ q)` into `¬ p ∨ ¬ q` instead of `p → ¬ q`.

Examples:
```lean4
variables (P Q R : Prop)

example (H : ¬ Q → ¬ P) : P → Q := by
  contrapose
  exact H

example (H : ¬ P ↔ ¬ Q) : P ↔ Q := by
  contrapose
  exact H

example (H : ¬ Q → ¬ P) (h : P) : Q := by
  contrapose h
  exact H h

example (H : ¬ R → P → ¬ Q) : (P ∧ Q) → R := by
  contrapose!
  exact H

example (H : ¬ R → ¬ P ∨ ¬ Q) : (P ∧ Q) → R := by
  contrapose! +distrib
  exact H
```
-/
syntax (name := contrapose) "contrapose" (ppSpace colGt ident (" with " ident)?)? : tactic
macro_rules
  | `(tactic| contrapose $e) => `(tactic| (revert $e:ident; contrapose; intro $e:ident))
  | `(tactic| contrapose $e with $e') => `(tactic| (revert $e:ident; contrapose; intro $e':ident))

open Lean Meta Elab.Tactic

elab_rules : tactic
| `(tactic| contrapose) => liftMetaTactic fun g => withReducible do
  let target ← g.getType'
  match target with
  | mkApp2 (.const ``Iff _) p q =>
    if ← contrapose.negate_iff.getM then
      -- we use reducible `whnf`, so that `a ≠ b` is recognized as a negation
      match (← whnf p).not?, (← whnf q).not? with
      | none, none => g.apply (mkApp2 (.const ``contrapose_iff₁ []) p q)
      | some p, none => g.apply (mkApp2 (.const ``contrapose_iff₂ []) p q)
      | none, some q => g.apply (mkApp2 (.const ``contrapose_iff₃ []) p q)
      | some p, some q => g.apply (mkApp2 (.const ``contrapose_iff₄ []) p q)
    else
      throwTacticEx `contrapose g "contraposing `↔` relations has been disabled.\n\
        To enable it, use `set_option contrapose.negate_iff true`."
  | .forallE _ p q _ =>
    if q.hasLooseBVars then
      throwTacticEx `contrapose g m!"the goal `{target}` is a dependent arrow"
    unless ← Meta.isProp p do
      throwTacticEx `contrapose g m!"hypothesis `{p}` is not a proposition"
    unless ← Meta.isProp q do
      throwTacticEx `contrapose g m!"conclusion `{q}` is not a proposition"
    match (← whnf p).not?, (← whnf q).not? with
    | none, none => g.apply (mkApp2 (.const ``contrapose₁ []) p q)
    | some p, none => g.apply (mkApp2 (.const ``contrapose₂ []) p q)
    | none, some q => g.apply (mkApp2 (.const ``contrapose₃ []) p q)
    | some p, some q => g.apply (mkApp2 (.const ``contrapose₄ []) p q)
  | _ =>
    throwTacticEx `contrapose g m!"the goal `{target}` is not of the form `_ → _` or `_ ↔ _`"

@[tactic_alt contrapose]
syntax (name := contrapose!)
  "contrapose!" optConfig (ppSpace colGt ident (" with " ident)?)? : tactic

local elab "try_push_neg" cfg:optConfig : tactic => do
  Push.push (← Push.elabPushConfig cfg) none (.const ``Not) (.targets #[] true)
    (ifUnchanged := .silent)

macro_rules
  | `(tactic| contrapose! $cfg) => `(tactic| (contrapose; try_push_neg $cfg))
  | `(tactic| contrapose! $cfg:optConfig $e) =>
    `(tactic| (revert $e:ident; contrapose! $cfg; intro $e:ident))
  | `(tactic| contrapose! $cfg:optConfig $e with $e') =>
    `(tactic| (revert $e:ident; contrapose! $cfg; intro $e':ident))

end Mathlib.Tactic.Contrapose
