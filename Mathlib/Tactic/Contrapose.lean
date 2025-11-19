/-
Copyright (c) 2022 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
-/
module

public meta import Mathlib.Tactic.Push

/-! # Contrapose

The `contrapose` tactic transforms the goal into its contrapositive when that goal is an
implication or an iff. It also avoids creating a double negation if there already is a negation.

* `contrapose` turns a goal `P → Q` into `¬ Q → ¬ P` and a goal `P ↔ Q` into `¬ P ↔ ¬ Q`
* `contrapose!` runs `contrapose` and then pushes negations inside `P` and `Q` using `push_neg`
* `contrapose h` first reverts the local assumption `h`, and then uses `contrapose` and `intro h`
* `contrapose! h` first reverts the local assumption `h`, and then uses `contrapose!` and `intro h`
* `contrapose h with new_h` uses the name `new_h` for the introduced hypothesis

-/

public meta section
namespace Mathlib.Tactic.Contrapose

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
Transforms the goal into its contrapositive.
* `contrapose` turns a goal `P → Q` into `¬ Q → ¬ P` and it turns a goal `P ↔ Q` into `¬ P ↔ ¬ Q`
* `contrapose h` first reverts the local assumption `h`, and then uses `contrapose` and `intro h`
* `contrapose h with new_h` uses the name `new_h` for the introduced hypothesis
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

/--
Transforms the goal into its contrapositive and pushes negations in the result.
Usage matches `contrapose`
-/
syntax (name := contrapose!) "contrapose!" (ppSpace colGt ident (" with " ident)?)? : tactic
macro_rules
  | `(tactic| contrapose!) => `(tactic| (contrapose; try push_neg))
  | `(tactic| contrapose! $e) => `(tactic| (revert $e:ident; contrapose!; intro $e:ident))
  | `(tactic| contrapose! $e with $e') => `(tactic| (revert $e:ident; contrapose!; intro $e':ident))

end Mathlib.Tactic.Contrapose
