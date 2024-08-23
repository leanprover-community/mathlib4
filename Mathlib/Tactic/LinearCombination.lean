/-
Copyright (c) 2022 Abby J. Goldberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abby J. Goldberg, Mario Carneiro
-/
import Mathlib.Tactic.Ring

/-!
# linear_combination Tactic

In this file, the `linear_combination` tactic is created.  This tactic, which
works over `Ring`s, attempts to simplify the target by creating a linear combination
of a list of equalities and subtracting it from the target.  This file also includes a
definition for `linear_combination_config`.  A `linear_combination_config`
object can be passed into the tactic, allowing the user to specify a
normalization tactic.

## Implementation Notes

This tactic works by creating a weighted sum of the given equations with the
given coefficients.  Then, it subtracts the right side of the weighted sum
from the left side so that the right side equals 0, and it does the same with
the target.  Afterwards, it sets the goal to be the equality between the
lefthand side of the new goal and the lefthand side of the new weighted sum.
Lastly, calls a normalization tactic on this target.

## References

* <https://leanprover.zulipchat.com/#narrow/stream/239415-metaprogramming-.2F.20tactics/topic/Linear.20algebra.20tactic/near/213928196>

-/

namespace Mathlib.Tactic.LinearCombination
open Lean hiding Rat
open Elab Meta Term

variable {α : Type*} {a a' a₁ a₂ b b' b₁ b₂ c : α}

theorem add_pf [Add α] (p₁ : (a₁:α) = b₁) (p₂ : a₂ = b₂) : a₁ + a₂ = b₁ + b₂ := p₁ ▸ p₂ ▸ rfl
theorem sub_pf [Sub α] (p₁ : (a₁:α) = b₁) (p₂ : a₂ = b₂) : a₁ - a₂ = b₁ - b₂ := p₁ ▸ p₂ ▸ rfl
theorem neg_pf [Neg α] (p : (a:α) = b) : -a = -b := p ▸ rfl
theorem pf_mul_c [Mul α] (p : a = b) (c : α) : a * c = b * c := p ▸ rfl
theorem c_mul_pf [Mul α] (p : b = c) (a : α) : a * b = a * c := p ▸ rfl
theorem pf_div_c [Div α] (p : a = b) (c : α) : a / c = b / c := p ▸ rfl

/-- Result of `expandLinearCombo`, either an equality proof or a value. -/
inductive Expanded
  /-- A proof of `a = b`. -/
  | proof (pf : Syntax.Term)
  /-- A value, equivalently a proof of `c = c`. -/
  | const (c : Syntax.Term)

/--
Performs macro expansion of a linear combination expression,
using `+`/`-`/`*`/`/` on equations and values.
* `.proof p` means that `p` is a syntax corresponding to a proof of an equation.
  For example, if `h : a = b` then `expandLinearCombo (2 * h)` returns `.proof (c_add_pf 2 h)`
  which is a proof of `2 * a = 2 * b`.
* `.const c` means that the input expression is not an equation but a value.
-/
partial def expandLinearCombo (ty : Expr) (stx : Syntax.Term) : TermElabM Expanded := withRef stx do
  match stx with
  | `(($e)) => expandLinearCombo ty e
  | `($e₁ + $e₂) => do
    match ← expandLinearCombo ty e₁, ← expandLinearCombo ty e₂ with
    | .const c₁, .const c₂ => .const <$> ``($c₁ + $c₂)
    | .proof p₁, .proof p₂ => .proof <$> ``(add_pf $p₁ $p₂)
    | _ , _ => throwError "'linear_combination' is agnostic to the addition of constants"
  | `($e₁ - $e₂) => do
    match ← expandLinearCombo ty e₁, ← expandLinearCombo ty e₂ with
    | .const c₁, .const c₂ => .const <$> ``($c₁ - $c₂)
    | .proof _, .const _ =>
      throwError "'linear_combination' is agnostic to the subtraction of constants"
    | .const _, .proof _ =>
      throwError "'linear_combination' is agnostic to the addition of constants"
    | .proof p₁, .proof p₂ => .proof <$> ``(sub_pf $p₁ $p₂)
  | `(-$e) => do
    match ← expandLinearCombo ty e with
    | .const c => .const <$> `(-$c)
    | .proof p => .proof <$> ``(neg_pf $p)
  | `($e₁ * $e₂) => do
    match ← expandLinearCombo ty e₁, ← expandLinearCombo ty e₂ with
    | .const c₁, .const c₂ => .const <$> ``($c₁ * $c₂)
    | .proof p₁, .const c₂ => .proof <$> ``(pf_mul_c $p₁ $c₂)
    | .const c₁, .proof p₂ => .proof <$> ``(c_mul_pf $p₂ $c₁)
    | .proof _, .proof _ => throwError "'linear_combination' supports only linear operations"
  | `($e₁ / $e₂) => do
    match ← expandLinearCombo ty e₁, ← expandLinearCombo ty e₂ with
    | .const c₁, .const c₂ => .const <$> ``($c₁ / $c₂)
    | .proof p₁, .const c₂ => .proof <$> ``(pf_div_c $p₁ $c₂)
    | _, .proof _ => throwError "'linear_combination' supports only linear operations"
  | e =>
    -- We have the expected type from the goal, so we can fully synthesize this leaf node.
    withSynthesize do
      -- It is OK to use `ty` as the expected type even if `e` is a proof.
      -- The expected type is just a hint.
      let c ← withSynthesizeLight <| Term.elabTerm e ty
      if (← whnfR (← inferType c)).isEq then
        .proof <$> c.toSyntax
      else
        .const <$> c.toSyntax

theorem eq_trans₃ (p : (a:α) = b) (p₁ : a = a') (p₂ : b = b') : a' = b' := p₁ ▸ p₂ ▸ p

theorem eq_of_add [AddGroup α] (p : (a:α) = b) (H : (a' - b') - (a - b) = 0) : a' = b' := by
  rw [← sub_eq_zero] at p ⊢; rwa [sub_eq_zero, p] at H

theorem eq_of_add_pow [Ring α] [NoZeroDivisors α] (n : ℕ) (p : (a:α) = b)
    (H : (a' - b')^n - (a - b) = 0) : a' = b' := by
  rw [← sub_eq_zero] at p ⊢; apply pow_eq_zero (n := n); rwa [sub_eq_zero, p] at H

/-- Implementation of `linear_combination` and `linear_combination2`. -/
def elabLinearCombination (tk : Syntax)
    (norm? : Option Syntax.Tactic) (exp? : Option Syntax.NumLit) (input : Option Syntax.Term) :
    Tactic.TacticM Unit := Tactic.withMainContext do
  let some (ty, _) := (← (← Tactic.getMainGoal).getType').eq? |
    throwError "'linear_combination' only proves equalities"
  let p ← match input with
  | none => `(Eq.refl 0)
  | some e =>
    match ← expandLinearCombo ty e with
    | .const _ => throwError "To run 'linear_combination' without hypotheses, call it without input"
    | .proof p => pure p
  let norm := norm?.getD (Unhygienic.run <| withRef tk `(tactic| ring1))
  Term.withoutErrToSorry <| Tactic.evalTactic <| ← withFreshMacroScope <|
  match exp? with
  | some n =>
    if n.getNat = 1 then `(tactic| (refine eq_of_add $p ?a; case' a => $norm:tactic))
    else `(tactic| (refine eq_of_add_pow $n $p ?a; case' a => $norm:tactic))
  | _ => `(tactic| (refine eq_of_add $p ?a; case' a => $norm:tactic))

/--
The `(norm := $tac)` syntax says to use `tac` as a normalization postprocessor for
`linear_combination`. The default normalizer is `ring1`, but you can override it with `ring_nf`
to get subgoals from `linear_combination` or with `skip` to disable normalization.
-/
syntax normStx := atomic(" (" &"norm" " := ") withoutPosition(tactic) ")"

/--
The `(exp := n)` syntax for `linear_combination` says to take the goal to the `n`th power before
subtracting the given combination of hypotheses.
-/
syntax expStx := atomic(" (" &"exp" " := ") withoutPosition(num) ")"

/--
`linear_combination` attempts to simplify the target by creating a linear combination
  of a list of equalities and subtracting it from the target.
  The tactic will create a linear
  combination by adding the equalities together from left to right, so the order
  of the input hypotheses does matter.  If the `normalize` field of the
  configuration is set to false, then the tactic will simply set the user up to
  prove their target using the linear combination instead of normalizing the subtraction.

Note: The left and right sides of all the equalities should have the same
  type, and the coefficients should also have this type.  There must be
  instances of `Mul` and `AddGroup` for this type.

* The input `e` in `linear_combination e` is a linear combination of proofs of equalities,
  given as a sum/difference of coefficients multiplied by expressions.
  The coefficients may be arbitrary expressions.
  The expressions can be arbitrary proof terms proving equalities.
  Most commonly they are hypothesis names `h1, h2, ...`.
* `linear_combination (norm := tac) e` runs the "normalization tactic" `tac`
  on the subgoal(s) after constructing the linear combination.
  * The default normalization tactic is `ring1`, which closes the goal or fails.
  * To get a subgoal in the case that it is not immediately provable, use
    `ring_nf` as the normalization tactic.
  * To avoid normalization entirely, use `skip` as the normalization tactic.
* `linear_combination (exp := n) e` will take the goal to the `n`th power before subtracting the
  combination `e`. In other words, if the goal is `t1 = t2`, `linear_combination (exp := n) e`
  will change the goal to `(t1 - t2)^n = 0` before proceeding as above.

Example Usage:
```
example (x y : ℤ) (h1 : x*y + 2*x = 1) (h2 : x = y) : x*y = -2*y + 1 := by
  linear_combination 1*h1 - 2*h2

example (x y : ℤ) (h1 : x*y + 2*x = 1) (h2 : x = y) : x*y = -2*y + 1 := by
  linear_combination h1 - 2*h2

example (x y : ℤ) (h1 : x*y + 2*x = 1) (h2 : x = y) : x*y = -2*y + 1 := by
  linear_combination (norm := ring_nf) -2*h2
  /- Goal: x * y + x * 2 - 1 = 0 -/

example (x y z : ℝ) (ha : x + 2*y - z = 4) (hb : 2*x + y + z = -2)
    (hc : x + 2*y + z = 2) :
    -3*x - 3*y - 4*z = 2 := by
  linear_combination ha - hb - 2*hc

example (x y : ℚ) (h1 : x + y = 3) (h2 : 3*x = 7) :
    x*x*y + y*x*y + 6*x = 3*x*y + 14 := by
  linear_combination x*y*h1 + 2*h2

example (x y : ℤ) (h1 : x = -3) (h2 : y = 10) : 2*x = -6 := by
  linear_combination (norm := skip) 2*h1
  simp

axiom qc : ℚ
axiom hqc : qc = 2*qc

example (a b : ℚ) (h : ∀ p q : ℚ, p = q) : 3*a + qc = 3*b + 2*qc := by
  linear_combination 3 * h a b + hqc
```
-/
syntax (name := linearCombination) "linear_combination"
  (normStx)? (expStx)? (ppSpace colGt term)? : tactic
elab_rules : tactic
  | `(tactic| linear_combination%$tk $[(norm := $tac)]? $[(exp := $n)]? $(e)?) =>
    elabLinearCombination tk tac n e

end Mathlib.Tactic.LinearCombination
