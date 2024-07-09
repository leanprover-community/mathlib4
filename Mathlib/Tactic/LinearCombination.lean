/-
Copyright (c) 2022 Abby J. Goldberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abby J. Goldberg, Mario Carneiro
-/
import Mathlib.Tactic.Ring

/-!
# linear_combination Tactic

In this file, the `linear_combination` tactic is created.  This tactic, which
works over `CommRing`s, attempts to simplify the target by creating a linear combination
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

def Lean.Expr.isLe (e : Expr) :=
  e.isAppOfArity ``LE.le 4

def Lean.Expr.isLt (e : Expr) :=
  e.isAppOfArity ``LT.lt 4

set_option autoImplicit true

namespace Mathlib.Tactic.LinearCombination
open Lean hiding Rat
open Elab Meta Term

theorem add_eq_const [Add α] (p : a = b) (c : α) : a + c = b + c := congr($p + c)
theorem add_const_eq [Add α] (p : b = c) (a : α) : a + b = a + c := congr(a + $p)
theorem add_eq_eq [Add α] (p₁ : (a₁:α) = b₁) (p₂ : a₂ = b₂) : a₁ + a₂ = b₁ + b₂ := congr($p₁ + $p₂)
theorem sub_eq_const [Sub α] (p : a = b) (c : α) : a - c = b - c := congr($p - c)
theorem sub_const_eq [Sub α] (p : b = c) (a : α) : a - b = a - c := congr(a - $p)
theorem sub_eq_eq [Sub α] (p₁ : (a₁:α) = b₁) (p₂ : a₂ = b₂) : a₁ - a₂ = b₁ - b₂ := congr($p₁ - $p₂)
theorem mul_eq_const [Mul α] (p : a = b) (c : α) : a * c = b * c := congr($p * c)
theorem mul_const_eq [Mul α] (p : b = c) (a : α) : a * b = a * c := congr(a * $p)
theorem mul_eq_eq [Mul α] (p₁ : (a₁:α) = b₁) (p₂ : a₂ = b₂) : a₁ * a₂ = b₁ * b₂ := congr($p₁ * $p₂)
theorem div_eq_const [Div α] (p : a = b) (c : α) : a / c = b / c := congr($p / c)
theorem div_const_eq [Div α] (p : b = c) (a : α) : a / b = a / c := congr(a / $p)
theorem div_eq_eq [Div α] (p₁ : (a₁:α) = b₁) (p₂ : a₂ = b₂) : a₁ / a₂ = b₁ / b₂ := congr($p₁ / $p₂)
theorem neg_eq [Neg α] (p : (a:α) = b) : -a = -b := congr(-$p)
theorem inv_eq [Inv α] (p : (a:α) = b) : a⁻¹ = b⁻¹ := congr($p⁻¹)

alias add_le_const := add_le_add_right
alias add_const_le := add_le_add_left
alias add_le_le := add_le_add

inductive RelType
  | Eq
  | Le
  | Lt

export RelType (Eq Le Lt)

/--
Performs macro expansion of a linear combination expression,
using `+`/`-`/`*`/`/` on equations and values.
* `some p` means that `p` is a syntax corresponding to a proof of an equation.
  For example, if `h : a = b` then `expandLinearCombo (2 * h)` returns `some (c_add_pf 2 h)`
  which is a proof of `2 * a = 2 * b`.
* `none` means that the input expression is not an equation but a value;
  the input syntax itself is used in this case.
-/
partial def expandLinearCombo : Syntax.Term → TermElabM (RelType × Option (Syntax.Term))
  | `(($e)) => expandLinearCombo e
  | `($e₁ + $e₂) => do
      let (rel₁, p₁) ← expandLinearCombo e₁
      let (rel₂, p₂) ← expandLinearCombo e₂
      match rel₁, rel₂ with
      | Eq, Eq => Prod.mk Eq <$>
        match p₁, p₂ with
        | none, none => pure none
        | some p₁, none => ``(add_eq_const $p₁ $e₂)
        | none, some p₂ => ``(add_const_eq $p₂ $e₁)
        | some p₁, some p₂ => ``(add_eq_eq $p₁ $p₂)
      | Le, Le => Prod.mk Le <$>
        match p₁, p₂ with
        | none, none => pure none
        | some p₁, none => ``(add_le_const $p₁ $e₂)
        | none, some p₂ => ``(add_const_le $p₂ $e₁)
        | some p₁, some p₂ => ``(add_le_le $p₁ $p₂)
      | _, _ => Prod.mk Eq <$> pure none
  | `($e₁ - $e₂) => do
      let (rel₁, p₁) ← expandLinearCombo e₁
      let (rel₂, p₂) ← expandLinearCombo e₂
      match rel₁, rel₂ with
      | Eq, Eq => Prod.mk Eq <$>
        match p₁, p₂ with
        | none, none => pure none
        | some p₁, none => ``(sub_eq_const $p₁ $e₂)
        | none, some p₂ => ``(sub_const_eq $p₂ $e₁)
        | some p₁, some p₂ => ``(sub_eq_eq $p₁ $p₂)
      | _, _ => Prod.mk Eq <$> pure none
  | `($e₁ * $e₂) => do
      let (rel₁, p₁) ← expandLinearCombo e₁
      let (rel₂, p₂) ← expandLinearCombo e₂
      match rel₁, rel₂ with
      | Eq, Eq => Prod.mk Eq <$>
        match p₁, p₂ with
        | none, none => pure none
        | some p₁, none => ``(mul_eq_const $p₁ $e₂)
        | none, some p₂ => ``(mul_const_eq $p₂ $e₁)
        | some p₁, some p₂ => ``(mul_eq_eq $p₁ $p₂)
      | _, _ => Prod.mk Eq <$> pure none
  | `($e₁ / $e₂) => do
      let (rel₁, p₁) ← expandLinearCombo e₁
      let (rel₂, p₂) ← expandLinearCombo e₂
      match rel₁, rel₂ with
      | Eq, Eq => Prod.mk Eq <$>
        match p₁, p₂ with
        | none, none => pure none
        | some p₁, none => ``(div_eq_const $p₁ $e₂)
        | none, some p₂ => ``(div_const_eq $p₂ $e₁)
        | some p₁, some p₂ => ``(div_eq_eq $p₁ $p₂)
      | _, _ => Prod.mk Eq <$> pure none
  | `(-$e) => do
      let (rel, p) ← expandLinearCombo e
      match rel with
      | Eq => Prod.mk Eq <$>
        match p with
        | none => pure none
        | some p => ``(neg_eq $p)
      | _ => Prod.mk Eq <$> pure none
  | `($e⁻¹) => do
      let (rel, p) ← expandLinearCombo e
      match rel with
      | Eq => Prod.mk Eq <$>
        match p with
        | none => pure none
        | some p => ``(inv_eq $p)
      | _ => Prod.mk Eq <$> pure none
  | `(← $e) => do
      let (rel, p) ← expandLinearCombo e
      match rel with
      | Eq => Prod.mk Eq <$>
        match p with
        | none => pure none
        | some p => ``(Eq.symm $p)
      | _ => Prod.mk Eq <$> pure none
  | e => do
      let e ← elabTerm e none
      let eType ← inferType e
      let whnfEType ← withReducible do whnf eType
      if whnfEType.isEq then
        pure (Eq, some (← e.toSyntax))
      else if whnfEType.isLe then
        pure (Le, some (← e.toSyntax))
      else if whnfEType.isLt then
        pure (Lt, some (← e.toSyntax))
      else
        pure (Eq, none)

def expandLinearComboClean (stx : Syntax.Term) : TermElabM (RelType × Option Syntax.Term) := do
  let (rel, result) ← expandLinearCombo stx
  return Prod.mk rel <| result.map fun r => ⟨r.raw.setInfo (SourceInfo.fromRef stx true)⟩

theorem eq_trans₃ (p : (a:α) = b) (p₁ : a = a') (p₂ : b = b') : a' = b' := p₁ ▸ p₂ ▸ p

theorem eq_of_add [AddGroup α] (p : (a:α) = b) (H : (a' - b') - (a - b) = 0) : a' = b' := by
  rw [← sub_eq_zero] at p ⊢; rwa [sub_eq_zero, p] at H

theorem eq_of_add_pow [Ring α] [NoZeroDivisors α] (n : ℕ) (p : (a:α) = b)
    (H : (a' - b')^n - (a - b) = 0) : a' = b' := by
  rw [← sub_eq_zero] at p ⊢; apply pow_eq_zero (n := n); rwa [sub_eq_zero, p] at H

/-- Implementation of `linear_combination` and `linear_combination2`. -/
def elabLinearCombination
    (norm? : Option Syntax.Tactic) (exp? : Option Syntax.NumLit) (input : Option Syntax.Term)
    (twoGoals := false) : Tactic.TacticM Unit := Tactic.withMainContext do
  let p ← match input with
  | none => `(Eq.refl 0)
  | some e => withSynthesize do
    match (← expandLinearComboClean e).2 with
    | none => `(Eq.refl $e)
    | some p => pure p
  let norm := norm?.getD (Unhygienic.run `(tactic| ring1))
  Tactic.evalTactic <| ← withFreshMacroScope <|
  if twoGoals then
    `(tactic| (
      refine eq_trans₃ $p ?a ?b
      case' a => $norm:tactic
      case' b => $norm:tactic))
  else
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
  This feature is not supported for `linear_combination2`.
* `linear_combination2 e` is the same as `linear_combination e` but it produces two
  subgoals instead of one: rather than proving that `(a - b) - (a' - b') = 0` where
  `a' = b'` is the linear combination from `e` and `a = b` is the goal,
  it instead attempts to prove `a = a'` and `b = b'`.
  Because it does not use subtraction, this form is applicable also to semirings.
  * Note that a goal which is provable by `linear_combination e` may not be provable
    by `linear_combination2 e`; in general you may need to add a coefficient to `e`
    to make both sides match, as in `linear_combination2 e + c`.
  * You can also reverse equalities using `← h`, so for example if `h₁ : a = b`
    then `2 * (← h)` is a proof of `2 * b = 2 * a`.

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
  | `(tactic| linear_combination $[(norm := $tac)]? $[(exp := $n)]? $(e)?) =>
    elabLinearCombination tac n e

@[inherit_doc linearCombination]
syntax "linear_combination2" (normStx)? (ppSpace colGt term)? : tactic
elab_rules : tactic
  | `(tactic| linear_combination2 $[(norm := $tac)]? $(e)?) => elabLinearCombination tac none e true
