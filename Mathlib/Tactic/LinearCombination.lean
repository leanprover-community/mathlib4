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

theorem add_eq_const [Add α] (p : a = b) (c : α) : a + c = b + c := p ▸ rfl
theorem add_const_eq [Add α] (p : b = c) (a : α) : a + b = a + c := p ▸ rfl
theorem add_eq_eq [Add α] (p₁ : (a₁:α) = b₁) (p₂ : a₂ = b₂) : a₁ + a₂ = b₁ + b₂ := p₁ ▸ p₂ ▸ rfl

theorem add_le_eq [Add α] [LE α] [CovariantClass α α (Function.swap (· + ·)) (· ≤ ·)]
    (p₁ : (a₁:α) ≤ b₁) (p₂ : a₂ = b₂) : a₁ + a₂ ≤ b₁ + b₂ :=
  p₂ ▸ add_le_add_right p₁ b₂

theorem add_eq_le [Add α] [LE α] [CovariantClass α α (· + ·) (· ≤ ·)]
    (p₁ : (a₁:α) = b₁) (p₂ : a₂ ≤ b₂) : a₁ + a₂ ≤ b₁ + b₂ :=
  p₁ ▸ add_le_add_left p₂ b₁

theorem add_lt_eq [Add α] [LT α] [CovariantClass α α (Function.swap (· + ·)) (· < ·)]
    {a₁ b₁ a₂ b₂ : α} (p₁ : a₁ < b₁) (p₂ : a₂ = b₂) : a₁ + a₂ < b₁ + b₂ :=
  p₂ ▸ add_lt_add_right p₁ b₂

theorem add_eq_lt [Add α] [LT α] [CovariantClass α α (· + ·) (· < ·)] {a₁ b₁ a₂ b₂ : α}
    (p₁ : a₁ = b₁) (p₂ : a₂ < b₂) : a₁ + a₂ < b₁ + b₂ :=
  p₁ ▸ add_lt_add_left p₂ b₁

theorem sub_eq_const [Sub α] (p : a = b) (c : α) : a - c = b - c := p ▸ rfl
theorem sub_const_eq [Sub α] (p : b = c) (a : α) : a - b = a - c := p ▸ rfl
theorem sub_eq_eq [Sub α] (p₁ : (a₁:α) = b₁) (p₂ : a₂ = b₂) : a₁ - a₂ = b₁ - b₂ := p₁ ▸ p₂ ▸ rfl
theorem mul_eq_const [Mul α] (p : a = b) (c : α) : a * c = b * c := p ▸ rfl
theorem mul_const_eq [Mul α] (p : b = c) (a : α) : a * b = a * c := p ▸ rfl
theorem mul_eq_eq [Mul α] (p₁ : (a₁:α) = b₁) (p₂ : a₂ = b₂) : a₁ * a₂ = b₁ * b₂ := p₁ ▸ p₂ ▸ rfl
theorem div_eq_const [Div α] (p : a = b) (c : α) : a / c = b / c := p ▸ rfl
theorem div_const_eq [Div α] (p : b = c) (a : α) : a / b = a / c := p ▸ rfl
theorem div_eq_eq [Div α] (p₁ : (a₁:α) = b₁) (p₂ : a₂ = b₂) : a₁ / a₂ = b₁ / b₂ := p₁ ▸ p₂ ▸ rfl
theorem neg_eq [Neg α] (p : (a:α) = b) : -a = -b := p ▸ rfl
theorem inv_eq [Inv α] (p : (a:α) = b) : a⁻¹ = b⁻¹ := p ▸ rfl

inductive RelType
  | Eq
  | Le
  | Lt
  deriving Repr, ToExpr

export RelType (Eq Le Lt)

def _root_.Lean.Expr.relType (e : Expr) : MetaM (Option RelType) := do
  let whnfEType ← withReducible do whnf e
  if whnfEType.isEq then
    pure <| some Eq
  else if whnfEType.isLe then
    pure <| some Le
  else if whnfEType.isLt then
    pure <| some Lt
  else
    pure none

def RelType.addRelConstData : RelType → RelType × Name
  | Eq => (Eq, ``add_const_eq)
  | Le => (Le, ``add_le_add_right)
  | Lt => (Lt, ``add_lt_add_right)

def RelType.addConstRelData : RelType → RelType × Name
  | Eq => (Eq, ``add_eq_const)
  | Le => (Le, ``add_le_add_left)
  | Lt => (Lt, ``add_lt_add_left)

def RelType.addRelRelData : RelType → RelType → RelType × Name
  | Eq, Eq => (Eq, ``add_eq_eq)
  | Eq, Le => (Le, ``add_eq_le)
  | Eq, Lt => (Lt, ``add_eq_lt)
  | Le, Eq => (Le, ``add_le_eq)
  | Le, Le => (Le, ``add_le_add)
  | Le, Lt => (Lt, ``add_lt_add_of_le_of_lt)
  | Lt, Eq => (Lt, ``add_lt_eq)
  | Lt, Le => (Lt, ``add_lt_add_of_lt_of_le)
  | Lt, Lt => (Lt, ``add_lt_add)

def mkRelConst (d : RelType × Name) (p₂ e₁ : Term) : TermElabM (Option (RelType × Term)) :=
  let i := mkIdent d.2
  Option.map (Prod.mk d.1) <$> ``($i $p₂ $e₁)

def mkConstRel (d : RelType × Name) (p₁ e₂ : Term) : TermElabM (Option (RelType × Term)) :=
  let i := mkIdent d.2
  Option.map (Prod.mk d.1) <$> ``($i $p₁ $e₂)

def mkRelRel (d : RelType × Name) (p₁ p₂ : Term) : TermElabM (Option (RelType × Term)) :=
  let i := mkIdent d.2
  Option.map (Prod.mk d.1) <$> ``($i $p₁ $p₂)

/--
Performs macro expansion of a linear combination expression,
using `+`/`-`/`*`/`/` on equations and values.
* `some p` means that `p` is a syntax corresponding to a proof of an equation.
  For example, if `h : a = b` then `expandLinearCombo (2 * h)` returns `some (c_add_pf 2 h)`
  which is a proof of `2 * a = 2 * b`.
* `none` means that the input expression is not an equation but a value;
  the input syntax itself is used in this case.
-/
partial def expandLinearCombo : Term → TermElabM (Option (RelType × Term))
  | `(($e)) => expandLinearCombo e
  | `($e₁ + $e₂) => do
      match ← expandLinearCombo e₁, ← expandLinearCombo e₂ with
      | none, none => pure none
      | none, some (rel₂, p₂) => mkRelConst rel₂.addRelConstData p₂ e₁
      | some (rel₁, p₁), none => mkConstRel rel₁.addConstRelData p₁ e₂
      | some (rel₁, p₁), some (rel₂, p₂) => mkRelRel (rel₁.addRelRelData rel₂) p₁ p₂
  | `($e₁ - $e₂) => do
      Option.map (Prod.mk Eq) <$>
      match ← expandLinearCombo e₁, ← expandLinearCombo e₂ with
      | none, none => pure none
      | some (Eq, p₁), none => ``(sub_eq_const $p₁ $e₂)
      | none, some (Eq, p₂) => ``(sub_const_eq $p₂ $e₁)
      | some (Eq, p₁), some (Eq, p₂) => ``(sub_eq_eq $p₁ $p₂)
      | _, _ => pure none
  | `($e₁ * $e₂) => do
      Option.map (Prod.mk Eq) <$>
      match ← expandLinearCombo e₁, ← expandLinearCombo e₂ with
      | none, none => pure none
      | some (Eq, p₁), none => ``(mul_eq_const $p₁ $e₂)
      | none, some (Eq, p₂) => ``(mul_const_eq $p₂ $e₁)
      | some (Eq, p₁), some (Eq, p₂) => ``(mul_eq_eq $p₁ $p₂)
      | _, _ => pure none
  | `($e₁ / $e₂) => do
      Option.map (Prod.mk Eq) <$>
      match ← expandLinearCombo e₁, ← expandLinearCombo e₂ with
      | none, none => pure none
      | some (Eq, p₁), none => ``(div_eq_const $p₁ $e₂)
      | none, some (Eq, p₂) => ``(div_const_eq $p₂ $e₁)
      | some (Eq, p₁), some (Eq, p₂) => ``(div_eq_eq $p₁ $p₂)
      | _, _ => pure none
  | `(-$e) => do
      Option.map (Prod.mk Eq) <$>
      match ← expandLinearCombo e with
      | none => pure none
      | some (Eq, p) => ``(neg_eq $p)
      | _ => pure none
  | `($e⁻¹) => do
      Option.map (Prod.mk Eq) <$>
      match ← expandLinearCombo e with
      | none => pure none
      | some (Eq, p) => ``(inv_eq $p)
      | _ => pure none
  | `(← $e) => do
      Option.map (Prod.mk Eq) <$>
      match ← expandLinearCombo e with
      | some (Eq, p) => ``(Eq.symm $p)
      | _ => pure none
  | e => do
      trace[debug] "leaf case"
      let e ← elabTerm e none
      trace[debug] "{e}"
      let eType ← inferType e
      let relType ← eType.relType
      let s ← e.toSyntax
      pure <| relType.map (fun r ↦ (r, s))

def expandLinearComboClean (stx : Syntax.Term) : TermElabM (Option (RelType × Syntax.Term)) := do
  let result ← expandLinearCombo stx
  trace[debug] "{result.map Prod.snd}"
  return result.map fun r => (r.1, ⟨r.2.raw.setInfo (SourceInfo.fromRef stx true)⟩)

theorem eq_trans₃ (p : (a:α) = b) (p₁ : a = a') (p₂ : b = b') : a' = b' := p₁ ▸ p₂ ▸ p

theorem eq_of_eq [AddGroup α] (p : (a:α) = b) (H : (a' - b') - (a - b) = 0) : a' = b' := by
  rw [← sub_eq_zero] at p ⊢
  rw [sub_eq_zero] at H
  exact H.trans p

theorem le_of_le [LinearOrderedAddCommGroup α] (p : (a:α) ≤ b) (H : (a' - b') - (a - b) ≤ 0) :
    a' ≤ b' := by
  rw [sub_nonpos] at H
  rw [← sub_nonpos] at p ⊢
  exact H.trans p

theorem le_of_eq [LinearOrderedAddCommGroup α] (p : (a:α) = b) (H : (a' - b') - (a - b) ≤ 0) :
    a' ≤ b' :=
  le_of_le p.le H

theorem le_of_lt [LinearOrderedAddCommGroup α] (p : (a:α) < b) (H : (a' - b') - (a - b) ≤ 0) :
    a' ≤ b' :=
  le_of_le p.le H

theorem lt_of_le [LinearOrderedAddCommGroup α] (p : (a:α) ≤ b) (H : (a' - b') - (a - b) < 0) :
    a' < b' := by
  rw [← sub_nonpos] at p
  rw [← sub_neg]
  rw [sub_neg] at H
  exact H.trans_le p

theorem lt_of_eq [LinearOrderedAddCommGroup α] (p : (a:α) = b) (H : (a' - b') - (a - b) < 0) :
    a' < b' :=
  lt_of_le p.le H

theorem lt_of_lt [LinearOrderedAddCommGroup α] (p : (a:α) < b) (H : (a' - b') - (a - b) ≤ 0) :
    a' < b' := by
  rw [sub_nonpos] at H
  rw [← sub_neg] at p ⊢
  exact lt_of_le_of_lt H p

theorem eq_of_add_pow [Ring α] [NoZeroDivisors α] (n : ℕ) (p : (a:α) = b)
    (H : (a' - b')^n - (a - b) = 0) : a' = b' := by
  rw [← sub_eq_zero] at p ⊢; apply pow_eq_zero (n := n); rwa [sub_eq_zero, p] at H

/-- Implementation of `linear_combination` and `linear_combination2`. -/
def elabLinearCombination
    (norm? : Option Syntax.Tactic) (exp? : Option Syntax.NumLit) (input : Option Syntax.Term)
    (twoGoals := false) : Tactic.TacticM Unit := Tactic.withMainContext do
  let (rel, p) ← match input with
  | none => (Prod.mk Eq) <$> `(Eq.refl 0)
  | some e => withSynthesize do
    match (← expandLinearComboClean e) with
    | none => (Prod.mk Eq) <$> `(Eq.refl $e)
    | some p => pure p
  trace[debug] "input is {input}"
  trace[debug] "built-up expression has the relation {reprStr rel}"
  trace[debug] "built-up expression is the proof {p}"
  trace[debug] "two goals? {twoGoals}"
  trace[debug] "exponent {exp?}"
  let norm := norm?.getD (Unhygienic.run `(tactic| ring1))
  let e ← Lean.Elab.Tactic.getMainTarget
  let goalRel : Option RelType ← e.relType
  Tactic.evalTactic <| ← withFreshMacroScope <|
  if twoGoals then
    `(tactic| (
      refine eq_trans₃ $p ?a ?b
      case' a => $norm:tactic
      case' b => $norm:tactic))
  else
    match goalRel with
    | none => `(tactic | fail "goal must be =, ≤ or <")
    | some goalRel =>
    let easy :=
      match rel, goalRel with
      | Eq, Eq => `(tactic| (refine eq_of_eq $p ?a; case' a => $norm:tactic))
      | _, Eq => `(tactic| fail "cannot prove an equality from inequality hypotheses")
      | Eq, Le => `(tactic| (apply le_of_eq $p ?a; case' a => $norm:tactic))
      | Le, Le => `(tactic| (apply le_of_le $p ?a; case' a => $norm:tactic))
      | Lt, Le => `(tactic| (apply le_of_lt $p ?a; case' a => $norm:tactic))
      | Eq, Lt => `(tactic| (refine lt_of_eq $p ?a; case' a => $norm:tactic))
      | Le, Lt => `(tactic| (refine lt_of_le $p ?a; case' a => $norm:tactic))
      | Lt, Lt => `(tactic| (refine lt_of_lt $p ?a; case' a => $norm:tactic))
    match exp? with
    | some n =>
      if n.getNat = 1 then
        easy
      else
        match rel with
        | Eq => `(tactic| (refine eq_of_add_pow $n $p ?a; case' a => $norm:tactic))
        | _ => `(tactic | fail "linear combination tactic not implemented for exponentiation of inequality goals")
    | _ => easy

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
