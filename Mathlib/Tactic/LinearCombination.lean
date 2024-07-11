/-
Copyright (c) 2022 Abby J. Goldberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abby J. Goldberg, Mario Carneiro
-/
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.Widget.Conv

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

@[inherit_doc Mathlib.Tactic.Ring.ring1] syntax (name := ring1Conv) "ring1" : conv

-- move this
open Lean Meta Elab Tactic Qq Mathlib.Tactic in
/-- Elaborator for `ring1` conv tactic. -/
@[tactic ring1Conv] def elabRing1Conv : Tactic := fun _ ↦ withMainContext do
  let e ← Conv.getLhs
  let α ← inferType e
  let .sort u ← whnf (← inferType α) | unreachable!
  let v ← try u.dec catch _ => throwError "not a type{indentExpr α}"
  have α : Q(Type v) := α
  let sα ← synthInstanceQ q(CommSemiring $α)
  let c ← Ring.mkCache sα
  let ⟨a, _, pa⟩ ← (Ring.eval sα c e).run .default
  Conv.updateLhs a pa

def Lean.Expr.isLe (e : Expr) :=
  e.isAppOfArity ``LE.le 4

def Lean.Expr.isLt (e : Expr) :=
  e.isAppOfArity ``LT.lt 4

set_option autoImplicit true

namespace Mathlib.Tactic.LinearCombination
open Lean hiding Rat
open Elab Meta Term

/-! ### Addition -/

theorem add_eq_eq [Add α] (p₁ : (a₁:α) = b₁) (p₂ : a₂ = b₂) : a₁ + a₂ = b₁ + b₂ := p₁ ▸ p₂ ▸ rfl

theorem add_le_eq [Add α] [LE α] [CovariantClass α α (Function.swap (· + ·)) (· ≤ ·)]
    (p₁ : (a₁:α) ≤ b₁) (p₂ : a₂ = b₂) : a₁ + a₂ ≤ b₁ + b₂ :=
  p₂ ▸ add_le_add_right p₁ b₂

theorem add_eq_le [Add α] [LE α] [CovariantClass α α (· + ·) (· ≤ ·)]
    (p₁ : (a₁:α) = b₁) (p₂ : a₂ ≤ b₂) : a₁ + a₂ ≤ b₁ + b₂ :=
  p₁ ▸ add_le_add_left p₂ b₁

theorem add_lt_eq [Add α] [LT α] [CovariantClass α α (Function.swap (· + ·)) (· < ·)]
    (p₁ : (a₁:α) < b₁) (p₂ : a₂ = b₂) : a₁ + a₂ < b₁ + b₂ :=
  p₂ ▸ add_lt_add_right p₁ b₂

theorem add_eq_lt [Add α] [LT α] [CovariantClass α α (· + ·) (· < ·)] {a₁ b₁ a₂ b₂ : α}
    (p₁ : a₁ = b₁) (p₂ : a₂ < b₂) : a₁ + a₂ < b₁ + b₂ :=
  p₁ ▸ add_lt_add_left p₂ b₁

/-! ### Subtraction -/

theorem sub_eq_eq [Sub α] (p₁ : (a₁:α) = b₁) (p₂ : a₂ = b₂) : a₁ - a₂ = b₁ - b₂ := p₁ ▸ p₂ ▸ rfl

theorem sub_le_eq [AddGroup α] [LE α] [CovariantClass α α (Function.swap (· + ·)) (· ≤ ·)]
    (p₁ : (a₁:α) ≤ b₁) (p₂ : a₂ = b₂) : a₁ - a₂ ≤ b₁ - b₂ :=
  p₂ ▸ sub_le_sub_right p₁ b₂

-- theorem sub_eq_le [AddGroup α] [LE α] [CovariantClass α α (· + ·) (· ≤ ·)]
--     [CovariantClass α α (Function.swap (· + ·)) (· ≤ ·)]
--     (p₁ : (a₁:α) = b₁) (p₂ : b₂ ≤ a₂) : a₁ - a₂ ≤ b₁ - b₂ :=
--   p₁ ▸ sub_le_sub_left p₂ b₁

-- theorem sub_lt_le [LinearOrderedAddCommGroup α]
--     (p₁ : (a₁:α) < b₁) (p₂ : b₂ ≤ a₂) : a₁ - a₂ < b₁ - b₂ :=
--   (sub_lt_sub_right p₁ a₂).trans_le (sub_le_sub_left p₂ _)

-- theorem sub_le_lt [AddGroup α] [Preorder α]
--     [CovariantClass α α (· + ·) (· < ·)]
--     [CovariantClass α α (Function.swap (· + ·)) (· ≤ ·)]
--     [CovariantClass α α (Function.swap (· + ·)) (· < ·)]
--     (p₁ : (a₁:α) ≤ b₁) (p₂ : b₂ < a₂) : a₁ - a₂ < b₁ - b₂ :=
--   (sub_le_sub_right p₁ a₂).trans_lt (sub_lt_sub_left p₂ _)

theorem sub_lt_eq [AddGroup α] [LT α] [CovariantClass α α (Function.swap (· + ·)) (· < ·)]
    (p₁ : (a₁:α) < b₁) (p₂ : a₂ = b₂) : a₁ - a₂ < b₁ - b₂ :=
  p₂ ▸ sub_lt_sub_right p₁ b₂

-- theorem sub_eq_lt [AddGroup α] [LT α] [CovariantClass α α (· + ·) (· < ·)]
--     [CovariantClass α α (Function.swap (· + ·)) (· < ·)]
--     (p₁ : (a₁:α) = b₁) (p₂ : b₂ < a₂) : a₁ - a₂ < b₁ - b₂ :=
--   p₁ ▸ sub_lt_sub_left p₂ b₁

/-! ### Negation -/

theorem neg_eq [Neg α] (p : (a:α) = b) : -a = -b := p ▸ rfl
-- alias ⟨_, neg_le⟩ := neg_le_neg_iff
-- alias ⟨_, neg_lt⟩ := neg_lt_neg_iff

/-! ### Multiplication -/

theorem mul_eq_const [Mul α] (p : a = b) (c : α) : a * c = b * c := p ▸ rfl

theorem mul_le_const [Mul α] [Zero α] [Preorder α] [MulPosMono α] (p : b ≤ c) (a : α)
    (ha : 0 ≤ a := by positivity) : b * a ≤ c * a :=
  mul_le_mul_of_nonneg_right p ha

theorem mul_lt_const [Mul α] [Zero α] [Preorder α] [MulPosStrictMono α] (p : b < c) (a : α)
    (ha : 0 < a := by positivity) : b * a < c * a :=
  mul_lt_mul_of_pos_right p ha

-- FIXME allow for this variant
theorem mul_lt_const' [Mul α] [Zero α] [Preorder α] [MulPosMono α] (p : b < c) (a : α)
    (ha : 0 ≤ a := by positivity) : b * a ≤ c * a :=
  mul_le_mul_of_nonneg_right p.le ha

theorem mul_const_eq [Mul α] (p : b = c) (a : α) : a * b = a * c := p ▸ rfl

theorem mul_const_le [Mul α] [Zero α] [Preorder α] [PosMulMono α] (p : b ≤ c) (a : α)
    (ha : 0 ≤ a := by positivity) : a * b ≤ a * c :=
  mul_le_mul_of_nonneg_left p ha

theorem mul_const_lt [Mul α] [Zero α] [Preorder α] [PosMulStrictMono α] (p : b < c) (a : α)
    (ha : 0 < a := by positivity) : a * b < a * c :=
  mul_lt_mul_of_pos_left p ha

-- FIXME allow for this variant
theorem mul_const_lt' [Mul α] [Zero α] [Preorder α] [PosMulMono α] (p : b < c) (a : α)
    (ha : 0 ≤ a := by positivity) : a * b ≤ a * c :=
  mul_le_mul_of_nonneg_left p.le ha

/-! ### Division -/

theorem div_eq_const [Div α] (p : a = b) (c : α) : a / c = b / c := p ▸ rfl

theorem div_le_const [LinearOrderedSemifield α] (p : b ≤ c) (a : α)
    (ha : 0 ≤ a := by positivity) : b / a ≤ c / a :=
  div_le_div_of_nonneg_right p ha

theorem div_lt_const [LinearOrderedSemifield α] (p : b < c) (a : α)
    (ha : 0 < a := by positivity) : b / a < c / a :=
  div_lt_div_of_pos_right p ha

-- FIXME allow for this variant
theorem div_lt_const' [LinearOrderedSemifield α] (p : b < c) (a : α)
    (ha : 0 ≤ a := by positivity) : b / a ≤ c / a :=
  div_le_div_of_nonneg_right p.le ha

inductive RelType
  | Eq
  | Le
  | Lt
  deriving Repr, ToExpr

export RelType (Eq Le Lt)

def _root_.Lean.Expr.relType (e : Expr) : Option RelType :=
  if e.isEq then
    some Eq
  else if e.isLe then
    some Le
  else if e.isLt then
    some Lt
  else
    none

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

def RelType.subRelEqData : RelType → RelType × Name
  | Eq => (Eq, ``sub_eq_eq)
  | Le => (Le, ``sub_le_eq)
  | Lt => (Lt, ``sub_lt_eq)

def RelType.mulConstRelData : RelType → RelType × Name
  | Eq => (Eq, ``mul_eq_const)
  | Le => (Le, ``mul_le_const)
  | Lt => (Lt, ``mul_lt_const)

def RelType.mulRelConstData : RelType → RelType × Name
  | Eq => (Eq, ``mul_const_eq)
  | Le => (Le, ``mul_const_le)
  | Lt => (Lt, ``mul_const_lt)

def RelType.divRelConstData : RelType → RelType × Name
  | Eq => (Eq, ``div_eq_const)
  | Le => (Le, ``div_le_const)
  | Lt => (Lt, ``div_lt_const)

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
      | some (rel₁, p₁), some (rel₂, p₂) =>
        let (rel, n) := rel₁.addRelRelData rel₂
        let i := mkIdent n
        Option.map (Prod.mk rel) <$> ``($i $p₁ $p₂)
      | _, _ => failure
  | `($e₁ - $e₂) => do
      match ← expandLinearCombo e₁, ← expandLinearCombo e₂ with
      | none, none => pure none
      | some (rel₁, p₁), some (Eq, p₂) =>
        let (rel, n) := rel₁.subRelEqData
        let i := mkIdent n
        Option.map (Prod.mk rel) <$> ``($i $p₁ $p₂)
      | _, _ => failure
  | `($e₁ * $e₂) => do
      match ← expandLinearCombo e₁, ← expandLinearCombo e₂ with
      | none, none => pure none
      | some (rel₁, p₁), none =>
        let (rel, n) := rel₁.mulRelConstData
        let i := mkIdent n
        Option.map (Prod.mk rel) <$> ``($i $p₁ $e₂)
      | none, some (rel₂, p₂) =>
        let (rel, n) := rel₂.mulConstRelData
        let i := mkIdent n
        Option.map (Prod.mk rel) <$> ``($i $p₂ $e₁)
      | _, _ => failure
  | `($e₁ / $e₂) => do
      match ← expandLinearCombo e₁, ← expandLinearCombo e₂ with
      | none, none => pure none
      | some (rel₁, p₁), none =>
        let (rel, n) := rel₁.divRelConstData
        let i := mkIdent n
        Option.map (Prod.mk rel) <$> ``($i $p₁ $e₂)
      | _, _ => failure
  | `(-$e) => do
      match ← expandLinearCombo e with
      | none => pure none
      | some (Eq, p) => Option.map (Prod.mk Eq) <$> ``(neg_eq $p)
      | _ => failure
  | `($e⁻¹) => do
      Option.map (Prod.mk Eq) <$>
      match ← expandLinearCombo e with
      | none => pure none
      | _ => failure
  | e => do
      trace[debug] "leaf case"
      let e ← elabTerm e none
      trace[debug] "{e}"
      let eType ← inferType e
      trace[debug] "type is {eType}"
      let whnfEType ← withReducible do whnf eType
      trace[debug] "whnf of above is {whnfEType}"
      let relType := whnfEType.relType
      trace[debug] "the relation is {reprStr relType}"
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

def RelType.relImpRelData : RelType → RelType → Option Name
  | Eq, Eq => ``eq_of_eq
  | Eq, Le => ``le_of_eq
  | Eq, Lt => ``lt_of_eq
  | Le, Eq => none
  | Le, Le => ``le_of_le
  | Le, Lt => ``lt_of_le
  | Lt, Eq => none
  | Lt, Le => ``le_of_lt
  | Lt, Lt => ``lt_of_lt

theorem eq_of_add_pow [Ring α] [NoZeroDivisors α] (n : ℕ) (p : (a:α) = b)
    (H : (a' - b')^n - (a - b) = 0) : a' = b' := by
  rw [← sub_eq_zero] at p ⊢; apply pow_eq_zero (n := n); rwa [sub_eq_zero, p] at H

/-! ### Default discharger tactic for combination -/

theorem nonpos_intRawCast {α : Type*} [LinearOrderedRing α] {a : ℕ} : (Int.rawCast (Int.negOfNat a) : α) + 0 ≤ 0 := by
  simp

theorem nonpos_ratRawCast {α : Type*} [LinearOrderedField α] {a b : ℕ} : (Rat.rawCast (Int.negOfNat a) b : α) + 0 ≤ 0 := by
  simp [div_nonpos_iff]

theorem neg_intRawCast {α : Type*} [LinearOrderedRing α] {a : ℕ} : (Int.rawCast (Int.negOfNat a.succ) : α) + 0 < 0 := by
  simp [-Nat.succ_eq_add_one]

theorem neg_ratRawCast {α : Type*} [LinearOrderedField α] {a b : ℕ} : (Rat.rawCast (Int.negOfNat a.succ) b.succ : α) + 0 < 0 := by
  simp [div_neg_iff, -Nat.succ_eq_add_one]

-- FIXME do I need parentheses around `(conv_lhs => ring1)`?
macro "linear_combination_discharger" : tactic =>
  `(tactic | ((conv_lhs => ring1); try first | exact nonpos_intRawCast | exact nonpos_ratRawCast | exact neg_intRawCast | exact neg_ratRawCast))

/-- Implementation of `linear_combination`. -/
def elabLinearCombination
    (norm? : Option Syntax.Tactic) (exp? : Option Syntax.NumLit) (input : Option Syntax.Term) :
    Tactic.TacticM Unit := Tactic.withMainContext do
  let (hypRel, p) ← match input with
  | none => (Prod.mk Eq) <$> `(Eq.refl 0)
  | some e => withSynthesize do
    match (← expandLinearComboClean e) with
    | none => (Prod.mk Eq) <$> `(Eq.refl $e)
    | some p => pure p
  trace[debug] "input is {input}"
  trace[debug] "built-up expression has the relation {reprStr hypRel}"
  trace[debug] "built-up expression is the proof {p}"
  trace[debug] "exponent {exp?}"
  let norm := norm?.getD (Unhygienic.run `(tactic| linear_combination_discharger))
  let e ← Lean.Elab.Tactic.getMainTarget
  let whnfEType ← withReducible do whnf e
  let goalRel : Option RelType := whnfEType.relType
  Tactic.evalTactic <| ← withFreshMacroScope <|
  match goalRel with
  | none => `(tactic | fail "goal must be =, ≤ or <")
  | some goalRel =>
  let exp1 :=
    match hypRel.relImpRelData goalRel with
    | none => `(tactic| fail "cannot prove an equality from inequality hypotheses")
    | some n => let i := mkIdent n; `(tactic| (refine $i $p ?a; case' a => $norm:tactic))
  match exp? with
  | some n =>
    if n.getNat = 1 then
      exp1
    else
      match hypRel with
      | Eq => `(tactic| (refine eq_of_add_pow $n $p ?a; case' a => $norm:tactic))
      | _ => `(tactic | fail "linear combination tactic not implemented for exponentiation of inequality goals")
  | _ => exp1

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
