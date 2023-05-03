/-
Copyright (c) 2020 Robert Y. Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Y. Lewis

! This file was ported from Lean 3 source module tactic.cancel_denoms
! leanprover-community/mathlib commit eaa771fc4f5f356afeacac4ab92e0cbf10b0b1df
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
--import Mathlib.Data.Rat.MetaDefs
import Mathlib.Tactic.NormNum
import Mathlib.Data.Tree
--import Mathlib.Meta.Expr

/-!
# A tactic for canceling numeric denominators

This file defines tactics that cancel numeric denominators from field expressions.

As an example, we want to transform a comparison `5*(a/3 + b/4) < c/3` into the equivalent
`5*(4*a + 3*b) < 4*c`.

## Implementation notes

The tooling here was originally written for `linarith`, not intended as an interactive tactic.
The interactive version has been split off because it is sometimes convenient to use on its own.
There are likely some rough edges to it.

Improving this tactic would be a good project for someone interested in learning tactic programming.
-/


namespace CancelFactors

/-! ### Lemmas used in the procedure -/


theorem mul_subst {α} [CommRing α] {n1 n2 k e1 e2 t1 t2 : α} (h1 : n1 * e1 = t1) (h2 : n2 * e2 = t2)
    (h3 : n1 * n2 = k) : k * (e1 * e2) = t1 * t2 := by
  rw [← h3, mul_comm n1, mul_assoc n2, ← mul_assoc n1, h1, ← mul_assoc n2, mul_comm n2, mul_assoc,
    h2]
#align cancel_factors.mul_subst CancelFactors.mul_subst

theorem div_subst {α} [Field α] {n1 n2 k e1 e2 t1 : α} (h1 : n1 * e1 = t1) (h2 : n2 / e2 = 1)
    (h3 : n1 * n2 = k) : k * (e1 / e2) = t1 := by
  rw [← h3, mul_assoc, mul_div_left_comm, h2, ← mul_assoc, h1, mul_comm, one_mul]
#align cancel_factors.div_subst CancelFactors.div_subst

theorem cancel_factors_eq_div {α} [Field α] {n e e' : α} (h : n * e = e') (h2 : n ≠ 0) :
    e = e' / n :=
  eq_div_of_mul_eq h2 <| by rwa [mul_comm] at h
#align cancel_factors.cancel_factors_eq_div CancelFactors.cancel_factors_eq_div

theorem add_subst {α} [Ring α] {n e1 e2 t1 t2 : α} (h1 : n * e1 = t1) (h2 : n * e2 = t2) :
    n * (e1 + e2) = t1 + t2 := by simp [left_distrib, *]
#align cancel_factors.add_subst CancelFactors.add_subst

theorem sub_subst {α} [Ring α] {n e1 e2 t1 t2 : α} (h1 : n * e1 = t1) (h2 : n * e2 = t2) :
    n * (e1 - e2) = t1 - t2 := by simp [left_distrib, *, sub_eq_add_neg]
#align cancel_factors.sub_subst CancelFactors.sub_subst

theorem neg_subst {α} [Ring α] {n e t : α} (h1 : n * e = t) : n * -e = -t := by simp [*]
#align cancel_factors.neg_subst CancelFactors.neg_subst

theorem cancel_factors_lt {α} [LinearOrderedField α] {a b ad bd a' b' gcd : α} (ha : ad * a = a')
    (hb : bd * b = b') (had : 0 < ad) (hbd : 0 < bd) (hgcd : 0 < gcd) :
    (a < b) = (1 / gcd * (bd * a') < 1 / gcd * (ad * b')) := by
  rw [mul_lt_mul_left, ← ha, ← hb, ← mul_assoc, ← mul_assoc, mul_comm bd, mul_lt_mul_left]
  exact mul_pos had hbd
  exact one_div_pos.2 hgcd
#align cancel_factors.cancel_factors_lt CancelFactors.cancel_factors_lt

theorem cancel_factors_le {α} [LinearOrderedField α] {a b ad bd a' b' gcd : α} (ha : ad * a = a')
    (hb : bd * b = b') (had : 0 < ad) (hbd : 0 < bd) (hgcd : 0 < gcd) :
    (a ≤ b) = (1 / gcd * (bd * a') ≤ 1 / gcd * (ad * b')) := by
  rw [mul_le_mul_left, ← ha, ← hb, ← mul_assoc, ← mul_assoc, mul_comm bd, mul_le_mul_left]
  exact mul_pos had hbd
  exact one_div_pos.2 hgcd
#align cancel_factors.cancel_factors_le CancelFactors.cancel_factors_le

theorem cancel_factors_eq {α} [LinearOrderedField α] {a b ad bd a' b' gcd : α} (ha : ad * a = a')
    (hb : bd * b = b') (had : 0 < ad) (hbd : 0 < bd) (hgcd : 0 < gcd) :
    (a = b) = (1 / gcd * (bd * a') = 1 / gcd * (ad * b')) := by
  rw [← ha, ← hb, ← mul_assoc bd, ← mul_assoc ad, mul_comm bd]
  ext; constructor
  · rintro rfl
    rfl
  · intro h
    simp only [← mul_assoc] at h
    refine' mul_left_cancel₀ (mul_ne_zero _ _) h
    apply mul_ne_zero
    apply div_ne_zero
    all_goals apply ne_of_gt ; first |assumption|exact zero_lt_one
#align cancel_factors.cancel_factors_eq CancelFactors.cancel_factors_eq


open Lean Parser Tactic

/--
`cancel_denoms` attempts to remove numerals from the denominators of fractions.
It works on propositions that are field-valued inequalities.
```lean
variable [LinearOrderedField α] (a b c : α)
example (h : a / 5 + b / 4 < c) : 4*a + 5*b < 20*c := by
  cancel_denoms at h
  exact h
example (h : a > 0) : a / 5 > 0 := by
  cancel_denoms
  exact h
```
-/
syntax (name := cancelDenoms) "cancel_denoms" (ppSpace location)? : tactic
