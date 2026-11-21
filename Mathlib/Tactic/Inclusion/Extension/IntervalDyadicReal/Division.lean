/-
Copyright (c) 2026 David Ledvinka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Ledvinka, Emlis
-/
module

public import Mathlib.Data.Rat.Floor
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational

/-!
# Division and inversion for interval_dyadic_real

This file defines division and inversion of dyadic intervals, rounding each finite output endpoint
once, using the `prec` parameter. In particular, it does not first round a reciprocal and then
multiply. Division by zero follows the real-number convention `x / 0 = 0`. Inversion is division by
the singleton interval `[1, 1]`.
-/

public section

open Dyadic

namespace Inclusion.IntervalDyadicReal

open Dyadic

attribute [local grind unfold] WithBot.some WithTop.some
attribute [local grind norm ←] WithBot.coe_zero WithTop.coe_zero
  WithBot.none_eq_bot WithTop.none_eq_top
attribute [local grind =] WithBot.coe_le_iff WithTop.le_coe_iff
  WithBot.lt_iff_exists WithTop.lt_iff_exists
local grind_pattern Dyadic.toReal_le_toReal => a ≤ b
local grind_pattern Dyadic.toReal_lt_toReal => a < b
attribute [local grind =] inv_nonneg inv_nonpos inv_le_inv₀ inv_le_inv_of_neg

section DyadicDiv

variable (a b : Dyadic) (prec : ℤ)

/-- Divide two dyadic numbers, rounding the quotient downward to the `2⁻prec` grid. -/
@[expose]
def Dyadic.fdiv : Dyadic :=
  match a, b with
  | ofOdd m p _, ofOdd n q _ =>
    .ofIntWithPrec ((m <<< (prec + q - p).toNat).fdiv (n <<< (-(prec + q - p)).toNat)) prec
  | _, _ => 0

/-- Divide two dyadic numbers, rounding the quotient upward to the `2⁻prec` grid. -/
@[expose]
def Dyadic.cdiv : Dyadic := -fdiv (-a) b prec

theorem fdiv_le : (fdiv a b prec).toRat ≤ a.toRat / b.toRat := by
  rcases a with _ | ⟨m, p, -⟩
  · simp [fdiv]
  rcases b with _ | ⟨n, q, -⟩
  · simp [fdiv]
  grw [fdiv, toRat_ofIntWithPrec_eq_mul_two_pow, Int.fdiv_eq_floor, Int.floor_le]
  on_goal 2 => exact Rat.zpow_nonneg rfl
  simp only [toRat_ofOdd_eq_mul_two_pow, Int.shiftLeft_eq, Int.cast_mul, Int.cast_pow,
    Int.cast_ofNat]
  rw [mul_div_mul_comm, ← zpow_natCast, ← zpow_natCast, ← zpow_sub₀ two_ne_zero,
    Int.toNat_sub_toNat_neg, Rat.mul_assoc, ← zpow_add₀ two_ne_zero,
    ← sub_eq_add_neg, add_sub_assoc, add_sub_cancel_left,
    mul_div_mul_comm, ← zpow_sub₀ two_ne_zero, neg_sub_neg]

theorem le_cdiv : a.toRat / b.toRat ≤ (cdiv a b prec).toRat := by
  rw [cdiv, ← neg_neg a.toRat, toRat_neg, neg_div, neg_le_neg_iff, ← toRat_neg]
  exact fdiv_le (-a) b prec

end DyadicDiv

/-- Divide dyadic interval bounds, rounding upward when `up` is true and downward otherwise.
A finite numerator divided by an infinite denominator gives the limiting bound zero; an infinite
numerator gives an infinite bound. The sign cases in `div` never divide two infinite bounds. -/
@[expose]
def divBound (up : Bool) (a b : Option Dyadic) (prec : ℕ) : Option Dyadic :=
  match a, b with
  | none, _ => none
  | some _, none => some 0
  | some a, some b => some (if up then cdiv a b prec else fdiv a b prec)

theorem map_divBound_le (a b : Option Dyadic) (prec : ℕ) {z : ℝ}
    (hdiv : ∀ x y, a = some x → b = some y → toReal x / toReal y ≤ z)
    (hzero : ∀ x, a = some x → b = none → 0 ≤ z) :
    WithBot.map Dyadic.toReal (divBound false a b prec) ≤ z := by
  rcases a with _ | a
  · exact bot_le
  rcases b with _ | b <;> apply WithBot.coe_le_coe.mpr
  · simpa using hzero a rfl rfl
  simp only [Bool.false_eq_true, ↓reduceIte]
  apply hdiv a b rfl rfl |>.trans'
  simpa only [toReal, ← Rat.cast_div] using mod_cast fdiv_le a b prec

theorem le_map_divBound (a b : Option Dyadic) (prec : ℕ) {z : ℝ}
    (hdiv : ∀ x y, a = some x → b = some y → z ≤ toReal x / toReal y)
    (hzero : ∀ x, a = some x → b = none → z ≤ 0) :
    z ≤ WithTop.map Dyadic.toReal (divBound true a b prec) := by
  rcases a with _ | a
  · exact le_top
  rcases b with _ | b <;> apply WithTop.coe_le_coe.mpr
  · simpa using hzero a rfl rfl
  simp only [↓reduceIte]
  apply hdiv a b rfl rfl |>.trans
  simpa only [toReal, ← Rat.cast_div] using mod_cast le_cdiv a b prec

/-- Divide dyadic intervals, rounding finite quotient bounds outward to the `2⁻prec` grid.

When the denominator excludes zero, select the two extremal quotients directly. Infinite
denominator bounds contribute the limiting value zero. When the denominator contains zero,
include the value `x / 0 = 0` as well as the nonzero quotients. For nonempty inputs, the result is
the smallest closed interval on this grid containing all real quotients. -/
@[expose]
def div (I J : Interval Dyadic) (prec : ℕ) : Interval Dyadic :=
  if 0 < J.lb then
    if 0 ≤ I.lb then
      ⟨divBound false I.lb J.ub prec, divBound true I.ub J.lb prec⟩
    else if I.ub ≤ 0 then
      ⟨divBound false I.lb J.lb prec, divBound true I.ub J.ub prec⟩
    else
      ⟨divBound false I.lb J.lb prec, divBound true I.ub J.lb prec⟩
  else if J.ub < 0 then
    if 0 ≤ I.lb then
      ⟨divBound false I.ub J.ub prec, divBound true I.lb J.lb prec⟩
    else if I.ub ≤ 0 then
      ⟨divBound false I.ub J.lb prec, divBound true I.lb J.ub prec⟩
    else
      ⟨divBound false I.ub J.ub prec, divBound true I.lb J.ub prec⟩
  else if I.lb = 0 ∧ I.ub = 0 ∨ J.lb = 0 ∧ J.ub = 0 then
    .singleton 0
  else if 0 ≤ J.lb then
    if 0 ≤ I.lb then .Ici 0
    else if I.ub ≤ 0 then .Iic 0
    else .univ Dyadic
  else if J.ub ≤ 0 then
    if 0 ≤ I.lb then .Iic 0
    else if I.ub ≤ 0 then .Ici 0
    else .univ Dyadic
  else
    .univ Dyadic

@[inclusion_op interval_dyadic_real]
theorem div_mem {x y : ℝ} {I J : Interval Dyadic} (hx : x ∈ I) (hy : y ∈ J) (prec : ℕ) :
    x / y ∈ div I J prec := by
  have hzero := Dyadic.toReal_zero
  unfold div
  split_ifs
  -- A positive denominator reverses the order of its endpoints under reciprocation.
  · constructor
    · apply map_divBound_le <;> grind [mul_le_mul, mul_nonneg]
    · apply le_map_divBound <;> grind [mul_le_mul]
  · constructor
    · apply map_divBound_le <;> grind [mul_le_mul_of_nonpos_of_nonneg]
    · apply le_map_divBound <;>
        grind [mul_le_mul_of_nonpos_of_nonneg, mul_nonpos_of_nonpos_of_nonneg]
  · constructor
    · apply map_divBound_le <;> grind [mul_le_mul_of_nonpos_of_nonneg'']
    · apply le_map_divBound <;> grind [mul_le_mul]
  -- The same reversal holds for a negative denominator.
  · constructor
    · apply map_divBound_le <;> grind [mul_le_mul_of_nonneg_of_nonpos]
    · apply le_map_divBound <;>
        grind [mul_le_mul_of_nonneg_of_nonpos, mul_nonpos_of_nonneg_of_nonpos]
  · constructor
    · apply map_divBound_le <;>
        grind [mul_le_mul_of_nonpos_of_nonpos', mul_nonneg_of_nonpos_of_nonpos]
    · apply le_map_divBound <;> grind [mul_le_mul_of_nonpos_of_nonpos]
  · constructor
    · apply map_divBound_le <;> grind [mul_le_mul_of_nonneg_of_nonpos']
    · apply le_map_divBound <;> grind [mul_le_mul_of_nonpos_of_nonpos]
  -- Denominators containing zero give zero, a half-line, or the universal interval.
  all_goals
    grind [Interval.singleton, Interval.Ici, Interval.Iic, Interval.univ,
      mul_nonneg, mul_nonneg_of_nonpos_of_nonpos,
      mul_nonpos_of_nonneg_of_nonpos, mul_nonpos_of_nonpos_of_nonneg]

/-- Invert a dyadic interval, rounding the finite quotient bounds outward to the `2⁻prec` grid.

This is division of the singleton interval `[1, 1]` by the given interval, so it inherits the
handling of denominator bounds that contain zero. -/
@[expose]
def inv (I : Interval Dyadic) (prec : ℕ) : Interval Dyadic :=
  div (.singleton 1) I prec

@[inclusion_op interval_dyadic_real]
theorem inv_mem {x : ℝ} {I : Interval Dyadic} (hx : x ∈ I) (prec : ℕ) : x⁻¹ ∈ inv I prec := by
  simpa [← one_div, ← toReal_one, inv] using div_mem (Interval.mem_map_singleton 1 _) hx prec

end Inclusion.IntervalDyadicReal
