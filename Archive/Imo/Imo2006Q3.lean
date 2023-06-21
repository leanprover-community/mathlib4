/-
Copyright (c) 2021 Tian Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tian Chen

! This file was ported from Lean 3 source module imo.imo2006_q3
! leanprover-community/mathlib commit 308826471968962c6b59c7ff82a22757386603e3
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# IMO 2006 Q3

Determine the least real number $M$ such that
$$
\left| ab(a^2 - b^2) + bc(b^2 - c^2) + ca(c^2 - a^2) \right|
≤ M (a^2 + b^2 + c^2)^2
$$
for all real numbers $a$, $b$, $c$.

## Solution

The answer is $M = \frac{9 \sqrt 2}{32}$.

This is essentially a translation of the solution in
https://web.evanchen.cc/exams/IMO-2006-notes.pdf.

It involves making the substitution
`x = a - b`, `y = b - c`, `z = c - a`, `s = a + b + c`.
-/


open Real

namespace Imo2006Q3

/-- Replacing `x` and `y` with their average increases the left side. -/
theorem lhs_ineq {x y : ℝ} (hxy : 0 ≤ x * y) :
    16 * x ^ 2 * y ^ 2 * (x + y) ^ 2 ≤ ((x + y) ^ 2) ^ 3 := by
  conv_rhs => rw [pow_succ']
  refine' mul_le_mul_of_nonneg_right _ (sq_nonneg _)
  apply le_of_sub_nonneg
  calc
    ((x + y) ^ 2) ^ 2 - 16 * x ^ 2 * y ^ 2 = (x - y) ^ 2 * ((x + y) ^ 2 + 4 * (x * y)) := by ring
    _ ≥ 0 := mul_nonneg (sq_nonneg _) <| add_nonneg (sq_nonneg _) <| mul_nonneg zero_lt_four.le hxy
#align imo2006_q3.lhs_ineq Imo2006Q3.lhs_ineq

theorem four_pow_four_pos : (0 : ℝ) < 4 ^ 4 :=
  pow_pos zero_lt_four _
#align imo2006_q3.four_pow_four_pos Imo2006Q3.four_pow_four_pos

theorem mid_ineq {s t : ℝ} : s * t ^ 3 ≤ (3 * t + s) ^ 4 / 4 ^ 4 :=
  (le_div_iff four_pow_four_pos).mpr <|
    le_of_sub_nonneg <|
      calc
        (3 * t + s) ^ 4 - s * t ^ 3 * 4 ^ 4 = (s - t) ^ 2 * ((s + 7 * t) ^ 2 + 2 * (4 * t) ^ 2) :=
          by ring
        _ ≥ 0 :=
          mul_nonneg (sq_nonneg _) <|
            add_nonneg (sq_nonneg _) <| mul_nonneg zero_le_two (sq_nonneg _)
#align imo2006_q3.mid_ineq Imo2006Q3.mid_ineq

/-- Replacing `x` and `y` with their average decreases the right side. -/
theorem rhs_ineq {x y : ℝ} : 3 * (x + y) ^ 2 ≤ 2 * (x ^ 2 + y ^ 2 + (x + y) ^ 2) :=
  le_of_sub_nonneg <|
    calc
      _ = (x - y) ^ 2 := by ring
      _ ≥ 0 := sq_nonneg _
#align imo2006_q3.rhs_ineq Imo2006Q3.rhs_ineq

theorem zero_lt_32 : (0 : ℝ) < 32 := by norm_num
#align imo2006_q3.zero_lt_32 Imo2006Q3.zero_lt_32

theorem subst_wlog {x y z s : ℝ} (hxy : 0 ≤ x * y) (hxyz : x + y + z = 0) :
    32 * |x * y * z * s| ≤ sqrt 2 * (x ^ 2 + y ^ 2 + z ^ 2 + s ^ 2) ^ 2 :=
  have hz : (x + y) ^ 2 = z ^ 2 := neg_eq_of_add_eq_zero_right hxyz ▸ (neg_sq _).symm
  have hs : 0 ≤ 2 * s ^ 2 := mul_nonneg zero_le_two (sq_nonneg s)
  have this :=
    calc
      2 * s ^ 2 * (16 * x ^ 2 * y ^ 2 * (x + y) ^ 2) ≤ (3 * (x + y) ^ 2 + 2 * s ^ 2) ^ 4 / 4 ^ 4 :=
        le_trans (mul_le_mul_of_nonneg_left (lhs_ineq hxy) hs) mid_ineq
      _ ≤ (2 * (x ^ 2 + y ^ 2 + (x + y) ^ 2) + 2 * s ^ 2) ^ 4 / 4 ^ 4 :=
        div_le_div_of_le four_pow_four_pos.le <|
          pow_le_pow_of_le_left (add_nonneg (mul_nonneg zero_lt_three.le (sq_nonneg _)) hs)
            (add_le_add_right rhs_ineq _) _
  le_of_pow_le_pow _ (mul_nonneg (sqrt_nonneg _) (sq_nonneg _)) Nat.succ_pos' <|
    calc
      (32 * |x * y * z * s|) ^ 2 = 32 * (2 * s ^ 2 * (16 * x ^ 2 * y ^ 2 * (x + y) ^ 2)) := by
        rw [mul_pow, sq_abs, hz]; ring
      _ ≤ 32 * ((2 * (x ^ 2 + y ^ 2 + (x + y) ^ 2) + 2 * s ^ 2) ^ 4 / 4 ^ 4) :=
        (mul_le_mul_of_nonneg_left this zero_lt_32.le)
      _ = (sqrt 2 * (x ^ 2 + y ^ 2 + z ^ 2 + s ^ 2) ^ 2) ^ 2 := by
        rw [mul_pow, sq_sqrt zero_le_two, hz, ← pow_mul, ← mul_add, mul_pow, ← mul_comm_div,
          ← mul_assoc, show 32 / 4 ^ 4 * 2 ^ 4 = (2 : ℝ) by norm_num, show 2 * 2 = 4 by rfl]
#align imo2006_q3.subst_wlog Imo2006Q3.subst_wlog

/-- Proof that `M = 9 * sqrt 2 / 32` works with the substitution. -/
theorem subst_proof₁ (x y z s : ℝ) (hxyz : x + y + z = 0) :
    |x * y * z * s| ≤ sqrt 2 / 32 * (x ^ 2 + y ^ 2 + z ^ 2 + s ^ 2) ^ 2 := by
  wlog h' : 0 ≤ x * y generalizing x y z; swap
  · rw [div_mul_eq_mul_div, le_div_iff' zero_lt_32]
    exact subst_wlog h' hxyz
  cases' (mul_nonneg_of_three x y z).resolve_left h' with h h
  · specialize this y z x _ h
    · rw [← hxyz]; ring
    · convert this using 2 <;> ring
  · specialize this z x y _ h
    · rw [← hxyz]; ring
    · convert this using 2 <;> ring
#align imo2006_q3.subst_proof₁ Imo2006Q3.subst_proof₁

theorem lhs_identity (a b c : ℝ) :
    a * b * (a ^ 2 - b ^ 2) + b * c * (b ^ 2 - c ^ 2) + c * a * (c ^ 2 - a ^ 2) =
      (a - b) * (b - c) * (c - a) * -(a + b + c) :=
  by ring
#align imo2006_q3.lhs_identity Imo2006Q3.lhs_identity

theorem proof₁ {a b c : ℝ} :
    |a * b * (a ^ 2 - b ^ 2) + b * c * (b ^ 2 - c ^ 2) + c * a * (c ^ 2 - a ^ 2)| ≤
      9 * sqrt 2 / 32 * (a ^ 2 + b ^ 2 + c ^ 2) ^ 2 :=
  calc
    _ = _ := congr_arg _ <| lhs_identity a b c
    _ ≤ _ := (subst_proof₁ (a - b) (b - c) (c - a) (-(a + b + c)) (by ring))
    _ = _ := by ring
#align imo2006_q3.proof₁ Imo2006Q3.proof₁

theorem proof₂ (M : ℝ)
    (h : ∀ a b c : ℝ,
      |a * b * (a ^ 2 - b ^ 2) + b * c * (b ^ 2 - c ^ 2) + c * a * (c ^ 2 - a ^ 2)| ≤
        M * (a ^ 2 + b ^ 2 + c ^ 2) ^ 2) :
    9 * sqrt 2 / 32 ≤ M := by
  have h₁ :
    ∀ x : ℝ,
      (2 - 3 * x - 2) * (2 - (2 + 3 * x)) * (2 + 3 * x - (2 - 3 * x)) *
          -(2 - 3 * x + 2 + (2 + 3 * x)) =
        -(18 ^ 2 * x ^ 2 * x) :=
    by intro; ring
  have h₂ : ∀ x : ℝ, (2 - 3 * x) ^ 2 + 2 ^ 2 + (2 + 3 * x) ^ 2 = 18 * x ^ 2 + 12 := by intro; ring
  have := h (2 - 3 * sqrt 2) 2 (2 + 3 * sqrt 2)
  rw [lhs_identity, h₁, h₂, sq_sqrt zero_le_two, abs_neg, abs_eq_self.mpr, ← div_le_iff] at this
  · convert this using 1; ring
  · apply pow_pos; norm_num
  · exact mul_nonneg (mul_nonneg (sq_nonneg _) zero_le_two) (sqrt_nonneg _)
#align imo2006_q3.proof₂ Imo2006Q3.proof₂

end Imo2006Q3

open Imo2006Q3

theorem imo2006_q3 (M : ℝ) :
    (∀ a b c : ℝ,
        |a * b * (a ^ 2 - b ^ 2) + b * c * (b ^ 2 - c ^ 2) + c * a * (c ^ 2 - a ^ 2)| ≤
          M * (a ^ 2 + b ^ 2 + c ^ 2) ^ 2) ↔
      9 * sqrt 2 / 32 ≤ M :=
  ⟨proof₂ M, fun h _ _ _ => le_trans proof₁ <| mul_le_mul_of_nonneg_right h <| sq_nonneg _⟩
#align imo2006_q3 imo2006_q3
