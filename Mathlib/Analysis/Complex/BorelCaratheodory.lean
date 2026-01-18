/-
Copyright (c) 2026 Maksym Radziwill. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maksym Radziwill
-/

module

public import Mathlib.Analysis.Complex.Schwarz

/-!
# Borel-Carathéodory theorem

This file proves the Borel-Carathéodory theorem: for any function `f` analytic on the
open ball `|z| < R` such that `Re(f z) < M` for all `|z| < R`, we have
`‖f z‖ ≤ 2 * M * ‖z‖ / (R - ‖z‖) + ‖f 0‖ * (R + ‖z‖) / (R - ‖z‖)`

## Main results

* `Complex.borelCaratheodory_zero`: The theorem under the assumption `f 0 = 0`
* `Complex.borelCaratheodory`: The general version of the theorem

## Implementation Notes

The proof applies the Schwarz lemma to the transformed function `w(z) = f(z) / (2M - f(z))`,
which maps the ball `|z| < R` into the unit disk provided that `(f z).re < M` for all `|z| < R`.
After obtaining bounds on `w`, we invert the transformation to recover bounds on `f`.

## Tags

complex analysis, Borel, Carathéodory, analytic function, growth bound
-/

open Metric

namespace Complex

variable {f : ℂ → ℂ} {s : Set ℂ} {M R : ℝ} {z w : ℂ}

section SchwarzTransform

/-- If a differentiable function avoids a value `M`, then it remains differentiable
when divided by `M - f z`. -/
private lemma div_const_sub (hf : DifferentiableOn ℂ f s) (hf₁ : Set.MapsTo f s {z | z ≠ M}) :
    DifferentiableOn ℂ (fun z ↦ f z / (M - f z)) s :=
  DifferentiableOn.div hf (DifferentiableOn.const_sub hf M) 
    fun _ hx => sub_ne_zero.mpr (hf₁ hx).symm

/-- If `w = z / (2M - z)`, then `z = 2M * w / (1 + w)`. This is the inverse of the
Schwarz transform used in the proof of the Borel-Carathéodory theorem. -/
lemma eq_mul_div_one_add_of_eq_div_sub (_ : M ≠ 0) (_ : 2 * M - z ≠ 0)
    (h : w = z / (2 * M - z)) : z = 2 * M * w / (1 + w) := by
  rw [h]; field_simp; ring_nf; rw [mul_inv_cancel_right₀]; norm_cast

/-- Norm inequality for the inverse Schwarz transform: if `‖w‖ < 1`, then
`‖2M * w / (1 + w)‖ ≤ 2M * ‖w‖ / (1 - ‖w‖)`. -/
lemma norm_two_mul_div_one_add_le (hM : 0 < M) (hw : ‖w‖ < 1) :
    ‖2 * ↑M * w / (1 + w)‖ ≤ 2 * M * ‖w‖ / (1 - ‖w‖) := by
  simp only [norm_div, norm_mul, norm_ofNat, norm_real, Real.norm_eq_abs, abs_of_pos hM]
  gcongr; · linarith
  rw [← norm_one (α := ℂ)]; exact norm_sub_le_norm_add 1 w

/-- If `z.re < M`, then `‖z‖ < ‖2M - z‖`. This shows that the Schwarz transform
`z ↦ z / (2M - z)` has numerator smaller than denominator when the real part is bounded by M -/
lemma norm_lt_norm_two_mul_sub (_ : 0 < M) (_ : z.re < M) : ‖z‖ < ‖2 * M - z‖ := by
  apply (sq_lt_sq₀ (norm_nonneg z) (norm_nonneg (2 * M - z))).mp
  rw [Complex.sq_norm, Complex.sq_norm]
  simp only [normSq_apply, sub_re, mul_re, re_ofNat, ofReal_re, im_ofNat, ofReal_im,
    mul_zero, sub_zero, sub_im, mul_im, zero_mul, add_zero, zero_sub, mul_neg, neg_mul,
    neg_neg, add_lt_add_iff_right]
  ring_nf
  nlinarith [sq_nonneg (z.re - M)]

/-- The Schwarz transform `z ↦ z / (2M - z)` maps values with `z.re < M` into the unit disk. -/
lemma norm_div_two_mul_sub_lt_one (hM : 0 < M) (hz : z.re < M) : ‖z / (2 * M - z)‖ < 1 := by
  by_cases h : 0 < ‖z‖
  · rw [norm_div, div_lt_one (h.trans (norm_lt_norm_two_mul_sub hM hz))]
    exact norm_lt_norm_two_mul_sub hM hz
  · simp [norm_le_zero_iff.mp (not_lt.mp h)]

/-- Application of the Schwarz lemma to the transformed function. If `f` is differentiable on
the ball, maps into `{z | z.re < M}`, and satisfies `f 0 = 0`, then the Schwarz transform
satisfies the bound from the Schwarz lemma. -/
private lemma schwarz_applied (hM : 0 < M) (hf : DifferentiableOn ℂ f (ball 0 R))
    (hf₁ : Set.MapsTo f (ball 0 R) {z | z.re < M}) (hz : z ∈ ball 0 R) (hf₂ : f 0 = 0) :
    dist (f z / (2 * M - f z)) 0 ≤ 1 / R * dist z 0 := by
  have h0 : 0 = f 0 / (2 * M - f 0) := by simp [hf₂]
  conv_lhs => rw [h0]
  apply dist_le_div_mul_dist_of_mapsTo_ball (R₂ := 1) ?_ ?_ hz
  · norm_cast
    exact Complex.div_const_sub hf
      (hf₁.mono_right fun a ha h => by simp [h] at ha; linarith [ha, hM])
  · rw [← h0]; intro x hx; rw [mem_closedBall, dist_zero_right]
    exact le_of_lt (norm_div_two_mul_sub_lt_one hM (hf₁ hx))

end SchwarzTransform

section BorelCaratheodory

/-- **Borel-Carathéodory theorem** for functions vanishing at the origin.

If `f` is analytic on the open ball `‖z‖ < R`, satisfies `(f z).re < M` for all such `z`,
and `f 0 = 0`, then `‖f z‖ ≤ 2 * M * ‖z‖ / (R - ‖z‖)` for all `‖z‖ < R`. -/
public theorem borelCaratheodory_zero (hM : 0 < M) (hf : DifferentiableOn ℂ f (ball 0 R))
    (hf₁ : Set.MapsTo f (ball 0 R) {z | z.re < M}) (hR : 0 < R) (hz : z ∈ ball 0 R)
    (hf₂ : f 0 = 0) : ‖f z‖ ≤ 2 * M * ‖z‖ / (R - ‖z‖) := by
  set w := f z / (2 * M - f z)
  have hzR : ‖z‖ < R := mem_ball_zero_iff.mp hz
  have hwR := by simpa only [dist_zero_right, div_one, mul_comm (1 / R), mul_one_div]
                   using schwarz_applied hM hf hf₁ hz hf₂
  have h_denom : 2 * M - f z ≠ 0 := sub_ne_zero_of_ne (fun h => by simpa [← h, hM] using hf₁ hz)
  calc ‖f z‖
    _ = ‖2 * M * w / (1 + w)‖ := by rw [eq_mul_div_one_add_of_eq_div_sub hM.ne' h_denom rfl]
    _ ≤ 2 * M * ‖w‖ / (1 - ‖w‖) := norm_two_mul_div_one_add_le hM
        (hwR.trans_lt ((div_lt_one₀ hR).mpr hzR))
    _ = 2 * M * (‖w‖ / (1 - ‖w‖)) := by ring
    _ ≤ 2 * M * (‖z‖ / R / (1 - ‖z‖ / R)) := by gcongr; simpa [div_lt_one hR]
    _ = 2 * M * ‖z‖ / (R - ‖z‖) := by field_simp

/-- **Borel-Carathéodory theorem**.

If `f` is analytic on the open ball `‖z‖ < R` and satisfies `(f z).re < M` for all such `z`,
then `‖f z‖ ≤ 2 * M * ‖z‖ / (R - ‖z‖) + ‖f 0‖ * (R + ‖z‖) / (R - ‖z‖)` for all `‖z‖ < R`. -/
public theorem borelCaratheodory (hM : 0 < M) (hf : DifferentiableOn ℂ f (ball 0 R))
    (hf₁ : Set.MapsTo f (ball 0 R) {z | z.re < M}) (hR : 0 < R) (hz : z ∈ ball 0 R) :
    ‖f z‖ ≤ 2 * M * ‖z‖ / (R - ‖z‖) + ‖f 0‖ * (R + ‖z‖) / (R - ‖z‖) := by
  have hfz : ‖f z - f 0‖ ≤ 2 * (M + ‖f 0‖) * ‖z‖ / (R - ‖z‖) := by
    apply borelCaratheodory_zero (by positivity) (by fun_prop) ?_ hR hz (by simp)
    intro x hx; simp only [Set.mem_setOf_eq, sub_re]
    calc (f x).re - (f 0).re < M - (f 0).re := by gcongr; exact hf₁ hx
         _ ≤ M + ‖f 0‖ := by linarith [neg_le_abs (f 0).re, abs_re_le_norm (f 0)]
  have h_denom_ne : R - ‖z‖ ≠ 0 := by linarith [mem_ball_zero_iff.mp hz]
  calc ‖f z‖ ≤ ‖f z - f 0‖ + ‖f 0‖ := norm_le_norm_sub_add _ _
       _ ≤ 2 * (M + ‖f 0‖) * ‖z‖ / (R - ‖z‖) + ‖f 0‖ := by gcongr
       _ = 2 * M * ‖z‖ / (R - ‖z‖) + ‖f 0‖ * (R + ‖z‖) / (R - ‖z‖) := by field_simp; ring

end BorelCaratheodory

end Complex
