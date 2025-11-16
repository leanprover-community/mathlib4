/-
Copyright (c) 2025 Maksym Radziwill. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maksym Radziwill
-/

import Mathlib.Analysis.Complex.Schwarz

/-!
# Borel-Carathéodory theorem

This file proves the Borel-Carathéodory theorem, stating that for any function `f`
analytic on the open ball `|z| < R` such that `Re(f z) < M` for all `|z| < R`,
we have the growth bound:

`‖f z‖ ≤ 2 * M * ‖z‖ / (R - ‖z‖) + ‖f 0‖ * (R + ‖z‖) / (R - ‖z‖)`

## Main results

* `Complex.borelCaratheodory_zero`: The theorem under the assumption `f 0 = 0`
* `Complex.borelCaratheodory`: The general version of the theorem

## Implementation notes

The proof proceeds by applying the Schwarz lemma to the transformed function
`φ(z) = f(z) / (2M - f(z))`, which maps the ball into the unit disk. We then
express `f` in terms of `φ`, use the Schwarz lemma bound for `φ` and conclude.
-/

open Metric

namespace DifferentiableOn

variable {s : Set ℂ} {f : ℂ → ℂ} {M : ℝ}

/-- A differentiable function that avoids a value M remains differentiable
when divided by M minus itself. -/
lemma div_const_sub (hf : DifferentiableOn ℂ f s)
    (hf₁ : Set.MapsTo f s {z | z ≠ M}) :
    DifferentiableOn ℂ (fun z ↦ f z / (M - f z)) s :=
  div hf (hf.const_sub ↑M) fun _ hx => sub_ne_zero.mpr (hf₁ hx).symm

end DifferentiableOn

namespace Complex

variable {s : Set ℂ} {f : ℂ → ℂ} {M R : ℝ} {z φ : ℂ}

section SchwarzTransform

/-- Algebraic identity relating the Schwarz transform and its inverse. -/
lemma eq_mul_div_one_add_of_eq_div_sub (M_ne_0 : M ≠ 0) (two_M_ne_z : 2 * M - z ≠ 0)
    (h : φ = z / (2 * M - z)) : z = 2 * M * φ / (1 + φ) := by
  rw [h]; field_simp; ring_nf; rw [mul_inv_cancel_right₀]; norm_cast

/-- Norm inequality for the inverse Schwarz transform. -/
lemma norm_two_mul_div_one_add_le (hM : M > 0) (hφ : ‖φ‖ < 1) :
    ‖2 * ↑M * φ / (1 + φ)‖ ≤ 2 * M * ‖φ‖ / (1 - ‖φ‖) := by
  simp only [norm_div, norm_mul, norm_ofNat, norm_real, Real.norm_eq_abs, abs_of_pos hM]
  gcongr
  · linarith
  · rw [← norm_one (α := ℂ)]; exact norm_sub_le_norm_add 1 φ

/-- The Schwarz transform z/(2M - z) has norm less than 1 when Re(z) < M. -/
lemma norm_lt_norm_two_mul_sub (hM : M > 0) (hz : z.re < M) : ‖z‖ < ‖2 * M - z‖ := by
  apply (sq_lt_sq₀ (norm_nonneg z) (norm_nonneg (2 * M - z))).mp
  rw [Complex.sq_norm, Complex.sq_norm]
  simp only [normSq_apply, sub_re, mul_re, re_ofNat, ofReal_re, im_ofNat, ofReal_im,
    mul_zero, sub_zero, sub_im, mul_im, zero_mul, add_zero, zero_sub, mul_neg, neg_mul,
    neg_neg, add_lt_add_iff_right]; ring_nf
  calc _ = - (M * M * 4) + z.re^2 + M^2 * 4 := by ring_nf
       _ < - (z.re * M * 4) + z.re^2 + M^2 * 4 := by gcongr

/-- The Schwarz transform maps values with real part < M into the unit disk. -/
lemma norm_div_lt_one (hM : M > 0) (hz : z.re < M) : ‖z / (2 * M - z)‖ < 1 := by
  by_cases h : ‖z‖ > 0
  · rw [norm_div, div_lt_one (h.trans (norm_lt_norm_two_mul_sub hM hz))]
    exact norm_lt_norm_two_mul_sub hM hz
  · simp [norm_le_zero_iff.mp (not_lt.mp h)]

/-- The Schwarz transform maps a set avoiding Re(z) ≥ M into the unit ball. -/
lemma mapsTo_ball_schwarz_transform (hM : M > 0) (hf : Set.MapsTo f s {z | z.re < M}) :
    Set.MapsTo (fun z ↦ f z / (2 * M - f z)) s (ball 0 1) :=
  fun _ hx ↦ mem_ball_zero_iff.mpr (norm_div_lt_one hM (hf hx))

/-- Application of Schwarz lemma to the transformed function. -/
lemma schwarz_applied (hM : M > 0) (hf : DifferentiableOn ℂ f (ball 0 R))
    (hf₁ : Set.MapsTo f (ball 0 R) {z | z.re < M}) (hz : z ∈ ball 0 R) (hf₂ : f 0 = 0) :
    dist (f z / (2 * M - f z)) 0 ≤ 1 / R * dist z 0 := by
  have h0 : 0 = f 0 / (2 * M - f 0) := by simp [hf₂]
  conv_lhs => rw [h0]
  apply dist_le_div_mul_dist_of_mapsTo_ball (R₂ := 1) ?_ ?_ hz
  · norm_cast
    exact DifferentiableOn.div_const_sub hf
      (hf₁.mono_right fun a ha h => by simp [h] at ha; linarith [ha, hM])
  · rw [← h0]; intro x hx; rw [mem_ball, dist_zero_right]; exact norm_div_lt_one hM (hf₁ hx)

end SchwarzTransform

section BorelCaratheodory

/-- **Borel-Carathéodory theorem** for functions vanishing at the origin.
If `f` is analytic on `|z| < R`, `Re(f z) < M` for all such `z`, and `f 0 = 0`,
then `‖f z‖ ≤ 2M‖z‖/(R - ‖z‖)`. -/
theorem borelCaratheodory_zero (hM : M > 0) (hf : DifferentiableOn ℂ f (ball 0 R))
    (hf₁ : Set.MapsTo f (ball 0 R) {z | z.re < M}) (hR : 0 < R) (hz : z ∈ ball 0 R)
    (hf₂ : f 0 = 0) : ‖f z‖ ≤ 2 * M * ‖z‖ / (R - ‖z‖) := by
  let φ := f z / (2 * M - f z)
  have hzR : ‖z‖ < R := mem_ball_zero_iff.mp hz
  have hφR : ‖φ‖ ≤ ‖z‖ / R := by
    simpa only [dist_zero_right, div_one, mul_comm (1 / R), mul_one_div]
      using schwarz_applied hM hf hf₁ hz hf₂
  have : 2 * M - f z ≠ 0 := sub_ne_zero_of_ne (fun h => by simpa [← h, hM] using hf₁ hz)
  calc ‖f z‖
    _ = ‖2 * M * φ / (1 + φ)‖ := by rw [eq_mul_div_one_add_of_eq_div_sub hM.ne' this rfl]
    _ ≤ 2 * M * ‖φ‖ / (1 - ‖φ‖) := norm_two_mul_div_one_add_le hM
        (hφR.trans_lt ((div_lt_one₀ hR).mpr hzR))
    _ = 2 * M * (‖φ‖ / (1 - ‖φ‖)) := by ring
    _ ≤ 2 * M * (‖z‖ / R / (1 - ‖z‖ / R)) := by gcongr; simpa [div_lt_one hR]
    _ = 2 * M * ‖z‖ / (R - ‖z‖) := by field_simp

/-- **Borel-Carathéodory theorem**.
If `f` is analytic on `|z| < R` and `Re(f z) < M` for all such `z`,
then `‖f z‖ ≤ 2M‖z‖/(R - ‖z‖) + ‖f 0‖(R + ‖z‖)/(R - ‖z‖)`. -/
theorem borelCaratheodory (hM : M > 0) (hf : DifferentiableOn ℂ f (ball 0 R))
    (hf₁ : Set.MapsTo f (ball 0 R) {z | z.re < M}) (hR : 0 < R) (hz : z ∈ ball 0 R) :
    ‖f z‖ ≤ 2 * M * ‖z‖ / (R - ‖z‖) + ‖f 0‖ * (R + ‖z‖) / (R - ‖z‖) := by
  have hfz : ‖f z - f 0‖ ≤ 2 * (M + ‖f 0‖) * ‖z‖ / (R - ‖z‖) := by
    apply borelCaratheodory_zero (by positivity) (by fun_prop) ?_ hR hz (by simp)
    intro x hx; simp only [Set.mem_setOf_eq, sub_re]
    calc (f x).re - (f 0).re
      _ < M - (f 0).re := by gcongr; exact hf₁ hx
      _ ≤ M + ‖f 0‖ := by linarith [neg_le_abs (f 0).re, abs_re_le_norm (f 0)]
  calc ‖f z‖
    _ ≤ ‖f z - f 0‖ + ‖f 0‖ := norm_le_norm_sub_add _ _
    _ ≤ 2 * (M + ‖f 0‖) * ‖z‖ / (R - ‖z‖) + ‖f 0‖ := by gcongr
    _ = 2 * M * ‖z‖ / (R - ‖z‖) + ‖f 0‖ * (R + ‖z‖) / (R - ‖z‖) := by
        have : R - ‖z‖ ≠ 0 := by linarith [mem_ball_zero_iff.mp hz]
        field_simp; ring

end BorelCaratheodory

end Complex
