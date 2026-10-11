/-
Copyright (c) 2026 Maksym Radziwill. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maksym Radziwill
-/

module

public import Mathlib.Analysis.Complex.Schwarz

import Mathlib.Analysis.Complex.MeanValue
import Mathlib.Analysis.Complex.TaylorSeries

/-!
# Borel-Carathéodory theorem

This file proves the Borel-Carathéodory theorem: for any function `f` analytic on the
open ball `|z| < R` such that `Re(f z) < M` for all `|z| < R`, we have
`‖f z‖ ≤ 2 * M * ‖z‖ / (R - ‖z‖) + ‖f 0‖ * (R + ‖z‖) / (R - ‖z‖)`

## Main results

* `Complex.borelCaratheodory_zero`: The theorem under the assumption `f 0 = 0`
* `Complex.borelCaratheodory`: The general version of the theorem

## Implementation Notes

The proof applies the Schwarz lemma to the transformed function `w z := f z / (2 * M - f z)`,
which maps the ball `|z| < R` into the unit disk provided that `(f z).re ≤ M` for all `|z| < R`.
After obtaining bounds on `w`, we invert the transformation to recover bounds on `f`.

## Tags

complex analysis, Borel, Carathéodory, analytic function, growth bound
-/

open Metric Real Topology

namespace Complex

variable {f : ℂ → ℂ} {M R : ℝ} {z w c : ℂ} {n : ℕ}

open scoped Nat ComplexConjugate 

private lemma circleAverage_eq_iteratedDeriv_div_factorial (hf : DiffContOnCl ℂ f (ball c R))
    (hR : 0 < R) :
    circleAverage (fun z ↦ f z / (z - c) ^ n) c R = iteratedDeriv n f c / n ! := by
  rw [circleAverage_eq_circleIntegral hR.ne.symm, inv_smul_eq_iff₀ (by simp)]
  convert hf.circleIntegral_one_div_sub_center_pow_smul hR n using 1
  · congr
    ext
    simp [pow_succ]
    field
  · simp; field

lemma circleAverage_fun_conj (hf : CircleIntegrable f c R) :
    circleAverage (fun z ↦ conj (f z)) c R = conj (circleAverage f c R) :=
  conjCLE.toContinuousLinearMap.circleAverage_comp_comm hf

private lemma circleAverage_conj_div_sub_pow_eq_zero (hR : 0 < R)
    (hf : DiffContOnCl ℂ f (ball c R)) (hn : n ≠ 0) :
    circleAverage (fun z ↦ conj (f z) / (z - c) ^ n) c R = 0 := by
  calc
  _ = circleAverage (fun z ↦ (1 / ((R : ℂ) ^ 2) ^ n) • conj (f z * (z - c) ^ n)) c R := by
    refine circleAverage_congr_sphere fun z hz ↦ ?_
    simp only [map_mul, map_pow, smul_eq_mul]
    suffices conj (z - c) = R ^ 2 / (z - c) by
      rw [this, div_pow]
      field [pow_ne_zero _ (ofReal_ne_zero.mpr hR.ne')]
    simp only [abs_of_pos hR, mem_sphere_iff_norm] at hz
    rw [eq_div_iff (fun _ ↦ (by simp_all)), mul_comm, mul_conj, normSq_eq_norm_sq, hz, ofReal_pow]
  _ = (1 / ((R : ℂ) ^ 2) ^ n) * circleAverage (fun z ↦ conj (f z * (z - c) ^ n)) c R := by
    rw [circleAverage_fun_smul, smul_eq_mul]
  _ = (1 / ((R : ℂ) ^ 2) ^ n) * conj (circleAverage (fun z ↦ f z * (z - c) ^ n) c R) := by
    rw [circleAverage_fun_conj]
    refine ContinuousOn.circleIntegrable hR.le ?_
    exact (hf.continuousOn_ball.mono sphere_subset_closedBall).mul (by fun_prop)
  _ = _ := by
    rw [DiffContOnCl.circleAverage, sub_self, zero_pow hn, mul_zero, map_zero, mul_zero]
    rw [abs_of_pos hR]
    exact DiffContOnCl.mk_ball (hf.differentiableOn.mul (by fun_prop))
      (hf.continuousOn_ball.mul (by fun_prop))

private lemma circleAverage_const_div_sub_pow_eq_zero (a : ℂ) (hR : 0 < R) (hn : n ≠ 0) :
    circleAverage (fun z ↦ a / (z - c) ^ n) c R = 0 := by
  convert circleAverage_eq_iteratedDeriv_div_factorial diffContOnCl_const hR
  simp [iteratedDeriv_const, hn]

private lemma iteratedDeriv_div_factorial_eq_circleAverage_re (M : ℝ)
    (hf : DiffContOnCl ℂ f (ball c R)) (hR : 0 < R) (hn : n ≠ 0) :
    iteratedDeriv n f c / n ! 
      = circleAverage (fun z ↦ ((2 * ((f z).re - M) : ℝ)) / (z - c) ^ n) c R := by
  simp only [mul_sub, ofReal_sub, ← add_conj, add_div, sub_div]
  have cont : ContinuousOn f (sphere c R) := hf.continuousOn_ball.mono sphere_subset_closedBall
  have ne_zero : ∀ x ∈ sphere c R, (x - c) ^ n ≠ 0 := by
    exact fun x hx ↦ pow_ne_zero _ fun h ↦ (by simp_all)
  rw [circleAverage_fun_sub, circleAverage_fun_add,
    circleAverage_eq_iteratedDeriv_div_factorial hf hR,
    circleAverage_conj_div_sub_pow_eq_zero hR hf hn,
    circleAverage_const_div_sub_pow_eq_zero _ hR hn, sub_zero, add_zero]
  all_goals exact ContinuousOn.circleIntegrable hR.le (by fun_prop)

lemma circleAverage_fun_re (hf : CircleIntegrable f c R) :
    circleAverage (fun z ↦ (f z).re) c R = (circleAverage f c R).re :=
  reCLM.circleAverage_comp_comm hf


theorem norm_iteratedDeriv_le_of_re_le_sphere (hR : 0 < R)
    (hf : DiffContOnCl ℂ f (ball c R)) (hf0 : f c = 0)
    (hM : ∀ z ∈ sphere c R, (f z).re ≤ M) (hn : n ≠ 0) :
    ‖iteratedDeriv n f c / (n !)‖ ≤ 2 * M / R ^ n := by
  grw [iteratedDeriv_div_factorial_eq_circleAverage_re M hf hR hn,
    norm_circleAverage_le_circleAverage_norm]
  apply le_of_eq
  simp only [norm_div, norm_pow, norm_real, Real.norm_eq_abs]
  have hRabs : |R| = R := abs_of_pos hR
  have hfs : ContinuousOn f (sphere c R) := hf.continuousOn_ball.mono sphere_subset_closedBall
  trans circleAverage (fun z => (2 / R ^ n) • (M - (f z).re)) c R
  · refine circleAverage_congr_sphere fun z hz ↦ ?_
    rw [hRabs] at hz
    rw [abs_of_nonpos (by grind)]
    simp [mem_sphere_iff_norm.mp hz, smul_eq_mul]
    ring
  · rw [← hRabs] at hf
    rw [circleAverage_fun_smul, smul_eq_mul,
      circleAverage_fun_sub (circleIntegrable_const M c R)
        (ContinuousOn.circleIntegrable hR.le (by fun_prop)),
      circleAverage_const,
      circleAverage_fun_re (hfs.circleIntegrable hR.le), 
      hf.circleAverage, hf0, zero_re]
    ring

/-- The bound on the derivatives at the centre, assuming only that `f` is holomorphic on the open
disc and that `Re f ≤ M` there : apply the previous estimate on the discs of radius `R' < R` and
let `R'` tend to `R`. -/
theorem norm_iteratedDeriv_le_of_re_le (hR : 0 < R)
    (hf : DifferentiableOn ℂ f (ball c R)) (hf0 : f c = 0)
    (hM : ∀ z ∈ ball c R, (f z).re ≤ M) :
    ‖iteratedDeriv n f c / (n !)‖ ≤ 2 * M / R ^ n := by
  by_cases! hn : n = 0
  · specialize hM c (mem_ball_self hR)
    simp_all
  refine ge_of_tendsto (f := fun R' : ℝ => 2 * M / R' ^ n) (x := 𝓝[<] R)
    (((continuousAt_const.div (by fun_prop) (by positivity)).tendsto).mono_left
      nhdsWithin_le_nhds) ?_
  filter_upwards [self_mem_nhdsWithin, eventually_nhdsWithin_of_eventually_nhds
    (eventually_gt_nhds hR)] with R' hR'R hR'0
  have hsub : closedBall c R' ⊆ ball c R := closedBall_subset_ball hR'R
  exact norm_iteratedDeriv_le_of_re_le_sphere hR'0 (hf.diffContOnCl_ball hsub) hf0
    (fun z hz => hM z (hsub (sphere_subset_closedBall hz))) hn

lemma hasSum_taylorSeries_on_ball_of_eq_zero (hf : DifferentiableOn ℂ f (ball c R))
    (hf0 : f c = 0) (hz : z ∈ ball c R) :
    HasSum (fun n : ℕ ↦ ((n + 1) ! : ℂ)⁻¹ • (z - c) ^ (n + 1) • iteratedDeriv (n + 1) f c)
      (f z) := by
  simpa [hf0] using (hasSum_nat_add_iff' 1).mpr (hasSum_taylorSeries_on_ball
    hf hz)

lemma hasSum_taylorSeries_deriv_on_ball (hf : DifferentiableOn ℂ f (ball c R))
    (hz : z ∈ ball c R) :
    HasSum (fun n : ℕ => ((n ! : ℂ))⁻¹ • (z - c) ^ n • iteratedDeriv (n + 1) f c) (deriv f z) := by
  simpa only [← iteratedDeriv_succ'] using hasSum_taylorSeries_on_ball (hf.deriv isOpen_ball) hz

theorem norm_le_of_re_le (hR : 0 < R)
    (hf : DifferentiableOn ℂ f (ball c R)) (hf0 : f c = 0)
    (hM : ∀ w ∈ ball c R, (f w).re ≤ M) (hz : z ∈ ball c R) :
    ‖f z‖ ≤ 2 * M * ‖z - c‖ / (R - ‖z - c‖) := by
  have hsum := hasSum_taylorSeries_on_ball_of_eq_zero hf hf0 hz
  simp only [mem_ball, dist_eq_norm_sub] at hz
  convert hsum.norm_le_of_bounded ((hasSum_geometric_of_lt_one (by positivity)
    ((div_lt_one hR).mpr hz)).mul_left (2 * M * (‖z - c‖ / R))) fun n ↦ _
  · field
  · simp only [smul_eq_mul]
    rw [mul_comm, mul_assoc, norm_mul, norm_pow]
    calc
    _ = ‖iteratedDeriv (n + 1) f c / ((n + 1) !)‖ * ‖z - c‖ ^ (n + 1) := by field_simp
    _ ≤ _ := by
      grw [norm_iteratedDeriv_le_of_re_le hR hf hf0 hM]
      exact le_of_eq (by ring)

/-- **Borel-Carathéodory theorem for the derivative**: under the hypotheses of `norm_le_of_re_le`,
the derivative of `f` on the disc of radius `r < R` is bounded by `2 * R * M / (R - r) ^ 2`. -/
theorem norm_deriv_le_of_re_le (hR : 0 < R)
    (hf : DifferentiableOn ℂ f (ball c R)) (hf0 : f c = 0)
    (hM : ∀ w ∈ ball c R, (f w).re ≤ M) (hz : z ∈ ball c R) :
    ‖deriv f z‖ ≤ 2 * R * M / (R - ‖z - c‖) ^ 2 := by
  have hgeo : HasSum (fun n : ℕ => 2 * M / R * (((n : ℝ) + 1) * (‖z - c‖ / R) ^ n))
      (2 * R * M / (R - ‖z - c‖) ^ 2) := by
    convert! (hasSum_choose_mul_geometric_of_norm_lt_one 1 (r := (‖z - c‖ / R))
      ?_).mul_left (2 * M / R) using 1
    · simp
    · grind
    · rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      simp only [mem_ball, dist_eq_norm_sub] at hz
      bound
  grw [(hasSum_taylorSeries_deriv_on_ball hf hz).norm_le_of_bounded hgeo fun n ↦ ?_]
  have hfacsucc : (((n + 1)! : ℝ)) = ((n : ℝ) + 1) * (n ! : ℝ) := by
    rw [Nat.factorial_succ]; push_cast; ring
  rw [norm_smul, norm_smul, norm_inv, Complex.norm_natCast, norm_pow, div_pow]
  calc
  _ = ‖z - c‖ ^ n * (n + 1) * (‖iteratedDeriv (n + 1) f c‖ / (n + 1) !) := by
    rw [hfacsucc]
    field
  _ = ‖z - c‖ ^ n * (n + 1) * (‖iteratedDeriv (n + 1) f c / ((n + 1) !)‖) := by simp
  _ ≤ _ := by
    grw [norm_iteratedDeriv_le_of_re_le hR hf hf0 hM]
    exact le_of_eq (by field)

section SchwarzTransform

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
  gcongr
  rw [← norm_one (α := ℂ)]; exact norm_sub_le_norm_add 1 w

/-- If `z.re ≤ M`, then `‖z‖ ≤ ‖2M - z‖`. This shows that the Schwarz transform
`z ↦ z / (2M - z)` has numerator smaller than denominator when the real part is bounded by M -/
lemma norm_le_norm_two_mul_sub (_ : 0 < M) (_ : z.re ≤ M) : ‖z‖ ≤ ‖2 * M - z‖ := by
  rw [← sq_le_sq₀ (by positivity) (by positivity)]
  suffices z.re * z.re ≤ (2 * M - z.re) * (2 * M - z.re) by simpa [Complex.sq_norm, normSq_apply]
  nlinarith

/-- Application of the Schwarz lemma to the transformed function. If `f` is differentiable on
the ball, maps into `{z | z.re ≤ M}`, and satisfies `f 0 = 0`, then the Schwarz transform
satisfies the bound from the Schwarz lemma. -/
lemma schwarz_applied (hM : 0 < M) (hf : DifferentiableOn ℂ f (ball 0 R))
    (hf₁ : Set.MapsTo f (ball 0 R) {z | z.re ≤ M}) (hz : z ∈ ball 0 R) (hf₂ : f 0 = 0) :
    ‖f z / (2 * M - f z)‖ ≤ (1 / R) * ‖z‖ := by
  rw [← dist_zero_right, ← dist_zero_right]
  nth_rw 1 [← zero_div (2 * M - f 0), ← hf₂]
  apply dist_le_div_mul_dist_of_mapsTo_ball (R₂ := 1) ?_ (fun x hx ↦ ?_) hz
  · apply hf.div (hf.const_sub _) fun x hx h ↦ ?_
    have := sub_eq_zero.mp h ▸ hf₁ hx
    aesop
  · simpa [hf₂] using
      div_le_one_of_le₀ (norm_le_norm_two_mul_sub hM (hf₁ hx)) (by positivity)

end SchwarzTransform

section BorelCaratheodory

/-- **Borel-Carathéodory theorem** for functions vanishing at the origin.

If `f` is analytic on the open ball `‖z‖ < R`, satisfies `(f z).re ≤ M` for all such `z`,
and `f 0 = 0`, then `‖f z‖ ≤ 2 * M * ‖z‖ / (R - ‖z‖)` for all `‖z‖ < R`. -/
public theorem borelCaratheodory_zero (hM : 0 < M) (hf : DifferentiableOn ℂ f (ball 0 R))
    (hf₁ : Set.MapsTo f (ball 0 R) {z | z.re ≤ M}) (hR : 0 < R) (hz : z ∈ ball 0 R)
    (hf₂ : f 0 = 0) : ‖f z‖ ≤ 2 * M * ‖z‖ / (R - ‖z‖) := by
  set w := f z / (2 * M - f z)
  have hzR : ‖z‖ < R := mem_ball_zero_iff.mp hz
  have hwR := by simpa only [dist_zero_right, div_one, mul_comm (1 / R), mul_one_div]
    using schwarz_applied hM hf hf₁ hz hf₂
  have h_denom : 2 * M - f z ≠ 0 := sub_ne_zero_of_ne (fun h => by simpa [← h, hM] using hf₁ hz)
  calc ‖f z‖
    _ = ‖2 * M * w / (1 + w)‖ := by rw [eq_mul_div_one_add_of_eq_div_sub hM.ne' h_denom rfl]
    _ ≤ 2 * M * ‖w‖ / (1 - ‖w‖) := by
      simp only [norm_div, norm_mul, norm_ofNat, norm_real, Real.norm_eq_abs, abs_of_pos hM]
      gcongr
      · linarith [hwR.trans_lt ((div_lt_one₀ hR).mpr hzR)]
      · simpa using norm_sub_le_norm_add 1 w
    _ = 2 * M * (‖w‖ / (1 - ‖w‖)) := by ring
    _ ≤ 2 * M * (‖z‖ / R / (1 - ‖z‖ / R)) := by gcongr; simpa [div_lt_one hR]
    _ = 2 * M * ‖z‖ / (R - ‖z‖) := by field_simp

/-- **Borel-Carathéodory theorem**.

If `f` is analytic on the open ball `‖z‖ < R` and satisfies `(f z).re ≤ M` for all such `z`,
then `‖f z‖ ≤ 2 * M * ‖z‖ / (R - ‖z‖) + ‖f 0‖ * (R + ‖z‖) / (R - ‖z‖)` for all `‖z‖ < R`. -/
public theorem borelCaratheodory (hM : 0 < M) (hf : DifferentiableOn ℂ f (ball 0 R))
    (hf₁ : Set.MapsTo f (ball 0 R) {z | z.re ≤ M}) (hR : 0 < R) (hz : z ∈ ball 0 R) :
    ‖f z‖ ≤ 2 * M * ‖z‖ / (R - ‖z‖) + ‖f 0‖ * (R + ‖z‖) / (R - ‖z‖) := by
  have hfz : ‖f z - f 0‖ ≤ 2 * (M + ‖f 0‖) * ‖z‖ / (R - ‖z‖) := by
    apply borelCaratheodory_zero (by positivity) (by fun_prop) ?_ hR hz (by simp)
    intro x hx
    simp only [Set.mem_ofPred_eq, sub_re]
    calc (f x).re - (f 0).re ≤ M - (f 0).re := by gcongr; exact hf₁ hx
      _ ≤ M + ‖f 0‖ := by linarith [neg_le_abs (f 0).re, abs_re_le_norm (f 0)]
  have h_denom_ne : R - ‖z‖ ≠ 0 := by linarith [mem_ball_zero_iff.mp hz]
  calc ‖f z‖ ≤ ‖f z - f 0‖ + ‖f 0‖ := norm_le_norm_sub_add _ _
    _ ≤ 2 * (M + ‖f 0‖) * ‖z‖ / (R - ‖z‖) + ‖f 0‖ := by gcongr
    _ = 2 * M * ‖z‖ / (R - ‖z‖) + ‖f 0‖ * (R + ‖z‖) / (R - ‖z‖) := by field_simp; ring

end BorelCaratheodory

end Complex
