/-
Copyright (c) 2026 Maksym Radziwill. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maksym Radziwill, Alastair Irving
-/

module

public import Mathlib.Analysis.Complex.MeanValue
public import Mathlib.Analysis.Complex.TaylorSeries

/-!
# Borel-Carathéodory theorem

This file proves the Borel-Carathéodory theorem: for any function `f` analytic on the
open ball `‖z - c‖ < R` such that `Re(f z) ≤ M` for all `‖z - c‖ < R` and `f c = 0`, we have
`‖f z‖ ≤ 2 * M * ‖z - c‖ / (R - ‖z - c‖)`
and `‖f' z‖ ≤ 2 * R * M / (R - ‖z - c‖) ^ 2`.

## Main results

* `Complex.BorelCaratheodory.norm_iteratedDeriv_le_of_re_le_sphere` and
  `Complex.BorelCaratheodory.norm_iteratedDeriv_le_of_re_le` bound the derivatives at the center.
* `Complex.BorelCaratheodory.norm_le_of_re_le_of_eq_zero` bounds `f` given a bound on its real part
  and `f c = 0`.
* `Complex.BorelCaratheodory.norm_le_of_re_le` bounds `f` given a bound on its real part.
* `Complex.BorelCaratheodory.norm_deriv_le_of_re_le_of_eq_zero` bounds `f'` given a bound on `re f`.

## Implementation Notes

We first estimate all the derivatives of `f` at `c` using an identity for them
using circle averages. The estimates for `f` and `f'` then follow from Taylor series expansions.

## Tags

complex analysis, Borel, Carathéodory, analytic function, growth bound
-/

open Metric Real Topology

namespace Complex

variable {f : ℂ → ℂ} {M R : ℝ} {z c : ℂ} {n : ℕ}

namespace BorelCaratheodory

open scoped Nat ComplexConjugate

/- Replacing `f` by `conj f` in Cauchy's formula gives an integral which evaluates to `0`.
The proof expresses the average as the conjugate of an average of a differentiable function. -/
lemma circleAverage_one_div_sub_center_pow_smul_conj (hR : 0 < R)
    (hf : DiffContOnCl ℂ f (ball c R)) (hn : n ≠ 0) :
    circleAverage (fun z ↦ (1 / (z - c) ^ n) • conj (f z)) c R = 0 := by
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

/- Main identity for the higher derivatives at the center. -/
variable (M) in
lemma iteratedDeriv_div_factorial_eq_circleAverage_re
    (hf : DiffContOnCl ℂ f (ball c R)) (hR : 0 < R) (hn : n ≠ 0) :
    iteratedDeriv n f c / n !
      = circleAverage (fun z ↦ (1 / (z - c) ^ n) • ((2 * ((f z).re - M) : ℝ) : ℂ)) c R := by
  simp only [mul_sub, smul_sub, ofReal_sub, ← add_conj, smul_add, smul_sub]
  have cont : ContinuousOn f (sphere c R) := hf.continuousOn_ball.mono sphere_subset_closedBall
  have ne_zero : ∀ x ∈ sphere c R, (x - c) ^ n ≠ 0 := fun x hx ↦ pow_ne_zero _ fun h ↦ (by simp_all)
  rw [circleAverage_fun_sub, circleAverage_fun_add,
    hf.circleAverage_one_div_sub_center_pow_smul n hR,
    circleAverage_one_div_sub_center_pow_smul_conj hR hf hn,
    diffContOnCl_const.circleAverage_one_div_sub_center_pow_smul n hR]
  · simp [iteratedDeriv_const, hn]
    field
  all_goals exact ContinuousOn.circleIntegrable hR.le (by fun_prop)

/-- **Borel-Carathéodory theorem:** estimates the derivatives of a differentiable function at the
center of a ball given a bound for its real part on the sphere. -/
public theorem norm_iteratedDeriv_le_of_re_le_sphere (hR : 0 < R)
    (hf : DiffContOnCl ℂ f (ball c R)) (hf0 : f c = 0)
    (hM : (sphere c R).MapsTo f {z | z.re ≤ M}) :
    ‖iteratedDeriv n f c / (n !)‖ ≤ 2 * M / R ^ n := by
  by_cases! hn : n = 0
  · simp only [hn, iteratedDeriv_zero, Nat.factorial_zero, Nat.cast_one, div_one, norm_zero, hf0,
      pow_zero, Nat.ofNat_pos, mul_nonneg_iff_of_pos_left]
    have hfs := hf.continuousOn_ball.mono sphere_subset_closedBall
    rw [← abs_of_pos hR] at hf hM
    rw [← zero_re, ← hf0, ← hf.circleAverage, ← circleAverage_re (hfs.circleIntegrable hR.le)]
    exact circleAverage_mono_on_of_le_circle (ContinuousOn.circleIntegrable hR.le (by fun_prop)) hM
  grw [iteratedDeriv_div_factorial_eq_circleAverage_re M hf hR hn,
    norm_circleAverage_le_circleAverage_norm]
  apply le_of_eq
  simp only [norm_smul, norm_div, norm_pow, norm_real, Real.norm_eq_abs]
  have hRabs : |R| = R := abs_of_pos hR
  have hfs : ContinuousOn f (sphere c R) := hf.continuousOn_ball.mono sphere_subset_closedBall
  trans circleAverage (fun z ↦ (2 / R ^ n) • (M - (f z).re)) c R
  · refine circleAverage_congr_sphere fun z hz ↦ ?_
    rw [hRabs] at hz
    rw [abs_of_nonpos (by grind [hM hz])]
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

/-- **Borel-Carathéodory theorem:** estimates the derivatives of a differentiable function at the
center of a ball given a bound for its real part on that ball. -/
public theorem norm_iteratedDeriv_le_of_re_le (hR : 0 < R)
    (hf : DifferentiableOn ℂ f (ball c R)) (hf0 : f c = 0)
    (hM : (ball c R).MapsTo f {z | z.re ≤ M}) :
    ‖iteratedDeriv n f c / (n !)‖ ≤ 2 * M / R ^ n := by
  refine ge_of_tendsto (f := fun R' : ℝ ↦ 2 * M / R' ^ n) (x := 𝓝[<] R)
    (((continuousAt_const.div (by fun_prop) (by positivity)).tendsto).mono_left
      nhdsWithin_le_nhds) ?_
  filter_upwards [self_mem_nhdsWithin, eventually_nhdsWithin_of_eventually_nhds
    (eventually_gt_nhds hR)] with R' hR'R hR'0
  exact norm_iteratedDeriv_le_of_re_le_sphere hR'0
    (hf.diffContOnCl_ball (closedBall_subset_ball hR'R)) hf0
    (hM.mono_left (sphere_subset_ball hR'R))

/-- **Borel-Carathéodory theorem:** estimates a differentiable function on a ball which vanishes
at the center given a bound for its real part on that ball. -/
public theorem norm_le_of_re_le_of_eq_zero (hf : DifferentiableOn ℂ f (ball c R)) (hf0 : f c = 0)
    (hM : (ball c R).MapsTo f {z | z.re ≤ M}) (hz : z ∈ ball c R) :
    ‖f z‖ ≤ 2 * M * ‖z - c‖ / (R - ‖z - c‖) := by
  have hR := pos_of_mem_ball hz
  have hsum := hasSum_taylorSeries_on_ball_of_eq_zero hf hz hf0
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

/-- **Borel-Carathéodory theorem:** estimates a differentiable function on a ball given a bound for
its real part on that ball. -/
public theorem norm_le_of_re_le (hf : DifferentiableOn ℂ f (ball c R))
    (hM : (ball c R).MapsTo f {z | z.re ≤ M}) (hz : z ∈ ball c R) :
    ‖f z‖ ≤ 2 * M * ‖z - c‖ / (R - ‖z - c‖) + ‖f c‖ * (R + ‖z - c‖) / (R - ‖z - c‖) := by
  have hfz : ‖f z - f c‖ ≤ 2 * (M + ‖f c‖) * ‖z - c‖ / (R - ‖z - c‖) := by
    refine norm_le_of_re_le_of_eq_zero (hf.sub_const (f c)) (by simp) (fun x hx ↦ ?_) hz
    simp only [Set.mem_ofPred_eq, sub_re]
    calc _ ≤ M - (f c).re := by gcongr; exact hM hx
      _ ≤ _ := by linarith [neg_le_abs (f c).re, abs_re_le_norm (f c)]
  have h_denom_ne : R - ‖z - c‖ ≠ 0 := by linarith [mem_ball_iff_norm.mp hz]
  calc _ ≤ ‖f z - f c‖ + ‖f c‖ := norm_le_norm_sub_add _ _
    _ ≤ 2 * (M + ‖f c‖) * ‖z - c‖ / (R - ‖z - c‖) + ‖f c‖ := by gcongr
    _ = _ := by field

/-- **Borel-Carathéodory theorem for the derivative**: estimates the derivative of a differentiable
function on a ball which vanishes at the center given a bound on its real part on that ball. -/
public theorem norm_deriv_le_of_re_le_of_eq_zero
    (hf : DifferentiableOn ℂ f (ball c R)) (hf0 : f c = 0)
    (hM : (ball c R).MapsTo f {z | z.re ≤ M}) (hz : z ∈ ball c R) :
    ‖deriv f z‖ ≤ 2 * R * M / (R - ‖z - c‖) ^ 2 := by
  have hR := pos_of_mem_ball hz
  have hgeo : HasSum (fun n : ℕ ↦ 2 * M / R * (((n : ℝ) + 1) * (‖z - c‖ / R) ^ n))
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

end BorelCaratheodory

/-- **Borel-Carathéodory theorem** for functions vanishing at the origin.

If `f` is analytic on the open ball `‖z‖ < R`, satisfies `(f z).re ≤ M` for all such `z`,
and `f 0 = 0`, then `‖f z‖ ≤ 2 * M * ‖z‖ / (R - ‖z‖)` for all `‖z‖ < R`. -/
@[deprecated BorelCaratheodory.norm_le_of_re_le_of_eq_zero +typeChanged (since := "2026-10-17")]
public theorem borelCaratheodory_zero (hf : DifferentiableOn ℂ f (ball 0 R))
    (hf₁ : Set.MapsTo f (ball 0 R) {z | z.re ≤ M}) (hz : z ∈ ball 0 R)
    (hf₂ : f 0 = 0) : ‖f z‖ ≤ 2 * M * ‖z‖ / (R - ‖z‖) := by
  convert BorelCaratheodory.norm_le_of_re_le_of_eq_zero hf hf₂ hf₁ hz <;> ring

/-- **Borel-Carathéodory theorem**.

If `f` is analytic on the open ball `‖z‖ < R` and satisfies `(f z).re ≤ M` for all such `z`,
then `‖f z‖ ≤ 2 * M * ‖z‖ / (R - ‖z‖) + ‖f 0‖ * (R + ‖z‖) / (R - ‖z‖)` for all `‖z‖ < R`. -/
@[deprecated BorelCaratheodory.norm_le_of_re_le +typeChanged (since := "2026-10-17")]
public theorem borelCaratheodory (hf : DifferentiableOn ℂ f (ball 0 R))
    (hf₁ : Set.MapsTo f (ball 0 R) {z | z.re ≤ M}) (hz : z ∈ ball 0 R) :
    ‖f z‖ ≤ 2 * M * ‖z‖ / (R - ‖z‖) + ‖f 0‖ * (R + ‖z‖) / (R - ‖z‖) := by
  convert BorelCaratheodory.norm_le_of_re_le hf hf₁ hz <;> ring

end Complex
