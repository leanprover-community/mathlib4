/-
Copyright (c) 2026 E. S. Markov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: E. S. Markov
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

/-!
# Second-Order Finite Differences and Convergence to Second Derivatives

This file defines backward and central second-order finite-difference operators on real functions
and proves their convergence to the second derivative `f''` as the step size `h → 0` (`h ≠ 0`),
as well as exact quadratic identities.

## Main definitions

* `backwardSecondDiff f t h`: the backward second-order difference quotient
  `(f t - 2 * f (t - h) + f (t - 2 * h)) / h ^ 2`.
* `centralSecondDiff f t h`: the central second-order difference quotient
  `(f (t + h) - 2 * f t + f (t - h)) / h ^ 2`.

## Main results

* `tendsto_backwardSecondDiff`: for any function `f : ℝ → ℝ` differentiable near `t` whose
  derivative `deriv f` is differentiable at `t`, `backwardSecondDiff f t h → f''` as `h → 0`
  (`h ≠ 0`).
* `tendsto_centralSecondDiff`: under the same hypotheses,
  `centralSecondDiff f t h → f''` as `h → 0` (`h ≠ 0`).
-/

@[expose] public section

noncomputable section

open Filter Metric Topology Set

section SecondFiniteDifference

/-- Backward second-order finite-difference operator `(f(t) - 2 f(t - h) + f(t - 2h)) / h²`. -/
def backwardSecondDiff (f : ℝ → ℝ) (t h : ℝ) : ℝ :=
  (f t - 2 * f (t - h) + f (t - 2 * h)) / h ^ 2

/-- Central second-order finite-difference operator `(f(t + h) - 2 f(t) + f(t - h)) / h²`. -/
def centralSecondDiff (f : ℝ → ℝ) (t h : ℝ) : ℝ :=
  (f (t + h) - 2 * f t + f (t - h)) / h ^ 2

/-- Algebraic identity for `backwardSecondDiff` on quadratic polynomials. -/
theorem backwardSecondDiff_quadratic (a b c t h : ℝ) (hh : h ≠ 0) :
    backwardSecondDiff (fun x => a * x ^ 2 + b * x + c) t h = 2 * a := by
  dsimp [backwardSecondDiff]
  field_simp
  ring

/-- Algebraic identity for `centralSecondDiff` on quadratic polynomials. -/
theorem centralSecondDiff_quadratic (a b c t h : ℝ) (hh : h ≠ 0) :
    centralSecondDiff (fun x => a * x ^ 2 + b * x + c) t h = 2 * a := by
  dsimp [centralSecondDiff]
  field_simp
  ring

/-- Helper lemma: first-order Peano remainder for a function differentiable at `t`. -/
lemma hasDerivAt_remainder_bound {g : ℝ → ℝ} {t g' : ℝ} (hg : HasDerivAt g g' t) :
    ∀ ε > 0, ∀ᶠ h in 𝓝 0, |g (t + h) - g t - g' * h| ≤ ε * |h| := by
  intro ε hε
  have h_littleO := hg.isLittleO
  rw [Asymptotics.isLittleO_iff] at h_littleO
  have h_ev := h_littleO hε
  rw [Metric.eventually_nhds_iff] at h_ev ⊢
  rcases h_ev with ⟨δ, hδ, h_bound⟩
  refine ⟨δ, hδ, fun h hh => ?_⟩
  have hx : dist (t + h) t < δ := by
    rw [dist_eq_norm, add_sub_cancel_left]
    simpa [dist_eq_norm] using hh
  have h1 := h_bound hx
  rw [add_sub_cancel_left, Real.norm_eq_abs, Real.norm_eq_abs, smul_eq_mul, mul_comm h g'] at h1
  exact h1
/-- Second-order Peano expansion for a function `f` differentiable on a neighborhood of `t`
with second derivative `f''` at `t`. -/
lemma second_order_peano_bound {f : ℝ → ℝ} {t f'' : ℝ}
    (hf_nhds : ∀ᶠ x in 𝓝 t, DifferentiableAt ℝ f x)
    (hf'' : HasDerivAt (deriv f) f'' t) :
    ∀ ε > 0, ∀ᶠ h in 𝓝 0,

      |f (t + h) - f t - deriv f t * h - (1 / 2) * f'' * h ^ 2| ≤ ε * h ^ 2 := by
  intro ε hε
  have h_rem := hasDerivAt_remainder_bound hf'' ε hε
  rw [Metric.eventually_nhds_iff] at hf_nhds h_rem ⊢
  rcases hf_nhds with ⟨δ₁, hδ₁, hdiff⟩
  rcases h_rem with ⟨δ₂, hδ₂, hrem⟩
  refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, fun h hh => ?_⟩
  have hh₁ : |h| < δ₁ := by
    have := lt_of_lt_of_le hh (min_le_left _ _)
    simpa [dist_eq_norm] using this
  have hh₂ : |h| < δ₂ := by
    have := lt_of_lt_of_le hh (min_le_right _ _)
    simpa [dist_eq_norm] using this
  let φ : ℝ → ℝ := fun s => f (t + s) - f t - deriv f t * s - (1 / 2) * f'' * s ^ 2
  have hφ0 : φ 0 = 0 := by simp [φ]
  have hφ_deriv : ∀ s : ℝ, |s| ≤ |h| →
      HasDerivAt φ (deriv f (t + s) - deriv f t - f'' * s) s := by
    intro s hs_abs
    have ht_s : dist (t + s) t < δ₁ := by
      rw [dist_eq_norm, add_sub_cancel_left, Real.norm_eq_abs]
      exact lt_of_le_of_lt hs_abs hh₁
    have hf_s : HasDerivAt f (deriv f (t + s)) (t + s) := (hdiff ht_s).hasDerivAt
    have h_comp : HasDerivAt (fun u => f (t + u)) (deriv f (t + s)) s :=
      (hf_s.comp s ((hasDerivAt_id s).const_add t)).congr_deriv (mul_one _)
    have h_lin : HasDerivAt (fun u => deriv f t * u) (deriv f t) s := by
      simpa using (hasDerivAt_id s).const_mul (deriv f t)
    have h_quad : HasDerivAt (fun u => (1 / 2) * f'' * u ^ 2) (f'' * s) s := by
      have hsq : HasDerivAt (fun u : ℝ => u ^ 2) (2 * s) s := by
        simpa using (hasDerivAt_pow 2 s)
      convert hsq.const_mul ((1 / 2) * f'') using 1
      ring
    exact ((h_comp.sub_const (f t)).sub h_lin).sub h_quad
  have h_deriv_bound : ∀ s : ℝ, |s| ≤ |h| → |deriv f (t + s) - deriv f t - f'' * s| ≤ ε * |h| := by
    intro s hs_abs
    have hs_d₂ : dist s 0 < δ₂ := by
      rw [dist_zero_right, Real.norm_eq_abs]
      exact lt_of_le_of_lt hs_abs hh₂
    have h1 := hrem hs_d₂
    exact h1.trans (mul_le_mul_of_nonneg_left hs_abs hε.le)
  have h_norm_bound : ‖φ h - φ 0‖ ≤ (ε * |h|) * ‖h - 0‖ := by
    refine Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
      (f := φ) (f' := fun s => deriv f (t + s) - deriv f t - f'' * s)
      (s := closedBall (0 : ℝ) |h|) (C := ε * |h|) ?_ ?_ (convex_closedBall (0 : ℝ) |h|)
      (by simp [abs_nonneg]) (by simp)
    · intro s hs
      rw [mem_closedBall, dist_zero_right, Real.norm_eq_abs] at hs
      exact (hφ_deriv s hs).hasDerivWithinAt
    · intro s hs
      rw [mem_closedBall, dist_zero_right, Real.norm_eq_abs] at hs
      rw [Real.norm_eq_abs]
      exact h_deriv_bound s hs
  rw [hφ0, sub_zero, sub_zero, Real.norm_eq_abs, Real.norm_eq_abs] at h_norm_bound
  calc |φ h| ≤ ε * |h| * |h| := h_norm_bound
    _ = ε * |h| ^ 2 := by ring
    _ = ε * h ^ 2 := by rw [sq_abs]

/-- **Convergence of backward second-order finite differences:**
if `f : ℝ → ℝ` is differentiable near `t` and `deriv f` is differentiable at `t`,
then `backwardSecondDiff f t h → f''` as `h → 0` (`h ≠ 0`). -/
theorem tendsto_backwardSecondDiff {f : ℝ → ℝ} {t f'' : ℝ}
    (hf_nhds : ∀ᶠ x in 𝓝 t, DifferentiableAt ℝ f x)
    (hf'' : HasDerivAt (deriv f) f'' t) :
    Tendsto (backwardSecondDiff f t) (𝓝[≠] 0) (𝓝 f'') := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hε12 : 0 < ε / 12 := by linarith
  rcases Metric.eventually_nhds_iff.mp (second_order_peano_bound hf_nhds hf'' (ε / 12) hε12) with
    ⟨δ, hδ, hP⟩
  rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff]
  refine ⟨δ / 2, half_pos hδ, fun h hh hh_ne => ?_⟩
  have hh_abs : |h| < δ / 2 := by simpa [dist_zero_right, Real.norm_eq_abs] using hh
  have hd1 : dist (-h) 0 < δ := by
    rw [dist_zero_right, Real.norm_eq_abs, abs_neg]
    linarith
  have hd2 : dist (-2 * h) 0 < δ := by
    rw [dist_zero_right, Real.norm_eq_abs, abs_mul]
    have h2 : |(-2 : ℝ)| = 2 := by norm_num
    rw [h2]
    linarith
  have h1 := hP hd1
  have h2 := hP hd2
  have hh2_pos : 0 < h ^ 2 := sq_pos_of_ne_zero hh_ne
  have h_eps_pos : 0 < ε * h ^ 2 := mul_pos hε hh2_pos
  rw [Real.dist_eq, backwardSecondDiff]
  have h_num : (f t - 2 * f (t - h) + f (t - 2 * h)) - f'' * h ^ 2 =
      -2 * (f (t + (-h)) - f t - deriv f t * (-h) - (1 / 2) * f'' * (-h) ^ 2) +
        (f (t + (-2 * h)) - f t - deriv f t * (-2 * h) - (1 / 2) * f'' * (-2 * h) ^ 2) := by
    have ht1 : t + (-h) = t - h := by ring
    have ht2 : t + (-2 * h) = t - 2 * h := by ring
    rw [ht1, ht2]
    ring
  have h_alg : (f t - 2 * f (t - h) + f (t - 2 * h)) / h ^ 2 - f'' =
      (-2 * (f (t + (-h)) - f t - deriv f t * (-h) - (1 / 2) * f'' * (-h) ^ 2) +
        (f (t + (-2 * h)) - f t - deriv f t * (-2 * h) -
          (1 / 2) * f'' * (-2 * h) ^ 2)) / h ^ 2 := by
    rw [← h_num, sub_div, mul_div_cancel_right₀ f'' hh2_pos.ne']
  rw [h_alg, abs_div, abs_of_pos hh2_pos, div_lt_iff₀ hh2_pos]
  have h_tri : |-2 * (f (t + (-h)) - f t - deriv f t * (-h) - (1 / 2) * f'' * (-h) ^ 2) +
        (f (t + (-2 * h)) - f t - deriv f t * (-2 * h) -
          (1 / 2) * f'' * (-2 * h) ^ 2)| ≤
      2 * |f (t + (-h)) - f t - deriv f t * (-h) - (1 / 2) * f'' * (-h) ^ 2| +
        |f (t + (-2 * h)) - f t - deriv f t * (-2 * h) -
          (1 / 2) * f'' * (-2 * h) ^ 2| := by
    calc |-2 * (f (t + (-h)) - f t - deriv f t * (-h) - (1 / 2) * f'' * (-h) ^ 2) +
          (f (t + (-2 * h)) - f t - deriv f t * (-2 * h) -
            (1 / 2) * f'' * (-2 * h) ^ 2)|
      _ ≤ |-2 * (f (t + (-h)) - f t - deriv f t * (-h) - (1 / 2) * f'' * (-h) ^ 2)| +
            |f (t + (-2 * h)) - f t - deriv f t * (-2 * h) -
              (1 / 2) * f'' * (-2 * h) ^ 2| :=
          abs_add_le _ _
      _ = 2 * |f (t + (-h)) - f t - deriv f t * (-h) - (1 / 2) * f'' * (-h) ^ 2| +
            |f (t + (-2 * h)) - f t - deriv f t * (-2 * h) -
              (1 / 2) * f'' * (-2 * h) ^ 2| := by
          rw [abs_mul]
          norm_num
  have h_sum : 2 * ((ε / 12) * (-h) ^ 2) + (ε / 12) * (-2 * h) ^ 2 = (ε / 2) * h ^ 2 := by ring
  linarith

/-- **Convergence of central second-order finite differences:**
if `f : ℝ → ℝ` is differentiable near `t` and `deriv f` is differentiable at `t`,
then `centralSecondDiff f t h → f''` as `h → 0` (`h ≠ 0`). -/
theorem tendsto_centralSecondDiff {f : ℝ → ℝ} {t f'' : ℝ}
    (hf_nhds : ∀ᶠ x in 𝓝 t, DifferentiableAt ℝ f x)
    (hf'' : HasDerivAt (deriv f) f'' t) :
    Tendsto (centralSecondDiff f t) (𝓝[≠] 0) (𝓝 f'') := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hε4 : 0 < ε / 4 := by linarith
  rcases Metric.eventually_nhds_iff.mp (second_order_peano_bound hf_nhds hf'' (ε / 4) hε4) with
    ⟨δ, hδ, hP⟩
  rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff]
  refine ⟨δ, hδ, fun h hh hh_ne => ?_⟩
  have hd_neg : dist (-h) 0 < δ := by
    simpa [dist_zero_right, Real.norm_eq_abs] using hh
  have h1 := hP hh
  have h2 := hP hd_neg
  have hh2_pos : 0 < h ^ 2 := sq_pos_of_ne_zero hh_ne
  have h_eps_pos : 0 < ε * h ^ 2 := mul_pos hε hh2_pos
  rw [Real.dist_eq, centralSecondDiff]
  have h_num : (f (t + h) - 2 * f t + f (t - h)) - f'' * h ^ 2 =
      (f (t + h) - f t - deriv f t * h - (1 / 2) * f'' * h ^ 2) +
        (f (t + (-h)) - f t - deriv f t * (-h) - (1 / 2) * f'' * (-h) ^ 2) := by
    have ht1 : t + (-h) = t - h := by ring
    rw [ht1]
    ring
  have h_alg : (f (t + h) - 2 * f t + f (t - h)) / h ^ 2 - f'' =
      ((f (t + h) - f t - deriv f t * h - (1 / 2) * f'' * h ^ 2) +
        (f (t + (-h)) - f t - deriv f t * (-h) - (1 / 2) * f'' * (-h) ^ 2)) / h ^ 2 := by
    rw [← h_num, sub_div, mul_div_cancel_right₀ f'' hh2_pos.ne']
  rw [h_alg, abs_div, abs_of_pos hh2_pos, div_lt_iff₀ hh2_pos]
  have h_tri := abs_add_le
    (f (t + h) - f t - deriv f t * h - (1 / 2) * f'' * h ^ 2)
    (f (t + (-h)) - f t - deriv f t * (-h) - (1 / 2) * f'' * (-h) ^ 2)
  have h_sum : (ε / 4) * h ^ 2 + (ε / 4) * (-h) ^ 2 = (ε / 2) * h ^ 2 := by ring
  linarith

end SecondFiniteDifference
