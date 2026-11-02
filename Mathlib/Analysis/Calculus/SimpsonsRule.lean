/-
Copyright (c) 2026 Chan Kwan Ho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chan Kwan Ho
-/
module

public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Simpson's rule

This file defines Simpson's quadrature sum on a real interval
for numerical integration and also establishes the C^4 error bounds
following the proof from Suli & Mayers.

It proves
that the rule is exact for real polynomials of degree at most three and
establishes the classical error formula for functions that are four times
continuously differentiable on `ℝ`.

## Main definitions
* `simpsonSum`: Approximates the integral of `f` over `[a,b]`

## Main statements
* `simpsonSum_add`: Provide the additivity for SimpsonSum in its integrand.

* `simpsonSum_smul`: Provide the commutativity of scalar multiplication for SimpsonSum.

* `simpson_exact_of_degree_le_three`: Provide the simpsonSum is exact for any ℝ[x]
polynomial of degree ≤ 3.

* `simpson_error_estimation`: Upper bound for the approximation error.


## Proof idea

For the error formula, the proof centers the interval at its midpoint and
considers the error on symmetric subintervals. It subtracts a suitable
degree-five polynomial from this auxiliary error function, applies Rolle's
theorem repeatedly, and then applies the mean value theorem to obtain the
fourth-derivative remainder.

## References

* E. Suli and D. Mayers, *An Introduction to Numerical Analysis*.
-/
public section

open Polynomial

noncomputable section



/-- Computes the Simpson's rule quadrature sum for a function `f`
over the real interval `[a, b]`. -/
def simpsonSum (f : ℝ → ℝ) (a b : ℝ) : ℝ :=
  (b - a) / 6 * (f a + 4 * f ((a + b) / 2) + f b)

/-- Simpson's quadrature sum is additive in its integrand. -/
lemma simpsonSum_add (f g : ℝ → ℝ) (a b : ℝ) :
    simpsonSum (f + g) a b = simpsonSum f a b + simpsonSum g a b   := by
  dsimp [simpsonSum]
  ring

/-- Simpson's quadrature sum commutes with scalar multiplication. -/
lemma simpsonSum_smul (c : ℝ) (f : ℝ → ℝ) (a b : ℝ) :
  simpsonSum (fun x => c * f x) a b = c * simpsonSum f a b := by
  dsimp [simpsonSum]
  ring

private lemma integrable_term (c : ℝ) (n : ℕ) (a b : ℝ) :
    IntervalIntegrable (fun x => c * x ^ n) MeasureTheory.volume a b := by
  exact (continuous_const.mul (continuous_pow n)).intervalIntegrable a b

/-- Simpson's rule is exact for real polynomials of degree at most three. -/
theorem simpson_exact_of_degree_le_three (p : ℝ[X]) (hp : p.natDegree ≤ 3) (a b : ℝ) :
    ∫ x in a..b, p.eval x = simpsonSum (fun x => p.eval x) a b := by
  have h4 : p.natDegree < 4 := by omega
  dsimp [simpsonSum]
  simp_rw [p.eval_eq_sum_range' h4]
  rw [intervalIntegral.integral_finsetSum]
  · simp only [Finset.sum_range_succ, Finset.range_zero,
    Finset.sum_empty, zero_add, pow_zero, pow_one]
    repeat' rw [intervalIntegral.integral_const_mul]
    have h0 : ∫ x in a..b, (1 : ℝ) = b - a := by simp [intervalIntegral.integral_const]
    have h1 : ∫ x in a..b, x = (b ^ 2 - a ^ 2) / 2 := by simp [integral_id]
    have h2 : ∫ x in a..b, x ^ 2 = (b ^ 3 - a ^ 3) / 3 := by simp [integral_pow 2]; ring
    have h3 : ∫ x in a..b, x ^ 3 = (b ^ 4 - a ^ 4) / 4 := by simp [integral_pow 3]; ring
    rw [h0, h1, h2, h3]
    ring
  · intro i _
    exact integrable_term (p.coeff i) i a b

private def simpsonAuxG (f : ℝ → ℝ) (m : ℝ) (t : ℝ) : ℝ :=
  (∫ x in (m - t)..(m + t), f x) - (t / 3) * (f (m - t) + 4 * f m + f (m + t))

private lemma simpsonAuxG_zero (f : ℝ → ℝ) (m : ℝ) : simpsonAuxG f m 0 = 0 := by
  simp[simpsonAuxG]

private lemma deriv_int_symm (f : ℝ → ℝ) (m t : ℝ) (hf : Continuous f) :
    HasDerivAt (fun t => ∫ x in (m-t)..(m+t), f x)
      (f (m + t) + f (m - t)) t := by
  have h_FTC (u : ℝ) : HasDerivAt (fun s => ∫ x in m..s, f x) (f u) u :=
    intervalIntegral.integral_hasDerivAt_right
      (hf.intervalIntegrable _ _ )
      (hf.stronglyMeasurableAtFilter _ _ )
      hf.continuousAt
  have hR : HasDerivAt (fun t => ∫ x in m..(m + t), f x) (f (m + t)) t := by
    simpa [Function.comp_def] using (h_FTC (m + t)).comp t ((hasDerivAt_id t).const_add m)
  have hL : HasDerivAt (fun t => ∫ x in m.. (m - t) , f x) (-f (m - t)) t := by
    simpa [Function.comp_def] using (h_FTC (m - t)).comp t ((hasDerivAt_id t).neg.const_add m)
  have h_split : (fun t => ∫ x in (m-t)..(m + t) , f x) =
                 (fun t => (∫ x in m..(m+t), f x)- (∫ x in m..(m-t), f x))  := by
    ext u
    rw[intervalIntegral.integral_symm (m-u) m]
    rw[← intervalIntegral.integral_add_adjacent_intervals
    (hf.intervalIntegrable (m-u) m) (hf.intervalIntegrable m (m + u))]
    ring
  rw [h_split]
  convert hR.sub hL using 1
  ring

private lemma simpsonAuxG_deriv1 (f : ℝ → ℝ) (m t : ℝ) (hf : ContDiff ℝ 1 f) :
    deriv (simpsonAuxG f m) t =
      (2 / 3) * (f (m + t) + f (m - t) - 2 * f m) -
      (t / 3) * (deriv f (m + t) - deriv f (m - t)) := by
  have hd : Differentiable ℝ f := hf.differentiable (by simp)
  have h1 := (hd (m + t)).hasDerivAt.comp t ((hasDerivAt_id t).const_add m)
  have h2 := (hd (m - t)).hasDerivAt.comp t ((hasDerivAt_id t).neg.const_add m)
  have h_prod := ((hasDerivAt_id t).div_const 3).mul
    ((h2.add (hasDerivAt_const t (4 * f m))).add h1)
  have h_G : HasDerivAt (simpsonAuxG f m) _ t := (deriv_int_symm f m t hf.continuous).sub h_prod
  rw [h_G.deriv]
  dsimp
  ring

private lemma deriv2_symm (f : ℝ → ℝ) (m t : ℝ) (hff : ContDiff ℝ 2 f) :
    HasDerivAt (fun s => deriv f (m + s) - deriv f (m - s))
    (iteratedDeriv 2 f (m + t) + iteratedDeriv 2 f (m - t)) t := by
  rw [← Pi.sub_def]
  have hdf : Differentiable ℝ (deriv f) := hff.differentiable_deriv_two
  have hd : Differentiable ℝ f := hff.differentiable (by simp)
  have h1 : HasDerivAt (fun s : ℝ => deriv f (m + s))
      (deriv (deriv f) (m + t)) t := by
    have h1i : HasDerivAt (fun s : ℝ => m + s) 1 t :=
      (hasDerivAt_id t).const_add m
    simpa [Function.comp_def] using (hdf (m + t)).hasDerivAt.comp t h1i
  have h2 : HasDerivAt (fun s : ℝ => deriv f (m-s))
      (-(deriv (deriv f) (m - t))) t := by
    have h2i : HasDerivAt (fun s : ℝ => m - s) (-1) t := by
      simpa [sub_eq_add_neg, add_comm] using
      (hasDerivAt_id t).neg.const_add m
    simpa [Function.comp_def] using (hdf (m - t)).hasDerivAt.comp t h2i
  have h_sub := h1.sub h2
  simpa [iteratedDeriv_succ, iteratedDeriv_one] using h_sub

private lemma simpsonAuxG_deriv1_zero (f : ℝ → ℝ) (m : ℝ) (hf : ContDiff ℝ 1 f) :
    deriv (simpsonAuxG f m) 0 = 0 := by
  rw [simpsonAuxG_deriv1 f m 0 hf]
  ring_nf

private lemma simpsonAuxG_deriv2 (f : ℝ → ℝ) (m t : ℝ) (hf : ContDiff ℝ 2 f) :
    iteratedDeriv 2 (simpsonAuxG f m) t =
      (1 / 3) * (deriv f (m + t) - deriv f (m - t)) -
      (t / 3) * (iteratedDeriv 2 f (m + t) + iteratedDeriv 2 f (m - t)) := by
  have hd : Differentiable ℝ f:= hf.differentiable (by simp)
  have hp := (hd (m + t)).hasDerivAt.comp t ((hasDerivAt_id t).const_add m)
  have hm := (hd (m - t)).hasDerivAt.comp t ((hasDerivAt_id t).neg.const_add m)
  have hc := ((hp.add hm).sub (hasDerivAt_const t (2 * f m))).const_mul (2/3)
  have hb := ((hasDerivAt_id t).div_const 3).mul (deriv2_symm f m t hf)
  have hd : deriv (simpsonAuxG f m) =
      (fun y => (2 / 3) * (f (m + y) + f (m - y) - 2 * f m)) -
      ((fun x => id x / 3) * (fun s => deriv f (m + s) - deriv f (m - s))) := by
    funext s
    exact simpsonAuxG_deriv1 f m s (hf.of_le (by norm_num))
  have h_lhs : iteratedDeriv 2 (simpsonAuxG f m) t = deriv (deriv (simpsonAuxG f m)) t := by
    simp [show (2 : ℕ) = 1 + 1 by norm_num, iteratedDeriv_succ]
  rw[h_lhs]
  simp [Function.comp_def] at hc
  rw [hd, (hc.sub hb).deriv]
  simp [show (2 : ℕ) = 1 + 1 by norm_num, iteratedDeriv_succ]
  ring_nf

private lemma simpsonAuxG_deriv2_zero (f : ℝ → ℝ) (m : ℝ) (hf : ContDiff ℝ 2 f) :
    iteratedDeriv 2 (simpsonAuxG f m) 0 = 0 := by
  rw [simpsonAuxG_deriv2 f m 0 hf]
  ring_nf

private lemma simpsonAuxG_deriv3 (f : ℝ → ℝ) (m t : ℝ) (hf : ContDiff ℝ 4 f) :
    iteratedDeriv 3 (simpsonAuxG f m) t =
      - (t / 3) * (iteratedDeriv 3 f (m + t) - iteratedDeriv 3 f (m - t)) := by
  have hf2 : ContDiff ℝ 2 f := hf.of_le (by norm_num )
  have hd3 := hf.differentiable_iteratedDeriv 2 (by norm_num)
  have h1 := (hd3 (m + t)).hasDerivAt.comp t ((hasDerivAt_id t).const_add m)
  have h2 := (hd3 (m - t)).hasDerivAt.comp t ((hasDerivAt_id t).neg.const_add m)
  simp only [Function.comp_def] at h1 h2 --else there is problem
  have hb1 := (deriv2_symm f m t hf2).const_mul (1 / 3)
  have hb2 := ((hasDerivAt_id t).div_const 3).mul (h1.add h2)
  have h_eq : iteratedDeriv 2 (simpsonAuxG f m) =
      (fun y => (1 / 3) * (deriv f (m + y) - deriv f (m - y))) -
      (fun x => id x / 3) *( (fun s => iteratedDeriv 2 f (m + s))
      + (fun s => iteratedDeriv 2 f (m - s))) := by
    funext s
    dsimp
    exact simpsonAuxG_deriv2 f m s hf2
  have h_lhs : iteratedDeriv 3 (simpsonAuxG f m) t =
      deriv (iteratedDeriv 2 (simpsonAuxG f m)) t := by
    simp [show (3 : ℕ) = 1 + 2 by norm_num, iteratedDeriv_succ]
  rw[h_lhs]
  rw [h_eq, (hb1.sub hb2).deriv]
  dsimp
  simp only [show (3 : ℕ) = 1 + 2 by norm_num, show (2 : ℕ) = 1 + 1 by norm_num, iteratedDeriv_succ]
  ring

-- This lemma use Rolle's Thm, apply successively to F, deriv F, iteratedDeriv 2 F
--the zero derivatives at 0 give end point to each stage.
private lemma exists_third_deriv_eq_zero {F : ℝ → ℝ} {h : ℝ} (hh : 0 < h)
    (hF0 : F 0 = 0) (hFh : F h = 0)
    (hF'0 : deriv F 0 = 0) (hF''0 : iteratedDeriv 2 F 0 = 0)
    (hF_cont : ContinuousOn F (Set.Icc 0 h))
    (hF'_cont : ContinuousOn (deriv F) (Set.Icc 0 h))
    (hF''_cont : ContinuousOn (iteratedDeriv 2 F) (Set.Icc 0 h)) :
    ∃ ξ ∈ Set.Ioo 0 h, iteratedDeriv 3 F ξ = 0 := by
  obtain ⟨ξ₁, hξ₁, hF'1⟩ := exists_deriv_eq_zero hh hF_cont (by rw [hF0, hFh])
  have h1 : Set.Icc 0 ξ₁ ⊆ Set.Icc 0 h := Set.Icc_subset_Icc le_rfl hξ₁.2.le
  obtain ⟨ξ₂, hξ₂, hF''1⟩ := exists_deriv_eq_zero hξ₁.1 (hF'_cont.mono h1) (by rw [hF'0, hF'1])
  have h2 : Set.Icc 0 ξ₂ ⊆ Set.Icc 0 h := Set.Icc_subset_Icc le_rfl (hξ₂.2.le.trans hξ₁.2.le)
  rw [← iteratedDeriv_one, ← iteratedDeriv_one, iteratedDeriv_one, ← iteratedDeriv_succ] at hF''1
  obtain ⟨ξ₃, hξ₃, hF'''1⟩ :=
      exists_deriv_eq_zero hξ₂.1 (hF''_cont.mono h2) (hF''0.trans hF''1.symm)
  rw [← iteratedDeriv_succ] at hF'''1
  exact ⟨ξ₃, ⟨hξ₃.1, hξ₃.2.trans (hξ₂.2.trans hξ₁.2)⟩, hF'''1⟩

/-- If `f` is four times continuously differentiable and `a < b`, then there
exists `ζ ∈ [a, b]` such that the error in Simpson's rule is
`-((b - a) ^ 5 / 2880) * iteratedDeriv 4 f ζ`. -/
theorem simpson_error_estimation
    (f : ℝ → ℝ) (a b : ℝ)
    (hab : a < b)
    (h_smooth : ContDiff ℝ 4 f) :
    ∃ ζ ∈ Set.uIcc a b,
      (∫ x in a..b, f x) - ((b - a) / 6) * (f a + 4 * f ((a + b) / 2) + f b) =
      - ((b - a) ^ 5 / 2880) * iteratedDeriv 4 f ζ := by
  set m := (a + b) / 2
  set h := (b - a) / 2
  -- Basic Definitions
  have hh: 0 < h := by dsimp [h]; linarith
  have h_left : m - h = a := by dsimp [m, h]; ring
  have h_right : m + h = b := by dsimp [m, h]; ring
  have h_mid : m = (a + b) / 2 := rfl
  have h_error :
      (∫ t in a..b, f t) -
        ((b - a) / 6) * (f a + 4 * f ((a + b) / 2) + f b) =
        simpsonAuxG f m h := by rw [simpsonAuxG, h_left, h_right, h_mid]; ring
  have h_scale : (b - a) ^ 5 / 2880 = h ^ 5 / 90 := by dsimp [h]; ring
  rw [h_error, h_scale]
  let G : ℝ → ℝ := simpsonAuxG f m
  let c : ℝ := G h / h ^ 5
  let P : ℝ → ℝ := fun t => c * t ^ 5
  let F : ℝ → ℝ := fun t => G t - P t
  -- We define F=G-P as another auxiliary function, since F(0)=F'(0)=F''(0)=0
  -- Defining Continuity and Differentiability
  have hf1 : ContDiff ℝ 1 f := h_smooth.of_le (by decide)
  have hf2 : ContDiff ℝ 2 f := h_smooth.of_le (by decide)
  have h_int3 : ContDiff ℝ 3 (fun t => ∫ x in (m - t)..(m + t), f x) := by
      change ContDiff ℝ (2 + 1) _
      rw [contDiff_succ_iff_deriv]
      refine ⟨fun t => (deriv_int_symm f m t hf1.continuous).differentiableAt,
          fun h => by contradiction, ?_⟩
      have h_deriv : deriv (fun t => ∫ x in (m - t)..(m + t), f x)
          = fun t => f (m + t) + f (m - t) := by
        ext t
        exact (deriv_int_symm f m t hf1.continuous).deriv
      rw [h_deriv]
      exact (hf2.comp (contDiff_const.add contDiff_id)).add
          (hf2.comp (contDiff_const.sub contDiff_id))
  have hf3 : ContDiff ℝ 3 f := h_smooth.of_le (by decide)
  have h_poly3 : ContDiff ℝ 3 (fun t => (t / 3) * (f (m - t) + 4 * f m + f (m + t))) := by fun_prop
  have hG_cd3 : ContDiff ℝ 3 G := h_int3.sub h_poly3
  have hG_cd2 : ContDiff ℝ 2 G := hG_cd3.of_le (by decide)
  have hG_d2 : ContDiffAt ℝ 2 G 0 := hG_cd2.contDiffAt
  have hP_d2 : ContDiffAt ℝ 2 P 0 := by fun_prop
  have hG_d : DifferentiableAt ℝ G 0 := hG_d2.differentiableAt (by norm_num)
  have hP_d : DifferentiableAt ℝ P 0 := hP_d2.differentiableAt (by norm_num)
  have hF_cd2 : ContDiff ℝ 2 F := hG_cd2.sub (by fun_prop)
  --Continuity used for private lemma 'exists_third_deriv_eq_zero'
  have hF_cont   : ContinuousOn F (Set.Icc 0 h) := hF_cd2.continuous.continuousOn
  have hF'_cont  : ContinuousOn (deriv F) (Set.Icc 0 h)
      := (hF_cd2.continuous_deriv (by norm_num)).continuousOn
  have hF''_cont : ContinuousOn (iteratedDeriv 2 F) (Set.Icc 0 h)
      := (hF_cd2.continuous_iteratedDeriv (m := 2) le_rfl).continuousOn
  -- Terms F(0), F(h), F'(0). F''(0) for lemma 'exists_third_deriv_eq_zero'
  have hF0 : F 0 = 0 := by simp [F,G,P,simpsonAuxG_zero]
  have hFh : F h = 0 := by
    dsimp[F,G,P,c];  have hh5 : h^5 ≠ 0 := pow_ne_zero 5 (ne_of_gt hh)
    field_simp[hh5]; ring
  have hP'0 : deriv P 0 = 0 := by simp [P]
  have hG'0 : deriv G 0 = 0 := simpsonAuxG_deriv1_zero f m hf1
  have hF'0 : deriv F 0 = 0 := by
    change deriv (G - P) 0 = 0
    rw [deriv_sub (hG_d) (hP_d)]
    rw [hG'0, hP'0, sub_zero]
  have hG''0 : iteratedDeriv 2 G 0 = 0 := simpsonAuxG_deriv2_zero f m hf2
  have hderivP : deriv P = fun t => 5 * c * t ^ 4 := by
    ext t
    have hP_t : HasDerivAt P (5 * c * t ^ 4) t := by
       dsimp [P]
       have := (hasDerivAt_pow 5 t).const_mul c
       convert this using 1
       ring_nf
    rw[hP_t.deriv]
  have hP''0 : iteratedDeriv 2 P 0 = 0 := by simp [P]
  have hF''0 : iteratedDeriv 2 F 0 = 0 := by
    change iteratedDeriv 2 (G - P) 0 = 0
    rw [iteratedDeriv_sub hG_d2 hP_d2]; rw [hG''0, hP''0]; ring
  obtain ⟨ξ₃, hξ₃, hF'''1⟩
      := exists_third_deriv_eq_zero hh hF0 hFh hF'0 hF''0 hF_cont hF'_cont hF''_cont
  -- Compute 3rd derivative of P and relate G'''(ξ₃) to c * ξ₃²
  have hP3_deriv : iteratedDeriv 3 P = fun t => 60 * c * t ^ 2 := by
    ext t
    simp [P, show (3 : ℕ) = 2 + 1 by rfl ];ring
  have hP_cd3 : ContDiff ℝ 3 P := by fun_prop
  have hF'''_eq : iteratedDeriv 3 F ξ₃ = iteratedDeriv 3 G ξ₃ - iteratedDeriv 3 P ξ₃ := by
    change iteratedDeriv 3 (G - P) ξ₃ = _
    rw [iteratedDeriv_sub hG_cd3.contDiffAt hP_cd3.contDiffAt]
  rw [hF'''1, hP3_deriv] at hF'''_eq
  have hG'''_eq : iteratedDeriv 3 G ξ₃ = 60 * c * ξ₃ ^ 2 := by
    linarith
  -- Plug in simpsonAuxG_deriv3 to express the 3rd derivative difference of f
  --We have 0 = F'''(ξ₃) = G'''(ξ₃) - 60 * ζ₃^2 * (G(h) / h ^ 5)
  --and G'''(ζ₃) = - ζ₃ / 3 (f'''(m + ζ₃) - f'''(m - ζ₃))
  rw [simpsonAuxG_deriv3 f m ξ₃ h_smooth] at hG'''_eq
  have hξ₃_ne : ξ₃ ≠ 0 := ne_of_gt hξ₃.1
  have h_diff_f3 : iteratedDeriv 3 f (m + ξ₃) - iteratedDeriv 3 f (m - ξ₃) = -180 * c * ξ₃ := by
    apply mul_right_cancel₀ hξ₃_ne
    calc (iteratedDeriv 3 f (m + ξ₃) - iteratedDeriv 3 f (m - ξ₃)) * ξ₃
      _ = -3 * (- (ξ₃ / 3) * (iteratedDeriv 3 f (m + ξ₃) - iteratedDeriv 3 f (m - ξ₃))) := by ring
      _ = -3 * (60 * c * ξ₃ ^ 2) := by rw [hG'''_eq]
      _ = -180 * c * ξ₃ * ξ₃ := by ring
  -- Apply Mean Value Theorem to (iteratedDeriv 3 f) on [m - ξ₃, m + ξ₃]
  -- to get f'''(m + ζ₃) - f'''(m - ζ₃) = 2 * ζ₃ * iteratedDeriv 4 f ζ
  have h_sub_lt : m - ξ₃ < m + ξ₃ := by linarith [hξ₃.1]
  have hf3_cont : ContinuousOn (iteratedDeriv 3 f) (Set.Icc (m - ξ₃) (m + ξ₃)) :=
    h_smooth.continuous_iteratedDeriv (m := 3) (by norm_num) |>.continuousOn
  have hf3_diff : DifferentiableOn ℝ (iteratedDeriv 3 f) (Set.Ioo (m - ξ₃) (m + ξ₃)) :=
    (h_smooth.differentiable_iteratedDeriv 3 (by norm_num)).differentiableOn
  obtain ⟨ζ, hζ, h_mvt⟩ := exists_deriv_eq_slope (iteratedDeriv 3 f) h_sub_lt hf3_cont hf3_diff
  -- Rewrite derivative of iteratedDeriv 3 into iteratedDeriv 4
  have h_4th : deriv (iteratedDeriv 3 f) ζ = iteratedDeriv 4 f ζ := by
    conv_rhs =>
      rw [show (4 : ℕ) = 3 + 1 by rfl, iteratedDeriv_succ]
  rw [h_4th, h_diff_f3] at h_mvt
  have h_mvt_sim : iteratedDeriv 4 f ζ = -90 * c := by
    have h_denom : (m + ξ₃) - (m - ξ₃) = 2 * ξ₃ := by ring
    rw [h_denom] at h_mvt
    calc iteratedDeriv 4 f ζ
      _ = -180 * c * ξ₃ / (2 * ξ₃) := h_mvt
      _ = -90 * c := by field_simp [hξ₃_ne]; ring
  -- Conclude c = - iteratedDeriv 4 f ζ / 90 and prove G(h) = - (h^5 / 90) * iteratedDeriv 4 f ζ
  have h_eq : c = - (iteratedDeriv 4 f ζ) / 90 := by linarith
  use ζ
  constructor
  · rw [Set.uIcc_of_lt hab]
    constructor
    · calc a = m - h := h_left.symm
        _ ≤ m - ξ₃ := by linarith [hξ₃.2]
        _ ≤ ζ := hζ.1.le
    · calc ζ ≤ m + ξ₃ := hζ.2.le
        _ ≤ m + h := by linarith [hξ₃.2]
        _ = b := h_right
  · have hGh : G h = c * h ^ 5  := by
      dsimp [c]
      have hh5 : h ^ 5 ≠ 0 := pow_ne_zero 5 (ne_of_gt hh)
      exact (div_mul_cancel₀ (G h) hh5).symm
    conv_rhs =>
      rw [neg_mul,mul_comm ,← neg_mul, ← mul_div_assoc, mul_div_right_comm]
    rw [← h_eq,← hGh]
