/-
Copyright (c) 2024 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler
-/

import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.Analysis.SpecialFunctions.Gamma.BohrMollerup
import Mathlib.Data.Nat.Factorial.Basic

/-!
# Derivative of Γ at positive integers

We prove the formula for the derivative of `Real.Gamma` at a positive integer:

`deriv Real.Gamma (n + 1) = Nat.factorial n * (-Real.eulerMascheroniConstant + harmonic n)`

-/

open Real Set Filter Topology

open Nat

/-- If `f : ℝ → ℝ` is convex on `S` and differentiable at `x ∈ S`, then the slope of any secant
line with left endpoint at `x` is bounded below by `deriv f x`. -/
lemma ConvexOn.deriv_le_slope {S : Set ℝ} {x y : ℝ} (hx : x ∈ S) {f : ℝ → ℝ} (hfc : ConvexOn ℝ S f)
    (hfd : DifferentiableAt ℝ f x) (hy : y ∈ S) (hxy : x < y) :
    deriv f x ≤ (f y - f x) / (y - x) := by
  apply le_of_tendsto hfd.hasDerivAt.tendsto_slope_zero_right
  rw [eventually_nhdsWithin_iff]
  filter_upwards [eventually_lt_nhds (sub_pos.mpr hxy)] with t ht (ht' : 0 < t)
  rw [smul_eq_mul, ← div_eq_inv_mul]
  have := hfc.secant_mono (x := x + t) hx ?_ hy (by linarith) hxy.ne' (by linarith)
  rwa [add_sub_cancel'] at this
  exact hfc.1.ordConnected.out hx hy ⟨by linarith, by linarith⟩

/-- If `f : ℝ → ℝ` is convex on `S` and differentiable at `y ∈ S`, then the slope of any secant
line with right endpoint at `y` is bounded below by `deriv f y`. -/
lemma ConvexOn.slope_le_deriv {S : Set ℝ} {x y : ℝ} (hx : x ∈ S)
    {f : ℝ → ℝ} (hfc : ConvexOn ℝ S f) (hfd : DifferentiableAt ℝ f y) (hy : y ∈ S) (hxy : x < y) :
    (f y - f x) / (y - x) ≤ deriv f y := by
  apply ge_of_tendsto hfd.hasDerivAt.tendsto_slope_zero_left
  rw [eventually_nhdsWithin_iff]
  filter_upwards [eventually_gt_nhds (sub_neg.mpr hxy)] with t ht (ht' : t < 0)
  rw [smul_eq_mul, ← div_eq_inv_mul]
  have := hfc.secant_mono (y := y + t) hy hx ?_ hxy.ne (by linarith) (by linarith)
  rwa [add_sub_cancel', ← neg_div_neg_eq, neg_sub, neg_sub] at this
  exact hfc.1.ordConnected.out hx hy ⟨by linarith, by linarith⟩

/-- If `f : ℝ → ℝ` is strictly convex on `S` and differentiable at `x ∈ S`, then the slope of any
secant line with left endpoint at `x` is strictly greater than `deriv f x`. -/
lemma StrictConvexOn.deriv_lt_slope {S : Set ℝ} {x y : ℝ} (hx : x ∈ S) {f : ℝ → ℝ}
    (hfc : StrictConvexOn ℝ S f) (hfd : DifferentiableAt ℝ f x) (hy : y ∈ S) (hxy : x < y) :
    deriv f x < (f y - f x) / (y - x) := by
  obtain ⟨u, hu, hu'⟩ := exists_between hxy
  have := hfc.secant_strict_mono hx (?_ : u ∈ S) hy hu.ne' hxy.ne' hu'
  refine (hfc.convexOn.deriv_le_slope hx hfd (?_ : u ∈ S) hu).trans_lt this
  all_goals exact hfc.1.ordConnected.out hx hy ⟨hu.le, hu'.le⟩

/-- If `f : ℝ → ℝ` is strictly convex on `S` and differentiable at `y ∈ S`, then the slope of any
secant line with right endpoint at `y` is strictly less than `deriv f y`. -/
lemma StrictConvexOn.slope_lt_deriv {S : Set ℝ} {x y : ℝ} (hx : x ∈ S) {f : ℝ → ℝ}
    (hfc : StrictConvexOn ℝ S f) (hfd : DifferentiableAt ℝ f y) (hy : y ∈ S) (hxy : x < y) :
    (f y - f x) / (y - x) < deriv f y := by
  obtain ⟨u, hu, hu'⟩ := exists_between hxy
  have := hfc.secant_strict_mono hy hx (?_ : u ∈ S) hxy.ne hu'.ne hu
  rw [← neg_div_neg_eq, neg_sub, neg_sub] at this
  apply this.trans_le
  rw [← neg_div_neg_eq, neg_sub, neg_sub]
  apply hfc.convexOn.slope_le_deriv (?_ : u ∈ S) hfd hy hu'
  all_goals exact hfc.1.ordConnected.out hx hy ⟨hu.le, hu'.le⟩

/-- If `f` is convex on `S` and differentiable at all points of `S`, then its derivative is monotone
on `S`. -/
lemma ConvexOn.derivMonoOn {S : Set ℝ} {f : ℝ → ℝ} (hfc : ConvexOn ℝ S f)
    (hfd : ∀ s ∈ S, DifferentiableAt ℝ f s) : MonotoneOn (deriv f) S := by
  intro x hx y hy hxy
  rcases eq_or_lt_of_le hxy with rfl | hxy'; rfl
  exact (hfc.deriv_le_slope hx (hfd x hx) hy hxy').trans (hfc.slope_le_deriv hx (hfd y hy) hy hxy')

/-- If `f` is strictly convex on `S` and differentiable at all points of `S`, then its derivative
is strictly monotone on `S`. -/
lemma StrictConvexOn.derivStrictMonoOn {S : Set ℝ} {f : ℝ → ℝ} (hfc : StrictConvexOn ℝ S f)
    (hfd : ∀ s ∈ S, DifferentiableAt ℝ f s) : StrictMonoOn (deriv f) S := by
  intro x hx y hy hxy
  exact (hfc.deriv_lt_slope hx (hfd x hx) hy hxy).trans (hfc.slope_lt_deriv hx (hfd y hy) hy hxy)

/-- Translation in the domain does not change the derivative. -/
lemma deriv_comp_const_add {𝕜 : Type*} [NontriviallyNormedField 𝕜] (a x : 𝕜) {𝕜' : Type*}
    [NormedAddCommGroup 𝕜'] [NormedSpace 𝕜 𝕜'] {h : 𝕜 → 𝕜'}
    (hh : DifferentiableAt 𝕜 h (a + x)) :
    deriv (fun x ↦ h (a + x)) x = deriv h (a + x) := HasDerivAt.deriv hh.hasDerivAt.comp_const_add

/-- Translation in the domain does not change the derivative. -/
lemma deriv_comp_add_const {𝕜 : Type*} [NontriviallyNormedField 𝕜] (a x : 𝕜) {𝕜' : Type*}
    [NormedAddCommGroup 𝕜'] [NormedSpace 𝕜 𝕜'] {h : 𝕜 → 𝕜'}
    (hh : DifferentiableAt 𝕜 h (x + a)) :
    deriv (fun x ↦ h (x + a)) x = deriv h (x + a) := HasDerivAt.deriv hh.hasDerivAt.comp_add_const

/-- Explicit formula for the derivative of the Gamma function at integers, in terms of harmonic
numbers and the Euler-Mascheroni constant `γ`. -/
lemma Real.deriv_Gamma_nat (n : ℕ) :
    deriv Gamma (n + 1) = (n)! * (-eulerMascheroniConstant + harmonic n) := by
  /- This follows from two properties of the function `f n = log (Gamma n)`:
  firstly, the elementary computation that `deriv f (n + 1) = deriv f n + 1 / n`, so that
  `deriv f n = deriv f 1 + harmonic n`; secondly, the convexity of `f` (the Bohr-Mollerup theorem),
  which shows that `deriv f n` is `log n + o(1)` as `n → ∞`.
  `-/
  let f := log ∘ Gamma
  -- First reduce to computing derivative of `log ∘ Gamma`.
  suffices deriv (log ∘ Gamma) (n + 1) = -eulerMascheroniConstant + harmonic n by
    rwa [Function.comp_def, deriv.log ?_ (by positivity), Gamma_nat_eq_factorial,
    div_eq_iff_mul_eq (by positivity), mul_comm, Eq.comm] at this
    exact differentiableAt_Gamma (fun m ↦ by linarith)
  have hc : ConvexOn ℝ (Ioi 0) f := convexOn_log_Gamma
  have h_rec (x : ℝ) (hx : 0 < x) : f (x + 1) = f x + log x := by simp only [f, Function.comp_apply,
      Gamma_add_one hx.ne', log_mul hx.ne' (Gamma_pos_of_pos hx).ne', add_comm]
  have hder {x : ℝ} (hx : 0 < x) : DifferentiableAt ℝ f x := by
    refine ((differentiableAt_Gamma ?_).log (Gamma_ne_zero ?_)) <;>
    exact fun m ↦ ne_of_gt (by linarith)
  -- Express derivative at general `n` in terms of value at `1` using recurrence relation
  have hder_rec (x : ℝ) (hx : 0 < x) : deriv f (x + 1) = deriv f x + 1 / x := by
    rw [← deriv_comp_add_const _ _ (hder <| by positivity), one_div, ← deriv_log,
      ← deriv_add (hder <| by positivity) (differentiableAt_log hx.ne')]
    apply EventuallyEq.deriv_eq
    filter_upwards [eventually_gt_nhds hx] using h_rec
  have hder_nat (n : ℕ) : deriv f (n + 1) = deriv f 1 + harmonic n := by
    induction' n with n hn
    · simp
    · rw [cast_succ, hder_rec (n + 1) (by positivity), hn, harmonic_succ]
      push_cast
      ring
  suffices -deriv f 1 = eulerMascheroniConstant by rw [hder_nat n, ← this, neg_neg]
  -- Use convexity to show derivative of `f` at `n + 1` is between `log n` and `log (n + 1)`
  have derivLB (n : ℕ) (hn : 0 < n) : log n ≤ deriv f (n + 1) := by
    refine (le_of_eq ?_).trans <| hc.slope_le_deriv (by positivity : (0 : ℝ) < n)
      (hder <| by positivity) (by positivity : _ < (_ : ℝ)) (by linarith)
    rw [show n + 1 - n = (1 : ℝ) by ring, div_one, h_rec n (by positivity), add_sub_cancel']
  have derivUB (n : ℕ) : deriv f (n + 1) ≤ log (n + 1) := by
    refine (hc.deriv_le_slope (by positivity : _ < _) (hder <| by positivity)
      (by positivity : (0 : ℝ) < n + 2) (by linarith)).trans (le_of_eq ?_)
    rw [show n + 2 - (n + 1) = (1 : ℝ) by ring, div_one, show n + 2 = (n + 1) + (1 : ℝ) by ring,
      h_rec (n + 1) (by positivity), add_sub_cancel']
  -- deduce `-deriv f 1` is bounded above + below by sequences which both tend to `γ`
  apply le_antisymm
  · apply ge_of_tendsto tendsto_harmonic_sub_log
    filter_upwards [eventually_gt_atTop 0] with n hn
    rw [le_sub_iff_add_le', ← sub_eq_add_neg, sub_le_iff_le_add', ← hder_nat]
    exact derivLB n hn
  · apply le_of_tendsto tendsto_harmonic_sub_log_add_one
    filter_upwards with n
    rw [sub_le_iff_le_add', ← sub_eq_add_neg, le_sub_iff_add_le', ← hder_nat]
    exact derivUB n

lemma Real.eulerMascheroniConstant_eq_neg_deriv : eulerMascheroniConstant = -deriv Gamma 1 := by
  rw [show (1 : ℝ) = ↑(0 : ℕ) + 1 by simp, deriv_Gamma_nat 0]
  simp
