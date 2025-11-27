/-
Copyright (c) 2025 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/
module

public import Mathlib.Analysis.Calculus.IteratedDeriv.ConvergenceOnBall
public import Mathlib.Analysis.Complex.OperatorNorm
public import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
public import Mathlib.Analysis.SpecialFunctions.OrdinaryHypergeometric
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.RingTheory.Binomial

/-!
# Binomial Series

This file introduces the binomial series:
$$
\sum_{k=0}^{\infty} \; \binom{a}{k} \; x^k = 1 + a x + \frac{a(a-1)}{2!} x^2 +
  \frac{a(a-1)(a-2)}{3!} x^3 + \cdots
$$
where $a$ is an element of a normed field $\mathbb{K}$,
and $x$ is an element of a normed algebra over $\mathbb{K}$.

## Main Statements

* `binomialSeries_radius_eq_one`: The radius of convergence of the binomial series is `1` when `a`
  is not a natural number.
* `binomialSeries_radius_eq_top_of_nat`: In case `a` is natural, the series converges everywhere,
  since it is finite.
-/

@[expose] public section

open scoped Nat

universe u v

@[norm_cast]
lemma Complex.ofReal_choose (a : ℝ) (n : ℕ) :
    ↑(Ring.choose a n) = Ring.choose (a : ℂ) n :=
  Ring.map_choose (algebraMap ℝ ℂ) _ _

/-- **Binomial series**: the (scalar) formal multilinear series with coefficients given
by `Ring.choose a`. The sum of this series is `fun x ↦ (1 + x) ^ a` within the radius
of convergence. -/
noncomputable def binomialSeries {𝕂 : Type u} [Field 𝕂] [CharZero 𝕂] (𝔸 : Type v)
    [Ring 𝔸] [Algebra 𝕂 𝔸] [TopologicalSpace 𝔸] [IsTopologicalRing 𝔸] (a : 𝕂) :
    FormalMultilinearSeries 𝕂 𝔸 𝔸 :=
  .ofScalars 𝔸 (Ring.choose a ·)

@[simp]
theorem binomialSeries_apply {𝕂 : Type u} [Field 𝕂] [CharZero 𝕂] (𝔸 : Type v)
    [Ring 𝔸] [Algebra 𝕂 𝔸] [TopologicalSpace 𝔸] [IsTopologicalRing 𝔸] (a : 𝕂) {n} (v : Fin n → 𝔸) :
    binomialSeries 𝔸 a n v = Ring.choose a n • (List.ofFn v).prod := by
  simp [binomialSeries, FormalMultilinearSeries.ofScalars]

theorem binomialSeries_eq_ordinaryHypergeometricSeries {𝕂 : Type u} [Field 𝕂] [CharZero 𝕂]
    {𝔸 : Type v} [Ring 𝔸] [Algebra 𝕂 𝔸] [TopologicalSpace 𝔸] [IsTopologicalRing 𝔸] {a b : 𝕂}
    (h : ∀ (k : ℕ), (k : 𝕂) ≠ -b) :
    binomialSeries 𝔸 a =
    (ordinaryHypergeometricSeries 𝔸 (-a) b b).compContinuousLinearMap (-(.id _ _)) := by
  simp only [binomialSeries, ordinaryHypergeometricSeries,
    FormalMultilinearSeries.ofScalars_comp_neg_id]
  congr! with n
  rw [ordinaryHypergeometricCoefficient,
    mul_inv_cancel_right₀ (by simp [ascPochhammer_eval_eq_zero_iff]; grind)]
  simp only [Ring.choose_eq_smul, Polynomial.descPochhammer_smeval_eq_ascPochhammer,
    Polynomial.ascPochhammer_smeval_cast, Polynomial.ascPochhammer_smeval_eq_eval,
    ascPochhammer_eval_neg_eq_descPochhammer, descPochhammer_eval_eq_ascPochhammer]
  ring_nf
  simp

/-- The radius of convergence of `binomialSeries 𝔸 a` is `⊤` for natural `a`. -/
theorem binomialSeries_radius_eq_top_of_nat {𝕂 : Type v} [RCLike 𝕂] {𝔸 : Type u}
    [NormedDivisionRing 𝔸] [NormedAlgebra 𝕂 𝔸] {a : ℕ} :
    (binomialSeries 𝔸 (a : 𝕂)).radius = ⊤ := by
  simp [binomialSeries_eq_ordinaryHypergeometricSeries (b := (1 : 𝕂)) (by norm_cast; simp),
    ordinaryHypergeometric_radius_top_of_neg_nat₁]

/-- The radius of convergence of `binomialSeries 𝔸 a` is `1`, when `a` is not natural. -/
theorem binomialSeries_radius_eq_one {𝕂 : Type v} [RCLike 𝕂] {𝔸 : Type u} [NormedDivisionRing 𝔸]
    [NormedAlgebra 𝕂 𝔸] {a : 𝕂} (ha : ∀ (k : ℕ), a ≠ k) : (binomialSeries 𝔸 a).radius = 1 := by
  simp only [binomialSeries_eq_ordinaryHypergeometricSeries (b := (1 : 𝕂)) (by norm_cast; simp),
    FormalMultilinearSeries.radius_compNeg]
  conv at ha => ext; rw [ne_comm]
  exact ordinaryHypergeometricSeries_radius_eq_one _ _ _ _ (by norm_cast; grind)

theorem binomialSeries_radius_ge_one {𝕂 : Type*} [RCLike 𝕂] {𝔸 : Type*} [NormedDivisionRing 𝔸]
    [NormedAlgebra 𝕂 𝔸] {a : 𝕂} :
    1 ≤ (binomialSeries 𝔸 a).radius := by
  by_cases ha : ∀ (k : ℕ), a ≠ k
  · rw [binomialSeries_radius_eq_one ha]
  · push_neg at ha
    rcases ha with ⟨k, rfl⟩
    simp [binomialSeries_radius_eq_top_of_nat]

theorem one_add_cpow_hasFPowerSeriesOnBall_zero {a : ℂ} :
    HasFPowerSeriesOnBall (fun x ↦ (1 + x) ^ a) (binomialSeries ℂ a) 0 1 := by
  suffices (binomialSeries ℂ a = FormalMultilinearSeries.ofScalars ℂ
      fun n ↦ iteratedDeriv n (fun (x : ℂ) ↦ (1 + x) ^ a) 0 / n !) by
    convert AnalyticOn.hasFPowerSeriesOnSubball _ _ _
    · norm_num
    · -- TODO: use `fun_prop` for this subgoal
      apply AnalyticOn.cpow (analyticOn_const.add analyticOn_id) analyticOn_const
      intro z hz
      apply Complex.mem_slitPlane_of_norm_lt_one
      rw [← ENNReal.ofReal_one, Metric.emetric_ball] at hz
      simpa using hz
    · rw [← this]
      exact binomialSeries_radius_ge_one
  simp only [binomialSeries, FormalMultilinearSeries.ofScalars_series_eq_iff]
  ext n
  rw [eq_div_iff_mul_eq (by simp [Nat.factorial_ne_zero]), ← nsmul_eq_mul',
    ← Ring.descPochhammer_eq_factorial_smul_choose]
  let B := Metric.ball (0 : ℂ) 1
  suffices Set.EqOn (iteratedDerivWithin n (fun x ↦ (1 + x) ^ a) B)
      (fun x ↦ (descPochhammer ℤ n).smeval a * (1 + x) ^ (a - n)) B by
    specialize this (show 0 ∈ _ by simp [B])
    rw [iteratedDerivWithin_of_isOpen Metric.isOpen_ball (by simp)] at this
    symm
    simpa using this
  induction n with
  | zero => simp [Set.EqOn]
  | succ n ih =>
    have : iteratedDerivWithin (n + 1) (fun (x : ℂ) ↦ (1 + x) ^ a) B =
        derivWithin (iteratedDerivWithin n (fun x ↦ (1 + x) ^ a) B) B := by
      ext z
      rw [iteratedDerivWithin_succ]
    rw [this]
    have : Set.EqOn (derivWithin (iteratedDerivWithin n (fun (x : ℂ) ↦ (1 + x) ^ a) B) B)
        (derivWithin (fun x ↦ (descPochhammer ℤ n).smeval a * (1 + x) ^ (a - ↑n)) B) B := by
      intro z hz
      rw [derivWithin_congr (fun _ hz ↦ ih hz) (ih hz)]
    apply Set.EqOn.trans this
    intro z hz
    simp only [Nat.cast_add, Nat.cast_one, B, derivWithin_of_isOpen Metric.isOpen_ball hz,
      deriv_const_mul_field']
    rw [deriv_cpow_const (by fun_prop), deriv_const_add', deriv_id'', mul_one,
      show a - (n + 1) = a - n - 1 by ring, ← mul_assoc]
    · congr
      simp [descPochhammer_succ_right, Polynomial.smeval_mul, Polynomial.smeval_natCast]
    · apply Complex.mem_slitPlane_of_norm_lt_one
      simpa [B] using hz

theorem one_add_cpow_hasFPowerSeriesAt_zero {a : ℂ} :
    HasFPowerSeriesAt (fun x ↦ (1 + x) ^ a) (binomialSeries ℂ a) 0 :=
  one_add_cpow_hasFPowerSeriesOnBall_zero.hasFPowerSeriesAt

attribute [local simp← ] Complex.ofReal_choose in
attribute [-simp] FormalMultilinearSeries.apply_eq_prod_smul_coeff in
theorem one_add_rpow_hasFPowerSeriesOnBall_zero {a : ℝ} :
    HasFPowerSeriesOnBall (fun x ↦ (1 + x) ^ a) (binomialSeries ℝ a) 0 1 := by
  have : binomialSeries ℂ a = (binomialSeries ℂ (a : ℂ)).restrictScalars (𝕜 := ℝ) := by aesop
  have : HasFPowerSeriesOnBall (fun x ↦ (1 + x) ^ (a : ℂ)) (binomialSeries ℂ a) (.ofRealCLM 0) 1 :=
    Complex.ofRealCLM.map_zero ▸ this ▸ one_add_cpow_hasFPowerSeriesOnBall_zero.restrictScalars
  convert (Complex.reCLM.comp_hasFPowerSeriesOnBall this.compContinuousLinearMap).congr ?_
  · ext; simp [Function.comp_def]
  · simp
  · intro x hx; simp_all; norm_cast

theorem one_add_rpow_hasFPowerSeriesAt_zero {a : ℝ} :
    HasFPowerSeriesAt (fun x ↦ (1 + x) ^ a) (binomialSeries ℝ a) 0 :=
  one_add_rpow_hasFPowerSeriesOnBall_zero.hasFPowerSeriesAt
