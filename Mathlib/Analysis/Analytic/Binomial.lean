/-
Copyright (c) 2025 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/
import Mathlib.Analysis.SpecialFunctions.OrdinaryHypergeometric
import Mathlib.RingTheory.Binomial

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

open scoped Nat

universe u v

/-- **Binomial series**: the (scalar) formal multilinear series with coefficients given
by `Ring.choose a`. The sum of this series is `fun x ↦ (1 + x) ^ a` within the radius
of convergence. -/
noncomputable def binomialSeries {𝕂 : Type u} [Field 𝕂] [CharZero 𝕂] (𝔸 : Type v)
    [Ring 𝔸] [Algebra 𝕂 𝔸] [TopologicalSpace 𝔸] [IsTopologicalRing 𝔸] (a : 𝕂) :
    FormalMultilinearSeries 𝕂 𝔸 𝔸 :=
  .ofScalars 𝔸 (Ring.choose a ·)

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
