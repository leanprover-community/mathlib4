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

* `binomialSeries_radius_eq_one`: The radius of convergence of the binomial series is `1`.

-/

open scoped Nat

universe u v

/-- Binomial series:
$$
\sum_{k=0}^{\infty} \; \binom{a}{k} \; x^k = 1 + a x + \frac{a(a-1)}{2!} x^2 +
  \frac{a(a-1)(a-2)}{3!} x^3 + \cdots
$$
-/
noncomputable def binomialSeries {𝕂 : Type u} [Field 𝕂] [CharZero 𝕂] (𝔸 : Type v)
    [Ring 𝔸] [Algebra 𝕂 𝔸] [TopologicalSpace 𝔸] [IsTopologicalRing 𝔸] (a : 𝕂) :
    FormalMultilinearSeries 𝕂 𝔸 𝔸 := .ofScalars 𝔸 (Ring.choose a ·)

theorem binomialSeries_eq_ordinaryHypergeometricSeries {𝕂 : Type u} [Field 𝕂] [CharZero 𝕂]
    {𝔸 : Type v} [Ring 𝔸] [Algebra 𝕂 𝔸] [TopologicalSpace 𝔸] [IsTopologicalRing 𝔸] {a b : 𝕂}
    (h : ∀ (k : ℕ), (k : 𝕂) ≠ -b) :
    binomialSeries 𝔸 a =
    (ordinaryHypergeometricSeries 𝔸 (-a) b b).compContinuousLinearMap (-(.id _ _)) := by
  simp [binomialSeries, ordinaryHypergeometricSeries]
  ext n v
  simp [FormalMultilinearSeries.ofScalars, ordinaryHypergeometricCoefficient]
  rw [mul_inv_cancel_right₀]
  swap
  · intro h_zero
    rw [ascPochhammer_eval_eq_zero_iff] at h_zero
    tauto
  have : ((-ContinuousLinearMap.id 𝕂 𝔸 : _) : 𝔸 → 𝔸) = Neg.neg := by
    ext
    simp
  rw [ascPochhammer_eval_neg_eq_descPochhammer, Ring.choose_eq_smul, ← List.map_ofFn, this,
    List.prod_map_neg (List.ofFn v), Polynomial.descPochhammer_smeval_eq_ascPochhammer,
    Polynomial.ascPochhammer_smeval_eq_eval, descPochhammer_eval_eq_ascPochhammer]
  simp
  -- hack
  by_cases h : (Even n)
  · rw [Even.neg_one_pow h, Even.neg_one_pow h]
    simp
  · rw [Nat.not_even_iff_odd] at h
    rw [Odd.neg_one_pow h, Odd.neg_one_pow h]
    simp

/-- The radius of convergence of `binomialSeries 𝔸 a` is `⊤` for natural `a`. -/
theorem binomialSeries_radius_eq_top_of_nat {𝕂 : Type v} [RCLike 𝕂] {𝔸 : Type u}
    [NormedDivisionRing 𝔸] [NormedAlgebra 𝕂 𝔸] {a : ℕ} :
    (binomialSeries 𝔸 (a : 𝕂)).radius = ⊤ := by
  have : ∀ (k : ℕ), (k : 𝕂) ≠ -1 := by
    -- TODO: golf
    intro k h
    replace h : (k : ℝ) = -1 := by
      rwa [← RCLike.ofReal_natCast, ← RCLike.ofReal_one, ← RCLike.ofReal_neg,
        RCLike.ofReal_inj] at h
    linarith
  simp [binomialSeries_eq_ordinaryHypergeometricSeries this,
    ordinaryHypergeometric_radius_top_of_neg_nat₁]

/-- The radius of convergence of `binomialSeries 𝔸 a` is `1`, when `a` is not natural. -/
theorem binomialSeries_radius_eq_one {𝕂 : Type v} [RCLike 𝕂] {𝔸 : Type u} [NormedDivisionRing 𝔸]
    [NormedAlgebra 𝕂 𝔸] {a : 𝕂} (ha : ∀ (k : ℕ), a ≠ k) : (binomialSeries 𝔸 a).radius = 1 := by
  have : ∀ (k : ℕ), (k : 𝕂) ≠ -1 := by
  -- TODO: golf
    intro k h
    replace h : (k : ℝ) = -1 := by
      rwa [← RCLike.ofReal_natCast, ← RCLike.ofReal_one, ← RCLike.ofReal_neg,
        RCLike.ofReal_inj] at h
    linarith
  simp [binomialSeries_eq_ordinaryHypergeometricSeries this]
  rw [ordinaryHypergeometricSeries_radius_eq_one]
  intro k
  simp only [neg_neg, ne_eq, one_div, and_self]
  exact ⟨(ha k).symm, this k⟩
