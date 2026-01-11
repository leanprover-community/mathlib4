/-
Copyright (c) 2026 Yuval Filmus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuval Filmus
-/

module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Orthogonality
public import Mathlib.Analysis.Complex.Trigonometric

/-!
TODO
-/
public section

namespace Polynomial.Chebyshev

open Real Polynomial Finset

private lemma exp_sub_one_ne_zero {n : ℕ} {k : ℤ} (hn : n ≠ 0)
  (hk₀ : k ≠ 0) (hk₁ : k.natAbs < 2 * n) : Complex.exp (k / n * π * Complex.I) ≠ 1 := by
  have : (n : ℂ) ≠ 0 := by aesop
  by_contra!
  obtain ⟨m, hx⟩ := Complex.exp_eq_one_iff.mp this
  have h : k = m * (2 * n) := by
    apply (@Int.cast_inj ℂ _ _).mp
    linear_combination (norm := (push_cast; field)) hx * (n / π / Complex.I)
  have : m < 1 := Int.lt_of_mul_lt_mul_right (a := 2 * n) (by grind) (by positivity)
  have : -1 < m := Int.lt_of_mul_lt_mul_right (a := 2 * n) (by grind) (by positivity)
  grind

private theorem sum_exp {n : ℕ} {k : ℤ} (hn : n ≠ 0) (hk₀ : k ≠ 0) (hk₁ : k.natAbs < 2 * n) :
    ∑ i ∈ range n, Complex.exp ((k * ((2 * i + 1) / (2 * n) * π)) * Complex.I) =
    (Complex.exp (k / (2 * n) * π * Complex.I) / (Complex.exp (k / n * π * Complex.I) - 1)) *
    ((-1) ^ k - 1) := by
  have : (n : ℂ) ≠ 0 := by aesop
  suffices (∑ i ∈ range n, Complex.exp ((k * ((2 * i + 1) / (2 * n) * π)) * Complex.I)) *
    Complex.exp (-(k / (2 * n) * π * Complex.I)) * (Complex.exp (k / n * π * Complex.I) - 1) =
    (-1) ^ k - 1 by
    rw [Complex.exp_neg] at this
    set s := ∑ i ∈ range n, Complex.exp ((k * ((2 * i + 1) / (2 * n) * π)) * Complex.I)
    set a := Complex.exp (k / (2 * n) * π * Complex.I)
    set b := Complex.exp (k / n * π * Complex.I) - 1
    have ha : a ≠ 0 := Complex.exp_ne_zero _
    have hb : b ≠ 0 := by grind [exp_sub_one_ne_zero]
    linear_combination (norm := (field_simp; ring))
      this * a / b
  convert geom_sum_mul (Complex.exp (k / n * π * Complex.I)) n using 1
  · congr 1
    rw [sum_mul]
    congr! 1 with i hi
    rw [← Complex.exp_nat_mul, ← Complex.exp_add]
    grind
  · rw [← Complex.exp_nat_mul, show (n * (k / n * π * Complex.I)) = k * (π * Complex.I) by field,
      Complex.exp_int_mul, Complex.exp_pi_mul_I]

/-- Weighted sum of P (x) where x goes over cos ((2 * i + 1) / (2 * n) * π) for 0 ≤ i < n. -/
noncomputable def sumZeroes (n : ℕ) (P : ℝ[X]) : ℝ :=
    (π / n) * ∑ i ∈ range n, P.eval (cos ((2 * i + 1) / (2 * n) * π))

theorem sumZeroes_T_zero {n : ℕ} (hn : n ≠ 0) :
    sumZeroes n (T ℝ 0) = π := by
  simp [sumZeroes, show π / n * n = π by field]

theorem sumZeroes_T_ne_zero {n : ℕ} (k : ℤ) (hk₀ : k ≠ 0) (hk₁ : k.natAbs < 2 * n) :
    sumZeroes n (T ℝ k) = 0 := by
  wlog! hn : n ≠ 0
  · simp [sumZeroes, hn]
  suffices ∑ i ∈ range n, 2 * cos (k * ((2 * i + 1) / (2 * n) * π)) = 0 by
    rw [sumZeroes, mul_eq_zero_iff_left (by aesop)]
    rw [← mul_sum, mul_eq_zero_iff_left (by norm_num)] at this
    simpa [T_real_cos]
  suffices (∑ i ∈ range n, 2 * cos (k * ((2 * i + 1) / (2 * n) * π)) : ℂ) = 0 by norm_cast at this ⊢
  suffices ∑ i ∈ range n, 2 * Complex.cos (k * ((2 * i + 1) / (2 * n) * π)) = 0 by aesop
  simp_rw [Complex.two_cos, ← neg_mul, ← Int.cast_neg]
  have : (-1 : ℂ) ^ (-k) = (-1) ^ k := by rw [← Int.cast_negOnePow, ← Int.cast_negOnePow]; simp
  rw [sum_add_distrib, sum_exp hn (by grind) (by grind), sum_exp hn (by grind) (by grind),
    Int.cast_neg, neg_div, neg_mul, neg_mul, Complex.exp_neg,
    neg_div, neg_mul, neg_mul, Complex.exp_neg, this, ← add_mul, mul_eq_zero_of_left]
  set z := Complex.exp (k / (2 * n) * π * Complex.I) with hz
  have hz₂ : Complex.exp (k / n * π * Complex.I) = z ^ 2 := by
    rw [hz, ← Complex.exp_nat_mul]; grind
  rw [hz₂, ← inv_pow z 2]
  have : z ≠ 0 := by grind [Complex.exp_ne_zero]
  have : z ^ 2 ≠ 1 := by grind [exp_sub_one_ne_zero]
  field [show (z ^ 2 - 1 ≠ 0) ∧ (1 - z ^ 2 ≠ 0) by grind]

end Polynomial.Chebyshev
