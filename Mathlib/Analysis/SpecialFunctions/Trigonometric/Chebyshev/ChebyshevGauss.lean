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
# Chebyshev polynomials over the reals: Chebyshev–Gauss

The Chebyshev–Gauss property calculates an integral of a polynomial of degree `< 2 * n`
with respect to the weight function `1 / √ (1 - x ^ 2)` supported on `[-1, 1]` by a sum
over appropriate evaluations of the polynomial.

## Main statements

* integral_eq_sumZeroes: Statement of the Chebyshev–Gauss property

## Implementation

The statement is proved for Chebyshev polynomials using the complex exponential representation
of `cos`, and then deduced for arbitrary polynomials.
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
    have hf {s a b t : ℂ} (h : s * a⁻¹ * b = t) (ha : a ≠ 0) (hb : b ≠ 0) : s = a / b * t := by
      linear_combination (norm := field) h * a / b
    apply hf this (Complex.exp_ne_zero _) (by grind [exp_sub_one_ne_zero])
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

@[simp]
theorem sumZeroes_sum (n : ℕ) {ι : Type*} (s : Finset ι) (P : ι → ℝ[X]) :
    sumZeroes n (∑ i ∈ s, P i) = ∑ i ∈ s, sumZeroes n (P i) := by
  unfold sumZeroes
  simp_rw [eval_finset_sum]
  rw [sum_comm, mul_sum]

@[simp]
theorem sumZeroes_smul (n : ℕ) (c : ℝ) (P : ℝ[X]) :
    sumZeroes n (c • P) = c * sumZeroes n P := by
  unfold sumZeroes
  simp_rw [eval_smul, ← smul_sum, smul_eq_mul]
  ring

theorem sumZeroes_T_zero {n : ℕ} (hn : n ≠ 0) :
    sumZeroes n (T ℝ 0) = π := by
  simp [sumZeroes, show π / n * n = π by field]

theorem sumZeroes_T_of_ne_zero {n : ℕ} {k : ℤ} (hk₀ : k ≠ 0) (hk₁ : k.natAbs < 2 * n) :
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

-- This probably belongs somewhere else
theorem poly_eq_sum_of_deg {F : Type*} [Field F] {n : ℕ} {P : F[X]} {Q : Fin n → F[X]}
    (hP : P.degree < n) (hQ : ∀ i, (Q i).degree = i) :
    ∃ c : Fin n → F, P = ∑ i, c i • Q i := by
  cases hd : P.degree
  case bot =>
    use fun _ => 0
    simp [P.degree_eq_bot.mp hd]
  case coe d =>
    replace hP : d < n := by rw [hd] at hP; exact WithBot.coe_lt_coe.mp hP
    induction d using Nat.strong_induction_on generalizing P
    case h d hind =>
      let γ := P.coeff d / (Q ⟨d, hP⟩).coeff d
      let cγ (i : Fin n) := if i = d then γ else 0
      have hcγ : ∑ i, cγ i • Q i = γ • Q ⟨d, hP⟩ := by
        rw [sum_eq_single ⟨d, hP⟩ (by aesop) (by simp)]
        simp [cγ]
      let P' := P - γ • Q ⟨d, hP⟩
      have hP' : P'.degree < d := by
        refine (degree_lt_iff_coeff_zero _ _).mpr (fun m hm => ?_)
        by_cases! m = d
        case pos hm' =>
          have : (Q ⟨d, hP⟩).coeff d ≠ 0 := coeff_ne_zero_of_eq_degree (hQ ⟨d, hP⟩)
          simp [hm', P', γ]; field
        case neg hm' =>
          have : P'.degree < d + 1 := by
            suffices P'.degree ≤ d by
              grw [this]
              rw [← Nat.cast_one, ← Nat.cast_add]
              norm_cast
              simp
            have := degree_sub_le P (γ • Q ⟨d, hP⟩)
            grw [this, hd, degree_smul_le, hQ]
            simp; rfl
          apply (degree_lt_iff_coeff_zero _ _).mp this
          grind
      cases hd' : P'.degree
      case bot =>
        use cγ
        suffices P = γ • Q ⟨d, hP⟩ by rw [this, hcγ]
        have := P'.degree_eq_bot.mp hd'
        grind
      case coe d' =>
        have : d' < d := by rw [hd'] at hP'; exact WithBot.coe_lt_coe.mp hP'
        obtain ⟨c, hc⟩ := hind d' this hd' (by grind)
        use fun i => c i + cγ i
        simp_rw [add_smul]
        rw [sum_add_distrib, ← hc, hcγ]
        grind

theorem integral_eq_sumZeroes {n : ℕ} {P : ℝ[X]} (hn : n ≠ 0) (hP : P.degree < 2 * n) :
    ∫ x in -1..1, P.eval x * (1 / √(1 - x ^ 2)) = sumZeroes n P := by
  obtain ⟨c, rfl⟩ := poly_eq_sum_of_deg hP (fun i => show (T ℝ i).degree = i by simp; rfl)
  simp_rw [eval_finset_sum, eval_smul, sum_mul]
  rw [intervalIntegral.integral_finset_sum, sumZeroes_sum]
  · simp_rw [sumZeroes_smul, smul_eq_mul, mul_assoc, intervalIntegral.integral_const_mul]
    congr! with i hi
    by_cases i.val = 0
    case pos hi => rw [hi, Nat.cast_zero, integral_T_real_zero, sumZeroes_T_zero hn]
    case neg hi =>
      rw [integral_T_real_of_ne_zero (by grind),
        sumZeroes_T_of_ne_zero (by grind) (by convert i.isLt)]
  · simp_rw [← eval_smul]
    exact fun i hi => integrable_poly_T _

end Polynomial.Chebyshev
