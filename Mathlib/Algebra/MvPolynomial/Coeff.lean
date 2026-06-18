/-
Copyright (c) 2026 Antoine Chambert-Loir, María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir, María Inés de Frutos-Fernández
-/
module

public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Data.Nat.Choose.Multinomial

/-!
# Formulas for coefficients of multivariate polynomials

## Main Results

* `MvPolynomial.coeff_add_pow`: the formula for the `d`th coefficient of `(X 0 + X 1) ^ n`.

-/

public section

noncomputable section

namespace MvPolynomial

open Finsupp

variable {R σ : Type*} [CommSemiring R] {s : σ →₀ ℕ}

private lemma coeff_linearCombination_X_pow_of_eq (a : σ →₀ R) {n : ℕ}
    (hs : s.sum (fun _ m ↦ m) = n) :
    coeff s (((a.linearCombination R X : MvPolynomial σ R)) ^ n) =
      s.multinomial * s.prod (fun r m ↦ a r ^ m) := by
  classical
  simp only [sum, linearCombination_apply, Finset.sum_pow_eq_sum_piAntidiag, coeff_sum,
    ← C_eq_coe_nat, coeff_C_mul, smul_eq_C_mul, mul_pow, Finset.prod_mul_distrib, ← map_pow,
    ← map_prod, coeff_prod_X_pow, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_eq_single (s : σ → ℕ)]
  · simp_rw [eq_indicator_self_iff]
    split_ifs with hs'
    · rw [prod_of_support_subset _ hs' _ (by simp), Finsupp.multinomial_of_support_subset hs']
    · rw [Finset.subset_iff] at hs'
      simp only [Finsupp.mem_support_iff, ne_eq, not_forall, Decidable.not_not] at hs'
      obtain ⟨i, hsi, hai⟩ := hs'
      rw [← mul_prod_erase _ i _ (by simpa), hai, zero_pow hsi, zero_mul, mul_zero]
  · simp only [Finset.mem_piAntidiag, ne_eq, Finsupp.mem_support_iff, ite_eq_right_iff, and_imp]
    intro _ _ _ _ hed
    simp [Finsupp.ext_iff] at hed
    grind
  · simp_rw [ite_eq_right_iff]
    intro hs' hs''
    rw [eq_indicator_self_iff] at hs''
    exfalso
    rw [Finset.mem_piAntidiag, not_and_or] at hs'
    rcases hs' with hs' | hs'
    · apply hs'
      rw [← hs, sum_of_support_subset _ hs'' _ (by simp)]
    · grind

private lemma coeff_linearCombination_X_pow_of_ne (a : σ →₀ R) {n : ℕ}
    (hs : s.sum (fun _ m ↦ m) ≠ n) :
    coeff s (((a.linearCombination R X : MvPolynomial σ R)) ^ n) = 0 := by
  classical
  simp only [sum, linearCombination_apply, Finset.sum_pow_eq_sum_piAntidiag, coeff_sum, ← map_pow,
    ← C_eq_coe_nat, coeff_C_mul, smul_eq_C_mul, mul_pow, Finset.prod_mul_distrib, ← map_prod,
    coeff_prod_X_pow, mul_ite, mul_one, mul_zero]
  apply Finset.sum_eq_zero (fun x hx ↦ ?_)
  rw [if_neg]
  rintro ⟨rfl⟩
  apply hs
  simp only [Finset.mem_piAntidiag] at hx
  rw [sum_of_support_subset _ (support_indicator_subset a.support _) _ (by simp), ← hx.1]
  congr
  ext i
  by_cases hi : i ∈ a.support
  · simp [Finsupp.indicator_of_mem hi]
  · grind [Finsupp.indicator_of_notMem hi]

lemma coeff_linearCombination_X_pow (a : σ →₀ R) (s : σ →₀ ℕ) (n : ℕ) :
    coeff s (((a.linearCombination R X : MvPolynomial σ R)) ^ n) =
      if s.sum (fun _ m ↦ m) = n then s.multinomial * s.prod (fun r m ↦ a r ^ m) else 0 := by
  split_ifs with hs
  · exact coeff_linearCombination_X_pow_of_eq a hs
  · exact coeff_linearCombination_X_pow_of_ne a hs

lemma coeff_linearCombination_X_pow_of_fintype [Fintype σ] (a : σ → R) (s : σ →₀ ℕ) (n : ℕ) :
    coeff s (((∑ i, a i • X i : MvPolynomial σ R)) ^ n) =
      if s.sum (fun _ m ↦ m) = n then s.multinomial * s.prod (fun r m ↦ a r ^ m) else 0 := by
  rw [← ofSupportFinite_coe (f := a) (hf := Set.toFinite _),
    prod_congr (fun r _ ↦ rfl), ← coeff_linearCombination_X_pow]
  simp [linearCombination_apply, sum_of_support_subset (s := Finset.univ)]

lemma coeff_sum_X_pow_of_fintype [Fintype σ] (d : σ →₀ ℕ) (n : ℕ) :
    coeff d (((∑ i, X i : MvPolynomial σ R)) ^ n) =
      if d.sum (fun _ m ↦ m) = n then d.multinomial else 0 := by
  have : (∑ i, X i : MvPolynomial σ R) = ∑ i, (1 : σ → R) i • X i := by simp
  simp [this, coeff_linearCombination_X_pow_of_fintype]

/-- The formula for the `d`th coefficient of `(X 0 + X 1) ^ n`. -/
theorem coeff_add_pow (d : Fin 2 →₀ ℕ) (n : ℕ) :
    coeff d ((X 0 + X 1 : MvPolynomial (Fin 2) R) ^ n) =
      if (d 0, d 1) ∈ Finset.antidiagonal n then n.choose (d 0) else 0 := by
  rw [← Fin.sum_univ_two, coeff_sum_X_pow_of_fintype]
  congr 1
  have : d.sum (fun x m ↦ m) = d 0 + d 1 := by
    simp [Finsupp.sum_of_support_subset d (Finset.subset_univ d.support)]
  simp only [Finset.mem_antidiagonal, this]
  split_ifs with hd
  · rw [multinomial_eq_of_support_subset (Finset.subset_univ d.support), Finset.univ_fin2,
      Nat.binomial_eq_choose Fin.zero_ne_one, hd]
  · rfl

end MvPolynomial
