/-
Copyright (c) 2025 Janos Wolosz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Janos Wolosz
-/
import Mathlib.Algebra.Algebra.Defs
import Mathlib.Algebra.BigOperators.GroupWithZero.Action
import Mathlib.Data.Nat.Cast.Field
import Mathlib.RingTheory.Nilpotent.Basic

/-!
# Exponential map on algebras

This file defines the exponential map `Algebra.exp` on `ℚ`-algebras. The definition of
`Algebra.exp a` applies to any element `a` in an algebra over `ℚ`, though it yields meaningful
(non-junk) values only when `a` is nilpotent.

The main result is `Algebra.exp_add_of_commute`, which establishes the expected connection between
the additive and multiplicative structures of `A` for commuting nilpotent elements.

Furthermore, in case `A` is a ring and `a` is nilpotent, `Algebra.exp_of_nilpotent_is_unit` shows
that `Algebra.exp a` is a unit in `A`.

Note: Although the definition works with `ℚ`-algebras, the results apply to any algebra over a
characteristic zero field.

## Main definitions

  * `Algebra.exp`

## Tags

algebra, exponential map, nilpotent
-/

namespace Algebra

variable {A : Type*} [Ring A] [Algebra ℚ A]

open Finset

/-- The exponential map on algebras, defined in analogy with the usual exponential series.
It provides meaningful (non-junk) values for nilpotent elements. -/
noncomputable def exp (a : A) : A :=
  ∑ i ∈ range (nilpotencyClass a), (i.factorial : ℚ)⁻¹ • (a ^ i)

theorem exp_eq_truncated {a : A} {k : ℕ}  (h : a ^ k = 0) :
    ∑ i ∈ range k, (i.factorial : ℚ)⁻¹ • (a ^ i) = exp a := by
  have h₁ : ∑ i ∈ range k, (i.factorial : ℚ)⁻¹ • (a ^ i) =
      ∑ i ∈ range (nilpotencyClass a), (i.factorial : ℚ)⁻¹ • (a ^ i) +
        ∑ i ∈ Ico (nilpotencyClass a) k, (i.factorial : ℚ)⁻¹ • (a ^ i) :=
    (sum_range_add_sum_Ico _ (csInf_le' h)).symm
  suffices ∑ i ∈ Ico (nilpotencyClass a) k, (i.factorial : ℚ)⁻¹ • (a ^ i) = 0 by
    dsimp [exp]
    rw [h₁, this, add_zero]
  exact sum_eq_zero fun _ h₂ => by
    rw [pow_eq_zero_of_le (mem_Ico.1 h₂).1 (pow_nilpotencyClass ⟨k, h⟩), smul_zero]

theorem exp_zero_eq_one : exp (0 : A) = 1 := by
  have h₁ := exp_eq_truncated (pow_one (0 : A))
  rw [range_one, sum_singleton, Nat.factorial_zero, Nat.cast_one, inv_one, pow_zero,
    one_smul] at h₁
  exact h₁.symm

theorem exp_add_of_commute {a b : A} (h₁ : Commute a b) (h₂ : IsNilpotent a) (h₃ : IsNilpotent b) :
    exp (a + b) = exp a * exp b := by
  obtain ⟨n₁, hn₁⟩ := h₂
  obtain ⟨n₂, hn₂⟩ := h₃
  let N := n₁ ⊔ n₂
  have h₄ : a ^ (N + 1) = 0 := pow_eq_zero_of_le (by omega) hn₁
  have h₅ : b ^ (N + 1) = 0 := pow_eq_zero_of_le (by omega) hn₂
  rw [← exp_eq_truncated (k := 2 * N + 1)
  (Commute.add_pow_eq_zero_of_add_le_succ_of_pow_eq_zero h₁ h₄ h₅ (by omega)),
  ← exp_eq_truncated h₄, ← exp_eq_truncated h₅]
  have s₁ := calc
    ∑ i ∈ range (2 * N + 1), (i.factorial : ℚ)⁻¹ • (a + b) ^ i =
      ∑ i ∈ range (2 * N + 1), (i.factorial : ℚ)⁻¹ •
        (∑ j ∈ range (i + 1), a ^ j * b ^ (i - j) * i.choose j) := by
      apply sum_congr rfl
      intro i _
      rw [Commute.add_pow h₁ i]
    _ = ∑ i ∈ range (2 * N + 1), (∑ j ∈ range (i + 1), ((j.factorial : ℚ)⁻¹ *
          ((i - j).factorial : ℚ)⁻¹) • (a ^ j * b ^ (i - j))) := by
      apply sum_congr rfl
      intro i hi
      rw [smul_sum]
      apply sum_congr rfl
      intro j hj
      simp only [mem_range] at hi hj
      suffices (i.factorial : ℚ)⁻¹ * (i.choose j) =
          ((j.factorial : ℚ)⁻¹ * ((i - j).factorial : ℚ)⁻¹) by
        rw [← Nat.cast_commute (i.choose j), ← this, ← Algebra.mul_smul_comm, ← nsmul_eq_mul,
        mul_smul, ← smul_assoc, smul_comm, smul_assoc]
        norm_cast
      rw [Nat.choose_eq_factorial_div_factorial (Nat.le_of_lt_succ hj), Nat.cast_div, mul_div]
      · rw [inv_mul_cancel₀ (mod_cast Nat.factorial_ne_zero i), Nat.cast_mul, one_div,
        mul_inv_rev, mul_comm]
      · exact Nat.factorial_mul_factorial_dvd_factorial (Nat.le_of_lt_succ hj)
      rw [Nat.cast_mul]
      apply mul_ne_zero <;> exact_mod_cast Nat.factorial_ne_zero _
    _ = ∑ ij ∈ (range (2 * N + 1)).product (range (2 * N + 1)) with ij.1 + ij.2 <= 2 * N,
          ((ij.1.factorial : ℚ)⁻¹ * (ij.2.factorial : ℚ)⁻¹) • (a ^ ij.1 * b ^ ij.2) := by
      rw [sum_sigma']
      apply sum_bij (fun ⟨i, j⟩ _ => (j, i - j))
      · simp only [mem_sigma, mem_range, product_eq_sprod, mem_filter, mem_product, and_imp]
        (intro _ _ _; omega)
      · simp only [mem_sigma, mem_range, Prod.mk.injEq, and_imp]
        (intro _ _ _ _ _ _ h _; exact Sigma.ext (by omega) (heq_of_eq h))
      · simp only [product_eq_sprod, mem_filter, mem_product, mem_range, mem_sigma, exists_prop,
          Sigma.exists, and_imp, Prod.forall, Prod.mk.injEq]
        (intro h₁ h₂ _ _ _; use h₁ + h₂, h₁; omega)
      simp only [mem_sigma, mem_range, implies_true]
  have z₁ : ∑ ij ∈ ((range (2 * N + 1)).product (range (2 * N + 1))) with ¬ ij.1 + ij.2 ≤ 2 * N,
      ((ij.1.factorial : ℚ)⁻¹ * (ij.2.factorial : ℚ)⁻¹) • (a ^ ij.1 * b ^ ij.2) = 0 :=
    sum_eq_zero fun i hi ↦ by
      rw [mem_filter] at hi
      cases le_or_lt (N + 1) i.1 with
        | inl h => rw [pow_eq_zero_of_le h h₄, zero_mul, smul_zero]
        | inr _ => rw [pow_eq_zero_of_le (by linarith) h₅, mul_zero, smul_zero]
  have split₁ := sum_filter_add_sum_filter_not ((range (2 * N + 1)).product (range (2 * N + 1)))
    (fun ij => ij.1 + ij.2 ≤ 2 * N)
    (fun ij => ((ij.1.factorial : ℚ)⁻¹ * (ij.2.factorial : ℚ)⁻¹) • (a ^ ij.1 * b ^ ij.2))
  rw [z₁, product_eq_sprod, add_zero] at split₁
  rw [product_eq_sprod, split₁] at s₁
  have z₂ : ∑ ij ∈ ((range (2 * N + 1)).product (range (2 * N + 1))) with ¬ (ij.1 ≤ N ∧ ij.2 ≤ N),
      ((ij.1.factorial : ℚ)⁻¹ * (ij.2.factorial : ℚ)⁻¹) • (a ^ ij.1 * b ^ ij.2) = 0 :=
    sum_eq_zero fun i hi ↦ by
    simp only [not_and, not_le, mem_filter] at hi
    cases le_or_lt (N + 1) i.1 with
      | inl h => rw [pow_eq_zero_of_le h h₄, zero_mul, smul_zero]
      | inr h => rw [pow_eq_zero_of_le (hi.2 (Nat.le_of_lt_succ h)) h₅, mul_zero, smul_zero]
  have split₂ := sum_filter_add_sum_filter_not ((range (2 * N + 1)).product (range (2 * N + 1)))
    (fun ij => ij.1 ≤ N ∧ ij.2 ≤ N)
    (fun ij => ((ij.1.factorial : ℚ)⁻¹ * (ij.2.factorial : ℚ)⁻¹) • (a ^ ij.1 * b ^ ij.2))
  rw [z₂, product_eq_sprod, add_zero] at split₂
  rw [← split₂] at s₁
  have restrict: ∑ ij ∈ (range (2 * N + 1)).product (range (2 * N + 1)) with ij.1 ≤ N ∧ ij.2 ≤ N,
      ((ij.1.factorial : ℚ)⁻¹ * (ij.2.factorial : ℚ)⁻¹) • (a ^ ij.1 * b ^ ij.2) =
        ∑ ij ∈ (range (N + 1)).product (range (N + 1)), ((ij.1.factorial : ℚ)⁻¹ *
      (ij.2.factorial : ℚ)⁻¹) • (a ^ ij.1 * b ^ ij.2) := by
    apply sum_congr
    · ext x
      simp only [product_eq_sprod, mem_filter, mem_product, mem_range]
      constructor <;> omega
    · (intro _ _; rfl)
  simp only [product_eq_sprod] at restrict
  rw [restrict] at s₁
  have s₂ := calc
    (∑ i ∈ range (N + 1), (i.factorial : ℚ)⁻¹ • a ^ i) * ∑ i ∈ range (N + 1),
      (i.factorial : ℚ)⁻¹ • b ^ i = ∑ i ∈ range (N + 1), ∑ j ∈ range (N + 1),
        ((i.factorial : ℚ)⁻¹ * (j.factorial : ℚ)⁻¹) • (a ^ i * b ^ j) := by
      rw [sum_mul_sum]
      apply sum_congr rfl
      intro _ _
      apply sum_congr rfl
      intro _ _
      rw [smul_mul_assoc, Algebra.mul_smul_comm, smul_smul]
    _ = ∑ ij ∈ (range (N + 1)).product (range (N + 1)), ((ij.1.factorial : ℚ)⁻¹ *
          (ij.2.factorial : ℚ)⁻¹) • (a ^ ij.1 * b ^ ij.2) := by
      rw [sum_sigma']
      apply sum_bijective (fun ⟨i, j⟩ => (i, j))
      exact ⟨fun ⟨i, j⟩ ⟨i', j'⟩ h => by cases h; rfl, fun ⟨i, j⟩ => ⟨⟨i, j⟩, rfl⟩⟩
      · simp only [mem_sigma, product_eq_sprod, mem_product, implies_true]
      simp only [implies_true]
  simp only [product_eq_sprod] at s₂
  rw [s₂.symm] at s₁
  exact s₁

theorem exp_of_nilpotent_is_unit {a : A} (h : IsNilpotent a) : IsUnit (exp a) := by
  have h₁ : Commute a (-a) := Commute.neg_right rfl
  have h₂ : IsNilpotent (-a) := IsNilpotent.neg h
  have h₃ := exp_add_of_commute h₁ h h₂
  rw [add_neg_cancel a, exp_zero_eq_one] at h₃
  apply isUnit_iff_exists.2
  refine ⟨exp (-a), h₃.symm, ?_⟩
  rw [← exp_add_of_commute h₁.symm h₂ h, neg_add_cancel a, exp_zero_eq_one]

end Algebra
