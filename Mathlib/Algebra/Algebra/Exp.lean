/-
Copyright (c) 2025 Janos Wolosz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Janos Wolosz
-/
import Mathlib.Algebra.Algebra.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.GroupWithZero.Action
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.Group.Basic
import Mathlib.RingTheory.Nilpotent.Basic
import Mathlib.Data.Nat.Cast.Field
import Mathlib.Data.Sigma.Basic
import LeanCopilot

/-!
# Exponential map on algebras

This file defines the exponential map `Algebra.exp` on algebras. The definition of `Algebra.exp a`
applies to any `R`-algebra `A` and any element `a`, though it yields meaningful (non-junk)
values only when `a` is nilpotent.

When `R` is a characteristic zero field, the theorem `Algebra.exp_add_of_commute` establishes
the expected connection between the additive and multiplicative structures of `A` for commuting
nilpotent elements.

Furthermore, in case `A` is a ring (rather than a general semiring) and `a` is nilpotent,
`Algebra.exp_of_nilpotent_is_unit` shows that `Algebra.exp a` is a unit in `A`.

## Main definitions

  * `Algebra.exp`

## Tags

algebra, exponential map, nilpotent
-/

universe u v

namespace Algebra

variable (R : Type u) [Field R]
variable (A : Type v)

open Finset

section SemiringAlgebras

variable [Semiring A] [Algebra R A]

/-- The exponential map on algebras, defined in analogy with the usual exponential series.
It provides meaningful (non-junk) values for nilpotent elements. -/
noncomputable def exp (a : A) : A :=
  ∑ n ∈ range (nilpotencyClass a), (n.factorial : R)⁻¹ • (a ^ n)

theorem exp_eq_truncated {k : ℕ} (a : A) (h : a ^ k = 0) :
    ∑ n ∈ range k, (Nat.factorial n : R)⁻¹ • (a ^ n) = exp R A a := by
  have h₁ : ∑ n ∈ range k, (Nat.factorial n : R)⁻¹ • (a ^ n) =
      ∑ n ∈ range (nilpotencyClass a), (Nat.factorial n : R)⁻¹ • (a ^ n) +
        ∑ n ∈ Ico (nilpotencyClass a) k, (Nat.factorial n : R)⁻¹ • (a ^ n) :=
    (sum_range_add_sum_Ico _ (csInf_le' h)).symm
  suffices ∑ n ∈ Ico (nilpotencyClass a) k, (Nat.factorial n : R)⁻¹ • (a ^ n) = 0 by
    dsimp [exp]
    rw [h₁, this, add_zero]
  exact sum_eq_zero fun _ h₂ => by
    rw [pow_eq_zero_of_le (mem_Ico.1 h₂).1 (pow_nilpotencyClass ⟨k, h⟩), smul_zero]

theorem exp_zero_eq_one : exp R A 0 = 1 := by
  have h₁ := exp_eq_truncated R A (0 : A) (pow_one 0)
  rw [range_one, sum_singleton, Nat.factorial_zero, Nat.cast_one, inv_one, pow_zero,
    one_smul] at h₁
  exact h₁.symm


--example (n : ℕ) (a : A) : (n.factorial : R) • ((n.factorial : R)⁻¹ • a) = a := by
--have h1 : (n.factorial : R) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
--simp_all only [ne_eq, Nat.cast_eq_zero, not_false_eq_true, smul_inv_smul₀]
  --exact mul_inv_cancel₀ h1


-- useful: add_pow_eq_zero_of_add_le_succ_of_pow_eq_zero
-- useful: add_pow (h : Commute x y) (n : ℕ) : ...
-- useful: isNilpotent_add (h_comm : Commute x y) ...

variable [CharZero R]

theorem exp_add_of_commute (a b : A) (h₁ : Commute a b) (h₂ : IsNilpotent a) (h₃ : IsNilpotent b) :
    exp R A (a + b) = exp R A a * exp R A b := by
  obtain ⟨n₁, hn₁⟩ := h₂
  obtain ⟨n₂, hn₂⟩ := h₃
  let N := n₁ ⊔ n₂
  have le₁ : n₁ ≤ N + 1 := by omega
  have le₂ : n₂ ≤ N + 1 := by omega
  have h₄ : a ^ (N + 1) = 0 := pow_eq_zero_of_le le₁ hn₁
  have h₅ : b ^ (N + 1) = 0 := pow_eq_zero_of_le le₂ hn₂
  have le₃ : (N + 1) + (N + 1) ≤ (2 * N + 1) + 1 := by omega
  have h₆ : (a + b) ^ (2 * N + 1) = 0 :=
    Commute.add_pow_eq_zero_of_add_le_succ_of_pow_eq_zero h₁ h₄ h₅ le₃
  rw [← exp_eq_truncated R A (a + b) h₆, ← exp_eq_truncated R A a h₄, ← exp_eq_truncated R A b h₅]

 -- have  hh (n : ℕ) (a : A) : n * a = (n : R) • a := by
  --  norm_cast
  --  simp_all only [nsmul_eq_mul, N]
  have s₁ :=
    calc
      ∑ n ∈ range (2 * N + 1), (n.factorial : R)⁻¹ • (a + b) ^ n
          = ∑ n ∈ range (2 * N + 1), (n.factorial : R)⁻¹ •
            (∑ m ∈ range (n + 1), a ^ m * b ^ (n - m) * n.choose m) := by
        apply sum_congr rfl
        intros n hn
        rw [Commute.add_pow h₁ n]
      _ = ∑ n ∈ range (2 * N + 1), (∑ m ∈ range (n + 1), ((m.factorial : R)⁻¹ *
            ((n - m).factorial : R)⁻¹) • (a ^ m * b ^ (n - m))) := by
        apply sum_congr rfl
        intro n hn
        rw [smul_sum]
        apply sum_congr rfl
        intro m hm
        simp_all only [mem_range]
        suffices (n.factorial : R)⁻¹ * (n.choose m) =
            ((m.factorial : R)⁻¹ * ((n - m).factorial : R)⁻¹) by
          have help : (n.factorial : R)⁻¹ • (a ^ m * b ^ (n - m) * (n.choose m)) =
              ((n.factorial : R)⁻¹ * (n.choose m)) • (a ^ m * b ^ (n - m)) := by
            rw [← Nat.cast_commute (n.choose m), mul_smul]
            norm_cast
            rw [nsmul_eq_mul]
          simp_all only [mem_range]
        have le₄ : m ≤ n := Nat.le_of_lt_succ hm
        rw [Nat.choose_eq_factorial_div_factorial le₄, Nat.cast_div, mul_div]
        · have inv : (n.factorial : R)⁻¹  * (n.factorial : R) = 1 := by
            have : (n.factorial : R) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
            simp_all only [ne_eq, Nat.cast_eq_zero, not_false_eq_true, inv_mul_cancel₀]
          rw [inv, Nat.cast_mul, one_div, mul_inv_rev, mul_comm]
        · exact Nat.factorial_mul_factorial_dvd_factorial le₄
        rw [Nat.cast_mul]
        apply mul_ne_zero <;> exact_mod_cast Nat.factorial_ne_zero _
      _ = ∑ ij ∈ (range (2 * N + 1)).product (range (2 * N + 1)) with ij.1 + ij.2 <= 2 * N,
            ((ij.1.factorial : R)⁻¹ * (ij.2.factorial : R)⁻¹) • (a ^ ij.1 * b ^ ij.2) := by
        rw [sum_sigma']
        apply sum_bij (fun ⟨i, j⟩ _ => (j, i - j))
        · simp only [mem_sigma, mem_range, product_eq_sprod, mem_filter, mem_product, and_imp]
          intro _ _ _
          try omega
        · simp only [mem_sigma, mem_range, Prod.mk.injEq, and_imp]
          (intro h1 h2 h3 h4 h5 h6 h7 h8; exact Sigma.ext (by omega) (heq_of_eq h7))
        · simp only [product_eq_sprod, mem_filter, mem_product, mem_range, mem_sigma, exists_prop,
            Sigma.exists, and_imp, Prod.forall, Prod.mk.injEq]
          (intro h1 h2 h3 h4 h5; use h1 + h2, h1; omega)
        simp only [mem_sigma, mem_range, implies_true]

  have z₁ : ∑ ij ∈ ((range (2 * N + 1)).product (range (2 * N + 1))) with ¬ ij.1 + ij.2 ≤ 2 * N,
      ((ij.1.factorial : R)⁻¹ * (ij.2.factorial : R)⁻¹) • (a ^ ij.1 * b ^ ij.2) = 0 := by
    apply sum_eq_zero
    intro i hi
    simp only [mem_filter] at hi
    obtain ⟨hi1, hi2⟩ := hi
    cases le_or_lt (N + 1) i.1 with
      | inl h => rw [pow_eq_zero_of_le h h₄, zero_mul, smul_zero]
      | inr _ => rw [pow_eq_zero_of_le (by linarith) h₅, mul_zero, smul_zero]

  have split₁ : ∑ ij ∈ (range (2 * N + 1)).product (range (2 * N + 1)), ((ij.1.factorial : R)⁻¹ *
      (ij.2.factorial : R)⁻¹) • (a ^ ij.1 * b ^ ij.2) =
        ∑ ij ∈ ((range (2 * N + 1)).product (range (2 * N + 1))) with ij.1 + ij.2 ≤ 2 * N,
          ((ij.1.factorial : R)⁻¹ * (ij.2.factorial : R)⁻¹) • (a ^ ij.1 * b ^ ij.2) +
        ∑ ij ∈ ((range (2 * N + 1)).product (range (2 * N + 1))) with ¬ ij.1 + ij.2 ≤ 2 * N,
          ((ij.1.factorial : R)⁻¹ * (ij.2.factorial : R)⁻¹) • (a ^ ij.1 * b ^ ij.2) := by
      rw [sum_filter_add_sum_filter_not]

  rw [z₁] at split₁
  simp only [product_eq_sprod, add_zero] at split₁
  simp only [product_eq_sprod] at s₁
  rw [← split₁] at s₁

  have z₂ : ∑ ij ∈ ((range (2 * N + 1)).product (range (2 * N + 1))) with ¬ (ij.1 ≤ N ∧ ij.2 ≤ N),
      ((ij.1.factorial : R)⁻¹ * (ij.2.factorial : R)⁻¹) • (a ^ ij.1 * b ^ ij.2) = 0 := by
    apply sum_eq_zero
    intro i hi
    simp at hi
    cases le_or_lt (N + 1) i.1 with
      | inl h => rw [pow_eq_zero_of_le h h₄, zero_mul, smul_zero]
      | inr h => rw [pow_eq_zero_of_le (hi.2 (Nat.le_of_lt_succ h)) h₅, mul_zero, smul_zero]

  have split₂ : ∑ ij ∈ (range (2 * N + 1)).product (range (2 * N + 1)),
      ((ij.1.factorial : R)⁻¹ * (ij.2.factorial : R)⁻¹) • (a ^ ij.1 * b ^ ij.2) =
          ∑ ij ∈ ((range (2 * N + 1)).product (range (2 * N + 1))) with ij.1 ≤ N ∧ ij.2 ≤ N,
            ((ij.1.factorial : R)⁻¹ * (ij.2.factorial : R)⁻¹) • (a ^ ij.1 * b ^ ij.2) +
          ∑ ij ∈ ((range (2 * N + 1)).product (range (2 * N + 1))) with ¬ (ij.1 ≤ N ∧ ij.2 ≤ N),
            ((ij.1.factorial : R)⁻¹ * (ij.2.factorial : R)⁻¹) • (a ^ ij.1 * b ^ ij.2) := by
      rw [sum_filter_add_sum_filter_not]

  rw [z₂] at split₂
  simp only [product_eq_sprod, add_zero] at split₂
  rw [split₂] at s₁

  have split₃: ∑ ij ∈ (range (2 * N + 1)).product (range (2 * N + 1)) with ij.1 ≤ N ∧ ij.2 ≤ N,
      ((ij.1.factorial : R)⁻¹ * (ij.2.factorial : R)⁻¹) • (a ^ ij.1 * b ^ ij.2) =
        ∑ ij ∈ (range (N + 1)).product (range (N + 1)), ((ij.1.factorial : R)⁻¹ *
      (ij.2.factorial : R)⁻¹) • (a ^ ij.1 * b ^ ij.2) := by
    apply sum_congr
    · ext x
      simp
      constructor <;> omega
    · intro x hx
      rfl

  simp only [product_eq_sprod] at split₃
  rw [split₃] at s₁

  have s₂ :=
    calc
      (∑ n ∈ range (N + 1), (n.factorial : R)⁻¹ • a ^ n) * ∑ n ∈ range (N + 1),
        (n.factorial : R)⁻¹ • b ^ n =
      ∑ i ∈ range (N + 1), ∑ j ∈ range (N + 1), ((i.factorial : R)⁻¹ * (j.factorial : R)⁻¹) •
        (a ^ i * b ^ j) := by
        rw [sum_mul_sum]
        apply sum_congr rfl
        intro n hn
        apply sum_congr rfl
        intro m hm
        rw [smul_mul_assoc, Algebra.mul_smul_comm, smul_smul]
      _ = ∑ ij ∈ (range (N + 1)).product (range (N + 1)), ((ij.1.factorial : R)⁻¹ *
          (ij.2.factorial : R)⁻¹) • (a ^ ij.1 * b ^ ij.2) := by
        rw [sum_sigma']
        apply sum_bij (fun ⟨i, j⟩ _ => (i, j))
        · simp only [mem_sigma, product_eq_sprod, mem_product, imp_self, implies_true]
        · simp only [mem_sigma, Prod.mk.injEq, and_imp]
          intro _ _ _ _ _ _ h₁ h₂
          exact Sigma.ext h₁ (heq_of_eq h₂)
        · simp only [product_eq_sprod, mem_product, mem_range, mem_sigma, exists_prop,
          Sigma.exists, and_imp, Prod.forall, Prod.mk.injEq, exists_eq_right_right, exists_eq_right]
          intro _ _ h₁ h₂
          exact ⟨h₁, h₂⟩
        simp only [implies_true]
  simp only [product_eq_sprod] at s₂
  rw [s₂.symm] at s₁
  exact s₁

end SemiringAlgebras

section RingAlgebras

variable [CharZero R]
variable [Ring A] [Algebra R A]

theorem exp_of_nilpotent_is_unit (a : A) (h : IsNilpotent a) : IsUnit (exp R A a) := by
  have h₁ : Commute a (-a) := Commute.neg_right rfl
  have h₂ : IsNilpotent (-a) := IsNilpotent.neg h
  have h₃ := exp_add_of_commute R A a (-a) h₁ h h₂
  rw [add_neg_cancel a, exp_zero_eq_one] at h₃
  apply isUnit_iff_exists.2
  refine ⟨exp R A (-a), h₃.symm, ?_⟩
  rw [← exp_add_of_commute R A (-a) a h₁.symm h₂ h, neg_add_cancel a, exp_zero_eq_one]

end RingAlgebras

end Algebra
