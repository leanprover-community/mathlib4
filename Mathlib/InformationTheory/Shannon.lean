/-
Copyright (c) 2026 Victor Boscaro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Victor Boscaro
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Data.Finset.Card

/-!
# Discrete Shannon entropy

This file defines the discrete Shannon entropy of a finitely-supported probability
distribution and proves the maximum-entropy bound: the entropy of any probability
distribution on a finite set `S` is at most `Real.log |S|`. This is the discrete
Gibbs inequality with the uniform reference distribution.

## Main definitions

* `Shannon.entropy`: discrete Shannon entropy `∑ x ∈ S, negMulLog (p x)` of a function
  `p : α → ℝ` over a `Finset`.

## Main results

* `Shannon.entropy_le_log_card`: for any nonneg `p` summing to `1` over a finite set `S`,
  `Shannon.entropy p S ≤ Real.log S.card`.

## References

* [Shannon, *A Mathematical Theory of Communication*][shannon1948]

## Tags

information theory, entropy, Shannon entropy, maximum entropy
-/

@[expose] public section

namespace Shannon

/-- Discrete Shannon entropy of `p : α → ℝ` summed over a finite set `S`. -/
noncomputable def entropy {α : Type*} (p : α → ℝ) (S : Finset α) : ℝ :=
  ∑ x ∈ S, Real.negMulLog (p x)

/-- **Maximum-entropy bound.** A nonneg function `p : α → ℝ` with total mass `1` over a
finite set `S` has discrete entropy at most `Real.log |S|`. -/
theorem entropy_le_log_card {α : Type*} {p : α → ℝ} {S : Finset α}
    (hp_nn : ∀ x ∈ S, 0 ≤ p x) (hp_sum : ∑ x ∈ S, p x = 1) :
    entropy p S ≤ Real.log S.card := by
  have hS_ne : S.Nonempty := by
    rcases Finset.eq_empty_or_nonempty S with rfl | hne
    · simp at hp_sum
    · exact hne
  set n : ℝ := (S.card : ℝ) with hn_def
  have hn_pos : 0 < n := by
    rw [hn_def]; exact_mod_cast Finset.card_pos.mpr hS_ne
  have key : ∀ x ∈ S, p x * n - 1 ≤ (p x * n) * Real.log (p x * n) := fun x hx =>
    Real.self_sub_one_le_mul_log (mul_nonneg (hp_nn x hx) hn_pos.le)
  have sum_ineq : ∑ x ∈ S, (p x * n - 1) ≤ ∑ x ∈ S, (p x * n) * Real.log (p x * n) :=
    Finset.sum_le_sum key
  have lhs_zero : ∑ x ∈ S, (p x * n - 1) = 0 := by
    have h1 : ∑ x ∈ S, p x * n = n := by
      rw [show (∑ x ∈ S, p x * n) = (∑ x ∈ S, p x) * n from (Finset.sum_mul ..).symm,
          hp_sum, one_mul]
    rw [Finset.sum_sub_distrib, h1, Finset.sum_const, Nat.smul_one_eq_cast, hn_def]
    ring
  have rhs_pointwise : ∀ x ∈ S, (p x * n) * Real.log (p x * n)
      = n * (p x * Real.log (p x)) + p x * (n * Real.log n) := by
    intros x hx
    rcases eq_or_lt_of_le (hp_nn x hx) with hpx_eq | hpx_pos
    · rw [← hpx_eq]; simp
    · rw [Real.log_mul hpx_pos.ne' hn_pos.ne']; ring
  have rhs_eq : ∑ x ∈ S, (p x * n) * Real.log (p x * n)
      = n * (∑ x ∈ S, p x * Real.log (p x)) + n * Real.log n := by
    rw [Finset.sum_congr rfl rhs_pointwise]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul, hp_sum, one_mul]
  rw [lhs_zero, rhs_eq] at sum_ineq
  unfold entropy
  have entropy_neg : ∑ x ∈ S, Real.negMulLog (p x) = -(∑ x ∈ S, p x * Real.log (p x)) := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl (fun x _ => ?_)
    rw [Real.negMulLog]; ring
  rw [entropy_neg]
  have h_factored : 0 ≤ n * ((∑ x ∈ S, p x * Real.log (p x)) + Real.log n) := by
    have : n * ((∑ x ∈ S, p x * Real.log (p x)) + Real.log n)
         = n * (∑ x ∈ S, p x * Real.log (p x)) + n * Real.log n := by ring
    linarith [this, sum_ineq]
  have h_div : 0 ≤ (∑ x ∈ S, p x * Real.log (p x)) + Real.log n :=
    (mul_nonneg_iff_of_pos_left hn_pos).mp h_factored
  linarith

end Shannon

end
