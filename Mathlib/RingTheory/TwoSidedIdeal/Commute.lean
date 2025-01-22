/-
Copyright (c) 2025 Antoine Chambert-Loir, María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir
-/


import Mathlib.Data.Nat.Choose.Sum
import Mathlib.RingTheory.TwoSidedIdeal.BigOperators

namespace TwoSidedIdeal

variable {R : Type*} [Ring R] (I : TwoSidedIdeal R) {a b : R}

theorem pow_mem_of_pow_mem {m n : ℕ} (ha : a ^ m ∈ I) (h : m ≤ n) : a ^ n ∈ I := by
  rw [← Nat.add_sub_of_le h, pow_add]
  exact I.mul_mem_right _ _ ha

theorem add_pow_mem_of_pow_mem_of_le {m n k : ℕ}
    (ha : a ^ m ∈ I) (hb : b ^ n ∈ I) (hk : m + n ≤ k + 1) (h : Commute a b) :
    (a + b) ^ k ∈ I := by
  rw [h.add_pow]
  apply I.finsetSum_mem
  intro c _
  apply mul_mem_right
  by_cases h : m ≤ c
  · exact I.mul_mem_right _ _ (I.pow_mem_of_pow_mem ha h)
  · refine I.mul_mem_left _ _ (I.pow_mem_of_pow_mem hb ?_)
    omega

theorem add_pow_add_pred_mem_of_pow_mem {m n : ℕ}
    (ha : a ^ m ∈ I) (hb : b ^ n ∈ I) (h : Commute a b) :
    (a + b) ^ (m + n - 1) ∈ I :=
  I.add_pow_mem_of_pow_mem_of_le ha hb (by rw [← Nat.sub_le_iff_le_add]) h

end TwoSidedIdeal


