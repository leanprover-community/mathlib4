/-
Copyright (c) 2024 Lean FRO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import Mathlib.Init

/-!
# Basic lemmas about division and modulo for integers

-/

namespace Int

/-! ### `ediv` and `fdiv` -/

theorem mul_ediv_le_mul_ediv_assoc {a : Int} (ha : 0 ≤ a) (b : Int) {c : Int} (hc : 0 ≤ c) :
    a * (b / c) ≤ a * b / c := by
  obtain rfl | hlt : c = 0 ∨ 0 < c := by omega
  · simp
  · rw [Int.le_ediv_iff_mul_le hlt, Int.mul_assoc]
    exact Int.mul_le_mul_of_nonneg_left (Int.ediv_mul_le b (Int.ne_of_gt hlt)) ha

theorem ediv_ediv_eq_ediv_mul (m : Int) {n k : Int} (hn : 0 ≤ n) :
    m / n / k = m / (n * k) := by
  have {k : Int} (hk : 0 < k) : m / n / k = m / (n * k) := by
    obtain rfl | hn' : n = 0 ∨ 0 < n := by omega
    · simp
    · apply Int.le_antisymm
      · apply Int.le_ediv_of_mul_le (Int.mul_pos hn' hk)
        calc
          m / n / k * (n * k) = m / n / k * k * n := by ac_rfl
          _ ≤ m / n * n :=
            Int.mul_le_mul_of_nonneg_right (Int.ediv_mul_le (m / n) (Int.ne_of_gt hk)) hn
          _ ≤ m :=
            Int.ediv_mul_le m (Int.ne_of_gt hn')
      · apply Int.le_ediv_of_mul_le hk
        rw [← Int.mul_ediv_mul_of_pos_left m n hk, Int.mul_comm m k, Int.mul_comm (_ / _) k]
        apply Int.mul_ediv_le_mul_ediv_assoc
        · exact Int.le_of_lt hk
        · exact Int.le_of_lt <| Int.mul_pos hn' hk
  · rcases Int.lt_trichotomy 0 k with hk | rfl | hk
    · exact this hk
    · simp
    · rw [← Int.neg_neg (m / n / k), ← Int.ediv_neg, this (Int.neg_pos_of_neg hk), ← Int.ediv_neg,
        Int.mul_neg, Int.neg_neg]

theorem fdiv_fdiv_eq_fdiv_mul (m : Int) {n k : Int} (hn : 0 ≤ n) (hk : 0 ≤ k) :
    (m.fdiv n).fdiv k = m.fdiv (n * k) := by
  rw [Int.fdiv_eq_ediv_of_nonneg _ hn,
    Int.fdiv_eq_ediv_of_nonneg _ hk,
    Int.fdiv_eq_ediv_of_nonneg _ (Int.mul_nonneg hn hk),
    ediv_ediv_eq_ediv_mul _ hn]

/-! ### `emod` -/

theorem emod_eq_sub_self_emod {a b : Int} : a % b = (a - b) % b :=
  (sub_emod_right a b).symm

end Int
