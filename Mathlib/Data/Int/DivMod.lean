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

theorem ediv_ediv_eq_ediv_mul (m : Int) {n k : Int} (hn : 0 < n) (hk : 0 < k) :
    m / n / k = m / (n * k) := by
  have ineq1 := Int.ediv_le_ediv (Int.mul_pos hk hn) (calc
    m / n / k * (k * n) ≤ m / n / k * (k * n) + (m / n % k * n + m % n) :=
      Int.le_add_of_nonneg_right (Int.add_nonneg
        (Int.mul_nonneg (Int.emod_nonneg _
          (Ne.symm (Int.ne_of_lt hk))) (Int.le_of_lt hn))
        (emod_nonneg _ (Ne.symm (Int.ne_of_lt hn))))
    _ = (m / n / k * k + m / n % k) * n + m % n := by
      rw [Int.add_mul, Int.mul_assoc, Int.add_assoc]
    _ = m := by rw [ediv_add_emod', ediv_add_emod'])
  rw [mul_ediv_cancel _ (Ne.symm (Int.ne_of_lt (Int.mul_pos hk hn))), Int.mul_comm] at ineq1
  have ineq2 := Int.le_of_lt_add_one (Int.ediv_lt_of_lt_mul (Int.mul_pos hn hk) (calc
    m = (m / n / k * k + m / n % k) * n + m % n := by rw [ediv_add_emod', ediv_add_emod']
    _ = m / n / k * (n * k) + (m / n % k * n + m % n) := by
        rw [Int.add_mul, Int.mul_assoc, Int.mul_comm n, Int.add_assoc]
    _ < m / n / k * (n * k) + ((k-1) * n + n) := by
      refine Int.add_lt_add_of_le_of_lt (Int.le_refl _)
        (Int.add_lt_add_of_le_of_lt ?_ (emod_lt_of_pos _ hn))
      exact Int.mul_le_mul_of_nonneg_right
        (le_sub_one_of_lt (emod_lt_of_pos (m / n) hk)) (Int.le_of_lt hn)
    _ = (m / n / k + 1) * (n * k) := by
      rw [Int.sub_mul, Int.add_mul, Int.one_mul, Int.one_mul, Int.sub_add_cancel, Int.mul_comm k]))
  exact Int.le_antisymm ineq1 ineq2

theorem fdiv_fdiv_eq_fdiv_mul (m : Int) {n k : Int} (hn : 0 < n) (hk : 0 < k) :
    (m.fdiv n).fdiv k = m.fdiv (n * k) := by
  rw [Int.fdiv_eq_ediv_of_nonneg _ (Int.le_of_lt hn),
    Int.fdiv_eq_ediv_of_nonneg _ (Int.le_of_lt hk),
    Int.fdiv_eq_ediv_of_nonneg _ (Int.le_of_lt (Int.mul_pos hn hk)),
    ediv_ediv_eq_ediv_mul _ hn hk]

/-! ### `emod` -/

theorem emod_eq_sub_self_emod {a b : Int} : a % b = (a - b) % b :=
  (emod_sub_cancel a b).symm

end Int
