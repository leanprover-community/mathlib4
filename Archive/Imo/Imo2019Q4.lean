/-
Copyright (c) 2020 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn
-/
import Mathlib.Data.Nat.Factorial.BigOperators
import Mathlib.Data.Nat.Multiplicity
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.GCongr

#align_import imo.imo2019_q4 from "leanprover-community/mathlib"@"308826471968962c6b59c7ff82a22757386603e3"

/-!
# IMO 2019 Q4

Find all pairs `(k, n)` of positive integers such that
```
  k! = (2 ^ n - 1)(2 ^ n - 2)(2 ^ n - 4)···(2 ^ n - 2 ^ (n - 1))
```
We show in this file that this property holds iff `(k, n) = (1, 1) ∨ (k, n) = (3, 2)`.

Proof sketch:
The idea of the proof is to count the factors of 2 on both sides. The LHS has less than `k` factors
of 2, and the RHS has exactly `n * (n - 1) / 2` factors of 2. So we know that `n * (n - 1) / 2 < k`.
Now for `n ≥ 6` we have `RHS < 2 ^ (n ^ 2) < (n(n-1)/2)! < k!`. We then treat the cases `n < 6`
individually.
-/


open scoped Nat

open Nat hiding zero_le Prime

open Finset multiplicity

namespace Imo2019Q4

theorem upper_bound {k n : ℕ} (hk : k > 0)
    (h : (k ! : ℤ) = ∏ i ∈ range n, ((2:ℤ) ^ n - (2:ℤ) ^ i)) : n < 6 := by
  have h2 : ∑ i ∈ range n, i < k := by
    suffices multiplicity 2 (k ! : ℤ) = ↑(∑ i ∈ range n, i : ℕ) by
      rw [← PartENat.coe_lt_coe, ← this]; change multiplicity ((2 : ℕ) : ℤ) _ < _
      simp_rw [Int.natCast_multiplicity, multiplicity_two_factorial_lt hk.lt.ne.symm]
    rw [h, multiplicity.Finset.prod Int.prime_two, Nat.cast_sum]
    apply sum_congr rfl; intro i hi
    rw [multiplicity_sub_of_gt, multiplicity_pow_self_of_prime Int.prime_two]
    rwa [multiplicity_pow_self_of_prime Int.prime_two, multiplicity_pow_self_of_prime Int.prime_two,
      PartENat.coe_lt_coe, ← mem_range]
  rw [← not_le]; intro hn
  apply _root_.ne_of_gt _ h
  calc ∏ i ∈ range n, ((2:ℤ) ^ n - (2:ℤ) ^ i) ≤ ∏ __ ∈ range n, (2:ℤ) ^ n := ?_
    _ < ↑ k ! := ?_
  · gcongr
    · intro i hi
      simp only [mem_range] at hi
      have : (2:ℤ) ^ i ≤ (2:ℤ) ^ n := by gcongr; norm_num
      linarith
    · apply sub_le_self
      positivity
  norm_cast
  calc ∏ __ ∈ range n, 2 ^ n = 2 ^ (n * n) := by rw [prod_const, card_range, ← pow_mul]
    _ < (∑ i ∈ range n, i)! := ?_
    _ ≤ k ! := by gcongr
  clear h h2
  induction' n, hn using Nat.le_induction with n' hn' IH
  · decide
  let A := ∑ i ∈ range n', i
  have le_sum : ∑ i ∈ range 6, i ≤ A := by
    apply sum_le_sum_of_subset
    simpa using hn'
  calc 2 ^ ((n' + 1) * (n' + 1))
      ≤ 2 ^ (n' * n' + 4 * n') := by gcongr <;> linarith
    _ = 2 ^ (n' * n') * (2 ^ 4) ^ n' := by rw [← pow_mul, ← pow_add]
    _ < A ! * (2 ^ 4) ^ n' := by gcongr
    _ = A ! * (15 + 1) ^ n' := rfl
    _ ≤ A ! * (A + 1) ^ n' := by gcongr; exact le_sum
    _ ≤ (A + n')! := factorial_mul_pow_le_factorial
    _ = (∑ i ∈ range (n' + 1), i)! := by rw [sum_range_succ]
#align imo2019_q4.upper_bound Imo2019Q4.upper_bound

end Imo2019Q4

theorem imo2019_q4 {k n : ℕ} (hk : k > 0) (hn : n > 0) :
    (k ! : ℤ) = ∏ i ∈ range n, ((2:ℤ) ^ n - (2:ℤ) ^ i) ↔ (k, n) = (1, 1) ∨ (k, n) = (3, 2) := by
  -- The implication `←` holds.
  constructor
  swap
  · rintro (h | h) <;> simp [Prod.ext_iff] at h <;> rcases h with ⟨rfl, rfl⟩ <;> decide
  intro h
  -- We know that n < 6.
  have := Imo2019Q4.upper_bound hk h
  interval_cases n
  -- n = 1
  · norm_num at h; simp [le_antisymm h (succ_le_of_lt hk)]
  -- n = 2
  · right; congr; norm_num [prod_range_succ] at h; norm_cast at h; rwa [← factorial_inj']
    norm_num
  all_goals exfalso; norm_num [prod_range_succ] at h; norm_cast at h
  -- n = 3
  · refine monotone_factorial.ne_of_lt_of_lt_nat 5 ?_ ?_ _ h <;> decide
  -- n = 4
  · refine monotone_factorial.ne_of_lt_of_lt_nat 7 ?_ ?_ _ h <;> decide
  -- n = 5
  · refine monotone_factorial.ne_of_lt_of_lt_nat 10 ?_ ?_ _ h <;> decide
#align imo2019_q4 imo2019_q4
