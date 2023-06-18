/-
Copyright (c) 2020 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn

! This file was ported from Lean 3 source module imo.imo2019_q4
! leanprover-community/mathlib commit 308826471968962c6b59c7ff82a22757386603e3
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.Tactic.IntervalCases
import Mathlib.Algebra.BigOperators.Order
import Mathlib.Data.Nat.Multiplicity

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


open scoped Nat BigOperators

local macro_rules | `($x ^ $y) => `(HPow.hPow $x $y) -- Porting note: See issue #2220

open Nat hiding zero_le Prime

open Finset multiplicity

namespace Imo2019Q4

theorem upper_bound {k n : ℕ} (hk : k > 0)
    (h : (k ! : ℤ) = ∏ i in range n, ((2:ℤ) ^ n - (2:ℤ) ^ i)) : n < 6 := by
  have h2 : n * (n - 1) / 2 < k := by
    suffices multiplicity 2 (k ! : ℤ) = (n * (n - 1) / 2 : ℕ) by
      rw [← PartENat.coe_lt_coe, ← this]; change multiplicity ((2 : ℕ) : ℤ) _ < _
      simp_rw [Int.coe_nat_multiplicity, multiplicity_two_factorial_lt hk.lt.ne.symm]
    rw [h, multiplicity.Finset.prod Int.prime_two, ← sum_range_id, Nat.cast_sum]
    apply sum_congr rfl; intro i hi
    rw [multiplicity_sub_of_gt, multiplicity_pow_self_of_prime Int.prime_two]
    rwa [multiplicity_pow_self_of_prime Int.prime_two, multiplicity_pow_self_of_prime Int.prime_two,
      PartENat.coe_lt_coe, ← mem_range]
  rw [← not_le]; intro hn
  apply _root_.ne_of_lt _ h.symm
  suffices (∏ i in range n, ↑2 ^ n : ℤ) < ↑k ! by
    apply lt_of_le_of_lt _ this; apply prod_le_prod
    · intros; rw [sub_nonneg]; apply pow_le_pow; norm_num; apply le_of_lt; rwa [← mem_range]
    · intros; apply sub_le_self; apply pow_nonneg; norm_num
  suffices 2 ^ (n * n) < (n * (n - 1) / 2)! by
    rw [prod_const, card_range, ← pow_mul]; rw [← Int.ofNat_lt] at this
    clear h; convert this.trans _ using 1; norm_cast; rwa [Int.ofNat_lt, factorial_lt]
    refine' Nat.div_pos _ (by norm_num)
    refine' le_trans _ (mul_le_mul hn (pred_le_pred hn) (zero_le _) (zero_le _))
    norm_num
  refine' le_induction _ _ n hn; · norm_num
  intro n' hn' ih
  have h5 : 1 ≤ 2 * n' := by linarith
  have : 2 ^ (2 + 2) ≤ (n' * (n' - 1) / 2).succ := by
    change succ (6 * (6 - 1) / 2) ≤ _
    apply succ_le_succ; apply Nat.div_le_div_right
    exact mul_le_mul hn' (pred_le_pred hn') (zero_le _) (zero_le _)
  rw [triangle_succ]; apply lt_of_lt_of_le _ factorial_mul_pow_le_factorial
  refine'
    lt_of_le_of_lt _
      (mul_lt_mul ih (Nat.pow_le_pow_of_le_left this _) (pow_pos (by norm_num) _) (zero_le _))
  rw [← pow_mul, ← pow_add]; apply pow_le_pow_of_le_right; norm_num
  rw [add_mul 2 2]
  convert add_le_add_left (add_le_add_left h5 (2 * n')) (n' * n') using 1; ring
#align imo2019_q4.upper_bound Imo2019Q4.upper_bound

end Imo2019Q4

theorem imo2019_q4 {k n : ℕ} (hk : k > 0) (hn : n > 0) :
    (k ! : ℤ) = ∏ i in range n, ((2:ℤ) ^ n - (2:ℤ) ^ i) ↔ (k, n) = (1, 1) ∨ (k, n) = (3, 2) := by
  -- The implication `←` holds.
  constructor
  swap
  · rintro (h | h) <;> simp [Prod.ext_iff] at h  <;> rcases h with ⟨rfl, rfl⟩ <;>
    norm_num [prod_range_succ, succ_mul]
  intro h
  -- We know that n < 6.
  have := Imo2019Q4.upper_bound hk h
  interval_cases n
  -- n = 1
  · left; congr; norm_num at h; rw [factorial_eq_one] at h; apply antisymm h
    apply succ_le_of_lt hk
  -- n = 2
  · right; congr; rw [prod_range_succ] at h; norm_num at h; norm_cast at h; rw [← factorial_inj]
    exact h; rw [h]; norm_num
  all_goals exfalso; (repeat rw [prod_range_succ] at h); norm_num at h; norm_cast at h
  -- n = 3
  · refine' monotone_factorial.ne_of_lt_of_lt_nat 5 _ _ _ h <;> norm_num
  -- n = 4
  · refine' monotone_factorial.ne_of_lt_of_lt_nat 7 _ _ _ h <;> norm_num
  -- n = 5
  · refine' monotone_factorial.ne_of_lt_of_lt_nat 10 _ _ _ h <;> norm_num
#align imo2019_q4 imo2019_q4
