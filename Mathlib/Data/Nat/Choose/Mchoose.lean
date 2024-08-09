/-
Copyright (c) 2024 Antoine Chambert-Loir & María-Inés de Frutos—Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir, María-Inés de Frutos—Fernández
-/

import Mathlib.Data.Nat.Choose.Vandermonde

/-! # Multiple choose 

* `Nat.mchoose m n` is the number of possibilities of dividing a set 
with `m * n` elements into `m` groups of `n`-element subsets

This integer is defined as a finite product.

* `Nat.mchoose_eq` shows that it equals `(m * n).factorial / (m.factorial * n.factorial ^ m)`
and `Nat.mchoose_mul_factorial_mul_pow_factorial` establishes the equality
  `mchoose m n * m.factorial * n.factorial ^ m = (m * n).factorial`.

* `Nat.mchoose_mul_add` and `Nat.choose_mul_right` are lemmas for `Nat.choose`
that couldn't lie in `Mathlib.Data.Nat.Choose.Basic` because their proof uses the `ring` tactic.

-/

namespace Nat

theorem choose_mul_add (m) {n : ℕ} (hn : n ≠ 0) :
    (m * n + n).choose n = (m + 1) * (m * n + n - 1).choose (n - 1) := by 
  rw [← mul_left_inj' (mul_ne_zero (factorial_ne_zero (m * n)) (factorial_ne_zero n))]
  set p := n - 1 
  have hp : n = p + 1 := (succ_pred_eq_of_ne_zero hn).symm
  simp only [hp, add_succ_sub_one]
  calc 
    (m * (p + 1) + (p + 1)).choose (p + 1) * ((m * (p+1))! * (p+1)!) 
      = (m * (p + 1) + (p + 1)).choose (p + 1) * (m * (p+1))! * (p+1)! := by ring
    _ = (m * (p+ 1) + (p + 1))! := by rw [add_choose_mul_factorial_mul_factorial]
    _ = ((m * (p+ 1) + p) + 1)! := by ring_nf
    _ = ((m * (p + 1) + p) + 1) * (m * (p + 1) + p)! := by rw [factorial_succ]
    _ = (m * (p + 1) + p)! * ((p + 1) * (m + 1)) := by ring
    _ = ((m * (p + 1) + p).choose p * (m * (p+1))! * (p)!) * ((p + 1) * (m + 1)) := by
        rw [add_choose_mul_factorial_mul_factorial]
    _ = (m * (p + 1) + p).choose p * (m * (p+1))! * (((p + 1) * (p)!) * (m + 1)) := by ring
    _ = (m * (p + 1) + p).choose p * (m * (p+1))! * ((p + 1)! * (m + 1)) := by rw [factorial_succ]
    _ = (m + 1) * (m * (p + 1) + p).choose p * ((m * (p + 1))! * (p + 1)!) := by ring
  
theorem choose_mul_right (m) {n : ℕ} (hn : n ≠ 0) :
    (m * n).choose n = m * (m * n - 1).choose (n - 1) := by 
  by_cases hm : m = 0 
  · simp only [hm, zero_mul, choose_eq_zero_iff]
    exact Nat.pos_of_ne_zero hn
  · set p := m - 1; have hp : m = p + 1 := (succ_pred_eq_of_ne_zero hm).symm
    simp only [hp]
    rw [add_mul, one_mul, choose_mul_add _ hn]

/-- Number of possibilities of dividing a set with `m * n` elements into `m` groups 
of `n`-element subsets. -/
def mchoose (m n : ℕ) : ℕ :=
  Finset.prod (Finset.range m) fun p => choose (p * n + n - 1) (n - 1)

theorem mchoose_zero (n : ℕ) : mchoose 0 n = 1 := by
  rw [mchoose, Finset.range_zero, Finset.prod_empty]

theorem mchoose_zero' (m : ℕ) : mchoose m 0 = 1 := by
  simp only [mchoose, MulZeroClass.mul_zero, choose_self, Finset.prod_const_one]

theorem mchoose_succ (m n : ℕ) :
    mchoose (m + 1) n = choose (m * n + n - 1) (n - 1) * mchoose m n := by
  simp only [mchoose, Finset.prod_range_succ, mul_comm]

theorem mchoose_one (n : ℕ) : mchoose 1 n = 1 := by
  simp only [mchoose, Finset.range_one, Finset.prod_singleton, zero_mul,
    zero_add, choose_self]

theorem mchoose_one' (m : ℕ) : mchoose m 1 = 1 := by
  simp only [mchoose, mul_one, add_tsub_cancel_right, ge_iff_le, le_refl,
    tsub_eq_zero_of_le, choose_zero_right, Finset.prod_const_one]

theorem mchoose_mul_factorial_mul_pow_factorial (m : ℕ) {n : ℕ} (hn : n ≠ 0) :
    mchoose m n * m.factorial * n.factorial ^ m = (m * n).factorial := by
  rw [← zero_lt_iff] at hn
  induction m with 
  | zero => rw [mchoose_zero, one_mul, MulZeroClass.zero_mul, factorial_zero, pow_zero, mul_one]
  | succ m ih => 
    calc mchoose (m + 1) n * (m+1)! * (n)! ^ (m+1)
        =  ((m * n + n - 1).choose (n-1) * mchoose m n) * (m + 1)! *(n)! ^(m + 1) := by 
          rw [mchoose_succ]
      _ = mchoose m n * ((m + 1) * (m * n + n - 1).choose (n-1)) * (m)! * (n)!  ^ (m +1) := by
          rw [factorial_succ]; ring 
      _ = mchoose m n * ((m*n+n).choose n) * (m)! * (n)! ^ (m+1) := by 
          rw [← choose_mul_add _ (not_eq_zero_of_lt hn)]
      _ = (mchoose m n * (m)! * (n)! ^ m) * (m*n+n).choose n * (n)! := by 
          rw [pow_succ]; ring_nf
      _ = (m  * n + n).choose n * (m * n)! * (n)! := by rw [ih]; ring
      _ = (m * n + n)! := by rw [add_choose_mul_factorial_mul_factorial]
      _ = ((m + 1)* n)! := by ring_nf
    
theorem mchoose_mul_eq (m : ℕ) {n : ℕ} (hn : n ≠ 0) :
    mchoose m n = (m * n).factorial / (m.factorial * n.factorial ^ m) := by
  rw [← Nat.mul_left_inj <|
    Nat.mul_ne_zero (factorial_ne_zero m) (pow_ne_zero m (factorial_ne_zero n)),
    ← mul_assoc, ← mchoose_mul_factorial_mul_pow_factorial m hn, eq_comm]
  apply Nat.div_mul_cancel
  rw [mul_assoc]
  apply Nat.dvd_mul_left

end Nat
