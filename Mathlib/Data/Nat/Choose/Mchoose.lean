/-
Copyright (c) 2024 Antoine Chambert-Loir & María-Inés de Frutos—Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir, María-Inés de Frutos—Fernández
-/

import Mathlib.Algebra.BigOperators.Group.Finset
import Mathlib.Tactic.Ring.RingNF

/-! # Multiple choose

* `Nat.mchoose m n` is the number of (unordered) partitions of a set
with `m * n` elements into `m` parts of `n`-element subsets

This integer is defined as a finite product.

* `Nat.mchoose_eq` shows that it equals `(m * n).factorial / (m.factorial * n.factorial ^ m)`
and `Nat.mchoose_mul_factorial_mul_pow_factorial` establishes the equality
  `mchoose m n * m.factorial * n.factorial ^ m = (m * n).factorial`.

* `Nat.mchoose_mul_add` and `Nat.choose_mul_right` are lemmas for `Nat.choose`
that couldn't lie in `Mathlib.Data.Nat.Choose.Basic` because their proof uses the `ring` tactic.


## Note :

* It has nothing to do with `Nat.multichoose`.

* It is a particular case of a more general counting problem, counting the number
of unordered paritions of a set with given “type” (a multiset).

-/

namespace Nat

theorem choose_mul_right (m) {n : ℕ} (hn : n ≠ 0) :
    (m * n).choose n = m * (m * n - 1).choose (n - 1) := by
  by_cases hm : m = 0
  · simp only [hm, zero_mul, choose_eq_zero_iff]
    exact Nat.pos_of_ne_zero hn
  · set p := m - 1; have hp : m = p + 1 := (succ_pred_eq_of_ne_zero hm).symm
    set q := n - 1; have hq : n = q + 1 := (succ_pred_eq_of_ne_zero hn).symm
    simp only [hp, hq]
    rw [← Nat.mul_left_inj (zero_ne_add_one q).symm, eq_comm]
    suffices (p + 1) * (q + 1) = (p * q + p + q).succ by
      rw [this, ← Nat.succ_mul_choose_eq]
      rw [mul_comm (p + 1), mul_assoc, mul_comm, this]
      simp only [succ_eq_add_one, add_tsub_cancel_right]
    simp only [succ_eq_add_one]; ring_nf

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
  induction m with
  | zero => rw [mchoose_zero, one_mul, MulZeroClass.zero_mul, factorial_zero, pow_zero, mul_one]
  | succ m ih =>
    calc mchoose (m + 1) n * (m+1)! * (n)! ^ (m+1)
        =  ((m * n + n - 1).choose (n-1) * mchoose m n) * (m + 1)! *(n)! ^(m + 1) := by
          rw [mchoose_succ]
      _ = (m * n + n - 1).choose (n-1) * (m + 1) * n ! * (mchoose m n * m ! *(n)! ^ m) := by
          rw [factorial_succ, pow_succ]; ring_nf
      _ =  ((m + 1) * ((m + 1) * n - 1).choose (n-1)) * n ! * (m * n)! := by
          rw [ih]; ring_nf
      _ = (m * n + n).choose n * (m * n)! * n ! := by
          rw [← choose_mul_right _ hn]; ring_nf
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
