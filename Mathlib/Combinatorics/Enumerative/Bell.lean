/-
Copyright (c) 2024 Antoine Chambert-Loir & María-Inés de Frutos—Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir, María-Inés de Frutos—Fernández
-/

import Mathlib.Data.Nat.Choose.Multinomial

/-! # Bell numbers for multisets

For `n : ℕ`, the `n`th Bell number is the number of partitions of a set of cardinality `n`.
Here, we define a refinement of these numbers, that count, for any `m : Multiset ℕ`,
the number of partitions of a set of cardinality `m.sum` whose parts have cardinalities
given by `m`.

The definition presents it as an integer.

* `Multiset.bell`: number of partitions of a set whose parts have cardinalities a given multiset

* `Nat.uniformBell m n` : short name for `Multiset.bell (replicate m n)`

* `Multiset.bell_mul_eq` shows that
    `m.bell * (m.map (fun j ↦ j !)).prod *
      Π j ∈ (m.toFinset.erase 0), (m.count j)! = m.sum !`

* `Nat.uniformBell_mul_eq`  shows that
    `uniformBell m n * n ! ^ m * m ! = (m * n)!`

* `Nat.uniformBell_succ_left` computes `Nat.uniformBell (m + 1) n` from `Nat.uniformBell m n`

## TODO

Prove that it actually counts the number of partitions as indicated.
(When `m` contains `0`, the result requires to admit repetitions of the empty set as a part.)

-/

open Multiset Nat

theorem Nat.choose_mul_add (m) {n : ℕ} (hn : n ≠ 0) :
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

theorem Nat.choose_mul_right (m) {n : ℕ} (hn : n ≠ 0) :
    (m * n).choose n = m * (m * n - 1).choose (n - 1) := by
  by_cases hm : m = 0
  · simp only [hm, zero_mul, choose_eq_zero_iff]
    exact Nat.pos_of_ne_zero hn
  · set p := m - 1; have hp : m = p + 1 := (succ_pred_eq_of_ne_zero hm).symm
    simp only [hp]
    rw [add_mul, one_mul, choose_mul_add _ hn]

namespace Multiset

/-- Number of partitions of a set of cardinality `m.sum`
whose parts have cardinalities given by `m` -/
def bell (m : Multiset ℕ) : ℕ :=
  Nat.multinomial m.toFinset (fun k ↦ k * m.count k) *
    ∏ k ∈ m.toFinset.erase 0, ∏ j ∈ .range (m.count k), (j * k + k - 1).choose (k - 1)

@[simp]
theorem bell_zero : bell 0 = 1 := rfl

private theorem bell_mul_eq_lemma {x : ℕ} (hx : x ≠ 0) (c : ℕ) :
    x ! ^ c * c ! * ∏ j ∈ Finset.range c, (j * x + x - 1).choose (x - 1) = (x * c)! := by
  induction c with
  | zero => simp
  | succ c hrec =>
    suffices  x ! ^ (c + 1) * (c + 1) ! = x ! * (c + 1) * (x ! ^ c * c !) by
      rw [this]
      rw [← mul_assoc]
      simp only [Finset.range_succ, Finset.mem_range, lt_self_iff_false, not_false_eq_true,
        Finset.prod_insert]
      simp only [mul_assoc]
      rw [mul_comm ((c * x + x - 1).choose (x-1))]
      rw [← mul_assoc]
      rw [mul_comm]
      simp only [← mul_assoc]
      rw [hrec]
      have : (x * c)! * ((c * x + x - 1).choose (x - 1)) * x ! * (c + 1)
        = ((c + 1) * ((c * x + x - 1).choose (x - 1))) * (x * c)! *  x ! := by
        ring_nf
      rw [this]
      rw [← Nat.choose_mul_add c hx]
      rw [mul_comm c x]
      rw [Nat.add_choose_mul_factorial_mul_factorial (x * c) x]
      rw [mul_add, mul_one]
    rw [factorial_succ, pow_succ]
    ring_nf

theorem bell_mul_eq (m : Multiset ℕ) :
    m.bell * (m.map (fun j ↦ j !)).prod *
      Π j ∈ (m.toFinset.erase 0) (m.count j)! = m.sum ! := by
  unfold bell
  rw [← Nat.mul_right_inj]
  · simp only [← mul_assoc]
    rw [Nat.multinomial_spec]
    simp only [mul_assoc]
    rw [mul_comm]
    apply congr_arg₂
    · rw [mul_comm, mul_assoc, ← Finset.prod_mul_distrib, Finset.prod_multiset_map_count]
      suffices this : _ by
        by_cases hm : 0 ∈ m.toFinset
        · rw [← Finset.prod_erase_mul _ _ hm]
          rw [← Finset.prod_erase_mul _ _ hm]
          simp only [factorial_zero, one_pow, mul_one, zero_mul]
          exact this
        · nth_rewrite 1 [← Finset.erase_eq_of_not_mem hm]
          nth_rewrite 3 [← Finset.erase_eq_of_not_mem hm]
          exact this
      rw [← Finset.prod_mul_distrib]
      apply Finset.prod_congr rfl
      intro x hx
      rw [← mul_assoc, bell_mul_eq_lemma]
      simp only [Finset.mem_erase, ne_eq, mem_toFinset] at hx
      simp only [ne_eq, hx.1, not_false_eq_true]
    · apply congr_arg
      rw [Finset.sum_multiset_count]
      simp only [smul_eq_mul, mul_comm]
  · rw [← Nat.pos_iff_ne_zero]
    apply Finset.prod_pos
    exact fun _ _ ↦ Nat.factorial_pos _

theorem bell_eq (m : Multiset ℕ) :
    m.bell = m.sum ! / ((m.map (fun j ↦ j !)).prod *
      Π j ∈ (m.toFinset.erase 0) (m.count j)!) := by
  rw [← Nat.mul_left_inj, Nat.div_mul_cancel _]
  · rw [← mul_assoc]
    exact bell_mul_eq m
  · rw [← bell_mul_eq, mul_assoc]
    apply Nat.dvd_mul_left
  · rw [← Nat.pos_iff_ne_zero]
    apply Nat.mul_pos
    · simp only [gt_iff_lt, CanonicallyOrderedCommSemiring.multiset_prod_pos, mem_map,
      forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
      exact fun _ _ ↦ Nat.factorial_pos _
    · apply Finset.prod_pos
      exact fun _ _ ↦ Nat.factorial_pos _

end Multiset

namespace Nat

/-- Number of possibilities of dividing a set with `m * n` elements into `m` groups
of `n`-element subsets. -/
def uniformBell (m n : ℕ) : ℕ := bell (replicate m n)

theorem uniformBell_eq (m n : ℕ) : m.uniformBell n =
    Π p ∈ (Finset.range m), Nat.choose (p * n + n - 1) (n - 1) := by
  unfold uniformBell bell
  rw [replicate_toFinset]
  split_ifs with hm
  · simp  [hm]
  · by_cases hn : n = 0
    · simp [hn]
    · rw [show ({n} : Finset ℕ).erase 0 = {n} by simp [Ne.symm hn]]
      simp [count_replicate]

theorem uniformBell_zero_left (n : ℕ) : uniformBell 0 n = 1 := by
  simp [uniformBell_eq]

theorem uniformBell_zero_right (m : ℕ) : uniformBell m 0 = 1 := by
  simp [uniformBell_eq]

theorem uniformBell_succ_left (m n : ℕ) :
    uniformBell (m+1) n = choose (m * n + n - 1) (n - 1) * uniformBell m n := by
  simp only [uniformBell_eq, Finset.prod_range_succ, mul_comm]

theorem uniformBell_one_left (n : ℕ) : uniformBell 1 n = 1 := by
  simp only [uniformBell_eq, Finset.range_one, Finset.prod_singleton, zero_mul,
    zero_add, choose_self]

theorem uniformBell_one_right (m : ℕ) : uniformBell m 1 = 1 := by
  simp only [uniformBell_eq, mul_one, add_tsub_cancel_right, ge_iff_le, le_refl,
    tsub_eq_zero_of_le, choose_zero_right, Finset.prod_const_one]

theorem uniformBell_mul_eq (m : ℕ) {n : ℕ} (hn : n ≠ 0) :
    uniformBell m n * n.factorial ^ m * m.factorial = (m * n).factorial := by
  convert bell_mul_eq (replicate m n)
  · simp only [map_replicate, prod_replicate]
  · simp only [replicate_toFinset]
    split_ifs with hm
    · rw [hm, factorial_zero, eq_comm]
      rw [show (∅ : Finset ℕ).erase 0 = ∅ from rfl,  Finset.prod_empty]
    · rw [show ({n} : Finset ℕ).erase 0 = {n} by simp [Ne.symm hn]]
      simp only [Finset.prod_singleton, count_replicate_self]
  · simp

theorem uniformBell_eq_div (m : ℕ) {n : ℕ} (hn : n ≠ 0) :
    uniformBell m n = (m * n) ! / (n ! ^ m * m !) := by
  rw [eq_comm]
  apply Nat.div_eq_of_eq_mul_left
  · exact Nat.mul_pos (Nat.pow_pos (Nat.factorial_pos n)) m.factorial_pos
  · rw [← mul_assoc, ← uniformBell_mul_eq _ hn]

end Nat
