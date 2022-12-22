/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Johannes Hölzl, Mario Carneiro
Ported by: Kevin Buzzard, Johan Commelin, Siddhartha Gadgil, Anand Rao
-/

import Mathlib.Data.Int.Order.Basic
import Mathlib.Data.Nat.Size

/-!

These are lemmas that were proved in the process of porting `Data.Nat.Sqrt`,
but not used in the final proof.

-/

namespace Nat

theorem twice_prod_le_sq_sum : (a b : ℕ) → a * b + a * b ≤ a * a + b * b
  | 0, _ => by simp
  | _, 0 => by simp
  | a + 1, b + 1 => by
    simp [add_mul, mul_add]
    simp only [add_assoc, add_left_comm, add_le_add_iff_left]
    rw [← add_assoc (a * a), ← add_assoc (a * b)]
    apply add_le_add_right
    exact twice_prod_le_sq_sum a b

protected lemma div_mul_div_le (a b c d : ℕ) :
  (a / b) * (c / d) ≤ (a * c) / (b * d) := by
  by_cases hb : b = 0
  case pos => simp [hb]
  by_cases hd : d = 0
  case pos => simp [hd]
  have hbd : b * d ≠ 0 := mul_ne_zero hb hd
  rw [le_div_iff_mul_le (pos_iff_ne_zero.2 hbd)]
  transitivity ((a / b) * b) * ((c / d) * d)
  · apply le_of_eq; simp only [mul_assoc, mul_left_comm]
  · apply Nat.mul_le_mul <;> apply div_mul_le_self

private abbrev iter_next (n guess : ℕ) : ℕ  :=
    (guess + n / guess) / 2

private lemma iter_fp_bound (n k : ℕ):
    sqrt.iter n k ≤ iter_next n (sqrt.iter n k)  := by
      unfold sqrt.iter
      by_cases h : (k + n / k) / 2 < k
      case pos => simp [if_pos h]; apply iter_fp_bound
      case neg => simp [if_neg h, Nat.le_of_not_lt h]

lemma am_gm_lemma (a b: ℤ) : 0 ≤ (a + b) * (a + b) - 4 * a * b := by
  convert sq_nonneg (a - b)
  simp only [sq, add_mul, mul_add, sub_mul, mul_sub, add_assoc, mul_comm b a, sub_eq_add_neg,
    neg_mul, mul_neg, neg_neg, add_right_inj, neg_add_rev, neg_neg, add_left_comm _ (b*b)]
  simp only [← two_mul, ← add_assoc, mul_neg, eq_neg_iff_add_eq_zero, mul_assoc]
  simp only [← neg_mul, ← add_mul, _root_.mul_eq_zero, true_or]

end Nat
