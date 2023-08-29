/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Johannes Hölzl, Mario Carneiro
-/

import Mathlib.Data.Nat.Size

/-!

These are lemmas that were proved in the process of porting `Data.Nat.Sqrt`.

-/

namespace Nat

section Misc

-- porting note: Miscellaneous lemmas that should be integrated with `Mathlib` in the future

protected lemma mul_le_of_le_div (k x y : ℕ) (h : x ≤ y / k) : x * k ≤ y := by
  by_cases hk : k = 0
  -- ⊢ x * k ≤ y
  case pos => rw [hk, mul_zero]; exact zero_le _
  -- ⊢ x * k ≤ y
  -- 🎉 no goals
  case neg => rwa [← le_div_iff_mul_le (pos_iff_ne_zero.2 hk)]
  -- 🎉 no goals
  -- 🎉 no goals

protected lemma div_mul_div_le (a b c d : ℕ) :
    (a / b) * (c / d) ≤ (a * c) / (b * d) := by
  by_cases hb : b = 0
  -- ⊢ a / b * (c / d) ≤ a * c / (b * d)
  case pos => simp [hb]
  -- ⊢ a / b * (c / d) ≤ a * c / (b * d)
  -- 🎉 no goals
  by_cases hd : d = 0
  -- ⊢ a / b * (c / d) ≤ a * c / (b * d)
  case pos => simp [hd]
  -- ⊢ a / b * (c / d) ≤ a * c / (b * d)
  -- 🎉 no goals
  have hbd : b * d ≠ 0 := mul_ne_zero hb hd
  -- ⊢ a / b * (c / d) ≤ a * c / (b * d)
  rw [le_div_iff_mul_le (Nat.pos_of_ne_zero hbd)]
  -- ⊢ a / b * (c / d) * (b * d) ≤ a * c
  transitivity ((a / b) * b) * ((c / d) * d)
  -- ⊢ a / b * (c / d) * (b * d) ≤ a / b * b * (c / d * d)
  · apply le_of_eq; simp only [mul_assoc, mul_left_comm]
    -- ⊢ a / b * (c / d) * (b * d) = a / b * b * (c / d * d)
                    -- 🎉 no goals
  · apply Nat.mul_le_mul <;> apply div_mul_le_self
    -- ⊢ a / b * b ≤ a
                             -- 🎉 no goals
                             -- 🎉 no goals

private lemma iter_fp_bound (n k : ℕ) :
    let iter_next (n guess : ℕ) := (guess + n / guess) / 2;
    sqrt.iter n k ≤ iter_next n (sqrt.iter n k) := by
  intro iter_next
  -- ⊢ sqrt.iter n k ≤ iter_next n (sqrt.iter n k)
  unfold sqrt.iter
  -- ⊢ (let next := (k + n / k) / 2;
  by_cases h : (k + n / k) / 2 < k
  case pos => simp [if_pos h]; exact iter_fp_bound _ _
  -- ⊢ (let next := (k + n / k) / 2;
  -- 🎉 no goals
  case neg => simp [if_neg h]; exact Nat.le_of_not_lt h
  -- 🎉 no goals
  -- 🎉 no goals

private lemma AM_GM : {a b : ℕ} → (4 * a * b ≤ (a + b) * (a + b))
  | 0, _ => by rw [mul_zero, zero_mul]; exact zero_le _
               -- ⊢ 0 ≤ (0 + x✝) * (0 + x✝)
                                        -- 🎉 no goals
  | _, 0 => by rw [mul_zero]; exact zero_le _
               -- ⊢ 0 ≤ (x✝ + 0) * (x✝ + 0)
                              -- 🎉 no goals
  | a + 1, b + 1 => by
    have ih := add_le_add_right (@AM_GM a b) 4
    -- ⊢ 4 * (a + 1) * (b + 1) ≤ (a + 1 + (b + 1)) * (a + 1 + (b + 1))
    simp only [mul_add, add_mul, show (4 : ℕ) = 1 + 1 + 1 + 1 from rfl, one_mul, mul_one] at ih ⊢
    -- ⊢ a * b + a * b + a * b + a * b + (b + b + b + b) + (a + a + a + a + (1 + 1 +  …
    simp only [add_assoc, add_left_comm, add_le_add_iff_left] at ih ⊢
    -- ⊢ a * b + (a * b + (a * b + (a * b + (1 + (1 + (1 + 1)))))) ≤ a * a + (a * b + …
    exact ih
    -- 🎉 no goals

end Misc

section Std

-- porting note: These two lemmas seem like they belong to `Std.Data.Nat.Basic`.

lemma sqrt.iter_sq_le (n guess : ℕ) : sqrt.iter n guess * sqrt.iter n guess ≤ n := by
  unfold sqrt.iter
  -- ⊢ ((let next := (guess + n / guess) / 2;
  let next := (guess + n / guess) / 2
  -- ⊢ ((let next := (guess + n / guess) / 2;
  by_cases h : next < guess
  case pos => simpa only [dif_pos h] using sqrt.iter_sq_le n next
  -- ⊢ ((let next := (guess + n / guess) / 2;
  -- 🎉 no goals
  case neg =>
    simp only [dif_neg h]
    apply Nat.mul_le_of_le_div
    apply le_of_add_le_add_left (a := guess)
    rw [← mul_two, ← le_div_iff_mul_le]
    · exact le_of_not_lt h
    · exact zero_lt_two

lemma sqrt.lt_iter_succ_sq (n guess : ℕ) (hn : n < (guess + 1) * (guess + 1)) :
    n < (sqrt.iter n guess + 1) * (sqrt.iter n guess + 1) := by
  unfold sqrt.iter
  -- ⊢ n <
  -- m was `next`
  let m := (guess + n / guess) / 2
  -- ⊢ n <
  by_cases h : m < guess
  case pos =>
    suffices : n < (m + 1) * (m + 1)
    · simpa only [dif_pos h] using sqrt.lt_iter_succ_sq n m this
    refine lt_of_mul_lt_mul_left ?_ (4 * (guess * guess)).zero_le
    apply lt_of_le_of_lt AM_GM
    rw [show (4 : ℕ) = 2 * 2 from rfl]
    rw [mul_mul_mul_comm 2, mul_mul_mul_comm (2 * guess)]
    refine mul_self_lt_mul_self (?_ : _ < _ * succ (_ / 2))
    rw [← add_div_right _ (by decide), mul_comm 2, mul_assoc,
      show guess + n / guess + 2 = (guess + n / guess + 1) + 1 from rfl]
    have aux_lemma {a : ℕ} : a ≤ 2 * ((a + 1) / 2) := by
      rw [mul_comm]
      exact (add_le_add_iff_right 2).1 $ succ_le_of_lt $ @lt_div_mul_add (a + 1) 2 zero_lt_two
    refine lt_of_lt_of_le ?_ (act_rel_act_of_rel _ aux_lemma)
    rw [add_assoc, mul_add]
    exact add_lt_add_left (lt_mul_div_succ _ (lt_of_le_of_lt (Nat.zero_le m) h)) _
  case neg =>
    simpa only [dif_neg h] using hn

end Std

end Nat
