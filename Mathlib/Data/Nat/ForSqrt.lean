/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Johannes Hölzl, Mario Carneiro
-/
import Mathlib.Data.Nat.Defs

/-!

These are lemmas that were proved in the process of porting `Data.Nat.Sqrt`.

-/

namespace Nat

section Misc

-- Porting note: Miscellaneous lemmas that should be integrated with `Mathlib` in the future

protected lemma mul_le_of_le_div (k x y : ℕ) (h : x ≤ y / k) : x * k ≤ y := by
  if hk : k = 0 then
    rw [hk, Nat.mul_zero]; exact zero_le _
  else
    rwa [← le_div_iff_mul_le (by omega)]

protected lemma div_mul_div_le (a b c d : ℕ) :
    (a / b) * (c / d) ≤ (a * c) / (b * d) := by
  if hb : b = 0 then simp [hb] else
  if hd : d = 0 then simp [hd] else
  have hbd : b * d ≠ 0 := Nat.mul_ne_zero hb hd
  rw [le_div_iff_mul_le (Nat.pos_of_ne_zero hbd)]
  transitivity ((a / b) * b) * ((c / d) * d)
  · apply Nat.le_of_eq; simp only [Nat.mul_assoc, Nat.mul_left_comm]
  · apply Nat.mul_le_mul <;> apply div_mul_le_self

private lemma iter_fp_bound (n k : ℕ) :
    let iter_next (n guess : ℕ) := (guess + n / guess) / 2;
    sqrt.iter n k ≤ iter_next n (sqrt.iter n k) := by
  intro iter_next
  unfold sqrt.iter
  if h : (k + n / k) / 2 < k then
    simpa [if_pos h] using iter_fp_bound _ _
  else
    simpa [if_neg h] using Nat.le_of_not_lt h

private lemma AM_GM : {a b : ℕ} → (4 * a * b ≤ (a + b) * (a + b))
  | 0, _ => by rw [Nat.mul_zero, Nat.zero_mul]; exact zero_le _
  | _, 0 => by rw [Nat.mul_zero]; exact zero_le _
  | a + 1, b + 1 => by
    have ih := Nat.add_le_add_right (@AM_GM a b) 4
    simp only [Nat.mul_add, Nat.add_mul, show (4 : ℕ) = 1 + 1 + 1 + 1 from rfl, Nat.one_mul,
      Nat.mul_one] at ih ⊢
    simp only [Nat.add_assoc, Nat.add_left_comm, Nat.add_le_add_iff_left] at ih ⊢
    omega

end Misc

section Std

-- Porting note: These two lemmas seem like they belong to `Std.Data.Nat.Basic`.

lemma sqrt.iter_sq_le (n guess : ℕ) : sqrt.iter n guess * sqrt.iter n guess ≤ n := by
  unfold sqrt.iter
  let next := (guess + n / guess) / 2
  if h : next < guess then
    simpa only [dif_pos h] using sqrt.iter_sq_le n next
  else
    simp only [dif_neg h]
    apply Nat.mul_le_of_le_div
    apply Nat.le_of_add_le_add_left (a := guess)
    rw [← Nat.mul_two, ← le_div_iff_mul_le]
    · exact Nat.le_of_not_lt h
    · exact Nat.zero_lt_two

lemma sqrt.lt_iter_succ_sq (n guess : ℕ) (hn : n < (guess + 1) * (guess + 1)) :
    n < (sqrt.iter n guess + 1) * (sqrt.iter n guess + 1) := by
  unfold sqrt.iter
  -- m was `next`
  let m := (guess + n / guess) / 2
  if h : m < guess then
    suffices n < (m + 1) * (m + 1) by
      simpa only [dif_pos h] using sqrt.lt_iter_succ_sq n m this
    apply Nat.lt_of_mul_lt_mul_left (a := 4 * (guess * guess))
    apply Nat.lt_of_le_of_lt AM_GM
    rw [show (4 : ℕ) = 2 * 2 from rfl]
    rw [Nat.mul_mul_mul_comm 2, Nat.mul_mul_mul_comm (2 * guess)]
    refine mul_self_lt_mul_self (?_ : _ < _ * succ (_ / 2))
    rw [← add_div_right _ (by decide), Nat.mul_comm 2, Nat.mul_assoc,
      show guess + n / guess + 2 = (guess + n / guess + 1) + 1 from rfl]
    have aux_lemma {a : ℕ} : a ≤ 2 * ((a + 1) / 2) := by omega
    -- apply lt_of_lt_of_le (b := guess * (guess + n / guess + 1))
    refine lt_of_lt_of_le ?_ (Nat.mul_le_mul_left _ aux_lemma)
    · rw [Nat.add_assoc, Nat.mul_add]
      exact Nat.add_lt_add_left (lt_mul_div_succ _ (lt_of_le_of_lt (Nat.zero_le m) h)) _

  else
    simpa only [dif_neg h] using hn

end Std

end Nat
