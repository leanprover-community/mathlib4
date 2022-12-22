import Mathlib.Data.Nat.Size

/-!

These are lemmas that were proved in the process of porting `Data.Nat.Sqrt`.

-/

namespace Nat

section Misc

-- porting note: Miscellaneous lemmas that should be integrated with `Mathlib` in the future

protected lemma mul_le_of_le_div (k x y : ℕ) (h : x ≤ y / k) : x * k ≤ y := by
  by_cases hk : k = 0
  case pos => rw [hk, mul_zero]; exact zero_le _
  case neg => rwa [← le_div_iff_mul_le (pos_iff_ne_zero.2 hk)]

private lemma AM_GM : {a b : ℕ} → (4 * a * b ≤ (a + b) * (a + b))
  | 0, _ => by rw [mul_zero, zero_mul]; exact zero_le _
  | _, 0 => by rw [mul_zero]; exact zero_le _
  | a + 1, b + 1 => by
    have ih := add_le_add_right (@AM_GM a b) 4
    simp only [mul_add, add_mul, show (4 : ℕ) = 1 + 1 + 1 + 1 from rfl, one_mul, mul_one] at ih ⊢
    simp only [add_assoc, add_left_comm, add_le_add_iff_left] at ih ⊢
    exact ih

end Misc

section Std

-- porting note: These two lemmas seem like they belong to `Std.Data.Nat.Basic`.

lemma sqrt.iter_sq_le (n guess : ℕ) : sqrt.iter n guess * sqrt.iter n guess ≤ n := by
  unfold sqrt.iter
  let next := (guess + n / guess) / 2
  by_cases h : next < guess
  case pos => simpa only [dif_pos h] using sqrt.iter_sq_le n next
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
  -- m was `next`
  let m := (guess + n / guess) / 2
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
