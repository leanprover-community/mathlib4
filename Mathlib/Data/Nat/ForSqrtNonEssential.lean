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

end Nat
