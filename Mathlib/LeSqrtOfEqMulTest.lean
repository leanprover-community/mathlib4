import Mathlib

lemma le_sqrt_of_eq_mul {a b c : ℕ} (a_eq_b_mul_c : a = b * c) : b ≤ a.sqrt ∨ c ≤ a.sqrt := by
  by_cases w_b_le_sqrt : b ≤ a.sqrt
  . exact Or.inl w_b_le_sqrt
  . right
    simp at w_b_le_sqrt
    have : (a.sqrt + 1) ^ 2 > a := by
      exact Nat.lt_succ_sqrt' a
    nlinarith
