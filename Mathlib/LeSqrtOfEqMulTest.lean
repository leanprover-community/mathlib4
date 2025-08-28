import Mathlib

lemma le_sqrt_of_eq_mul {a b c : ℕ} (h : a = b * c) : b ≤ a.sqrt ∨ c ≤ a.sqrt := by
  by_cases hle : b ≤ a.sqrt
  · exact Or.inl hle
  · right
    simp at hle
    have : (a.sqrt + 1) ^ 2 > a := by
      exact Nat.lt_succ_sqrt' a
    nlinarith
