import Mathlib

lemma le_sqrt_of_eq_mul {a b c : ℕ} (h : a = b * c) : b ≤ a.sqrt ∨ c ≤ a.sqrt :=
  if hle : b ≤ a.sqrt then
    Or.inl hle
  else
    Or.inr (Nat.le_of_lt_succ (Nat.lt_of_mul_lt_mul_left (lt_mul_of_lt_mul_right
      (h ▸ Nat.lt_succ_sqrt a) (Nat.gt_of_not_le hle))))
    -- or : `by right; nlinarith [Nat.lt_succ_sqrt' a]`
