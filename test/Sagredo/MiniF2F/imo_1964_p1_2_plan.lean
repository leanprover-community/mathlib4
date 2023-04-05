import Mathlib.Data.Nat.Prime
import Mathlib.Tactic.GPT.Sagredo.Widget

theorem imo_1964_p1_2 (n : ℕ) : ¬ 7 ∣ (2^n + 1) := by
  -- We first show that 2^n mod 7 only depends on n mod 3,
  -- and in particular is always either 1, 2, or 4.
  sagredo!
