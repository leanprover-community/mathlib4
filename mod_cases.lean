import Mathlib.Tactic.ModCases

example (n : ℤ) : 3 ∣ n ^ 3 - n := by
  mod_cases n % 3
  · guard_hyp H :ₛ n ≡ 0 [ZMOD 3]; guard_target = 3 ∣ n ^ 3 - n; sorry
  · guard_hyp H :ₛ n ≡ 1 [ZMOD 3]; guard_target = 3 ∣ n ^ 3 - n; sorry
  · guard_hyp H :ₛ n ≡ 2 [ZMOD 3]; guard_target = 3 ∣ n ^ 3 - n; sorry
