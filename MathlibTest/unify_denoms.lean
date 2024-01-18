import Mathlib

open BigOperators

example (n : ℕ ) (h : 2 ∣ n * (n + 1)) : n * (n + 1) / 2 + n + 1 = (n + 1) * (n + 2) / 2 := by
  unify_denoms
  · ring
  · exact Nat.succ_pos 1
  · induction' n with m hm
    · use 0
    · cases' hm with x hx
      rw [←Nat.add_one]
      use x + m + 2
      ring_nf at *
      rw [←hx]
      ring
  · exact Nat.succ_pos 1
  ·
