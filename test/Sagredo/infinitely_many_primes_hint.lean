import Mathlib.Tactic.GPT.Sagredo.Widget
import Mathlib.Data.Nat.Prime

example : ∀ N : Nat, ∃ n, N < n ∧ Prime n := by
  -- We'll let `p` be the smallest prime factor of `N! + 1`.
  -- By construction this is prime.
  -- To see that it is larger than `N`, we argue by contradiction.
  -- If `p ≤ N`, then it must divide `N`.
  -- Since it divides `N!` and `N! + 1`, it must divide `1`, which is not possible.
  sagredo!
