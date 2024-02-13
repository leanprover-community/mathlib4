import Mathlib.Tactic.LibrarySearch
import Mathlib.Tactic.Linarith
import Mathlib.Data.Nat.Prime

open Nat

set_option maxHeartbeats 150000 in
theorem euclid (n : ℕ) : ∃ N, n < N ∧ N.Prime := by
  let N := n.factorial + 1
  let p := minFac N
  use p
  have prime : p.Prime := by
    -- we write this in a funny way,
    -- so that we can test that `observe` (aka `apply?`)
    -- finds `minFac_prime` in time
    observe : n.factorial > 0
    have : N ≠ 1 := by linarith
    observe : p.Prime
    assumption
  constructor
  · by_contra!
    observe : p ∣ n.factorial
    observe : p ∣ N
    observe : p ∣ 1
    observe : ¬ p ∣ 1
    contradiction
  · exact prime
