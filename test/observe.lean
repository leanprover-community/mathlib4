import Mathlib.Tactic.LibrarySearch
import Mathlib.Tactic.Linarith
import Mathlib.Data.Nat.Prime

open Nat

theorem euclid (n : ℕ) : ∃ N, n < N ∧ N.Prime := by
  let N := n.factorial + 1
  let p := minFac N
  use p
  have prime : p.Prime := by
    apply minFac_prime
    observe : n.factorial > 0
    linarith
  constructor
  · by_contra!
    observe : p ∣ n.factorial
    observe : p ∣ N
    observe : p ∣ 1
    observe : ¬ p ∣ 1
    contradiction
  · exact prime
