import Mathlib.Data.Nat.Prime

open Nat

-- Adaptation note: at nightly-2024-03-27,
-- we had to increase `maxHeartbeats` here from 8000 to 16000.
-- Adaptation note: at nightly-2024-04-01,
-- we had to increase `maxHeartbeats` here from 16000 to 24000.
set_option maxHeartbeats 24000 in
theorem euclid (n : ℕ) : ∃ N, n < N ∧ N.Prime := by
  let N := n.factorial + 1
  let p := minFac N
  use p
  have prime : p.Prime := by
    apply minFac_prime
    observe : n.factorial > 0
    omega
  constructor
  · by_contra!
    have this₁ : p ∣ n.factorial := (Prime.dvd_factorial prime).mpr this
    have this₂ : p ∣ N := minFac_dvd N
    have this₃ : p ∣ 1 := (Nat.dvd_add_iff_right this₁).mpr this₂
    observe : ¬ p ∣ 1
    contradiction
  · exact prime
