import Mathlib.Data.Nat.Prime.Infinite
import Mathlib.Data.Nat.Factorial.Basic

/-!
# Prime gaps are unbounded

This file proves the classical theorem that prime gaps are unbounded: for every `k`
there exist `k` consecutive composite numbers. The construction is factorial:
`(k+1)! + 2, …, (k+1)! + (k+1)` are all composite (each is divisible by its offset).

This is the elementary statement underlying the dynamics of prime gaps
(`gₙ = pₙ₊₁ − pₙ`): the gaps cannot be bounded by any constant, ruling out any
fixed-degree polynomial law for the gap sequence.

## Main results
* `Nat.exists_consecutive_composites`: for every `k`, there exist `k` consecutive
  composite numbers.
* `Nat.exists_prime_gap_gt`: for every `k`, there exist primes `p < q` with `q - p > k`.
-/

namespace Nat

/-- For every `k`, there exist `k` consecutive composite numbers.
  Witness: `n = (k+1)! + 1`; each `n + m` is divisible by `m + 1`, hence composite. -/
theorem exists_consecutive_composites (k : ℕ) :
    ∃ n : ℕ, ∀ m : ℕ, 1 ≤ m → m ≤ k → ¬ (n + m).Prime := by
  refine ⟨(k + 1)! + 1, ?_⟩
  intro m hm1 hmk
  let j := m + 1
  have hj2 : 2 ≤ j := by omega
  have hjk : j ≤ k + 1 := by omega
  have hdvd : j ∣ (k + 1)! := Nat.dvd_factorial (by omega : 0 < j) hjk
  have hdvd_sum : j ∣ (k + 1)! + j := Nat.dvd_add hdvd (dvd_rfl : j ∣ j)
  have hn : (k + 1)! + 1 + m = (k + 1)! + j := by omega
  intro hp
  have hdvd_n : j ∣ (k + 1)! + 1 + m := by
    rw [hn]
    exact hdvd_sum
  have hdiv : j = 1 ∨ j = (k + 1)! + 1 + m := hp.eq_one_or_self_of_dvd j hdvd_n
  have hne1 : j ≠ 1 := by omega
  have hbig : j ≠ (k + 1)! + 1 + m := by
    intro h
    have : (k + 1)! = 0 := by omega
    exact Nat.factorial_ne_zero (k + 1) this
  omega

/-- For every `k`, there exist primes `p < q` with `q - p > k`.
  A weak form of "prime gaps are unbounded". -/
theorem exists_prime_gap_gt (k : ℕ) : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p < q ∧ k < q - p := by
  let w := (k + 1)! + 1
  have hfact : 0 < (k + 1)! := Nat.factorial_pos (k + 1)
  rcases Nat.exists_infinite_primes (w + k + 2) with ⟨q, hqge, hqprime⟩
  refine ⟨2, q, Nat.prime_two, hqprime, ?_, ?_⟩
  · have : 4 ≤ q := by omega
    omega
  · have hsub : (w + k + 2) - 2 ≤ q - 2 := Nat.sub_le_sub_right hqge 2
    have : q - 2 ≥ (k + 1)! + k + 1 := by omega
    omega

end Nat
