/-
Copyright (c) 2023 Ruben Van de Velde. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruben Van de Velde
-/

import Mathlib.NumberTheory.FLT.Four

/-!
# Reduce Fermat's Last Theorem to odd primes

To prove Fermat's Last Theorem, it suffices to prove it for odd prime exponents, and the well-known
case of exponent 4 (`fermatLastTheoremFour`).
-/

theorem FermatLastTheoremWith.of_odd_primes
    (hprimes : ∀ p : ℕ, Nat.Prime p → Odd p → FermatLastTheoremWith ℕ p) : FermatLastTheorem := by
  intro n h
  rw [ge_iff_le, Nat.succ_le_iff] at h
  obtain hdvd|⟨p, hdvd, hpprime, hpodd⟩ := Nat.four_dvd_or_exists_odd_prime_and_dvd_of_two_lt h <;>
    apply FermatLastTheoremWith.mono hdvd
  · have := (fermatLastTheoremWith_nat_int_rat_tfae 4).out 0 1
    rw [this]
    exact fermatLastTheoremFour
  · exact hprimes p hpprime hpodd
