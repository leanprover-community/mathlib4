/-
Copyright (c) 2026 Meta Platforms, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Kiezun
-/
module

public import Mathlib.Data.Nat.Choose.Bounds
public import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Tactic.IntervalCases

/-!
# Prime-counting estimates for Sylvester-Schur

This file contains the prime-counting estimates and the basic large-prime extraction
lemmas used in the Sylvester--Schur proof.
-/

@[expose] public section

namespace Nat.SylvesterSchur

open scoped BigOperators

open Finset Nat

/-! ### Prime-counting estimates -/

/-- Failure of the no-large-prime hypothesis produces a prime divisor of `Nat.choose N r`
strictly greater than `r`. -/
theorem exists_large_prime_dvd_choose_of_not_forall_prime_dvd_le {N r : ℕ}
    (hsmall : ¬ ∀ p : ℕ, p.Prime → p ∣ Nat.choose N r → p ≤ r) :
    ∃ p : ℕ, p.Prime ∧ r < p ∧ p ∣ Nat.choose N r := by
  by_contra h
  exact hsmall fun p hp hdvd => le_of_not_gt fun hgt => h ⟨p, hp, hgt, hdvd⟩

/-- If a no-large-prime upper bound for `Nat.choose N r` is smaller than Mathlib's lower
bound, then `Nat.choose N r` has a prime divisor greater than `r`. -/
theorem exists_large_prime_dvd_choose_of_upper_lt_lower {N r U : ℕ}
    (hupper :
      (∀ p : ℕ, p.Prime → p ∣ Nat.choose N r → p ≤ r) → Nat.choose N r ≤ U)
    (hbound : (U : ℚ) < ((N + 1 - r : ℕ) ^ r : ℚ) / (r ! : ℚ)) :
    ∃ p : ℕ, p.Prime ∧ r < p ∧ p ∣ Nat.choose N r := by
  apply exists_large_prime_dvd_choose_of_not_forall_prime_dvd_le
  intro hsmall
  have hupper_q : ((Nat.choose N r : ℕ) : ℚ) ≤ (U : ℚ) := by
    exact_mod_cast hupper hsmall
  have hlower :
      ((N + 1 - r : ℕ) ^ r : ℚ) / (r ! : ℚ) ≤ ((Nat.choose N r : ℕ) : ℚ) :=
    Nat.pow_le_choose (α := ℚ) r N
  exact (not_lt_of_ge (hlower.trans hupper_q)) hbound

/-- A very elementary bound: there are at most `r - 1` primes up to `r`, since all such primes
lie in `{2, ..., r}`. -/
theorem primeCounting_le_sub_one {r : ℕ} (hr : 2 ≤ r) :
    Nat.primeCounting r ≤ r - 1 := by
  rw [Nat.primeCounting, ← Nat.primesBelow_card_eq_primeCounting' (r + 1)]
  have hsubset :
      (r + 1).primesBelow ⊆ Finset.Icc 2 r := by
    intro p hp
    rw [Finset.mem_Icc]
    exact ⟨(Nat.prime_of_mem_primesBelow hp).two_le, by
      have hlt := Nat.lt_of_mem_primesBelow hp
      omega⟩
  exact (Finset.card_le_card hsubset).trans_eq (by rw [card_Icc]; omega)

/-- A Mathlib-derived linear prime-counting bound.  This uses
`Nat.primeCounting'_add_le` with modulus `2`, rather than reproving the odd-prime counting
argument locally. -/
theorem primeCounting_le_half_add_one (r : ℕ) :
    Nat.primeCounting r ≤ r / 2 + 1 := by
  by_cases hr : r ≤ 1
  · have hz : Nat.primeCounting r = 0 := Nat.primeCounting_eq_zero_iff.mpr hr
    omega
  · have hr2 : 2 ≤ r := by omega
    have h :=
      Nat.primeCounting'_add_le (a := 2) (k := 3) (by decide) (by decide) (r - 2)
    have harg : 3 + (r - 2) = r + 1 := by omega
    have hpi3 : Nat.primeCounting' 3 = 1 := by decide
    have htot : Nat.totient 2 = 1 := by decide
    rw [harg, hpi3, htot, one_mul] at h
    change Nat.primeCounting' (r + 1) ≤ r / 2 + 1
    omega

/- An explicit prime-counting bound from residue classes modulo `30`.  Beyond the primes below
`31`, every prime is coprime to `30`, and Mathlib's `Nat.primeCounting'_add_le` counts at most
one residue-class block plus a tail. -/
private lemma primeCounting_le_mod_thirty (r : ℕ) :
    Nat.primeCounting r ≤ 10 + 8 * ((r - 30) / 30 + 1) := by
  by_cases hr : r ≤ 30
  · have hmono : Nat.primeCounting r ≤ Nat.primeCounting 30 :=
      Nat.monotone_primeCounting hr
    have hpi30 : Nat.primeCounting 30 = 10 := by decide
    omega
  · have h :=
      Nat.primeCounting'_add_le (a := 30) (k := 31) (by decide) (by decide) (r - 30)
    have harg : 31 + (r - 30) = r + 1 := by omega
    have hpi31 : Nat.primeCounting' 31 = 10 := by decide
    have htot : Nat.totient 30 = 8 := by decide
    rw [harg, hpi31, htot] at h
    change Nat.primeCounting' (r + 1) ≤ 10 + 8 * ((r - 30) / 30 + 1)
    exact h

/-- Erdős's `3r/8` prime-counting estimate.  The infinite tail follows from the
residue-class estimate modulo `30`; the range `38 ≤ r < 91` is checked directly. -/
theorem primeCounting_le_three_mul_div_eight {r : ℕ} (hr : 38 ≤ r) :
    Nat.primeCounting r ≤ 3 * r / 8 := by
  by_cases h91 : 91 ≤ r
  · exact (primeCounting_le_mod_thirty r).trans (by omega)
  · interval_cases r <;> decide

end Nat.SylvesterSchur
