/-
Copyright (c) 2025 Robin Langer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robin Langer
-/
module

public import Mathlib.RingTheory.PowerSeries.WellKnown
public import Mathlib.Data.Nat.Choose.Basic

/-!
# Lah numbers as Jabotinsky matrix entries

The **Lah numbers** `L(n,k) = C(n-1,k-1) · n!/k!` are the change-of-basis
coefficients between rising and falling factorials. They arise as the
normalized Jabotinsky matrix of the geometric delta series `y/(1-y)`.

The raw (unnormalized) Jabotinsky entry is:

  `[yⁿ] (y/(1-y))ᵏ = C(n-1, k-1)`

This is proved by factoring `(y/(1-y))ᵏ = Xᵏ · (mk 1)ᵏ` and using
Mathlib's `mk_one_pow_eq_mk_choose_add` for the negative binomial
coefficients of `(mk 1)ᵏ = (1-X)⁻ᵏ`.

## Main results

* `PowerSeries.coeff_lahSeries_pow_succ`: the Jabotinsky entry (k+1 form)
* `PowerSeries.coeff_lahSeries_pow`: the Jabotinsky entry (k ≥ 1 form)

## References

* Langer, R., *Determinantal bases and the symmetric group*, arXiv:0907.3950, §1.2.2
-/

@[expose] public section

noncomputable section

open PowerSeries

namespace PowerSeries

variable (R : Type*) [CommRing R]

/-- The geometric delta series `y/(1-y) = X · (1-X)⁻¹` as a formal power series. -/
def lahSeries : R⟦X⟧ := X * mk 1

/-- `(y/(1-y))ᵏ = Xᵏ · (mk 1)ᵏ`. -/
theorem lahSeries_pow (k : ℕ) :
    lahSeries R ^ k = X ^ k * (mk 1 : R⟦X⟧) ^ k := by
  rw [lahSeries, mul_pow]

/-- `[yⁿ] (y/(1-y))ᵏ⁺¹ = C(n-1, k)` for `n ≥ k+1`, and `0` for `n < k+1`. -/
theorem coeff_lahSeries_pow_succ (k n : ℕ) :
    coeff n (lahSeries R ^ (k + 1)) =
      if n < k + 1 then 0 else Nat.choose (n - 1) k := by
  rw [lahSeries_pow, mk_one_pow_eq_mk_choose_add, coeff_X_pow_mul']
  by_cases h : k + 1 ≤ n
  · -- n ≥ k+1: the shift gives coeff (n-k-1) = C(k + (n-k-1), k) = C(n-1, k)
    rw [if_pos h, if_neg (by omega), coeff_mk]
    have : k + (n - (k + 1)) = n - 1 := by omega
    rw [this]
  · -- n < k+1: the X^{k+1} factor kills the coefficient
    rw [if_neg h, if_pos (by omega)]
    simp

/-- **Jabotinsky entry for Lah numbers**: `[yⁿ] (y/(1-y))ᵏ = C(n-1, k-1)`
for `k ≥ 1`. The normalized entry `n!/k! · C(n-1, k-1)` is the unsigned
Lah number `L(n,k)`. -/
theorem coeff_lahSeries_pow {k : ℕ} (hk : 1 ≤ k) (n : ℕ) :
    coeff n (lahSeries R ^ k) =
      if n < k then 0 else Nat.choose (n - 1) (k - 1) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
  exact coeff_lahSeries_pow_succ R k n

end PowerSeries

end
