/-
Copyright (c) 2025 Xavier Roblot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Roblot
-/
import Mathlib.NumberTheory.KummerDedekind
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.Ideal.Norm.AbsNorm

/-!
# Kummer-Dedekind criterion for the splitting of prime numbers

In this file, we give a specialized version of the Kummer-Dedekind criterion for the case of the
splitting of rational primes in number fields.

## Main definitions

## Main results

-/

noncomputable section

open Ideal NumberField

variable {K : Type*} [Field K]


namespace RingOfIntegers

/-
The smallest positive integer `d` such that `d • 𝓞 K ⊆ ℤ[θ]`. It is equal to `0` if `d` does not
exists.
-/
def exponent (θ : 𝓞 K) : ℕ := absNorm (under ℤ (conductor ℤ θ))

variable {θ : 𝓞 K}

theorem exponent_eq_one_iff :
    exponent θ = 1 ↔ Algebra.adjoin ℤ {θ} = ⊤ := by
  rw [exponent, absNorm_eq_one_iff, comap_eq_top_iff, conductor_eq_top_iff_adjoin_eq_top]

theorem not_dvd_exponent_iff {p : ℕ} :
    ¬ p ∣ exponent θ ↔ comap (algebraMap ℤ (𝓞 K)) (conductor ℤ θ) ⊔ span {(p : ℤ)} = ⊤ := by
  rw [sup_comm, IsCoatom.sup_eq_top_iff, ← under_def, ← Ideal.dvd_iff_le,
    Int.ideal_eq_span_absNorm_self (under ℤ (conductor ℤ θ)),
    span_singleton_dvd_span_singleton_iff_dvd, Int.natCast_dvd_natCast, exponent]
  refine isMaximal_def.mp <| Int.ideal_span_isMaximal_of_prime p

end RingOfIntegers
