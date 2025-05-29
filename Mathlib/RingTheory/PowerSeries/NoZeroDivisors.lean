/-
Copyright (c) 2019 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Kenny Lau
-/
import Mathlib.RingTheory.PowerSeries.Order
import Mathlib.RingTheory.Ideal.Maps

/-!
# Power series over rings with no zero divisors

This file proves, using the properties of orders of power series,
that `R⟦X⟧` is an integral domain when `R` is.

We then state various results about `R⟦X⟧` with `R` an integral domain.

##  Instance

If `R` has `NoZeroDivisors`, then so does `R⟦X⟧`.

-/


variable {R : Type*}

namespace PowerSeries

section NoZeroDivisors

variable [Semiring R]

instance [NoZeroDivisors R] : NoZeroDivisors R⟦X⟧ where
  eq_zero_or_eq_zero_of_mul_eq_zero {φ ψ} h := by
    simp_rw [← order_eq_top, order_mul] at h ⊢
    exact WithTop.add_eq_top.mp h

end NoZeroDivisors

section IsDomain

instance [Ring R] [IsDomain R] : IsDomain R⟦X⟧ :=
  NoZeroDivisors.to_isDomain _

variable [CommRing R] [IsDomain R]

/-- The ideal spanned by the variable in the power series ring
over an integral domain is a prime ideal. -/
theorem span_X_isPrime : (Ideal.span ({X} : Set R⟦X⟧)).IsPrime := by
  suffices Ideal.span ({X} : Set R⟦X⟧) = RingHom.ker (constantCoeff R) by
    rw [this]
    exact RingHom.ker_isPrime _
  apply Ideal.ext
  intro φ
  rw [RingHom.mem_ker, Ideal.mem_span_singleton, X_dvd_iff]

/-- The variable of the power series ring over an integral domain is prime. -/
theorem X_prime : Prime (X : R⟦X⟧) := by
  rw [← Ideal.span_singleton_prime]
  · exact span_X_isPrime
  · intro h
    simpa [map_zero (coeff R 1)] using congr_arg (coeff R 1) h

/-- The variable of the power series ring over an integral domain is irreducible. -/
theorem X_irreducible : Irreducible (X : R⟦X⟧) := X_prime.irreducible

theorem rescale_injective {a : R} (ha : a ≠ 0) : Function.Injective (rescale a) := by
  intro p q h
  rw [PowerSeries.ext_iff] at *
  intro n
  specialize h n
  rwa [coeff_rescale, coeff_rescale, mul_right_inj' <| pow_ne_zero _ ha] at h

end IsDomain

end PowerSeries
