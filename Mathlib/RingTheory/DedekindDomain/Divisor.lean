/-
Copyright (c) 2026 Guanghao Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Guanghao Li
-/
module

public import Mathlib.RingTheory.DedekindDomain.Factorization

/-!
# Divisors of a Dedekind domain

This file identifies the group of nonzero fractional ideals of a Dedekind domain with the free
abelian group on its height-one prime ideals. The coefficient of a prime `v` is the existing
function `FractionalIdeal.count K v`. This formal-sum model exposes addition and coefficients
directly, while `FractionalIdeal.divisorEquiv` connects it to multiplicative fractional ideals.

## Main definitions

* `IsDedekindDomain.Divisor`: the free abelian group on height-one prime ideals.
* `FractionalIdeal.divisor`: the divisor associated to a nonzero fractional ideal.
* `FractionalIdeal.divisorEquiv`: the additive equivalence between nonzero fractional ideals and
  divisors.
-/

@[expose] public section

open IsDedekindDomain
open scoped nonZeroDivisors

namespace IsDedekindDomain

/-- The group of divisors supported on height-one prime ideals of a ring. -/
abbrev Divisor (R : Type*) [CommRing R] := HeightOneSpectrum R →₀ ℤ

end IsDedekindDomain

namespace FractionalIdeal

variable {R K : Type*} [CommRing R] [IsDedekindDomain R] [Field K]
  [Algebra R K] [IsFractionRing R K]

/-- The divisor of a nonzero fractional ideal. -/
noncomputable def divisor (I : (FractionalIdeal R⁰ K)ˣ) : Divisor R :=
  Finsupp.mk (finite_factors (I : FractionalIdeal R⁰ K)).toFinset
    (fun v ↦ count K v I) fun _ ↦ (finite_factors (I : FractionalIdeal R⁰ K)).mem_toFinset

@[simp]
theorem divisor_apply (I : (FractionalIdeal R⁰ K)ˣ) (v : HeightOneSpectrum R) :
    divisor I v = count K v I := by
  classical
  simp [divisor]

/-- Reconstruct a nonzero fractional ideal from a divisor. -/
noncomputable def ofDivisor (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K]
    (D : Divisor R) : (FractionalIdeal R⁰ K)ˣ :=
  Units.mk0 (D.prod fun v n ↦ (v.asIdeal : FractionalIdeal R⁰ K) ^ n) <| by
    classical
    rw [Finsupp.prod]
    exact Finset.prod_ne_zero_iff.mpr fun v _ ↦
      zpow_ne_zero _ (coeIdeal_ne_zero.mpr v.ne_bot)

@[simp]
theorem count_ofDivisor (D : Divisor R) (v : HeightOneSpectrum R) :
    count K v (ofDivisor K D : FractionalIdeal R⁰ K) = D v := by
  classical
  simpa [ofDivisor] using count_finsuppProd K v D

private theorem eq_of_count_eq {I J : FractionalIdeal R⁰ K} (hI : I ≠ 0) (hJ : J ≠ 0)
    (h : ∀ v, count K v I = count K v J) : I = J := by
  rw [← finprod_heightOneSpectrum_factorization' K hI,
    ← finprod_heightOneSpectrum_factorization' K hJ]
  exact finprod_congr fun v ↦ congr_arg ((v.asIdeal : FractionalIdeal R⁰ K) ^ ·) (h v)

/-- Nonzero fractional ideals of a Dedekind domain are additively equivalent to its divisors.

Multiplication of fractional ideals corresponds to addition of divisors.
-/
noncomputable def divisorEquiv : Additive (FractionalIdeal R⁰ K)ˣ ≃+ Divisor R where
  toFun I := divisor I.toMul
  invFun D := Additive.ofMul (ofDivisor K D)
  left_inv I := by
    apply Additive.toMul.injective
    apply Units.ext
    change (ofDivisor K (divisor I.toMul) : FractionalIdeal R⁰ K) = I.toMul
    apply eq_of_count_eq (ofDivisor K (divisor I.toMul)).ne_zero I.toMul.ne_zero
    intro v
    rw [count_ofDivisor, divisor_apply]
  right_inv D := by
    ext v
    change count K v (ofDivisor K D : FractionalIdeal R⁰ K) = D v
    rw [count_ofDivisor]
  map_add' I J := by
    change divisor (I.toMul * J.toMul) = divisor I.toMul + divisor J.toMul
    ext v
    simp only [divisor_apply, Units.val_mul]
    exact count_mul K v I.toMul.ne_zero J.toMul.ne_zero

end FractionalIdeal
