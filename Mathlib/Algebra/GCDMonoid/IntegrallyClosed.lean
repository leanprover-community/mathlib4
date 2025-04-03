/-
Copyright (c) 2022 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import Mathlib.Algebra.GCDMonoid.Basic
import Mathlib.RingTheory.IntegrallyClosed
import Mathlib.RingTheory.Polynomial.Eisenstein.Basic

#align_import algebra.gcd_monoid.integrally_closed from "leanprover-community/mathlib"@"2032a878972d5672e7c27c957e7a6e297b044973"

/-!

# GCD domains are integrally closed

-/


open scoped Polynomial

variable {R A : Type*} [CommRing R] [IsDomain R] [CommRing A] [Algebra R A]

theorem IsLocalization.surj_of_gcd_domain [GCDMonoid R] (M : Submonoid R) [IsLocalization M A]
    (z : A) : ∃ a b : R, IsUnit (gcd a b) ∧ z * algebraMap R A b = algebraMap R A a := by
  obtain ⟨x, ⟨y, hy⟩, rfl⟩ := IsLocalization.mk'_surjective M z
  obtain ⟨x', y', hx', hy', hu⟩ := extract_gcd x y
  use x', y', hu
  rw [mul_comm, IsLocalization.mul_mk'_eq_mk'_of_mul]
  convert IsLocalization.mk'_mul_cancel_left (M := M) (S := A) _ _ using 2
  rw [Subtype.coe_mk, hy', ← mul_comm y', mul_assoc]; conv_lhs => rw [hx']
#align is_localization.surj_of_gcd_domain IsLocalization.surj_of_gcd_domain

instance (priority := 100) GCDMonoid.toIsIntegrallyClosed
    [h : Nonempty (GCDMonoid R)] : IsIntegrallyClosed R :=
  (isIntegrallyClosed_iff (FractionRing R)).mpr fun {X} ⟨p, hp₁, hp₂⟩ => by
    cases h
    obtain ⟨x, y, hg, he⟩ := IsLocalization.surj_of_gcd_domain (nonZeroDivisors R) X
    have :=
      Polynomial.dvd_pow_natDegree_of_eval₂_eq_zero (IsFractionRing.injective R <| FractionRing R)
        hp₁ y x _ hp₂ (by rw [mul_comm, he])
    have : IsUnit y := by
      rw [isUnit_iff_dvd_one, ← one_pow]
      exact
        (dvd_gcd this <| dvd_refl y).trans
          (gcd_pow_left_dvd_pow_gcd.trans <| pow_dvd_pow_of_dvd (isUnit_iff_dvd_one.1 hg) _)
    use x * (this.unit⁻¹ : _)
    erw [map_mul, ← Units.coe_map_inv, eq_comm, Units.eq_mul_inv_iff_mul_eq]
    exact he
#align gcd_monoid.to_is_integrally_closed GCDMonoid.toIsIntegrallyClosed
